(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Generation for Basic Matrix Operations\<close>

text \<open>In this theory we provide efficient implementations
  for the elementary row-transformations. These are necessary since the default
  implementations would construct a whole new matrix in every step.\<close>

theory Gauss_Jordan_IArray_Impl
imports 
  "../Polynomial_Interpolation/Missing_Unsorted"
  Matrix_IArray_Impl
  Gauss_Jordan
begin

lift_definition mat_swaprows_impl :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat_impl \<Rightarrow> 'a mat_impl" is
  "\<lambda> i j (nr,nc,A). if i < nr \<and> j < nr then 
  let Ai = IArray.sub A i; 
      Aj = IArray.sub A j;
      Arows = IArray.list_of A;
      A' = IArray.IArray (Arows [i := Aj, j := Ai])  
   in (nr,nc,A')
     else (nr,nc,A)" 
proof (auto split: if_splits, goal_cases)
  case (1 i j A nc row)
  thus ?case by (cases A, auto)
qed

lemma [code]: "mat_swaprows k l (mat_impl A) = (let nr = mat_dim_row_impl A in
  if l < nr \<and> k < nr then 
  mat_impl (mat_swaprows_impl k l A) else Code.abort (STR ''index out of bounds in mat_swaprows'') 
  (\<lambda> _. mat_swaprows k l (mat_impl A)))" (is "?l = ?r")
proof (cases "l < mat_dim_row_impl A \<and> k < mat_dim_row_impl A")
  case True
  hence id: "?r = mat_impl (mat_swaprows_impl k l A)" by simp
  show ?thesis unfolding id unfolding mat_swaprows_def
  proof (rule mat_eqI, goal_cases)
    case (1 i j)
    thus ?case using True
    proof (transfer, goal_cases)
      case (1 i k l A j)
      obtain nr nc rows where A: "A = (nr,nc,rows)" by (cases A, auto)
      from 1[unfolded A]
      have nr: "length (IArray.list_of rows) = nr"
        and nc: "IArray.all (\<lambda>r. length (IArray.list_of r) = nc) rows"
        and ij: "i < nr" "j < nc" and ij': "(i < nr \<and> j < nc) = True" 
        and l: "l < nr" "k < nr" by auto
      show ?case unfolding A prod.simps fst_conv o_def snd_conv Let_def mk_mat_def ij' if_True
        using ij nr nc l
        by (cases "k = i"; cases "l = i", auto)
    qed
  qed ((transfer, auto)+)
qed auto


lift_definition mat_multrow_gen_impl :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a mat_impl \<Rightarrow> 'a mat_impl" is
  "\<lambda> mul k a (nr,nc,A). let Ak = IArray.sub A k; Arows = IArray.list_of A;
     Ak' = IArray.IArray (map (mul a) (IArray.list_of Ak));
     A' = IArray.IArray (Arows [k := Ak'])
     in (nr,nc,A')" 
proof (auto, goal_cases)
  case (1 mul k a nc b row)
  show ?case 
  proof (cases b)
    case (IArray rows)
    with 1 have "row \<in> set rows \<or> k < length rows \<and> row = IArray (map (mul a) (IArray.list_of (rows ! k)))"
      by (cases "k < length rows", auto simp: set_list_update dest: in_set_takeD in_set_dropD)
    with 1 IArray show ?thesis by (cases, auto)
  qed
qed

lemma [code]: "mat_multrow_gen mul k a (mat_impl A) = mat_impl (mat_multrow_gen_impl mul k a A)"
  unfolding mat_multrow_gen_def
proof (rule mat_eqI, goal_cases)
  case (1 i j)
  thus ?case 
  proof (transfer, goal_cases)
    case (1 i mul k a A j)
    obtain nr nc rows where A: "A = (nr,nc,rows)" by (cases A, auto)
    from 1[unfolded A]
    have nr: "length (IArray.list_of rows) = nr"
      and nc: "IArray.all (\<lambda>r. length (IArray.list_of r) = nc) rows"
      and ij: "i < nr" "j < nc" and ij': "(i < nr \<and> j < nc) = True" by auto
    have len: "j < length (IArray.list_of (IArray.list_of rows ! i))"
      using ij nc nr by (cases rows, auto)
    show ?case unfolding A prod.simps fst_conv o_def snd_conv Let_def mk_mat_def ij' if_True
      using ij nr nc 
      by (cases "k = i", auto simp: len)
  qed
qed ((transfer, auto)+)

lift_definition mat_addrow_gen_impl 
  :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat_impl \<Rightarrow> 'a mat_impl" is
  "\<lambda> ad mul a k l (nr,nc,A). if l < nr then let Ak = IArray.sub A k; Al = IArray.sub A l; Arows = IArray.list_of A;
     Ak' = IArray.IArray (map (\<lambda> (al,ak). ad (mul a al) ak) (zip (IArray.list_of Al) (IArray.list_of Ak)));
     A' = IArray.IArray (Arows [k := Ak'])
     in (nr,nc,A') else (nr,nc,A)" 
proof (goal_cases)
  case (1 ad mul a k l pp)
  obtain nr nc A where pp: "pp = (nr,nc,A)" by (cases pp)
  obtain rows where A: "A = IArray rows" by (cases A)
  from 1[unfolded pp A, simplified]
  have nr: "length rows = nr" and nc: "\<And> r. r\<in>set rows \<Longrightarrow> length (IArray.list_of r) = nc" by auto  
  show ?case 
  proof (cases "l < nr")
    case False
    thus ?thesis unfolding pp A prod.simps using nr nc by auto
  next
    case True    
    thus ?thesis unfolding pp A prod.simps Let_def using nr nc
      by (auto simp: set_list_update dest: in_set_takeD in_set_dropD)
  qed
qed

lemma [code]: "mat_addrow_gen ad mul a k l (mat_impl A) = (if l < mat_dim_row_impl A then
  mat_impl (mat_addrow_gen_impl ad mul a k l A) else Code.abort (STR ''index out of bounds in mat_addrow'') 
  (\<lambda> _. mat_addrow_gen ad mul a k l (mat_impl A)))" (is "?l = ?r")
proof (cases "l < mat_dim_row_impl A")
  case True
  hence id: "?r = mat_impl (mat_addrow_gen_impl ad mul a k l A)" by simp
  show ?thesis unfolding id unfolding mat_addrow_gen_def
  proof (rule mat_eqI, goal_cases)
    case (1 i j)
    thus ?case using True
    proof (transfer, goal_cases)
      case (1 i ad mul a k l A j)
      obtain nr nc rows where A: "A = (nr,nc,rows)" by (cases A, auto)
      from 1[unfolded A]
      have nr: "length (IArray.list_of rows) = nr"
        and nc: "IArray.all (\<lambda>r. length (IArray.list_of r) = nc) rows"
        and ij: "i < nr" "j < nc" and ij': "(i < nr \<and> j < nc) = True" 
        and l: "l < nr" by auto
      have len: "j < length (IArray.list_of (IArray.list_of rows ! i))"
        "j < length (IArray.list_of (IArray.list_of rows ! l))"
        using ij nc nr l by (cases rows, auto)+
      show ?case unfolding A prod.simps fst_conv o_def snd_conv Let_def mk_mat_def ij' if_True
        using ij nr nc l
        by (cases "k = i", auto simp: len)
    qed
  qed ((transfer, auto)+)
qed simp

end
