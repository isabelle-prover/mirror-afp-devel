(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Generation for Basic Matrix Operations\<close>

text \<open>In this theory we implement matrices as arrays of arrays.
  Due to the target language serialization, access to matrix
  entries should be constant time. Hence operations like
  matrix addition, multiplication, etc.~should all have their 
  standard complexity. 

  There might be room for optimizations.\<close>

theory Matrix_IArray_Impl
imports
  Matrix
  "HOL-Library.IArray"
begin

typedef 'a vec_impl = "{(n,v :: 'a iarray). IArray.length v = n}" by auto
typedef 'a mat_impl = "{(nr,nc,m :: 'a iarray iarray). 
  IArray.length m = nr \<and> IArray.all (\<lambda> r. IArray.length r = nc) m}" 
  by (rule exI[of _ "(0,0,IArray [])"], auto)

setup_lifting type_definition_vec_impl
setup_lifting type_definition_mat_impl

lift_definition vec_impl :: "'a vec_impl \<Rightarrow> 'a vec" is
  "\<lambda> (n,v). (n,mk_vec n (IArray.sub v))" by auto

lift_definition vec_add_impl :: "'a::plus vec_impl \<Rightarrow> 'a vec_impl \<Rightarrow> 'a vec_impl" is
  "\<lambda> (n,v) (m,w).
  (n, IArray.of_fun (\<lambda>i. IArray.sub v i + IArray.sub w i) n)"
by auto

lift_definition mat_impl :: "'a mat_impl \<Rightarrow> 'a mat" is
  "\<lambda> (nr,nc,m). (nr,nc,mk_mat nr nc (\<lambda> (i,j). IArray.sub (IArray.sub m i) j))" by auto

lift_definition vec_of_list_impl :: "'a list \<Rightarrow> 'a vec_impl" is
  "\<lambda> v. (length v, IArray v)" by auto

lift_definition list_of_vec_impl :: "'a vec_impl \<Rightarrow> 'a list" is
  "\<lambda> (n,v). IArray.list_of v" .
  
lift_definition vec_of_fun :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vec_impl" is
  "\<lambda> n f. (n, IArray.of_fun f n)" by auto

lift_definition mat_of_fun :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> 'a mat_impl" is
  "\<lambda> nr nc f. (nr, nc, IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. f (i,j)) nc) nr)" by auto

lift_definition vec_index_impl :: "'a vec_impl \<Rightarrow> nat \<Rightarrow> 'a"
  is "\<lambda> (n,v). IArray.sub v" .

lift_definition index_mat_impl :: "'a mat_impl \<Rightarrow> nat \<times> nat \<Rightarrow> 'a"
  is "\<lambda> (nr,nc,m) (i,j). if i < nr then IArray.sub (IArray.sub m i) j 
    else IArray.sub (IArray ([] ! (i - nr))) j" .

lift_definition vec_equal_impl :: "'a vec_impl \<Rightarrow> 'a vec_impl \<Rightarrow> bool"
  is "\<lambda> (n1,v1) (n2,v2). n1 = n2 \<and> v1 = v2" .

lift_definition mat_equal_impl :: "'a mat_impl \<Rightarrow> 'a mat_impl \<Rightarrow> bool"
  is "\<lambda> (nr1,nc1,m1) (nr2,nc2,m2). nr1 = nr2 \<and> nc1 = nc2 \<and> m1 = m2" .

lift_definition dim_vec_impl :: "'a vec_impl \<Rightarrow> nat" is fst .

lift_definition dim_row_impl :: "'a mat_impl \<Rightarrow> nat" is fst .
lift_definition dim_col_impl :: "'a mat_impl \<Rightarrow> nat" is "fst o snd" .

code_datatype vec_impl
code_datatype mat_impl

lemma vec_code[code]: "vec n f = vec_impl (vec_of_fun n f)"
  by (transfer, auto simp: mk_vec_def)

lemma mat_code[code]: "mat nr nc f = mat_impl (mat_of_fun nr nc f)"
  by (transfer, auto simp: mk_mat_def, intro ext, clarsimp, 
  auto intro: undef_cong_mat)

lemma vec_of_list[code]: "vec_of_list v = vec_impl (vec_of_list_impl v)"
  by (transfer, auto simp: mk_vec_def)

lemma list_of_vec_code[code]: "list_of_vec (vec_impl v) = list_of_vec_impl v"
  by (transfer, auto simp: mk_vec_def, case_tac b, auto intro: nth_equalityI)

lemma empty_nth: "\<not> i < length x \<Longrightarrow> x ! i = [] ! (i - length x)"
  by (metis append_Nil2 nth_append)

lemma undef_vec: "\<not> i < length x \<Longrightarrow> undef_vec (i - length x) = x ! i"
  unfolding undef_vec_def by (rule empty_nth[symmetric])
  
lemma vec_index_code[code]: "(vec_impl v) $ i = vec_index_impl v i"
  by (transfer, auto simp: mk_vec_def, case_tac b, auto simp: undef_vec)

lemma index_mat_code[code]: "(mat_impl m) $$ ij = (index_mat_impl m ij :: 'a)"
proof (transfer, unfold o_def, clarify)
  fix m :: "'a iarray iarray" and i j nc
  assume all: "IArray.all (\<lambda>r. IArray.length r = nc) m"
  obtain mm where m: "m = IArray mm" by (cases m)
  with all have all: "\<And> v. v \<in> set mm \<Longrightarrow> IArray.length v = nc" by auto
  show "snd (snd (IArray.length m, nc, mk_mat (IArray.length m) nc (\<lambda>(i, y). m !! i !! y))) (i, j) =
     (if i < IArray.length m then m !! i !! j
        else IArray ([] ! (i - IArray.length m)) !! j)" (is "?l = ?r")
  proof (cases "i < length mm")
    case False
    hence "\<And> f. \<not> i < length (map f [0..<length mm])" by simp
    note [simp] = empty_nth[OF this]
    have "?l = [] ! (i - length mm) ! j" using False unfolding m mk_mat_def undef_mat_def by simp
    also have "\<dots> = ?r" unfolding m by (simp add: False empty_nth[OF False])
    finally show ?thesis .
  next
    case True
    obtain v where mm: "mm ! i = IArray v" by (cases "mm ! i")
    with True all[of "mm ! i"] have len: "length v = nc" unfolding set_conv_nth by force
    from mm True have "?l = map ((!) v) [0..<nc] ! j" (is "_ = ?m") unfolding m mk_mat_def undef_mat_def by simp
    also have "?m = m !! i !! j"
    proof (cases "j < length v")
      case True
      thus ?thesis unfolding m using mm len by auto
    next
      case False
      hence j: "\<not> j < length (map ((!) v) [0..<length v])" by simp
      show ?thesis unfolding m using mm len by (auto simp: empty_nth[OF j] empty_nth[OF False])
    qed
    also have "\<dots> = ?r" using True m by simp
    finally show ?thesis .
  qed
qed

lift_definition (code_dt) mat_of_rows_list_impl :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat_impl option" is
  "\<lambda> n rows. if list_all (\<lambda> r. length r = n) rows then Some (length rows, n, IArray (map IArray rows)) 
  else None" 
  by (auto split: if_splits simp: list_all_iff)

lemma mat_of_rows_list_impl: "mat_of_rows_list_impl n rs = Some A \<Longrightarrow> mat_impl A = mat_of_rows_list n rs" 
  unfolding mat_of_rows_list_def
  by (transfer, auto split: if_splits simp: list_all_iff intro!: cong_mk_mat)
  
lemma mat_of_rows_list_code[code]: "mat_of_rows_list nc vs = 
  (case mat_of_rows_list_impl nc vs of Some A \<Rightarrow> mat_impl A 
  | None \<Rightarrow> mat_of_rows nc (map (\<lambda> v. vec nc (nth v)) vs))"
proof (cases "mat_of_rows_list_impl nc vs")
  case (Some A)
  from mat_of_rows_list_impl[OF this] show ?thesis unfolding Some by simp
next
  case None
  show ?thesis unfolding None unfolding mat_of_rows_list_def mat_of_rows_def
    by (intro eq_matI, auto)  
qed

lemma dim_vec_code[code]: "dim_vec (vec_impl v) = dim_vec_impl v"
  by (transfer, auto)

lemma dim_row_code[code]: "dim_row (mat_impl m) = dim_row_impl m"
  by (transfer, auto)

lemma dim_col_code[code]: "dim_col (mat_impl m) = dim_col_impl m"
  by (transfer, auto)

context
begin

private lemma aux:
  \<open>length (IArray.list_of xs) = m\<close>
    if len: \<open>\<And>xs. xs \<in> set (IArray.list_of ys) \<Longrightarrow> length (IArray.list_of xs) = m\<close>
      and upd: \<open>xs \<in> set ((IArray.list_of ys) [n := IArray (map2 f [0..<m] (IArray.list_of (IArray.list_of ys ! n)))])\<close>
    for xs ys and f :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close> and m n
proof (cases \<open>n < length (IArray.list_of ys)\<close>)
  case False
  with len upd show ?thesis
    by (simp add: list_update_beyond)
next
  case True
  moreover have *: \<open>xs \<in> set (IArray.list_of ys) \<longleftrightarrow>
    xs \<in> set (take n (IArray.list_of ys) @ IArray.list_of ys ! n # drop (Suc n) (IArray.list_of ys))\<close>
    for xs
    using \<open>n < length (IArray.list_of ys)\<close> by (simp flip: id_take_nth_drop)
  ultimately show ?thesis
    using len upd by (auto simp add: set_list_update *)
qed

lift_definition change_row_impl :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat_impl \<Rightarrow> 'a mat_impl" is
  "\<lambda>k f (nr, nc, A). let Ak = IArray.sub A k; Arows = IArray.list_of A;
     Ak' = IArray.IArray (map (\<lambda> (i,c). f i c) (zip [0 ..< nc] (IArray.list_of Ak)));
     A' = IArray.IArray (Arows [k := Ak'])
     in (nr, nc, A')"
  by (auto intro: aux)

end

lemma change_row_code [code]:
  "change_row k f (mat_impl A) = (if k < dim_row_impl A
  then mat_impl (change_row_impl k f A)
  else Code.abort (STR ''index out of bounds in change_row'') (\<lambda> _. change_row k f (mat_impl A)))"
  (is "?lhs = ?rhs")
proof (cases \<open>k < dim_row_impl A\<close>)
  case False
  then show ?thesis
    by simp
next
  case True
  have \<open>?lhs = mat (dim_row (mat_impl A)) (dim_col (mat_impl A))
     (\<lambda>(i, j).
         if i = k then f j (mat_impl A $$ (k, j))
         else mat_impl A $$ (i, j))\<close>
    by (simp add: change_row_def)
  also have \<open>\<dots> = mat_impl (change_row_impl k f A)\<close>
    by (rule eq_matI; transfer) (auto simp add: mk_mat_def)
  finally show ?thesis
    by simp
qed

instantiation vec :: (type)equal
begin
  definition "(equal_vec :: ('a vec \<Rightarrow> 'a vec \<Rightarrow> bool)) = (=)"
instance
  by (intro_classes, auto simp: equal_vec_def)
end

instantiation mat :: (type)equal
begin
  definition "(equal_mat :: ('a mat \<Rightarrow> 'a mat \<Rightarrow> bool)) = (=)"
instance
  by (intro_classes, auto simp: equal_mat_def)
end

lemma veq_equal_code[code]: "HOL.equal (vec_impl (v1 :: 'a vec_impl)) (vec_impl v2) = vec_equal_impl v1 v2"
proof - 
  {
    fix x1 x2 :: "'a list"
    assume len: "length x1 = length x2"
       and index: "(\<lambda>i. if i < length x2 then IArray x1 !! i else undef_vec (i - length (IArray.list_of (IArray x1)))) =
            (\<lambda>i. if i < length x2 then IArray x2 !! i else undef_vec (i - length (IArray.list_of (IArray x2))))"    
    have "x1 = x2"
    proof (intro nth_equalityI[OF len])
      fix i
      assume "i < length x1"
      with fun_cong[OF index, of i] len show "x1 ! i = x2 ! i" by simp
    qed
  } note * = this
  show ?thesis unfolding equal_vec_def
    by (transfer, insert *, auto simp: mk_vec_def, case_tac b, case_tac ba, auto)
qed

lemma mat_equal_code[code]: "HOL.equal (mat_impl (m1 :: 'a mat_impl)) (mat_impl m2) = mat_equal_impl m1 m2"
proof - 
  show ?thesis unfolding equal_mat_def
  proof (transfer, auto, case_tac b, case_tac ba, auto)
    fix x1 x2 :: "'a iarray list" and nc
    assume len: "\<forall>r\<in>set x1. length (IArray.list_of r) = nc"
      "\<forall>r\<in>set x2. length (IArray.list_of r) = nc"
      "length x1 = length x2"
    and index: "mk_mat (length x2) nc (\<lambda>(i, j). x1 ! i !! j) = mk_mat (length x2) nc (\<lambda>(i, j). x2 ! i !! j)"
    show "x1 = x2"
    proof (rule nth_equalityI[OF len(3)])
      fix i
      assume i: "i < length x1"
      obtain ia1 where 1: "x1 ! i = IArray ia1" by (cases "x1 ! i")
      obtain ia2 where 2: "x2 ! i = IArray ia2" by (cases "x2 ! i")
      from i 1 len(1) have l1: "length ia1 = nc" using nth_mem by fastforce
      from i 2 len(2-3) have l2: "length ia2 = nc" using nth_mem by fastforce
      from l1 l2 have l: "length ia1 = length ia2" by simp
      show "x1 ! i = x2 ! i" unfolding 1 2
      proof (simp, rule nth_equalityI[OF l])
        fix j
        assume j: "j < length ia1"
        with fun_cong[OF index, of "(i,j)"] i len(3)
        have "x1 ! i !! j = x2 ! i !! j"
          by (simp add: mk_mat_def l1)
        thus "ia1 ! j = ia2 ! j" unfolding 1 2 by simp
      qed
    qed
  qed
qed


partial_function (tailrec) scalar_prod_main where 
  [code]: "scalar_prod_main (n :: integer) v w i (s :: 'a :: semiring_0) = (if i = n then s else
     scalar_prod_main n v w (i+1) (s + v i * w i))" 

definition "scalar_prod_gen n v w = scalar_prod_main n v w 0 0" 

lemma scalar_prod_gen: "scalar_prod_gen (integer_of_nat n) v w = (\<Sum>i = 0..<n. (v (integer_of_nat i) * w (integer_of_nat i)))" 
proof -
  define p where "p i = v (integer_of_nat i) * w (integer_of_nat i)" for i
  define s :: 'a where "s = 0" 
  define m :: nat where "m = 0" 
  have mn: "m \<le> n" unfolding m_def by auto
  have "scalar_prod_gen (integer_of_nat n) v w = scalar_prod_main (integer_of_nat n) v w (integer_of_nat m) s" 
    unfolding scalar_prod_gen_def m_def s_def by (simp add: integer_of_nat_0)
  also have "\<dots> = s + (\<Sum>i = m..<n. p i)" using mn
  proof (induct "n - m" arbitrary: s m)
    case 0
    hence id: "m = n" by simp
    show ?case unfolding id scalar_prod_main.simps[of _ _ _"integer_of_nat n"] by simp
  next
    case (Suc d m s)
    hence "m \<noteq> n" by auto
    hence diff: "(integer_of_nat m = integer_of_nat n) = False" 
      by (simp add: integer_of_nat_eq_of_nat)
    from Suc have mn: "m < n" by auto
    hence "(\<Sum>i = m..<n. p i) = (p m + (\<Sum>i = Suc m..<n. p i))"         
      by (meson sum.atLeast_Suc_lessThan)
    also have "s + \<dots> = (s + p m) + (\<Sum>i = Suc m..<n. p i)" by (simp add: ac_simps)
    also have "\<dots> = scalar_prod_main (integer_of_nat n) v w (integer_of_nat (Suc m)) (s + p m)"
      by (subst Suc(1), insert Suc(2-), auto)
    also have "integer_of_nat (Suc m) = integer_of_nat m + 1"
      by (simp add: integer_of_nat_eq_of_nat)
    finally have id: "s + sum p {m..<n} = scalar_prod_main (integer_of_nat n) v w (integer_of_nat m + 1)  (s + p m)" .
    show ?case unfolding id scalar_prod_main.simps[of _ _ _ "integer_of_nat m"] diff if_False
      by (rule arg_cong[of _ _ "\<lambda> x. scalar_prod_main _ _ _ _ (_ + x)"], auto simp: p_def)
  qed
  finally show ?thesis unfolding p_def s_def m_def by simp
qed

lift_definition scalar_prod_impl :: "'a vec_impl \<Rightarrow> 'a vec_impl \<Rightarrow> 'a :: semiring_0" is 
  "\<lambda> (n,v) (n',w). scalar_prod_gen (integer_of_nat n) (\<lambda> i. IArray.sub' (v, i)) (\<lambda> i. IArray.sub' (w,i))" .

lemma scalar_prod_impl[code]: "scalar_prod (vec_impl v) (vec_impl w) = (if dim_vec_impl v = dim_vec_impl w then
   scalar_prod_impl v w else Code.abort (STR ''scalar-prod on vectors of different dimension'') 
      (\<lambda> _. scalar_prod (vec_impl v) (vec_impl w)))" 
proof (cases "dim_vec_impl v = dim_vec_impl w")
  case True
  hence id: "(dim_vec_impl v = dim_vec_impl w) = True" by simp
  show ?thesis unfolding id if_True scalar_prod_def using True
  proof (transfer, goal_cases)
    case (1 nv nw)
    then obtain v w :: "'a iarray" and n where 
      nv: "nv = (n,v)" "nw = (n,w)" and len: "IArray.length v = n" "IArray.length w = n"
      by (cases nv, cases nw, auto)
    show ?case unfolding nv split fst_conv snd_conv
      by (subst scalar_prod_gen, rule sum.cong) (auto simp: mk_vec_def)
  qed
qed auto

partial_function (tailrec) upt_integer_main :: "integer list \<Rightarrow> integer \<Rightarrow> integer list" where
  [code]: "upt_integer_main xs x = (if x = 0 then 0 # xs else upt_integer_main (x # xs) (x - 1))"

definition "upt_integer x = (if x = 0 then [] else upt_integer_main [] (x - 1))" 

fun scalar_prod_list_main :: "'a :: semiring_0 \<Rightarrow> _" where 
  "scalar_prod_list_main s (x # xs) (y # ys) = scalar_prod_list_main (s + x * y) xs ys" 
| "scalar_prod_list_main s _ _ = s" 

definition "scalar_prod_list = scalar_prod_list_main 0" 

lemma scalar_prod_list: "scalar_prod_list (map f [m..<n]) (map g [m..<n])
   = (\<Sum>i = m..<n. f i * g i)"
proof -
  have id: "scalar_prod_list_main s (map f xs) (map g xs)
    = s + (\<Sum>i \<in> set xs. f i * g i)" if "distinct xs" for s xs 
    using that
  proof (induct xs arbitrary: s)
    case (Cons x xs s)
    from Cons(2) have d: "distinct xs" and x: "x \<notin> set xs" by auto
    show ?case unfolding list.simps scalar_prod_list_main.simps Cons(1)[OF d]
      using x by (auto simp: ac_simps)
  qed auto
  show ?thesis unfolding scalar_prod_list_def 
    by (subst id, auto)
qed

lemma upt_integer[simp]: "upt_integer (integer_of_nat n) = map integer_of_nat [0..< n]"
proof (cases n)
  case 0
  thus ?thesis unfolding upt_integer_def by (simp add: integer_of_nat_0)
next
  case (Suc m)
  hence m: "m < n" by auto
  have "1 + of_nat m > (0 :: integer)"
    by (simp add: add_pos_nonneg)
  hence "upt_integer (integer_of_nat n) = upt_integer_main (map integer_of_nat [Suc m..< n]) (integer_of_nat m)"
    unfolding upt_integer_def using Suc by (simp add: integer_of_nat_eq_of_nat)
  also have "\<dots> = map integer_of_nat [0..<n]" using m 
  proof (induct m)
    case 0
    hence "[0..<n] = 0 # [Suc 0..<n]" by (rule upt_conv_Cons)
    thus ?case unfolding integer_of_nat_0 upt_integer_main.simps[of _ 0]
      by (simp add: integer_of_nat_0)
  next
    case (Suc x)
    have id: "integer_of_nat (Suc x) = integer_of_nat x + 1" 
      by (simp add: integer_of_nat_eq_of_nat)
    have id2: "(integer_of_nat x + 1 = 0) = False"
      by (metis integer_of_nat_eq_of_nat local.id nat.discI of_nat_eq_0_iff)
    from Suc have "x < n" by auto
    show ?case unfolding id id2 upt_integer_main.simps[of _ "integer_of_nat x + 1"] if_False
    proof (subst Suc(1)[symmetric, OF \<open>x < n\<close>], rule arg_cong2[of _ _ _ _ upt_integer_main])
      show "(integer_of_nat x + 1) # map integer_of_nat [Suc (Suc x)..<n] = map integer_of_nat [Suc x..<n]" 
        by (simp add: Suc id upt_conv_Cons)
    qed auto
  qed
  finally show ?thesis .
qed

lift_definition times_mat_impl :: "'a mat_impl \<Rightarrow> 'a mat_impl \<Rightarrow> 'a :: semiring_0 mat_impl" is
  "\<lambda> (nr,n,a) (n',nc,b). let 
        nri = integer_of_nat nr; 
        ni = integer_of_nat n;
        nci = integer_of_nat nc;
        n_idx = upt_integer ni;
        a_list = IArray.tabulate (nri, (\<lambda> i. let row_i = IArray.sub' (a,i)
           in map (\<lambda> j. IArray.sub' (row_i,j)) n_idx));
        b_transpose_list = IArray.tabulate (nci, (\<lambda> j. 
           map (\<lambda> i. IArray.sub' (IArray.sub' (b,i), j)) n_idx))
      in (nr,nc, IArray.tabulate (nri, (\<lambda> i. 
        let a_row_i = IArray.sub' (a_list,i)
        in 
           IArray.tabulate (nci, (\<lambda> j. 
              let b_col_j = IArray.sub' (b_transpose_list,j)
              in scalar_prod_list a_row_i b_col_j)))))" 
  by auto

declare [[code drop: "(*) :: (_ mat \<Rightarrow> _ mat \<Rightarrow> _mat)"]]

lemma sub'_IArray: "IArray.sub' (IArray as, n) = as ! nat_of_integer n" by simp

lemma times_mat_code[code]: "mat_impl a * mat_impl b = (if dim_col_impl a = dim_row_impl b
  then mat_impl (times_mat_impl a b) else Code.abort (STR ''matrix-mult with incompatible dimensions'')
     (\<lambda> _. mat_impl a * mat_impl b))" 
proof (cases "dim_col_impl a = dim_row_impl b")
  case True
  hence id: "(dim_col_impl a = dim_row_impl b) = True" by auto
  from True have True': "dim_col (mat_impl a) = dim_row (mat_impl b)" 
    by transfer auto
  show ?thesis unfolding id if_True 
  proof (rule sym, intro eq_matI)
    show "dim_row (mat_impl (times_mat_impl a b)) = dim_row (mat_impl a * mat_impl b)" 
      by (simp, transfer, auto)
    show "dim_col (mat_impl (times_mat_impl a b)) = dim_col (mat_impl a * mat_impl b)" 
      by (simp, transfer, auto)
    fix i j
    assume i: "i < dim_row (mat_impl a * mat_impl b)" 
    assume j: "j < dim_col (mat_impl a * mat_impl b)" 
    from i j have ij: "i < dim_row_impl a" "j < dim_col_impl b" 
      by (auto simp: dim_row_code dim_col_code)
    have "(mat_impl a * mat_impl b) $$ (i, j) = scalar_prod (row (mat_impl a) i) (col (mat_impl b) j)" 
      using i j by simp
    also have "\<dots> = (\<Sum>k = 0..<dim_row (mat_impl b). mat_impl a $$ (i,k) * mat_impl b $$ (k,j))" 
      unfolding scalar_prod_def 
      by (rule sum.cong, insert i j True', auto)
    also have "\<dots> = (\<Sum>k = 0..<dim_row_impl b. index_mat_impl a (i,k) * index_mat_impl b (k,j))" 
      unfolding index_mat_code dim_row_code ..
    also have "\<dots> = index_mat_impl (times_mat_impl a b) (i, j)" using True ij
    proof (transfer, goal_cases)
      case (1 A B i j)
      then obtain nr n nc a b where A: "A = (nr,n,a)" and 
        Ac: "IArray.length a = nr" "IArray.all (\<lambda>r. IArray.length r = n) a" and
        B: "B = (n,nc,b)" and 
        Bc: "IArray.length b = n" "IArray.all (\<lambda>r. IArray.length r = nc) b" and
        i: "i < nr" and
        j: "j < nc" and
        id: "(i < nr) = True" "[0..<nr] ! i = i" "[0..<nc] ! j = j" 
        by auto
      from i have inr: "i < length [0..<nr]" by auto
      from j have jnc: "j < length [0..<nc]" by auto
      show ?case unfolding A B split Let_def fst_conv id if_True
          IArray.tabulate.simps IArray.sub_def IArray.list_of.simps o_def nat_of_integer_integer_of_nat
          nth_map[OF inr] nth_map[OF jnc] upt_integer map_map sub'_IArray
        unfolding scalar_prod_list
        by (rule sum.cong[OF refl], insert i j, auto)
    qed
    finally show "mat_impl (times_mat_impl a b) $$ (i, j) = (mat_impl a * mat_impl b) $$ (i, j)"
      by (simp add: index_mat_code)
  qed
qed auto
    
lift_definition row_impl :: "'a mat_impl \<Rightarrow> nat \<Rightarrow> 'a vec_impl" 
  is "\<lambda> (nr,nc,m) i. if i < nr then (nc, IArray.sub' (m, integer_of_nat i)) else 
    (Code.abort (STR ''row index too large'') (\<lambda> _.  (nc, IArray.of_fun (\<lambda>j. IArray.sub (IArray ([] ! (i - nr))) j) nc)))"
  by (auto split: if_splits)


declare [[code drop: row]]

lemma row_code[code]: "row (mat_impl a) i = vec_impl (row_impl a i)" 
  unfolding row_def
proof (transfer, goal_cases)
  case (1 a i)
  then obtain nr nc m where a: "a = (nr,nc,m)" and 
    inv: "IArray.length m = nr" "IArray.all (\<lambda>r. IArray.length r = nc) m" by auto
  show ?case 
  proof (cases "i < nr") 
    case True
    hence i: "(i < nr) = True" by auto
    show ?thesis unfolding a split o_def fst_conv snd_conv i if_True
      using i inv by (auto simp: mk_vec_def mk_mat_def)
  next
    case False
    hence i: "(i < nr) = False" by auto
    hence "\<not> i < length (map f [0..<nr])" for f :: "nat \<Rightarrow> 'a list" by auto
    from empty_nth[OF this] 
    show ?thesis unfolding a split o_def fst_conv snd_conv i if_False Code.abort_def using i
      by (auto simp: mk_vec_def mk_mat_def undef_mat_def)
  qed
qed

lift_definition col_impl :: "'a mat_impl \<Rightarrow> nat \<Rightarrow> 'a vec_impl" 
  is "\<lambda> (nr,nc,m) j. if j < nc then (nr, IArray.tabulate (integer_of_nat nr, \<lambda> i. IArray.sub' (IArray.sub' (m,i),integer_of_nat j)))
      else Code.abort (STR ''col index too large'') (\<lambda> _.  (nr, IArray.of_fun (\<lambda>i. IArray.sub (IArray.sub m i) j) nr))" 
  by (auto split: if_splits)

declare [[code drop: col]] 

lemma col_impl_code[code]: "col (mat_impl a) i = vec_impl (col_impl a i)" 
  unfolding col_def
proof (transfer, goal_cases)
  case (1 a j)
  then obtain nr nc m where a: "a = (nr,nc,m)" and 
    inv: "IArray.length m = nr" "IArray.all (\<lambda>r. IArray.length r = nc) m" by auto
  show ?case 
  proof (cases "j < nc") 
    case True
    hence j: "(j < nc) = True" by auto
    show ?thesis unfolding a split o_def fst_conv snd_conv j if_True
      using j inv by (auto simp: mk_vec_def mk_mat_def)
  next
    case False
    {
      fix i
      assume "i < nr" 
      hence len: "length (IArray.list_of (IArray.list_of m ! i)) = nc" using inv 
        by auto
      from empty_nth[OF False[folded len], unfolded len] 
      have "IArray.list_of (IArray.list_of m ! i) ! j = [] ! (j - nc)" by simp
    } note undef = this
    from False
    have j: "(j < nc) = False" by auto
    hence "\<not> j < length (map f [0..<nc])" for f :: "nat \<Rightarrow> 'a" by auto
    from empty_nth[OF this] 
    show ?thesis unfolding a split o_def fst_conv snd_conv j if_False
      using j undef by (auto simp: mk_vec_def mk_mat_def undef_mat_def)
  qed
qed


end
