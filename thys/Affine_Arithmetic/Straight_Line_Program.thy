section \<open>Straight Line Programs\<close>
theory Straight_Line_Program
imports Affine_Approximation
begin

subsection \<open>Definition\<close>

datatype 'a slp =
  ConsSLP "('a, 'a) euclarith" "'a slp"  (infixr ";slp" 65)
| ReturnSLP "nat list"

primrec interpret_slp::"'a::real_inner slp \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "interpret_slp (ReturnSLP is) = (\<lambda>xs. map (nth xs) is)"
| "interpret_slp (ConsSLP ea eas) =
    (\<lambda>xs. interpret_slp eas (xs @ [interpret_euclarith ea xs]))"

primrec approx_slp::"nat \<Rightarrow> real \<Rightarrow> 'a::executable_euclidean_space slp \<Rightarrow> 'a aform list \<Rightarrow>
    'a aform list option"
where
  "approx_slp p t (ReturnSLP is) xs = (if \<forall>i\<in>set is. i < length xs then Some (map (nth xs) is) else None)"
| "approx_slp p t (ConsSLP ea eas) xs =
    do {
      r \<leftarrow> approx_euclarith_outer p t ea xs;
      approx_slp p t eas (xs @ [r])
    }"

lemma Nil_mem_Joints[intro, simp]: "[] \<in> Joints []"
  by (force simp: Joints_def valuate_def)

lemma map_nth_Joints: "xs \<in> Joints XS \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length XS) \<Longrightarrow> map (nth xs) is @ xs \<in> Joints (map (nth XS) is @ XS)"
  by (auto simp: Joints_def valuate_def)

lemma map_nth_Joints': "xs \<in> Joints XS \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length XS) \<Longrightarrow> map (nth xs) is \<in> Joints (map (nth XS) is)"
  by (rule Joints_appendD2[OF map_nth_Joints]) (auto )

lemma approx_slp:
  assumes "approx_slp p t eas XS = Some YS"
  assumes "xs \<in> Joints XS"
  shows "interpret_slp eas xs \<in> Joints (YS)"
  using assms 
  by (induction eas arbitrary: xs XS YS)
     (auto simp: bind_eq_Some_conv map_nth_Joints' Joints2_JointsI Joints_imp_length_eq
        dest!: approx_euclarith_outer split: if_split_asm)


subsection \<open>free variable bound\<close>

primrec max_Var_slp::"'a slp \<Rightarrow> nat \<Rightarrow> bool" where
  "max_Var_slp (ReturnSLP rs) n \<longleftrightarrow> (\<forall>r \<in> set rs. r < n)"
| "max_Var_slp (x ;slp slp) n \<longleftrightarrow> max_Var_euclarith x < n \<and> (max_Var_slp slp (Suc n))"

lemma nth_takeI:
  assumes "take (Suc x) ys = take (Suc x) zs"
  assumes "x < length ys"
  assumes "x < length zs"
  shows "ys ! x = zs ! x"
proof -
  from assms
  have "take (Suc x) ys ! x = take (Suc x) zs ! x"
    by simp
  then show ?thesis
    by simp
qed


subsection \<open>Example\<close>

lemma
  fixes y x::real
  shows "interpret_slp
    ( add_ea 1 0   ;slp
      hadamard_ea 0 2 ;slp
      add_ea 3 2   ;slp
      ReturnSLP [3, 4]) [y, x] =
    [y * (x + y), y * (x + y) + (x + y)]"
  by simp

end