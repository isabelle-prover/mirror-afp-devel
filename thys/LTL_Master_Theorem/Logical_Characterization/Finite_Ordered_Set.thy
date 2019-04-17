(*  
    Author:      Salomon Sickert (copied from LTL_to_DRA)
    License:     BSD
*)

section \<open>Ordered Induction on Finite Sets\<close>

theory Finite_Ordered_Set
  imports Main
begin


(* TODO move to HOL.Finite_Set *)

inductive finite_ordered :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> bool" for f :: "'a \<Rightarrow> nat" 
where
  empty_ordered: "finite_ordered f {}"
| insert_ordered: "finite_ordered f A \<Longrightarrow> (\<And>b. b \<in> A \<Longrightarrow> f b \<le> f a) \<Longrightarrow> finite_ordered f (insert a A)"

lemma sort_list:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "sort_key f xs = a @ [z] @ b"
  assumes "y \<in> set a"
  shows "f y \<le> f z"
proof -
  have "sorted ((map f a @ [f z]) @ map f b)"
    using assms(1) sorted_sort_key[of f xs] 
    unfolding map_append by simp
  hence "sorted (map f a @ [f z])"
    using sorted_append by blast
  hence "\<forall>fy \<in> set (map f a). fy \<le> f z"
    unfolding sorted_append by simp
  thus ?thesis
    using `y \<in> set a` set_map by simp
qed

lemma finite_to_finite_ordered:
  "finite A \<Longrightarrow> finite_ordered f A" 
proof -
  assume "finite A"
  then obtain xs where "set xs = A"
    using finite_list by blast
  moreover
  obtain ys where "set xs = set ys" 
    and "\<And>a b y z. ys = a @ [z] @ b \<Longrightarrow> y \<in> set a \<Longrightarrow> f y \<le> f z"
    using sort_list[of f xs] set_sort by metis
  moreover
  have "finite_ordered f (foldl (\<lambda>S x. insert x S) {} ys)"
    using `\<And>a b y z. ys = a @ [z] @ b \<Longrightarrow> y \<in> set a \<Longrightarrow> f y \<le> f z`
  proof (induction ys rule: rev_induct)
    case (snoc y ys)
      hence "finite_ordered f (foldl (\<lambda>S x. insert x S) {} ys)"
        by simp
      moreover
      have "\<And>z. z \<in> set ys \<Longrightarrow> f z \<le> f y"
        using snoc by simp
      moreover
      have "set ys = (foldl (\<lambda>S x. insert x S) {} ys)"
        by (induction ys rule: rev_induct) auto
      ultimately
      show ?case 
        unfolding foldl_append foldl.simps 
        using insert_ordered by metis
  qed (simp add: empty_ordered)
  moreover
  have "set ys = (foldl (\<lambda>S x. insert x S) {} ys)"
    by (induction ys rule: rev_induct) auto
  ultimately
  show ?thesis
    by simp
qed

lemma finite_finite_ordered_eq:
  "finite A = finite_ordered f A"
  by (rule, blast intro: finite_to_finite_ordered, induction rule: finite_ordered.induct, auto)

lemma finite_induct_ordered [case_names empty insert, induct set: finite]:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite S"
  assumes "P {}" 
  assumes "\<And>x S. finite S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f y \<le> f x) \<Longrightarrow> P S \<Longrightarrow> P (insert x S)"
  shows "P S"
  using `finite S` unfolding finite_finite_ordered_eq[of _ f] 
proof (induction rule: finite_ordered.induct) 
  case (insert_ordered A a)
    thus ?case
      using assms unfolding finite_finite_ordered_eq[of _ f] by simp
qed (blast intro: `P {}`)



end