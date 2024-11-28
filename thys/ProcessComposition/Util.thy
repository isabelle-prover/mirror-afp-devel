theory Util
  imports Main
begin

section\<open>Utility Theorems\<close>

text\<open>
  This theory contains general facts that we use in our proof but which do not depend on our
  development.
\<close>

text\<open>@{const list_all} and @{const list_ex} are dual\<close>
lemma not_list_all:
  "(\<not> list_all P xs) = list_ex (\<lambda>x. \<not> P x) xs"
  by (metis Ball_set Bex_set)
lemma not_list_ex:
  "(\<not> list_ex P xs) = list_all (\<lambda>x. \<not> P x) xs"
  by (metis Ball_set Bex_set)

text\<open>A list of length more than one starts with two elements\<close>
lemma list_obtain_2:
  assumes "1 < length xs"
  obtains v vb vc where "xs = v # vb # vc"
  using assms by (cases xs rule: remdups_adj.cases) simp_all

text\<open>Generalise the theorem @{thm Nat.less_add_eq_less}\<close>
lemma less_add_eq_less_general:
    fixes k l m n :: "'a :: {comm_monoid_add, ordered_cancel_ab_semigroup_add, linorder}"
  assumes "k < l"
      and "m + l = k + n"
    shows "m < n"
  using assms by (metis add.commute add_strict_left_mono linorder_not_less nless_le)

text\<open>
  Consider a list of elements and two functions, one of which is always at less-than or equal to the
  other on elements of that list.
  If for one element of that list the first function is strictly less than the other, then summing
  the list with the first function is also strictly less summing it with the second function.
\<close>
lemma sum_list_mono_one_strict:
  fixes f g :: "'a \<Rightarrow> 'b :: {comm_monoid_add, ordered_cancel_ab_semigroup_add, linorder}"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x"
      and "x \<in> set xs"
      and "f x < g x"
    shows "sum_list (map f xs) < sum_list (map g xs)"
proof -
  have "sum_list (map f xs) \<le> sum_list (map g xs)"
    using assms sum_list_mono by blast
  moreover have "sum_list (map f xs) \<noteq> sum_list (map g xs)"
  proof
    assume "sum_list (map f xs) = sum_list (map g xs)"
    then have "sum_list (map f (remove1 x xs)) > sum_list (map g (remove1 x xs))"
      by (metis add.commute assms(2,3) less_add_eq_less_general sum_list_map_remove1)
    then show False
      by (metis assms(1) leD notin_set_remove1 sum_list_mono)
  qed
  ultimately show ?thesis
    by simp
qed

text\<open>Generalise @{thm Groups_List.sum_list_mono} to allow for different lists\<close>
lemma sum_list_mono_list_all2:
    fixes f g :: "'a \<Rightarrow> 'b::{monoid_add, ordered_ab_semigroup_add}"
  assumes "list_all2 (\<lambda>x y. f x \<le> g y) xs ys"
    shows "(\<Sum>x\<leftarrow>xs. f x) \<le> (\<Sum>x\<leftarrow>ys. g x)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  moreover obtain b bs where "ys = b # bs"
    using Cons by (meson list_all2_Cons1)
  ultimately show ?case
    by (simp add: add_mono)
qed

text\<open>Generalise @{thm sum_list_mono_one_strict} to allow for different lists\<close>
lemma sum_list_mono_one_strict_list_all2:
    fixes f g :: "'a \<Rightarrow> 'b :: {comm_monoid_add, ordered_cancel_ab_semigroup_add, linorder}"
  assumes "list_all2 (\<lambda>x y. f x \<le> g y) xs ys"
      and "(x, y) \<in> set (zip xs ys)"
      and "f x < g y"
    shows "sum_list (map f xs) < sum_list (map g ys)"
proof -
  note len = list_all2_lengthD[OF assms(1)]

  have "sum_list (map f xs) = (\<Sum>x\<leftarrow>zip xs ys. f (fst x))"
  proof -
    have "map f xs = map f (map fst (zip xs ys))"
      using len by simp
    then have "map f xs = map (\<lambda>x. f (fst x)) (zip xs ys)"
      by simp
    then show ?thesis
      by metis
  qed
  moreover have "sum_list (map g ys) = (\<Sum>x\<leftarrow>zip xs ys. g (snd x))"
  proof -
    have "map g ys = map g (map snd (zip xs ys))"
      using len by simp
    then have "map g ys = map (\<lambda>x. g (snd x)) (zip xs ys)"
      by simp
    then show ?thesis
      by metis
  qed
  moreover have "x \<in> set (zip xs ys) \<Longrightarrow> f (fst x) \<le> g (snd x)" for x
    using assms(1) by (fastforce simp add: in_set_zip list_all2_conv_all_nth)
  ultimately show ?thesis
    using assms(2,3) by (simp add: sum_list_mono_one_strict)
qed

text\<open>Define a function to count the number of list elements satisfying a predicate\<close>
primrec count_if :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"
  where
    "count_if P [] = 0"
  | "count_if P (x#xs) = (if P x then Suc (count_if P xs) else count_if P xs)"

lemma count_if_append [simp]:
  "count_if P (xs @ ys) = count_if P xs + count_if P ys"
  by (induct xs) simp_all

lemma count_if_0_conv:
  "(count_if P xs = 0) = (\<not> list_ex P xs)"
  by (induct xs) simp_all

text\<open>Intersection of sets that are the same is any of those sets\<close>
lemma Inter_all_same:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> f x = f y"
      and "x \<in> A"
    shows "(\<Inter>x \<in> A. f x) = f x"
  using assms by blast

end