theory Suffix
  imports Main
begin

section \<open>Suffix\<close>

abbreviation suffix :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
"suffix xs i \<equiv> drop i xs"

lemma suffixes_neq:
  "\<lbrakk>i < length s; j < length s; i \<noteq> j\<rbrakk> \<Longrightarrow> suffix s i \<noteq> suffix s j"
  by (metis diff_diff_cancel length_drop less_or_eq_imp_le)

lemma distinct_suffixes:
  "\<lbrakk>distinct xs; \<forall>x \<in> set xs. x < length s\<rbrakk> \<Longrightarrow> distinct (map (suffix s) xs)"
  by (simp add: distinct_conv_nth suffixes_neq)

lemma suffix_eq_index:
  "\<lbrakk>i < length xs; j < length xs; suffix xs i = suffix xs j\<rbrakk> \<Longrightarrow> i = j"
  by (metis diff_diff_cancel le_eq_less_or_eq length_drop)

lemma suffix_neq_nil:
  "i < length s \<Longrightarrow> suffix s i \<noteq> []"
  by simp

lemma suffix_map:
  "suffix (map f xs) i = map f (suffix xs i)"
  by (simp add: drop_map)

lemma set_suffix_subset:
  "set (suffix s i) \<subseteq> set s"
  by (simp add: set_drop_subset)
lemma suffix_cons_suc:
  "suffix (a # xs) (Suc i) = suffix xs i"
  by simp

lemma suffix_app:
  "i < length xs \<Longrightarrow> suffix (xs @ ys) i = suffix xs i @ ys"
  by simp

lemma suffix_cons_ex:
  "i < length T \<Longrightarrow> \<exists>x xs. suffix T i = x # xs \<and> x = T ! i"
  by (metis Cons_nth_drop_Suc)

lemma suffix_cons_Suc:
  "i < length T \<Longrightarrow> suffix T i = T ! i # suffix T (Suc i)"
  by (metis Cons_nth_drop_Suc)

lemma suffix_cons_app:
  "suffix T i = as @ bs \<Longrightarrow> suffix T (i + length as) = bs"
  by (metis add.commute append_eq_conv_conj drop_drop)

lemma suffix_0:
  "suffix T 0 = T"
  by simp

end