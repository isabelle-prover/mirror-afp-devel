theory Prefix
  imports Main
begin

section \<open>Prefix Definition\<close>

abbreviation prefix :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
"prefix xs i \<equiv> take i xs"

lemma prefix_neq:
  assumes "i < length s"
  and     "j < length s"
  and     "i \<noteq> j"
shows "prefix s i \<noteq> prefix s j"
  by (metis assms length_take less_imp_le min_absorb2)

lemma not_prefix_app:
  "(\<forall>k. s1 \<noteq> prefix s2 k) \<longleftrightarrow> (\<forall>xs. s2 \<noteq> s1 @ xs)"
  by (metis append_eq_conv_conj append_take_drop_id)

lemma not_prefix_imp_not_nil:
  "\<forall>k. s1 \<noteq> prefix s2 k \<Longrightarrow> s1 \<noteq> []"
  by (metis take0)

end