subsection \<open>Miscellaneous\<close>

theory Worklist_Algorithms_Misc
  imports "HOL-Library.Multiset"
begin

lemma mset_eq_empty_iff:
  "M = {#} \<longleftrightarrow> set_mset M = {}"
  by auto

lemma filter_mset_eq_empty_iff:
  "{#x \<in># A. P x#} = {#} \<longleftrightarrow> (\<forall>x \<in> set_mset A. \<not> P x)"
  by (auto simp: mset_eq_empty_iff)

lemma mset_remove_member:
  "x \<in># A - B" if "x \<in># A" "x \<notin># B"
  using that
  by (metis count_greater_zero_iff in_diff_count not_in_iff)

end