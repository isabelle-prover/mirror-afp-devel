theory Multiset_Order_Extra
  imports "HOL-Library.Multiset_Order"
begin

lemma strict_subset_implies_multp\<^sub>H\<^sub>O: "A \<subset># B \<Longrightarrow> multp\<^sub>H\<^sub>O r A B"
  unfolding multp\<^sub>H\<^sub>O_def
  by (simp add: leD mset_subset_eq_count)

end