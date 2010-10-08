theory MiscAdd
imports "Misc"
begin


lemma restrict_subset: "(m |` S) x = Some y \<Longrightarrow> m x = Some y"
  by (metis not_None_eq restrict_in restrict_out)

    (* TODO: Test whether simp loops somewhere ;)*)
lemma min_simps[simp]:
  "a<(b::'a::order) \<Longrightarrow> min a b = a"
  "b<(a::'a::order) \<Longrightarrow> min a b = b"
  by (auto simp add: min_def dest: less_imp_le)

lemma min_linorder_simps[simp]:
  "\<not> a<(b::'a::linorder) \<Longrightarrow> min a b = b"
  "\<not> b<(a::'a::linorder) \<Longrightarrow> min a b = a"
  by (auto simp add: min_def)

lemma listsum_split: "listsum (l @ (a::'a::monoid_add) # r) = (listsum l) + a + (listsum r)"
  by (induct l) (auto simp add: add_assoc)

lemma multiset_moep: "multiset_of (l @ a # r) = multiset_of l + {# a #} + multiset_of r"
  by(metis Cons_eq_append_conv multiset_of.simps(2) multiset_of_append union_commute union_lcomm)

lemma multiset_moep2: "a + {#b#} + c - {#b#} = a + c"
  by (metis diff_union_cancelR mset_le_add_right multiset_diff_union_assoc union_commute union_lcomm)  

end