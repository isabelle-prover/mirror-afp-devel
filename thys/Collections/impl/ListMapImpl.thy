(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Map Implementation by Associative Lists} *}
theory ListMapImpl
imports 
  "../spec/MapSpec" 
  "../common/Assoc_List" 
  "../gen_algo/MapGA"
begin
text_raw {*\label{thy:ListMapImpl}*}

(*@impl Map
  @type 'a lm
  @abbrv lm,l
  Maps implemented by associative lists. If you need efficient 
  @{text "insert_dj"} operation, you should use list sets with explicit 
  invariants (lmi).
*)

type_synonym ('k,'v) lm = "('k,'v) assoc_list"

subsection "Functions"

definition "lm_\<alpha> == Assoc_List.lookup"
abbreviation (input) lm_invar where "lm_invar == \<lambda>_. True"
definition "lm_empty = (\<lambda>_::unit. Assoc_List.empty)"
definition "lm_lookup k m == Assoc_List.lookup m k"
definition "lm_update == Assoc_List.update"
text {* 
  Since we use the abstract type @{typ "('k, 'v) assoc_list"} for associative lists,
  to preserve the invariant of distinct maps, we cannot just use Cons for disjoint update,
  but must resort to ordinary update. The same applies to @{text lm_add_dj} below.
*}
definition "lm_update_dj == lm_update"  
definition "lm_delete k m == Assoc_List.delete k m"
definition "lm_iteratei == Assoc_List.iteratei"

definition "lm_isEmpty m == m=Assoc_List.empty"

definition "lm_add == it_add lm_update lm_iteratei"
definition "lm_add_dj == lm_add"

definition "lm_sel == iti_sel lm_iteratei"
definition "lm_sel' == iti_sel_no_map lm_iteratei"
definition lm_to_list :: "('u,'v) lm \<Rightarrow> ('u \<times> 'v) list"
  where "lm_to_list = Assoc_List.impl_of"
definition "list_to_lm == gen_list_to_map lm_empty lm_update"

subsection "Correctness"

lemmas lm_defs =
  lm_\<alpha>_def
  lm_empty_def
  lm_lookup_def
  lm_update_def
  lm_update_dj_def
  lm_delete_def
  lm_iteratei_def
  lm_isEmpty_def
  lm_add_def
  lm_add_dj_def
  lm_sel_def
  lm_sel'_def
  lm_to_list_def
  list_to_lm_def

lemma lm_empty_impl: 
  "map_empty lm_\<alpha> lm_invar lm_empty"
by (unfold_locales) (auto simp add: lm_defs fun_eq_iff)

interpretation lm: map_empty lm_\<alpha> lm_invar lm_empty by(fact lm_empty_impl)

lemma lm_lookup_impl: 
  "map_lookup lm_\<alpha> lm_invar lm_lookup"
by (unfold_locales)(simp add: lm_defs)

interpretation lm: map_lookup lm_\<alpha> lm_invar lm_lookup using lm_lookup_impl .

lemma lm_update_impl: 
  "map_update lm_\<alpha> lm_invar lm_update"
by (unfold_locales)(simp_all add: lm_defs)

interpretation lm: map_update lm_\<alpha> lm_invar lm_update using lm_update_impl .

lemma lm_update_dj_impl: 
  "map_update_dj lm_\<alpha> lm_invar lm_update_dj"
by (unfold_locales) (simp_all add: lm_defs)

interpretation lm: map_update_dj lm_\<alpha> lm_invar lm_update_dj using lm_update_dj_impl .

lemma lm_delete_impl: 
  "map_delete lm_\<alpha> lm_invar lm_delete"
by (unfold_locales)(simp_all add: lm_defs)

interpretation lm: map_delete lm_\<alpha> lm_invar lm_delete using lm_delete_impl .

lemma lm_isEmpty_impl: 
  "map_isEmpty lm_\<alpha> lm_invar lm_isEmpty"
  apply (unfold_locales)
  apply (unfold lm_defs)
  apply(rule iffI)
   apply(simp add: impl_of_inject lookup_empty')
  apply(case_tac m)
  apply(simp add: Assoc_List.empty_def Assoc_List.lookup_def Assoc_List_inverse Assoc_List_inject)
  apply(case_tac y)
  apply simp_all
  done

interpretation lm: map_isEmpty lm_\<alpha> lm_invar lm_isEmpty using lm_isEmpty_impl .

lemma lm_is_finite_map: "finite_map lm_\<alpha> lm_invar"
by unfold_locales(simp add: lm_defs)

interpretation lm: finite_map lm_\<alpha> lm_invar using lm_is_finite_map .

lemma lm_iteratei_impl: 
  "map_iteratei lm_\<alpha> lm_invar lm_iteratei"
unfolding map_iteratei_def finite_map_def map_iteratei_axioms_def lm_defs
by (simp add: iteratei_correct)

interpretation lm: map_iteratei lm_\<alpha> lm_invar lm_iteratei using lm_iteratei_impl .

declare lm.finite[simp del, rule del]

lemma lm_finite[simp, intro!]: "finite (dom (lm_\<alpha> m))"
  by (auto simp add: lm_\<alpha>_def)

lemmas lm_add_impl = it_add_correct[OF lm_iteratei_impl lm_update_impl, folded lm_add_def]
interpretation lm: map_add lm_\<alpha> lm_invar lm_add using lm_add_impl .

lemmas lm_add_dj_impl =
  map_add.add_dj_by_add[OF lm_add_impl, folded lm_add_dj_def]
  
interpretation lm: map_add_dj lm_\<alpha> lm_invar lm_add_dj using lm_add_dj_impl .

lemmas lm_sel_impl = iti_sel_correct[OF lm_iteratei_impl, folded lm_sel_def]
interpretation lm: map_sel lm_\<alpha> lm_invar lm_sel using lm_sel_impl .

lemmas lm_sel'_impl = iti_sel'_correct [OF lm_iteratei_impl, folded lm_sel'_def]
interpretation lm: map_sel' lm_\<alpha> lm_invar lm_sel' using lm_sel'_impl .

lemma lm_to_list_impl: "map_to_list lm_\<alpha> lm_invar lm_to_list"
by(unfold_locales)(auto simp add: lm_defs Assoc_List.lookup_def)

interpretation lm: map_to_list lm_\<alpha> lm_invar lm_to_list using lm_to_list_impl .

lemmas list_to_lm_impl = 
  gen_list_to_map_correct[OF lm_empty_impl lm_update_impl, 
                          folded list_to_lm_def]

interpretation lm: list_to_map lm_\<alpha> lm_invar list_to_lm 
  using list_to_lm_impl .


subsection "Code Generation"

lemmas lm_correct = 
  lm.empty_correct
  lm.lookup_correct
  lm.update_correct
  lm.update_dj_correct
  lm.delete_correct
  lm.isEmpty_correct
  lm.add_correct
  lm.add_dj_correct
  lm.to_list_correct
  lm.to_map_correct

export_code
  lm_empty
  lm_lookup
  lm_update
  lm_update_dj
  lm_delete
  lm_isEmpty
  lm_iteratei
  lm_add
  lm_add_dj
  lm_sel
  lm_sel'
  lm_to_list
  list_to_lm
  in SML
  module_name ListMap
  file -

end
