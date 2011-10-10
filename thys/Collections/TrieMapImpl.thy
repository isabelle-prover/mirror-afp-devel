(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Map implementation via tries} *}
theory TrieMapImpl imports
  Trie
  MapGA
begin

text {* 
  Trie maps are only for keys of type @{typ "'a list"}.
*}

subsection {* Operations *}

type_synonym ('k, 'v) tm = "('k, 'v) trie"

definition tm_\<alpha> :: "('k, 'v) tm \<Rightarrow> 'k list \<rightharpoonup> 'v"
where "tm_\<alpha> = Trie.lookup"

abbreviation (input) tm_invar :: "('k, 'v) tm \<Rightarrow> bool"
where "tm_invar \<equiv> \<lambda>_. True"

definition tm_empty :: "('k, 'v) tm"
where "tm_empty == Trie.empty"

definition tm_lookup :: "'k list \<Rightarrow> ('k, 'v) tm \<Rightarrow> 'v option"
where "tm_lookup k t = Trie.lookup t k"

definition tm_update :: "'k list \<Rightarrow> 'v \<Rightarrow> ('k, 'v) tm \<Rightarrow> ('k, 'v) tm"
where "tm_update = Trie.update"

definition "tm_update_dj == tm_update"

definition tm_delete :: "'k list \<Rightarrow> ('k, 'v) tm \<Rightarrow> ('k, 'v) tm"
where "tm_delete = Trie.delete"

definition tm_iteratei :: "(('k, 'v) tm, 'k list, 'v, '\<sigma>) map_iteratori"
where
  "tm_iteratei = Trie.iteratei"

definition "tm_iterate == iti_iterate tm_iteratei"

definition "tm_add == it_add tm_update tm_iterate"

definition "tm_add_dj == tm_add"

definition tm_isEmpty :: "('k, 'v) tm \<Rightarrow> bool"
where "tm_isEmpty = Trie.isEmpty"

definition "tm_sel == iti_sel tm_iteratei"
definition "tm_sel' == sel_sel' tm_sel"

definition "tm_ball == sel_ball tm_sel"
definition "tm_to_list == it_map_to_list tm_iterate"
definition "list_to_tm == gen_list_to_map tm_empty tm_update"

lemmas tm_defs = 
  tm_\<alpha>_def
  tm_empty_def
  tm_lookup_def
  tm_update_def
  tm_update_dj_def
  tm_delete_def
  tm_iteratei_def
  tm_iterate_def
  tm_add_def
  tm_add_dj_def
  tm_isEmpty_def
  tm_sel_def
  tm_sel'_def
  tm_ball_def
  tm_to_list_def
  list_to_tm_def

subsection {* Correctness *}

lemma tm_empty_impl: "map_empty tm_\<alpha> tm_invar tm_empty"
by(unfold_locales)(simp_all add: tm_defs fun_eq_iff)

lemma tm_lookup_impl: "map_lookup tm_\<alpha> tm_invar tm_lookup"
by(unfold_locales)(auto simp add: tm_defs)

lemma tm_update_impl: "map_update tm_\<alpha> tm_invar tm_update"
by(unfold_locales)(simp_all add: tm_defs)

lemma tm_update_dj_impl: "map_update_dj tm_\<alpha> tm_invar tm_update_dj"
unfolding tm_update_dj_def
by(rule map_update.update_dj_by_update)(rule tm_update_impl)

lemma tm_delete_impl: "map_delete tm_\<alpha> tm_invar tm_delete"
by(unfold_locales)(simp_all add: tm_defs)

lemma tm_\<alpha>_finite [simp, intro!]:
  "finite (dom (tm_\<alpha> m))"
by(simp add: tm_defs finite_dom_lookup)

lemma tm_is_finite_map: "finite_map tm_\<alpha> tm_invar"
by unfold_locales simp

lemma tm_iteratei_impl: "map_iteratei tm_\<alpha> tm_invar tm_iteratei"
by(unfold_locales)(simp, unfold tm_defs, rule iteratei_correct)

lemma tm_iterate_impl: "map_iterate tm_\<alpha> tm_invar tm_iterate"
by(unfold tm_iterate_def)(intro map_iteratei.iti_iterate_correct tm_iteratei_impl)

lemma tm_add_impl: "map_add tm_\<alpha> tm_invar tm_add"
unfolding tm_add_def
by(rule it_add_correct tm_iterate_impl tm_update_impl)+

lemma tm_add_dj_impl: "map_add_dj tm_\<alpha> tm_invar tm_add_dj"
unfolding tm_add_dj_def
by(rule map_add.add_dj_by_add tm_add_impl)+

lemma tm_isEmpty_impl: "map_isEmpty tm_\<alpha> tm_invar tm_isEmpty"
by unfold_locales(simp add: tm_defs isEmpty_lookup)

lemma tm_sel_impl: "map_sel tm_\<alpha> tm_invar tm_sel"
unfolding tm_sel_def
by(rule iti_sel_correct tm_iteratei_impl)+

lemma tm_sel'_impl: "map_sel' tm_\<alpha> tm_invar tm_sel'"
unfolding tm_sel'_def
by(rule sel_sel'_correct tm_sel_impl)+

lemma tm_ball_impl: "map_ball tm_\<alpha> tm_invar tm_ball"
unfolding tm_ball_def
by(rule sel_ball_correct tm_sel_impl)+

lemma tm_to_list_impl: "map_to_list tm_\<alpha> tm_invar tm_to_list"
unfolding tm_to_list_def
by(rule it_map_to_list_correct tm_iterate_impl)+

lemma list_to_tm_impl: "list_to_map tm_\<alpha> tm_invar list_to_tm"
unfolding list_to_tm_def
by(rule gen_list_to_map_correct tm_empty_impl tm_update_impl)+


interpretation tm: map_empty tm_\<alpha> tm_invar tm_empty 
  using tm_empty_impl .
interpretation tm: map_lookup tm_\<alpha> tm_invar tm_lookup 
  using tm_lookup_impl .
interpretation tm: map_update tm_\<alpha> tm_invar tm_update 
  using tm_update_impl .
interpretation tm: map_update_dj tm_\<alpha> tm_invar tm_update_dj 
  using tm_update_dj_impl .
interpretation tm: map_delete tm_\<alpha> tm_invar tm_delete 
  using tm_delete_impl .
interpretation tm: finite_map tm_\<alpha> tm_invar 
  using tm_is_finite_map .
interpretation tm: map_iterate tm_\<alpha> tm_invar tm_iterate 
  using tm_iterate_impl .
interpretation tm: map_iteratei tm_\<alpha> tm_invar tm_iteratei
  using tm_iteratei_impl .
interpretation tm: map_add tm_\<alpha> tm_invar tm_add 
  using tm_add_impl .
interpretation tm: map_add_dj tm_\<alpha> tm_invar tm_add_dj 
  using tm_add_dj_impl .
interpretation tm: map_isEmpty tm_\<alpha> tm_invar tm_isEmpty 
  using tm_isEmpty_impl .
interpretation tm: map_sel tm_\<alpha> tm_invar tm_sel 
  using tm_sel_impl .
interpretation tm: map_sel' tm_\<alpha> tm_invar tm_sel' 
  using tm_sel'_impl .
interpretation tm: map_ball tm_\<alpha> tm_invar tm_ball 
  using tm_ball_impl .
interpretation tm: map_to_list tm_\<alpha> tm_invar tm_to_list 
  using tm_to_list_impl .
interpretation tm: list_to_map tm_\<alpha> tm_invar list_to_tm 
  using list_to_tm_impl . 

declare tm.finite[simp del, rule del]

lemmas tm_correct =
  tm.empty_correct
  tm.lookup_correct
  tm.update_correct
  tm.update_dj_correct
  tm.delete_correct
  tm.add_correct
  tm.add_dj_correct
  tm.isEmpty_correct
  tm.ball_correct
  tm.to_list_correct
  tm.to_map_correct

subsection "Code Generation"

export_code
  tm_empty
  tm_lookup
  tm_update
  tm_update_dj
  tm_delete
  tm_iterate
  tm_iteratei
  tm_add
  tm_add_dj
  tm_isEmpty
  tm_sel
  tm_sel'
  tm_ball
  tm_to_list
  list_to_tm
  in SML
  module_name TrieMap
  file -

end
