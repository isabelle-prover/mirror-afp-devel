(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Array-based hash maps without explicit invariants} *}
theory ArrayHashMap 
  imports ArrayHashMap_Impl
begin

(*@impl Map
  @type ('k,'v) ahm
  @abbrv ahm,a
  Array based hash maps without explicit invariant.
*)

subsection {* Abstract type definition *}

typedef (open) ('key :: hashable, 'val) hashmap =
  "{hm :: ('key, 'val) ArrayHashMap_Impl.hashmap. ArrayHashMap_Impl.ahm_invar hm}"
  morphisms impl_of HashMap
proof
  interpret map_empty ArrayHashMap_Impl.ahm_\<alpha> ArrayHashMap_Impl.ahm_invar ArrayHashMap_Impl.ahm_empty
    by(rule ahm_empty_impl)
  show "ArrayHashMap_Impl.ahm_empty () \<in> ?hashmap"
    by(simp add: empty_correct)
qed

type_synonym ('k,'v) ahm = "('k,'v) hashmap"

lemma ahm_invar_impl_of [simp, intro]: "ArrayHashMap_Impl.ahm_invar (impl_of hm)"
using impl_of[of hm] by simp

lemma HashMap_impl_of [code abstype]: "HashMap (impl_of t) = t"
by(rule impl_of_inverse)

subsection {* Primitive operations *}

definition ahm_empty_const :: "('key :: hashable, 'val) hashmap"
where "ahm_empty_const \<equiv> (HashMap (ArrayHashMap_Impl.ahm_empty ()))"

definition ahm_empty :: "unit \<Rightarrow> ('key :: hashable, 'val) hashmap"
where "ahm_empty \<equiv> \<lambda>_. ahm_empty_const"

definition ahm_\<alpha> :: "('key :: hashable, 'val) hashmap \<Rightarrow> 'key \<Rightarrow> 'val option"
where "ahm_\<alpha> hm = ArrayHashMap_Impl.ahm_\<alpha> (impl_of hm)"

definition ahm_lookup :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> 'val option"
where "ahm_lookup k hm = ArrayHashMap_Impl.ahm_lookup k (impl_of hm)"

definition ahm_iteratei :: "('key :: hashable, 'val) hashmap \<Rightarrow> ('key \<times> 'val, '\<sigma>) set_iterator"
where "ahm_iteratei hm = ArrayHashMap_Impl.ahm_iteratei (impl_of hm)"

definition ahm_update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_update k v hm = HashMap (ArrayHashMap_Impl.ahm_update k v (impl_of hm))"

definition ahm_delete :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_delete k hm = HashMap (ArrayHashMap_Impl.ahm_delete k (impl_of hm))"

lemma impl_of_ahm_empty [code abstract]:
  "impl_of ahm_empty_const = ArrayHashMap_Impl.ahm_empty ()"
by(simp add: ahm_empty_const_def HashMap_inverse)

lemma impl_of_ahm_update [code abstract]:
  "impl_of (ahm_update k v hm) = ArrayHashMap_Impl.ahm_update k v (impl_of hm)"
by(simp add: ahm_update_def HashMap_inverse ahm_update_correct)

lemma impl_of_ahm_delete [code abstract]:
  "impl_of (ahm_delete k hm) = ArrayHashMap_Impl.ahm_delete k (impl_of hm)"
by(simp add: ahm_delete_def HashMap_inverse ahm_delete_correct)

subsection {* Derived operations. *}

abbreviation (input) ahm_invar :: "('key :: hashable, 'val) hashmap \<Rightarrow> bool"
where "ahm_invar \<equiv> \<lambda>_. True"

text {*
  Implementation for @{text "ahm_update_dj"} and @{text "ahm_add_dj"} could be more efficient: 
  Adjusting the size field of the hashmap need not check whether the key
  was in the domain before and for we could just use Cons for updating the bucket.
*}
definition "ahm_update_dj == ahm_update"


definition "ahm_add == it_add ahm_update ahm_iteratei"
definition "ahm_add_dj == ahm_add"
definition "ahm_isEmpty == iti_isEmpty ahm_iteratei"
definition "ahm_sel == iti_sel ahm_iteratei"
definition "ahm_sel' == iti_sel_no_map ahm_iteratei"

definition "ahm_to_list == it_map_to_list ahm_iteratei"
definition "list_to_ahm == gen_list_to_map ahm_empty ahm_update"

lemmas ahm_defs = 
  ahm_\<alpha>_def
  ahm_empty_def
  ahm_lookup_def
  ahm_update_def
  ahm_update_dj_def
  ahm_delete_def
  ahm_iteratei_def
  ahm_add_def
  ahm_add_dj_def
  ahm_isEmpty_def
  ahm_sel_def
  ahm_sel'_def
  ahm_to_list_def
  list_to_ahm_def

subsection {* Correctness *}

lemma finite_dom_ahm_\<alpha>:
  "finite (dom (ahm_\<alpha> hm))"
by(simp add: ahm_\<alpha>_def finite_dom_ahm_\<alpha>)

lemma finite_map_ahm_\<alpha>:
  "finite_map ahm_\<alpha> ahm_invar"
by(unfold_locales)(rule finite_dom_ahm_\<alpha>)

interpretation ahm!: finite_map ahm_\<alpha> ahm_invar
by(rule finite_map_ahm_\<alpha>)

lemma ahm_empty_correct [simp]: "ahm_\<alpha> (ahm_empty ()) = Map.empty"
by(simp add: ahm_\<alpha>_def ahm_empty_def ahm_empty_const_def HashMap_inverse)

lemma ahm_empty_impl: "map_empty ahm_\<alpha> ahm_invar ahm_empty"
by unfold_locales simp_all

interpretation ahm!: map_empty ahm_\<alpha> ahm_invar ahm_empty by(rule ahm_empty_impl)

lemma ahm_lookup_impl: "map_lookup ahm_\<alpha> ahm_invar ahm_lookup"
by(unfold_locales)(simp add: ahm_lookup_def ArrayHashMap_Impl.ahm_lookup_def ahm_\<alpha>_def)

interpretation ahm!: map_lookup ahm_\<alpha> ahm_invar ahm_lookup by(rule ahm_lookup_impl)

lemma ahm_iteratei_impl:
  "map_iteratei ahm_\<alpha> ahm_invar ahm_iteratei"
proof
  fix m :: "('a, 'b) hashmap"

  from map_iteratei.iteratei_rule [OF ahm_iteratei_correct, of "impl_of m"]
  show "map_iterator (ahm_iteratei m) (ahm_\<alpha> m)" 
    unfolding ahm_iteratei_def ahm_\<alpha>_def 
    by simp
qed

interpretation ahm!: map_iteratei ahm_\<alpha> ahm_invar ahm_iteratei
by(rule ahm_iteratei_impl)

lemma ahm_update_correct: "ahm_\<alpha> (ahm_update k v hm) = (ahm_\<alpha> hm)(k \<mapsto> v)"
by(simp add: ahm_\<alpha>_def ahm_update_def ahm_update_correct HashMap_inverse)

lemma ahm_update_impl:
  "map_update ahm_\<alpha> ahm_invar ahm_update"
by(unfold_locales)(simp_all add: ahm_update_correct)

interpretation ahm!: map_update ahm_\<alpha> ahm_invar ahm_update by(rule ahm_update_impl)

lemma ahm_delete_correct:
  "ahm_\<alpha> (ahm_delete k hm) = (ahm_\<alpha> hm) |` (- {k})"
by(simp add: ahm_\<alpha>_def ahm_delete_def HashMap_inverse ahm_delete_correct)

lemma ahm_delete_impl:
  "map_delete ahm_\<alpha> ahm_invar ahm_delete"
by(unfold_locales)(blast intro: ahm_delete_correct)+

interpretation ahm!: map_delete ahm_\<alpha> ahm_invar ahm_delete by(rule ahm_delete_impl)

lemma ahm_update_dj_impl: "map_update_dj ahm_\<alpha> ahm_invar ahm_update_dj"
unfolding ahm_update_dj_def
by(rule map_update.update_dj_by_update)(rule ahm_update_impl)

lemma ahm_add_impl: "map_add ahm_\<alpha> ahm_invar ahm_add"
unfolding ahm_add_def by(rule it_add_correct)(rule ahm_iteratei_impl ahm_update_impl)+

lemma ahm_add_dj_impl: "map_add_dj ahm_\<alpha> ahm_invar ahm_add_dj"
unfolding ahm_add_dj_def by(rule map_add.add_dj_by_add)(rule ahm_add_impl)

lemma ahm_isEmpty_impl: "map_isEmpty ahm_\<alpha> ahm_invar ahm_isEmpty"
unfolding ahm_isEmpty_def by(rule iti_isEmpty_correct)(rule ahm_iteratei_impl)

lemma ahm_sel_impl: "map_sel ahm_\<alpha> ahm_invar ahm_sel"
unfolding ahm_sel_def by(rule iti_sel_correct)(rule ahm_iteratei_impl)

lemma ahm_sel'_impl: "map_sel' ahm_\<alpha> ahm_invar ahm_sel'"
unfolding ahm_sel'_def by (rule iti_sel'_correct) (rule ahm_iteratei_impl)

lemma ahm_to_list_impl: "map_to_list ahm_\<alpha> ahm_invar ahm_to_list"
unfolding ahm_to_list_def by(rule it_map_to_list_correct)(rule ahm_iteratei_impl)

lemma list_to_ahm_impl: "list_to_map ahm_\<alpha> ahm_invar list_to_ahm"
unfolding list_to_ahm_def by(rule gen_list_to_map_correct)(rule ahm_empty_impl ahm_update_impl)+

interpretation ahm!: map_update_dj ahm_\<alpha> ahm_invar ahm_update_dj 
  using ahm_update_dj_impl .
interpretation ahm!: map_add ahm_\<alpha> ahm_invar ahm_add 
  using ahm_add_impl .
interpretation ahm!: map_add_dj ahm_\<alpha> ahm_invar ahm_add_dj 
  using ahm_add_dj_impl .
interpretation ahm!: map_isEmpty ahm_\<alpha> ahm_invar ahm_isEmpty 
  using ahm_isEmpty_impl .
interpretation ahm!: map_sel ahm_\<alpha> ahm_invar ahm_sel 
  using ahm_sel_impl .
interpretation ahm!: map_sel' ahm_\<alpha> ahm_invar ahm_sel'
  using ahm_sel'_impl .
interpretation ahm!: map_to_list ahm_\<alpha> ahm_invar ahm_to_list
  using ahm_to_list_impl .
interpretation ahm!: list_to_map ahm_\<alpha> ahm_invar list_to_ahm 
  using list_to_ahm_impl . 

declare ahm.finite[simp del, rule del]

lemmas ahm_correct =
  ahm.empty_correct
  ahm.lookup_correct
  ahm.update_correct
  ahm.update_dj_correct
  ahm.delete_correct
  ahm.add_correct
  ahm.add_dj_correct
  ahm.isEmpty_correct
  ahm.to_list_correct
  ahm.to_map_correct

subsection "Code Generation"

export_code
  ahm_empty
  ahm_lookup
  ahm_update
  ahm_update_dj
  ahm_delete
  ahm_iteratei
  ahm_add
  ahm_add_dj
  ahm_isEmpty
  ahm_sel
  ahm_sel'
  ahm_to_list
  list_to_ahm
  in SML
  module_name ArrayHashMap
  file -

end

