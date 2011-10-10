(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Hash maps} *}
theory HashMap imports HashMap_Impl begin

subsection "Type definition"

typedef (open) ('k, 'v) hashmap = "{hm :: ('k :: hashable, 'v) hm_impl. HashMap_Impl.invar hm}"
  morphisms impl_of_RBT_HM RBT_HM
proof
  show "HashMap_Impl.empty \<in> ?hashmap" by(simp add: HashMap_Impl.empty_correct')
qed

lemma impl_of_RBT_HM_invar [simp, intro!]: "HashMap_Impl.invar (impl_of_RBT_HM hm)"
using impl_of_RBT_HM[of hm] by simp

lemma RBT_HM_imp_of_RBT_HM [code abstype]:
  "RBT_HM (impl_of_RBT_HM hm) = hm"
by(fact impl_of_RBT_HM_inverse)

definition hm_empty :: "('k :: hashable, 'v) hashmap"
where "hm_empty = RBT_HM HashMap_Impl.empty"

definition "hm_lookup k hm == HashMap_Impl.lookup k (impl_of_RBT_HM hm)"

definition hm_update :: "('k :: hashable) \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_update k v hm = RBT_HM (HashMap_Impl.update k v (impl_of_RBT_HM hm))"

definition hm_update_dj :: "('k :: hashable) \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_update_dj = hm_update"

definition hm_delete :: "('k :: hashable) \<Rightarrow> ('k, 'v) hashmap \<Rightarrow> ('k, 'v) hashmap"
where "hm_delete k hm = RBT_HM (HashMap_Impl.delete k (impl_of_RBT_HM hm))"

definition hm_isEmpty :: "('k :: hashable, 'v) hashmap \<Rightarrow> bool"
where "hm_isEmpty hm = HashMap_Impl.isEmpty (impl_of_RBT_HM hm)"

definition hm_sel :: "('k :: hashable, 'v) hashmap \<Rightarrow> ('k \<Rightarrow> 'v \<rightharpoonup> 'a) \<rightharpoonup> 'a"
where "hm_sel hm = HashMap_Impl.sel (impl_of_RBT_HM hm)"

definition "hm_sel' = sel_sel' hm_sel"

definition "hm_iterate f hm == HashMap_Impl.iterate f (impl_of_RBT_HM hm)"
definition "hm_iteratei c f hm == HashMap_Impl.iteratei c f (impl_of_RBT_HM hm)"

lemma impl_of_hm_empty [simp, code abstract]:
  "impl_of_RBT_HM (hm_empty) = HashMap_Impl.empty"
by(simp add: hm_empty_def empty_correct' RBT_HM_inverse)

lemma impl_of_hm_update [simp, code abstract]:
  "impl_of_RBT_HM (hm_update k v hm) = HashMap_Impl.update k v (impl_of_RBT_HM hm)"
by(simp add: hm_update_def update_correct' RBT_HM_inverse)

lemma impl_of_hm_delete [simp, code abstract]:
  "impl_of_RBT_HM (hm_delete k hm) = HashMap_Impl.delete k (impl_of_RBT_HM hm)"
by(simp add: hm_delete_def delete_correct' RBT_HM_inverse)

subsection "Correctness w.r.t. Map"
text {* 
  The next lemmas establish the correctness of the hashmap operations w.r.t. the 
  associated map. This is achieved by chaining the correctness lemmas of the 
  concrete hashmap w.r.t. the abstract hashmap and the correctness lemmas of the
  abstract hashmap w.r.t. maps.
*}

type_synonym ('k, 'v) hm = "('k, 'v) hashmap"

  -- "Abstract concrete hashmap to map"
definition "hm_\<alpha> == ahm_\<alpha> \<circ> hm_\<alpha>' \<circ> impl_of_RBT_HM"

abbreviation (input) hm_invar :: "('k :: hashable, 'v) hashmap \<Rightarrow> bool"
where "hm_invar == \<lambda>_. True"


lemma hm_aux_correct:
  "hm_\<alpha> hm_empty = empty"
  "hm_lookup k m = hm_\<alpha> m k"
  "hm_\<alpha> (hm_update k v m) = (hm_\<alpha> m)(k\<mapsto>v)"
  "hm_\<alpha> (hm_delete k m) = (hm_\<alpha> m) |` (-{k})"
by(auto simp add: hm_\<alpha>_def hm_correct' ahm_correct hm_lookup_def)

subsection "Integration in Isabelle Collections Framework"
text {*
  In this section, we integrate hashmaps into the Isabelle Collections Framework.
*}

lemma hm_empty_impl: "map_empty hm_\<alpha> hm_invar hm_empty"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_lookup_impl: "map_lookup hm_\<alpha> hm_invar hm_lookup"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_update_impl: "map_update hm_\<alpha> hm_invar hm_update"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemmas hm_update_dj_impl 
  = map_update.update_dj_by_update[OF hm_update_impl, 
                                   folded hm_update_dj_def]

lemma hm_delete_impl: "map_delete hm_\<alpha> hm_invar hm_delete"
  by (unfold_locales)
     (simp_all add: hm_aux_correct)

lemma hm_finite[simp, intro!]:
  "finite (dom (hm_\<alpha> m))"
proof(cases m)
  case (RBT_HM m')
  hence SS: "dom (hm_\<alpha> m) \<subseteq> \<Union>{ dom (lm_\<alpha> lm) | lm hc. rm_\<alpha> m' hc = Some lm }"
    apply(clarsimp simp add: RBT_HM_inverse hm_\<alpha>_def hm_\<alpha>'_def_raw ahm_\<alpha>_def_raw)
    apply(auto split: option.split_asm option.split)
    done
  moreover have "finite \<dots>" (is "finite (\<Union>?A)")
  proof
    have "{ dom (lm_\<alpha> lm) | lm hc. rm_\<alpha> m' hc = Some lm } 
          \<subseteq> (\<lambda>hc. dom (lm_\<alpha> (the (rm_\<alpha> m' hc)) )) ` (dom (rm_\<alpha> m'))" 
      (is "?S \<subseteq> _")
      by force
    thus "finite ?A" by(rule finite_subset) auto
  next
    fix M
    assume "M \<in> ?A"
    thus "finite M" by auto
  qed
  ultimately show ?thesis unfolding RBT_HM by(rule finite_subset)
qed

lemma hm_is_finite_map: "finite_map hm_\<alpha> hm_invar"
by(unfold_locales) auto

lemma hm_isEmpty_impl: "map_isEmpty hm_\<alpha> hm_invar hm_isEmpty"
by(unfold_locales)(simp add: hm_isEmpty_def hm_\<alpha>_def isEmpty_correct')

lemma hm_sel_impl: "map_sel hm_\<alpha> hm_invar hm_sel"
  unfolding hm_sel_def_raw hm_\<alpha>_def o_def
  by(rule map_sel_altI)(blast intro: sel_correct'[OF impl_of_RBT_HM_invar])+

lemma hm_sel'_impl: "map_sel' hm_\<alpha> hm_invar hm_sel'"
  unfolding hm_sel'_def
  by(rule sel_sel'_correct hm_sel_impl)+

lemma hm_iterate_impl: 
  "map_iterate hm_\<alpha> hm_invar hm_iterate"
apply (unfold_locales)
apply simp
apply(unfold hm_\<alpha>_def hm_iterate_def o_def)
apply(rule iterate_correct'[OF impl_of_RBT_HM_invar]) .


lemma hm_iteratei_impl: 
  "map_iteratei hm_\<alpha> hm_invar hm_iteratei"
apply (unfold_locales)
apply simp
apply (unfold hm_\<alpha>_def hm_iteratei_def o_def)
apply(rule iteratei_correct'[OF impl_of_RBT_HM_invar]) .

definition "hm_add == it_add hm_update hm_iterate"
lemmas hm_add_impl = it_add_correct[OF hm_iterate_impl hm_update_impl, 
                                      folded hm_add_def]

definition "hm_add_dj == it_add_dj hm_update_dj hm_iterate"
lemmas hm_add_dj_impl = 
  it_add_dj_correct[OF hm_iterate_impl hm_update_dj_impl, 
                 folded hm_add_dj_def]

definition "hm_to_list == it_map_to_list hm_iterate"
lemmas hm_to_list_impl = it_map_to_list_correct[OF hm_iterate_impl, 
                                                  folded hm_to_list_def]

definition "list_to_hm == gen_list_to_map hm_empty hm_update"
lemmas list_to_hm_impl = 
  gen_list_to_map_correct[OF hm_empty_impl hm_update_impl, 
                          folded list_to_hm_def]


interpretation hm: map_empty hm_\<alpha> hm_invar hm_empty using hm_empty_impl .
interpretation hm: map_lookup hm_\<alpha> hm_invar hm_lookup using hm_lookup_impl .
interpretation hm: map_update hm_\<alpha> hm_invar hm_update using hm_update_impl .
interpretation hm: map_update_dj hm_\<alpha> hm_invar hm_update_dj using hm_update_dj_impl .
interpretation hm: map_delete hm_\<alpha> hm_invar hm_delete using hm_delete_impl .
interpretation hm: finite_map hm_\<alpha> hm_invar using hm_is_finite_map .
interpretation hm: map_sel hm_\<alpha> hm_invar hm_sel using hm_sel_impl .
interpretation hm: map_sel' hm_\<alpha> hm_invar hm_sel' using hm_sel'_impl .
interpretation hm: map_isEmpty hm_\<alpha> hm_invar hm_isEmpty using hm_isEmpty_impl .
interpretation hm: map_iterate hm_\<alpha> hm_invar hm_iterate using hm_iterate_impl .
interpretation hm: map_iteratei hm_\<alpha> hm_invar hm_iteratei using hm_iteratei_impl .
interpretation hm: map_add hm_\<alpha> hm_invar hm_add using hm_add_impl .
interpretation hm: map_add_dj hm_\<alpha> hm_invar hm_add_dj using hm_add_dj_impl .
interpretation hm: map_to_list hm_\<alpha> hm_invar hm_to_list using hm_to_list_impl .
interpretation hm: list_to_map hm_\<alpha> hm_invar list_to_hm using list_to_hm_impl .

declare hm.finite[simp del, rule del]

lemmas hm_correct =
  hm.empty_correct
  hm.lookup_correct
  hm.update_correct
  hm.update_dj_correct
  hm.delete_correct
  hm.add_correct
  hm.add_dj_correct
  hm.isEmpty_correct
  hm.to_list_correct
  hm.to_map_correct


subsection "Code Generation"

export_code 
  hm_empty
  hm_lookup
  hm_update
  hm_update_dj
  hm_delete
  hm_sel
  hm_sel'
  hm_isEmpty
  hm_iterate
  hm_iteratei
  hm_add
  hm_add_dj
  hm_to_list
  list_to_hm
  in SML
  module_name HashMap
  file -

end

