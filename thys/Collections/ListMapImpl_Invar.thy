(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Map Implementation by Association Lists with explicit invariants} *}
theory ListMapImpl_Invar
imports Main MapSpec "common/Assoc_List" MapGA
begin
text_raw {*\label{thy:ListMapImpl}*}

text {*
  In this theory, we implement maps by lists of (key,value) pairs.

  This implementation uses the abbreviations: lmi, l
 *}

type_synonym ('k,'v) lmi = "('k\<times>'v) list"

subsection "Functions"

definition "lmi_\<alpha> == Map.map_of"
definition "lmi_invar m == distinct (List.map fst m)"
definition "lmi_empty == []"
definition "lmi_lookup k m == Map.map_of m k"
definition "lmi_update == AList_Impl.update"
definition "lmi_update_dj k v m == (k, v) # m"  
definition "lmi_delete k m == Assoc_List.delete_aux k m"
definition lmi_iteratei :: "(('k,'v) lmi,'k,'v,'\<sigma>) map_iteratori"
  where "lmi_iteratei = Assoc_List.iteratei_aux"
definition "lmi_iterate == iti_iterate lmi_iteratei"
definition "lmi_isEmpty m == m=[]"

definition "lmi_add == it_add lmi_update lmi_iterate"
definition lmi_add_dj :: "('k,'v) lmi \<Rightarrow> ('k,'v) lmi \<Rightarrow> ('k,'v) lmi"
  where "lmi_add_dj m1 m2 == revg m1 m2" 

definition "lmi_sel == iti_sel lmi_iteratei"
definition "lmi_sel' == sel_sel' lmi_sel"
definition lmi_to_list :: "('u,'v) lmi \<Rightarrow> ('u\<times>'v) list"
  where "lmi_to_list = id"
definition "list_to_lmi == gen_list_to_map lmi_empty lmi_update"
definition list_to_lmi_dj :: "('u\<times>'v) list \<Rightarrow> ('u,'v) lmi"
  where "list_to_lmi_dj == id"

subsection "Correctness"
lemmas lmi_defs =
  lmi_\<alpha>_def
  lmi_invar_def
  lmi_empty_def
  lmi_lookup_def
  lmi_update_def
  lmi_update_dj_def
  lmi_delete_def
  lmi_iteratei_def
  lmi_iterate_def
  lmi_isEmpty_def
  lmi_add_def
  lmi_add_dj_def
  lmi_sel_def
  lmi_sel'_def
  lmi_to_list_def
  list_to_lmi_def
  list_to_lmi_dj_def

lemma lmi_empty_impl: 
  "map_empty lmi_\<alpha> lmi_invar lmi_empty"
  apply (unfold_locales)
  apply (auto 
    simp add: lmi_defs AList_Impl.update_conv' AList_Impl.distinct_update)
  done

interpretation lmi: map_empty lmi_\<alpha> lmi_invar lmi_empty using lmi_empty_impl .

lemma lmi_lookup_impl: 
  "map_lookup lmi_\<alpha> lmi_invar lmi_lookup"
  apply (unfold_locales)
  apply (auto 
    simp add: lmi_defs AList_Impl.update_conv' AList_Impl.distinct_update)
  done

interpretation lmi: map_lookup lmi_\<alpha> lmi_invar lmi_lookup using lmi_lookup_impl .

lemma lmi_update_impl: 
  "map_update lmi_\<alpha> lmi_invar lmi_update"
  apply (unfold_locales)
  apply (auto 
    simp add: lmi_defs AList_Impl.update_conv' AList_Impl.distinct_update)
  done

interpretation lmi: map_update lmi_\<alpha> lmi_invar lmi_update using lmi_update_impl .

lemma lmi_update_dj_impl: 
  "map_update_dj lmi_\<alpha> lmi_invar lmi_update_dj"
  apply (unfold_locales)
  apply (auto simp add: lmi_defs)
  done

interpretation lmi: map_update_dj lmi_\<alpha> lmi_invar lmi_update_dj using lmi_update_dj_impl .

lemma lmi_delete_impl: 
  "map_delete lmi_\<alpha> lmi_invar lmi_delete"
  apply (unfold_locales)
  apply (auto simp add: lmi_defs AList_Impl.update_conv' AList_Impl.distinct_update
                        Assoc_List.map_of_delete_aux')
  done

interpretation lmi: map_delete lmi_\<alpha> lmi_invar lmi_delete using lmi_delete_impl .

lemma lmi_isEmpty_impl: 
  "map_isEmpty lmi_\<alpha> lmi_invar lmi_isEmpty"
  apply (unfold_locales)
  apply (unfold lmi_defs)
  apply (case_tac m)
  apply auto
  done

interpretation lmi: map_isEmpty lmi_\<alpha> lmi_invar lmi_isEmpty using lmi_isEmpty_impl .

lemma lmi_is_finite_map: "finite_map lmi_\<alpha> lmi_invar" 
by unfold_locales(auto simp add: lmi_defs)

interpretation lmi: finite_map lmi_\<alpha> lmi_invar using lmi_is_finite_map .

lemma lmi_iteratei_impl: 
  "map_iteratei lmi_\<alpha> lmi_invar lmi_iteratei"
by(unfold_locales)(unfold lmi_iteratei_def lmi_invar_def lmi_\<alpha>_def, rule iteratei_aux_correct)

interpretation lmi: map_iteratei lmi_\<alpha> lmi_invar lmi_iteratei using lmi_iteratei_impl .

lemmas lmi_iterate_impl = lmi.iti_iterate_correct[folded lmi_iterate_def]
interpretation lmi: map_iterate lmi_\<alpha> lmi_invar lmi_iterate using lmi_iterate_impl .

declare lmi.finite[simp del, rule del]

lemma lmi_finite[simp, intro!]: "finite (dom (lmi_\<alpha> m))"
  by (auto simp add: lmi_\<alpha>_def)

lemmas lmi_add_impl = 
  it_add_correct[OF lmi_iterate_impl lmi_update_impl, folded lmi_add_def]
interpretation lmi: map_add lmi_\<alpha> lmi_invar lmi_add using lmi_add_impl .


lemma lmi_add_dj_impl: 
  shows "map_add_dj lmi_\<alpha> lmi_invar lmi_add_dj"
  apply (unfold_locales)
  apply (auto simp add: lmi_defs)
  apply (blast intro: map_add_comm)
  apply (simp add: rev_map[symmetric])
  apply fastforce
  done
  
interpretation lmi: map_add_dj lmi_\<alpha> lmi_invar lmi_add_dj using lmi_add_dj_impl .

lemmas lmi_sel_impl = iti_sel_correct[OF lmi_iteratei_impl, folded lmi_sel_def]
interpretation lmi: map_sel lmi_\<alpha> lmi_invar lmi_sel using lmi_sel_impl .

lemmas lmi_sel'_impl = sel_sel'_correct[OF lmi_sel_impl, folded lmi_sel'_def]
interpretation lmi: map_sel' lmi_\<alpha> lmi_invar lmi_sel' using lmi_sel'_impl .

lemma lmi_to_list_impl: "map_to_list lmi_\<alpha> lmi_invar lmi_to_list"
  by (unfold_locales)
     (auto simp add: lmi_defs)
interpretation lmi: map_to_list lmi_\<alpha> lmi_invar lmi_to_list using lmi_to_list_impl .

lemmas list_to_lmi_impl = 
  gen_list_to_map_correct[OF lmi_empty_impl lmi_update_impl, 
                          folded list_to_lmi_def]

interpretation lmi: list_to_map lmi_\<alpha> lmi_invar list_to_lmi 
  using list_to_lmi_impl .

lemma list_to_lmi_dj_correct: 
  assumes [simp]: "distinct (map fst l)"
  shows "lmi_\<alpha> (list_to_lmi_dj l) = map_of l"
        "lmi_invar (list_to_lmi_dj l)"
  by (auto simp add: lmi_defs)

lemma lmi_to_list_to_lm[simp]: 
  "lmi_invar m \<Longrightarrow> lmi_\<alpha> (list_to_lmi_dj (lmi_to_list m)) = lmi_\<alpha> m"
  by (simp add: lmi.to_list_correct list_to_lmi_dj_correct)

subsection "Code Generation"

lemma lmi_iterate_code [code]:
  "lmi_iterate f [] \<sigma> = \<sigma>"
  "lmi_iterate f ((k, v) # l) \<sigma> = lmi_iterate f l (f k v \<sigma>)"
by(simp_all add: lmi_defs iti_iterate_def)

lemmas lmi_correct = 
  lmi.empty_correct
  lmi.lookup_correct
  lmi.update_correct
  lmi.update_dj_correct
  lmi.delete_correct
  lmi.isEmpty_correct
  lmi.add_correct
  lmi.add_dj_correct
  lmi.to_list_correct
  lmi.to_map_correct
  list_to_lmi_dj_correct

export_code
  lmi_empty
  lmi_lookup
  lmi_update
  lmi_update_dj
  lmi_delete
  lmi_isEmpty
  lmi_iterate
  lmi_iteratei
  lmi_add
  lmi_add_dj
  lmi_sel
  lmi_sel'
  lmi_to_list
  list_to_lmi
  list_to_lmi_dj
  in SML
  module_name ListMap
  file -

end
