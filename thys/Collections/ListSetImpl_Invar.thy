(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Set Implementation by List with explicit invariants} *}
theory ListSetImpl_Invar
imports SetSpec SetGA "common/Misc" "common/Dlist_add"
begin
text_raw {*\label{thy:ListSetImpl}*}

text {*
  In this theory, sets are implemented by lists with explicit distinctness invariant. Abbreviations: lsi,l
*}


type_synonym
  'a lsi = "'a list"

subsection "Definitions"

definition lsi_\<alpha> :: "'a lsi \<Rightarrow> 'a set" where "lsi_\<alpha> == set"
definition lsi_invar :: "'a lsi \<Rightarrow> bool" where "lsi_invar == distinct"
definition lsi_empty :: "'a lsi" where "lsi_empty == []"
definition lsi_memb :: "'a \<Rightarrow> 'a lsi \<Rightarrow> bool" where "lsi_memb x l == List.member l x"
definition lsi_ins :: "'a \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" where "lsi_ins x l == if  List.member l x then l else x#l"
definition lsi_ins_dj :: "'a \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" where "lsi_ins_dj x l == x#l"

definition lsi_delete :: "'a \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" where "lsi_delete x l == Dlist_add.remove1' x [] l"

definition lsi_iteratei :: "('a lsi,'a,'\<sigma>) iteratori" 
where "lsi_iteratei = Dlist_add.iteratei_aux"

definition lsi_iterate :: "('a lsi,'a,'\<sigma>) iterator" 
  where "lsi_iterate == iti_iterate lsi_iteratei"

definition lsi_isEmpty :: "'a lsi \<Rightarrow> bool" where "lsi_isEmpty s == s=[]"

definition lsi_union :: "'a lsi \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" 
  where "lsi_union == it_union lsi_iterate lsi_ins"
definition lsi_inter :: "'a lsi \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" 
  where "lsi_inter == it_inter lsi_iterate lsi_memb lsi_empty lsi_ins_dj"
definition lsi_union_dj :: "'a lsi \<Rightarrow> 'a lsi \<Rightarrow> 'a lsi" 
  where "lsi_union_dj s1 s2 == revg s1 s2" -- "Union of disjoint sets"

definition lsi_image_filter 
  where "lsi_image_filter == it_image_filter lsi_iterate lsi_empty lsi_ins"

definition lsi_inj_image_filter 
  where "lsi_inj_image_filter == it_inj_image_filter lsi_iterate lsi_empty lsi_ins_dj"

definition "lsi_image == iflt_image lsi_image_filter"
definition "lsi_inj_image == iflt_inj_image lsi_inj_image_filter"

definition lsi_sel :: "'a lsi \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "lsi_sel == iti_sel lsi_iteratei"
definition "lsi_sel' == SetGA.sel_sel' lsi_sel"

definition lsi_to_list :: "'a lsi \<Rightarrow> 'a list" where "lsi_to_list == id"
definition list_to_lsi :: "'a list \<Rightarrow> 'a lsi" where "list_to_lsi == remdups"

subsection "Correctness"
lemmas lsi_defs = 
  lsi_\<alpha>_def
  lsi_invar_def
  lsi_empty_def
  lsi_memb_def
  lsi_ins_def
  lsi_ins_dj_def
  lsi_delete_def
  lsi_iteratei_def
  lsi_iterate_def
  lsi_isEmpty_def
  lsi_union_def
  lsi_inter_def
  lsi_union_dj_def
  lsi_image_filter_def
  lsi_inj_image_filter_def
  lsi_image_def
  lsi_inj_image_def
  lsi_sel_def
  lsi_sel'_def
  lsi_to_list_def
  list_to_lsi_def

lemma lsi_empty_impl: "set_empty lsi_\<alpha> lsi_invar lsi_empty"
by (unfold_locales) (auto simp add: lsi_defs)

lemma lsi_memb_impl: "set_memb lsi_\<alpha> lsi_invar lsi_memb"
by (unfold_locales)(auto simp add: lsi_defs in_set_member)

lemma lsi_ins_impl: "set_ins lsi_\<alpha> lsi_invar lsi_ins"
by (unfold_locales) (auto simp add: lsi_defs in_set_member)

lemma lsi_ins_dj_impl: "set_ins_dj lsi_\<alpha> lsi_invar lsi_ins_dj"
by (unfold_locales) (auto simp add: lsi_defs)

lemma lsi_delete_impl: "set_delete lsi_\<alpha> lsi_invar lsi_delete"
by(unfold_locales)(simp_all add: lsi_defs set_remove1' distinct_remove1')

lemma lsi_\<alpha>_finite[simp, intro!]: "finite (lsi_\<alpha> l)"
  by (auto simp add: lsi_defs)

lemma lsi_is_finite_set: "finite_set lsi_\<alpha> lsi_invar"
by (unfold_locales) (auto simp add: lsi_defs)

lemma lsi_iteratei_impl: "set_iteratei lsi_\<alpha> lsi_invar lsi_iteratei"
by(unfold_locales)(simp, unfold lsi_invar_def lsi_\<alpha>_def lsi_iteratei_def, rule Dlist_add.iteratei_aux_correct)

lemmas lsi_iterate_impl = set_iteratei.iti_iterate_correct[OF lsi_iteratei_impl, folded lsi_iterate_def]

lemma lsi_isEmpty_impl: "set_isEmpty lsi_\<alpha> lsi_invar lsi_isEmpty"
by(unfold_locales)(auto simp add: lsi_defs)

lemmas lsi_union_impl = it_union_correct[OF lsi_iterate_impl lsi_ins_impl, folded lsi_union_def] 

lemmas lsi_inter_impl = it_inter_correct[OF lsi_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lsi_inter_def]

lemma lsi_union_dj_impl: "set_union_dj lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_union_dj"
by(unfold_locales)(auto simp add: lsi_defs)

lemmas lsi_image_filter_impl = it_image_filter_correct[OF lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded lsi_image_filter_def]
lemmas lsi_inj_image_filter_impl = it_inj_image_filter_correct[OF lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lsi_inj_image_filter_def]

lemmas lsi_image_impl = iflt_image_correct[OF lsi_image_filter_impl, folded lsi_image_def]
lemmas lsi_inj_image_impl = iflt_inj_image_correct[OF lsi_inj_image_filter_impl, folded lsi_inj_image_def]

lemmas lsi_sel_impl = iti_sel_correct[OF lsi_iteratei_impl, folded lsi_sel_def]
lemmas lsi_sel'_impl = SetGA.sel_sel'_correct[OF lsi_sel_impl, folded lsi_sel'_def]

lemma lsi_to_list_impl: "set_to_list lsi_\<alpha> lsi_invar lsi_to_list"
by(unfold_locales)(auto simp add: lsi_defs)

lemma list_to_lsi_impl: "list_to_set lsi_\<alpha> lsi_invar list_to_lsi"
by(unfold_locales)(auto simp add: lsi_defs)

interpretation lsi: set_empty lsi_\<alpha> lsi_invar lsi_empty using lsi_empty_impl .
interpretation lsi: set_memb lsi_\<alpha> lsi_invar lsi_memb using lsi_memb_impl .   
interpretation lsi: set_ins lsi_\<alpha> lsi_invar lsi_ins using lsi_ins_impl .      
interpretation lsi: set_ins_dj lsi_\<alpha> lsi_invar lsi_ins_dj using lsi_ins_dj_impl .
interpretation lsi: set_delete lsi_\<alpha> lsi_invar lsi_delete using lsi_delete_impl .
interpretation lsi: finite_set lsi_\<alpha> lsi_invar using lsi_is_finite_set .
interpretation lsi: set_iteratei lsi_\<alpha> lsi_invar lsi_iteratei using lsi_iteratei_impl .
interpretation lsi: set_iterate lsi_\<alpha> lsi_invar lsi_iterate using lsi_iterate_impl .
interpretation lsi: set_isEmpty lsi_\<alpha> lsi_invar lsi_isEmpty using lsi_isEmpty_impl .
interpretation lsi: set_union lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_union using lsi_union_impl .
interpretation lsi: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_inter using lsi_inter_impl .
interpretation lsi: set_union_dj lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_union_dj using lsi_union_dj_impl .
interpretation lsi: set_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_image_filter using lsi_image_filter_impl .
interpretation lsi: set_inj_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_inj_image_filter using lsi_inj_image_filter_impl .
interpretation lsi: set_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_image using lsi_image_impl .
interpretation lsi: set_inj_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_inj_image using lsi_inj_image_impl .
interpretation lsi: set_sel lsi_\<alpha> lsi_invar lsi_sel using lsi_sel_impl .
interpretation lsi: set_sel' lsi_\<alpha> lsi_invar lsi_sel' using lsi_sel'_impl .
interpretation lsi: set_to_list lsi_\<alpha> lsi_invar lsi_to_list using lsi_to_list_impl .
interpretation lsi: list_to_set lsi_\<alpha> lsi_invar list_to_lsi using list_to_lsi_impl .

declare lsi.finite[simp del, rule del]

lemmas lsi_correct =
  lsi.empty_correct                                                                                                 
  lsi.memb_correct                                                                                                  
  lsi.ins_correct                                                                                                   
  lsi.ins_dj_correct
  lsi.delete_correct
  lsi.isEmpty_correct
  lsi.union_correct
  lsi.inter_correct
  lsi.union_dj_correct
  lsi.image_filter_correct
  lsi.inj_image_filter_correct
  lsi.image_correct
  lsi.inj_image_correct
  lsi.to_list_correct
  lsi.to_set_correct


subsection "Code Generation"

lemma ls_iterate_code [code]:
  "lsi_iterate f [] \<sigma> = \<sigma>"
  "lsi_iterate f (x # xs) \<sigma> = lsi_iterate f xs (f x \<sigma>)"
by(simp_all add: lsi_defs iti_iterate_def)

export_code
  lsi_empty
  lsi_memb
  lsi_ins
  lsi_ins_dj
  lsi_delete
  lsi_iteratei
  lsi_iterate
  lsi_isEmpty
  lsi_union
  lsi_inter
  lsi_union_dj
  lsi_image_filter
  lsi_inj_image_filter
  lsi_image
  lsi_inj_image
  lsi_sel
  lsi_sel'
  lsi_to_list
  list_to_lsi
  in SML
  module_name ListSet
  file -

end
