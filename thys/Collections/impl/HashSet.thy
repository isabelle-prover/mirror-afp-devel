(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Hash Set} *}
theory HashSet
  imports 
  "../spec/SetSpec" 
  "HashMap" 
  "../gen_algo/SetByMap" 
  "../gen_algo/SetGA"
begin
text_raw {*\label{thy:HashSet}*}
(*@impl Set
  @type 'a::hashable hs
  @abbrv hs,h
  Hash sets based on red-black trees.
*)

subsection "Definitions"
type_synonym
  'a hs = "('a::hashable,unit) hm"

definition hs_\<alpha> :: "'a::hashable hs \<Rightarrow> 'a set" where "hs_\<alpha> == s_\<alpha> hm_\<alpha>"
abbreviation (input) hs_invar :: "'a::hashable hs \<Rightarrow> bool" where "hs_invar == \<lambda>_. True"
definition hs_empty :: "unit \<Rightarrow> 'a::hashable hs" where "hs_empty == s_empty hm_empty"
definition hs_memb :: "'a::hashable \<Rightarrow> 'a hs \<Rightarrow> bool" 
  where "hs_memb == s_memb hm_lookup"
definition hs_ins :: "'a::hashable \<Rightarrow> 'a hs \<Rightarrow> 'a hs" 
  where "hs_ins == s_ins hm_update"
definition hs_ins_dj :: "'a::hashable \<Rightarrow> 'a hs \<Rightarrow> 'a hs" where
  "hs_ins_dj == s_ins_dj hm_update_dj"
definition hs_delete :: "'a::hashable \<Rightarrow> 'a hs \<Rightarrow> 'a hs" 
  where "hs_delete == s_delete hm_delete"
definition hs_sel :: "'a::hashable hs \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "hs_sel == s_sel hm_sel"
definition "hs_sel' == sel_sel' hs_sel"
definition hs_isEmpty :: "'a::hashable hs \<Rightarrow> bool"
  where "hs_isEmpty == s_isEmpty hm_isEmpty"

definition hs_iteratei :: "'a::hashable hs \<Rightarrow> ('a,'\<sigma>) set_iterator" 
  where "hs_iteratei == s_iteratei hm_iteratei"
definition hs_union :: "'a::hashable hs \<Rightarrow> 'a hs \<Rightarrow> 'a hs" 
  where "hs_union == s_union hm_add"
definition hs_union_dj :: "'a::hashable hs \<Rightarrow> 'a hs \<Rightarrow> 'a hs" 
  where "hs_union_dj == s_union_dj hm_add_dj"
definition hs_inter :: "'a::hashable hs \<Rightarrow> 'a hs \<Rightarrow> 'a hs" 
  where "hs_inter == it_inter hs_iteratei hs_memb hs_empty hs_ins_dj"
definition hs_image_filter 
  where "hs_image_filter == it_image_filter hs_iteratei hs_empty hs_ins"
definition hs_inj_image_filter 
  where "hs_inj_image_filter == it_inj_image_filter hs_iteratei hs_empty hs_ins_dj"

definition hs_image where "hs_image == iflt_image hs_image_filter"
definition hs_inj_image where "hs_inj_image == iflt_inj_image hs_inj_image_filter"

definition "hs_to_list == it_set_to_list hs_iteratei"
definition "list_to_hs == gen_list_to_set hs_empty hs_ins"

subsection "Correctness"

lemmas hs_defs =
  list_to_hs_def
  hs_\<alpha>_def
  hs_delete_def
  hs_empty_def
  hs_image_def
  hs_image_filter_def
  hs_inj_image_def
  hs_inj_image_filter_def
  hs_ins_def
  hs_ins_dj_def
  hs_inter_def
  hs_isEmpty_def
  hs_iteratei_def
  hs_memb_def
  hs_sel_def
  hs_sel'_def
  hs_to_list_def
  hs_union_def
  hs_union_dj_def


lemmas hs_empty_impl = s_empty_correct[OF hm_empty_impl, folded hs_defs]
lemmas hs_memb_impl = s_memb_correct[OF hm_lookup_impl, folded hs_defs]
lemmas hs_ins_impl = s_ins_correct[OF hm_update_impl, folded hs_defs]
lemmas hs_ins_dj_impl = s_ins_dj_correct[OF hm_update_dj_impl, folded hs_defs]
lemmas hs_delete_impl = s_delete_correct[OF hm_delete_impl, folded hs_defs]
lemmas hs_iteratei_impl = s_iteratei_correct[OF hm_iteratei_impl, folded hs_defs]
lemmas hs_isEmpty_impl = s_isEmpty_correct[OF hm_isEmpty_impl, folded hs_defs]
lemmas hs_union_impl = s_union_correct[OF hm_add_impl, folded hs_defs]
lemmas hs_union_dj_impl = s_union_dj_correct[OF hm_add_dj_impl, folded hs_defs]
lemmas hs_sel_impl = s_sel_correct[OF hm_sel_impl, folded hs_defs]
lemmas hs_sel'_impl = sel_sel'_correct[OF hs_sel_impl, folded hs_sel'_def]
lemmas hs_inter_impl = it_inter_correct[OF hs_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hs_inter_def]
lemmas hs_image_filter_impl = it_image_filter_correct[OF hs_iteratei_impl hs_empty_impl hs_ins_impl, folded hs_image_filter_def]
lemmas hs_inj_image_filter_impl = it_inj_image_filter_correct[OF hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hs_inj_image_filter_def]
lemmas hs_image_impl = iflt_image_correct[OF hs_image_filter_impl, folded hs_image_def]
lemmas hs_inj_image_impl = iflt_inj_image_correct[OF hs_inj_image_filter_impl, folded hs_inj_image_def]
lemmas hs_to_list_impl = it_set_to_list_correct[OF hs_iteratei_impl, folded hs_to_list_def]
lemmas list_to_hs_impl = gen_list_to_set_correct[OF hs_empty_impl hs_ins_impl, folded list_to_hs_def]

interpretation hs: set_iteratei hs_\<alpha> hs_invar hs_iteratei using hs_iteratei_impl .                               
interpretation hs: set_inj_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_inj_image_filter using hs_inj_image_filter_impl .
interpretation hs: set_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_image_filter using hs_image_filter_impl .
interpretation hs: set_inj_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_inj_image using hs_inj_image_impl .
interpretation hs: set_union_dj hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_union_dj using hs_union_dj_impl .
interpretation hs: set_union hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_union using hs_union_impl .
interpretation hs: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_inter using hs_inter_impl .
interpretation hs: set_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_image using hs_image_impl .
interpretation hs: set_sel hs_\<alpha> hs_invar hs_sel using hs_sel_impl .
interpretation hs: set_sel' hs_\<alpha> hs_invar hs_sel' using hs_sel'_impl .
interpretation hs: set_ins_dj hs_\<alpha> hs_invar hs_ins_dj using hs_ins_dj_impl .
interpretation hs: set_delete hs_\<alpha> hs_invar hs_delete using hs_delete_impl .
interpretation hs: set_ins hs_\<alpha> hs_invar hs_ins using hs_ins_impl .
interpretation hs: set_memb hs_\<alpha> hs_invar hs_memb using hs_memb_impl .
interpretation hs: set_to_list hs_\<alpha> hs_invar hs_to_list using hs_to_list_impl .
interpretation hs: list_to_set hs_\<alpha> hs_invar list_to_hs using list_to_hs_impl .
interpretation hs: set_isEmpty hs_\<alpha> hs_invar hs_isEmpty using hs_isEmpty_impl .
interpretation hs: set_empty hs_\<alpha> hs_invar hs_empty using hs_empty_impl .


lemmas hs_correct = 
  hs.inj_image_filter_correct
  hs.image_filter_correct
  hs.inj_image_correct
  hs.union_dj_correct
  hs.union_correct
  hs.inter_correct
  hs.image_correct
  hs.ins_dj_correct
  hs.delete_correct
  hs.ins_correct
  hs.memb_correct
  hs.to_list_correct
  hs.to_set_correct
  hs.isEmpty_correct
  hs.empty_correct

subsection "Code Generation"
export_code
  hs_iteratei
  hs_inj_image_filter
  hs_image_filter
  hs_inj_image
  hs_union_dj
  hs_union
  hs_inter
  hs_image
  hs_sel
  hs_sel'
  hs_ins_dj
  hs_delete
  hs_ins
  hs_memb
  hs_to_list
  list_to_hs
  hs_isEmpty
  hs_empty
  in SML
  module_name HashSet
  file -

end
