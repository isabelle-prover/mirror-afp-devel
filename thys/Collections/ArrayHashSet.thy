(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
theory ArrayHashSet
imports ArrayHashMap SetByMap SetGA
begin

text {*
  This implementation is based on the corresponding map implementation.
  Abbreviations: ahs,a
*}

subsection "Definitions"
types
  'a ahs = "('a::hashable,unit) ahm"

definition ahs_\<alpha> :: "'a::hashable ahs \<Rightarrow> 'a set" where "ahs_\<alpha> == s_\<alpha> ahm_\<alpha>"
abbreviation (input) ahs_invar :: "'a::hashable ahs \<Rightarrow> bool" where "ahs_invar == ahm_invar"
definition ahs_empty :: "'a::hashable ahs" where "ahs_empty == s_empty ahm_empty"
definition ahs_memb :: "'a::hashable \<Rightarrow> 'a ahs \<Rightarrow> bool" 
  where "ahs_memb == s_memb ahm_lookup"
definition ahs_ins :: "'a::hashable \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" 
  where "ahs_ins == s_ins ahm_update"
definition ahs_ins_dj :: "'a::hashable \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" where
  "ahs_ins_dj == s_ins_dj ahm_update_dj"
definition ahs_delete :: "'a::hashable \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" 
  where "ahs_delete == s_delete ahm_delete"
definition ahs_sel :: "'a::hashable ahs \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "ahs_sel == s_sel ahm_sel"
definition ahs_isEmpty :: "'a::hashable ahs \<Rightarrow> bool"
  where "ahs_isEmpty == s_isEmpty ahm_isEmpty"

definition ahs_iterate :: "('a::hashable ahs,'a,'\<sigma>) iterator" 
  where "ahs_iterate == s_iterate ahm_iterate"
definition ahs_iteratei :: "('a::hashable ahs,'a,'\<sigma>) iteratori" 
  where "ahs_iteratei == s_iteratei ahm_iteratei"

definition ahs_ball :: "'a::hashable ahs \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "ahs_ball == s_ball ahm_ball"
definition ahs_union :: "'a::hashable ahs \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" 
  where "ahs_union == s_union ahm_add"
definition ahs_union_dj :: "'a::hashable ahs \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" 
  where "ahs_union_dj == s_union_dj ahm_add_dj"
definition ahs_inter :: "'a::hashable ahs \<Rightarrow> 'a ahs \<Rightarrow> 'a ahs" 
  where "ahs_inter == it_inter ahs_iterate ahs_memb ahs_empty ahs_ins_dj"

definition "ahs_size == it_size ahs_iterate"

definition ahs_image_filter 
  where "ahs_image_filter == it_image_filter ahs_iterate ahs_empty ahs_ins"
definition ahs_inj_image_filter 
  where "ahs_inj_image_filter == it_inj_image_filter ahs_iterate ahs_empty ahs_ins_dj"

definition ahs_image where "ahs_image == iflt_image ahs_image_filter"
definition ahs_inj_image where "ahs_inj_image == iflt_inj_image ahs_inj_image_filter"

definition "ahs_to_list == it_set_to_list ahs_iterate"
definition "list_to_ahs == gen_list_to_set ahs_empty ahs_ins"

subsection "Correctness"

lemmas ahs_defs =
  list_to_ahs_def
  ahs_\<alpha>_def
  ahs_ball_def
  ahs_delete_def
  ahs_empty_def
  ahs_image_def
  ahs_image_filter_def
  ahs_inj_image_def
  ahs_inj_image_filter_def
  ahs_ins_def
  ahs_ins_dj_def
  ahs_inter_def
  ahs_isEmpty_def
  ahs_iterate_def
  ahs_iteratei_def
  ahs_memb_def
  ahs_sel_def
  ahs_size_def
  ahs_to_list_def
  ahs_union_def
  ahs_union_dj_def


lemmas ahs_empty_impl = s_empty_correct[OF ahm_empty_impl, folded ahs_defs]
lemmas ahs_memb_impl = s_memb_correct[OF ahm_lookup_impl, folded ahs_defs]
lemmas ahs_ins_impl = s_ins_correct[OF ahm_update_impl, folded ahs_defs]
lemmas ahs_ins_dj_impl = s_ins_dj_correct[OF ahm_update_dj_impl, folded ahs_defs]
lemmas ahs_delete_impl = s_delete_correct[OF ahm_delete_impl, folded ahs_defs]
lemmas ahs_iteratei_impl = s_iteratei_correct[OF ahm_iteratei_impl, folded ahs_defs]
lemmas ahs_iterate_impl = s_iterate_correct[OF ahm_iterate_impl, folded ahs_defs]
lemmas ahs_isEmpty_impl = s_isEmpty_correct[OF ahm_isEmpty_impl, folded ahs_defs]
lemmas ahs_union_impl = s_union_correct[OF ahm_add_impl, folded ahs_defs]
lemmas ahs_union_dj_impl = s_union_dj_correct[OF ahm_add_dj_impl, folded ahs_defs]
lemmas ahs_ball_impl = s_ball_correct[OF ahm_ball_impl, folded ahs_defs]
lemmas ahs_sel_impl = s_sel_correct[OF ahm_sel_impl, folded ahs_defs]
lemmas ahs_inter_impl = it_inter_correct[OF ahs_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded ahs_inter_def]
lemmas ahs_size_impl = it_size_correct[OF ahs_iterate_impl, folded ahs_size_def]
lemmas ahs_image_filter_impl = it_image_filter_correct[OF ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ahs_image_filter_def]
lemmas ahs_inj_image_filter_impl = it_inj_image_filter_correct[OF ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ahs_inj_image_filter_def]
lemmas ahs_image_impl = iflt_image_correct[OF ahs_image_filter_impl, folded ahs_image_def]
lemmas ahs_inj_image_impl = iflt_inj_image_correct[OF ahs_inj_image_filter_impl, folded ahs_inj_image_def]
lemmas ahs_to_list_impl = it_set_to_list_correct[OF ahs_iterate_impl, folded ahs_to_list_def]
lemmas list_to_ahs_impl = gen_list_to_set_correct[OF ahs_empty_impl ahs_ins_impl, folded list_to_ahs_def]


interpretation ahs: set_iteratei ahs_\<alpha> ahs_invar ahs_iteratei using ahs_iteratei_impl .                               
interpretation ahs: set_iterate ahs_\<alpha> ahs_invar ahs_iterate using ahs_iterate_impl .

interpretation ahs: set_inj_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_inj_image_filter using ahs_inj_image_filter_impl .
interpretation ahs: set_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_image_filter using ahs_image_filter_impl .
interpretation ahs: set_inj_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_inj_image using ahs_inj_image_impl .
interpretation ahs: set_union_dj ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_union_dj using ahs_union_dj_impl .
interpretation ahs: set_union ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_union using ahs_union_impl .
interpretation ahs: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_inter using ahs_inter_impl .
interpretation ahs: set_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_image using ahs_image_impl .
interpretation ahs: set_sel ahs_\<alpha> ahs_invar ahs_sel using ahs_sel_impl .
interpretation ahs: set_ins_dj ahs_\<alpha> ahs_invar ahs_ins_dj using ahs_ins_dj_impl .
interpretation ahs: set_delete ahs_\<alpha> ahs_invar ahs_delete using ahs_delete_impl .
interpretation ahs: set_ball ahs_\<alpha> ahs_invar ahs_ball using ahs_ball_impl .
interpretation ahs: set_ins ahs_\<alpha> ahs_invar ahs_ins using ahs_ins_impl .
interpretation ahs: set_memb ahs_\<alpha> ahs_invar ahs_memb using ahs_memb_impl .
interpretation ahs: set_to_list ahs_\<alpha> ahs_invar ahs_to_list using ahs_to_list_impl .
interpretation ahs: list_to_set ahs_\<alpha> ahs_invar list_to_ahs using list_to_ahs_impl .
interpretation ahs: set_isEmpty ahs_\<alpha> ahs_invar ahs_isEmpty using ahs_isEmpty_impl .
interpretation ahs: set_size ahs_\<alpha> ahs_invar ahs_size using ahs_size_impl .
interpretation ahs: set_empty ahs_\<alpha> ahs_invar ahs_empty using ahs_empty_impl .


lemmas ahs_correct = 
  ahs.inj_image_filter_correct
  ahs.image_filter_correct
  ahs.inj_image_correct
  ahs.union_dj_correct
  ahs.union_correct
  ahs.inter_correct
  ahs.image_correct
  ahs.ins_dj_correct
  ahs.delete_correct
  ahs.ball_correct
  ahs.ins_correct
  ahs.memb_correct
  ahs.to_list_correct
  ahs.to_set_correct
  ahs.isEmpty_correct
  ahs.size_correct
  ahs.empty_correct

subsection "Code Generation"
export_code
  ahs_iteratei
  ahs_iterate
  ahs_inj_image_filter
  ahs_image_filter
  ahs_inj_image
  ahs_union_dj
  ahs_union
  ahs_inter
  ahs_image
  ahs_sel
  ahs_ins_dj
  ahs_delete
  ahs_ball
  ahs_ins
  ahs_memb
  ahs_to_list
  list_to_ahs
  ahs_isEmpty
  ahs_size
  ahs_empty
  in SML
  module_name RBTSet
  file -

end
