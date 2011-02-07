(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Set implementation via tries} *}
theory TrieSetImpl imports
  TrieMapImpl
  SetByMap
  SetGA
begin

text {*
  This implementation is based on the corresponding map implementation.
  Abbreviations: ts,t
*}

subsection "Definitions"

types
  'a ts = "('a, unit) trie"

definition ts_\<alpha> :: "'a ts \<Rightarrow> 'a list set" 
where "ts_\<alpha> == s_\<alpha> tm_\<alpha>"

abbreviation (input) ts_invar :: "'a ts \<Rightarrow> bool"
where "ts_invar == \<lambda>_. True"

definition ts_empty :: "'a ts" 
where "ts_empty == s_empty tm_empty"

definition ts_memb :: "'a list \<Rightarrow> 'a ts \<Rightarrow> bool" 
where "ts_memb == s_memb tm_lookup"

definition ts_ins :: "'a list \<Rightarrow> 'a ts \<Rightarrow> 'a ts" 
where "ts_ins == s_ins tm_update"

definition ts_ins_dj :: "'a list \<Rightarrow> 'a ts \<Rightarrow> 'a ts" where
  "ts_ins_dj == s_ins_dj tm_update_dj"

definition ts_delete :: "'a list \<Rightarrow> 'a ts \<Rightarrow> 'a ts" 
  where "ts_delete == s_delete tm_delete"

definition ts_sel :: "'a ts \<Rightarrow> ('a list \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "ts_sel == s_sel tm_sel"

definition "ts_sel' == sel_sel' ts_sel"

definition ts_isEmpty :: "'a ts \<Rightarrow> bool"
  where "ts_isEmpty == s_isEmpty tm_isEmpty"

definition ts_iterate :: "('a ts,'a list,'\<sigma>) iterator" 
  where "ts_iterate == s_iterate tm_iterate"

definition ts_iteratei :: "('a ts,'a list,'\<sigma>) iteratori" 
  where "ts_iteratei == s_iteratei tm_iteratei"

definition ts_ball :: "'a ts \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "ts_ball == s_ball tm_ball"

definition ts_union :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> 'a ts" 
  where "ts_union == s_union tm_add"

definition ts_union_dj :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> 'a ts" 
  where "ts_union_dj == s_union_dj tm_add_dj"

definition ts_inter :: "'a ts \<Rightarrow> 'a ts \<Rightarrow> 'a ts" 
  where "ts_inter == it_inter ts_iterate ts_memb ts_empty ts_ins_dj"

definition ts_size :: "'a ts \<Rightarrow> nat"
where "ts_size == it_size ts_iterate"

definition ts_image_filter 
  where "ts_image_filter == it_image_filter ts_iterate ts_empty ts_ins"

definition ts_inj_image_filter 
  where "ts_inj_image_filter == it_inj_image_filter ts_iterate ts_empty ts_ins_dj"

definition ts_image where "ts_image == iflt_image ts_image_filter"
definition ts_inj_image where "ts_inj_image == iflt_inj_image ts_inj_image_filter"

definition "ts_to_list == it_set_to_list ts_iterate"
definition "list_to_ts == gen_list_to_set ts_empty ts_ins"

subsection "Correctness"

lemmas ts_defs =
  list_to_ts_def
  ts_\<alpha>_def
  ts_ball_def
  ts_delete_def
  ts_empty_def
  ts_image_def
  ts_image_filter_def
  ts_inj_image_def
  ts_inj_image_filter_def
  ts_ins_def
  ts_ins_dj_def
  ts_inter_def
  ts_isEmpty_def
  ts_iterate_def
  ts_iteratei_def
  ts_memb_def
  ts_sel_def
  ts_sel'_def
  ts_size_def
  ts_to_list_def
  ts_union_def
  ts_union_dj_def

lemmas ts_empty_impl = s_empty_correct[OF tm_empty_impl, folded ts_defs]
lemmas ts_memb_impl = s_memb_correct[OF tm_lookup_impl, folded ts_defs]
lemmas ts_ins_impl = s_ins_correct[OF tm_update_impl, folded ts_defs]
lemmas ts_ins_dj_impl = s_ins_dj_correct[OF tm_update_dj_impl, folded ts_defs]
lemmas ts_delete_impl = s_delete_correct[OF tm_delete_impl, folded ts_defs]
lemmas ts_iteratei_impl = s_iteratei_correct[OF tm_iteratei_impl, folded ts_defs]
lemmas ts_iterate_impl = s_iterate_correct[OF tm_iterate_impl, folded ts_defs]
lemmas ts_isEmpty_impl = s_isEmpty_correct[OF tm_isEmpty_impl, folded ts_defs]
lemmas ts_union_impl = s_union_correct[OF tm_add_impl, folded ts_defs]
lemmas ts_union_dj_impl = s_union_dj_correct[OF tm_add_dj_impl, folded ts_defs]
lemmas ts_ball_impl = s_ball_correct[OF tm_ball_impl, folded ts_defs]
lemmas ts_sel_impl = s_sel_correct[OF tm_sel_impl, folded ts_defs]
lemmas ts_sel'_impl = sel_sel'_correct[OF ts_sel_impl, folded ts_defs]
lemmas ts_inter_impl = it_inter_correct[OF ts_iterate_impl ts_memb_impl ts_empty_impl ts_ins_dj_impl, folded ts_inter_def]
lemmas ts_size_impl = it_size_correct[OF ts_iterate_impl, folded ts_size_def]
lemmas ts_image_filter_impl = it_image_filter_correct[OF ts_iterate_impl ts_empty_impl ts_ins_impl, folded ts_image_filter_def]
lemmas ts_inj_image_filter_impl = it_inj_image_filter_correct[OF ts_iterate_impl ts_empty_impl ts_ins_dj_impl, folded ts_inj_image_filter_def]
lemmas ts_image_impl = iflt_image_correct[OF ts_image_filter_impl, folded ts_image_def]
lemmas ts_inj_image_impl = iflt_inj_image_correct[OF ts_inj_image_filter_impl, folded ts_inj_image_def]
lemmas ts_to_list_impl = it_set_to_list_correct[OF ts_iterate_impl, folded ts_to_list_def]
lemmas list_to_ts_impl = gen_list_to_set_correct[OF ts_empty_impl ts_ins_impl, folded list_to_ts_def]


interpretation ts: set_iteratei ts_\<alpha> ts_invar ts_iteratei using ts_iteratei_impl .                               
interpretation ts: set_iterate ts_\<alpha> ts_invar ts_iterate using ts_iterate_impl .
interpretation ts: set_inj_image_filter ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_inj_image_filter using ts_inj_image_filter_impl .
interpretation ts: set_image_filter ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_image_filter using ts_image_filter_impl .
interpretation ts: set_inj_image ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_inj_image using ts_inj_image_impl .
interpretation ts: set_union_dj ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_union_dj using ts_union_dj_impl .
interpretation ts: set_union ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_union using ts_union_impl .
interpretation ts: set_inter ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_inter using ts_inter_impl .
interpretation ts: set_image ts_\<alpha> ts_invar ts_\<alpha> ts_invar ts_image using ts_image_impl .
interpretation ts: set_sel ts_\<alpha> ts_invar ts_sel using ts_sel_impl .
interpretation ts: set_sel' ts_\<alpha> ts_invar ts_sel' using ts_sel'_impl .
interpretation ts: set_ins_dj ts_\<alpha> ts_invar ts_ins_dj using ts_ins_dj_impl .
interpretation ts: set_delete ts_\<alpha> ts_invar ts_delete using ts_delete_impl .
interpretation ts: set_ball ts_\<alpha> ts_invar ts_ball using ts_ball_impl .
interpretation ts: set_ins ts_\<alpha> ts_invar ts_ins using ts_ins_impl .
interpretation ts: set_memb ts_\<alpha> ts_invar ts_memb using ts_memb_impl .
interpretation ts: set_to_list ts_\<alpha> ts_invar ts_to_list using ts_to_list_impl .
interpretation ts: list_to_set ts_\<alpha> ts_invar list_to_ts using list_to_ts_impl .
interpretation ts: set_isEmpty ts_\<alpha> ts_invar ts_isEmpty using ts_isEmpty_impl .
interpretation ts: set_size ts_\<alpha> ts_invar ts_size using ts_size_impl .
interpretation ts: set_empty ts_\<alpha> ts_invar ts_empty using ts_empty_impl .

lemmas ts_correct = 
  ts.inj_image_filter_correct
  ts.image_filter_correct
  ts.inj_image_correct
  ts.union_dj_correct
  ts.union_correct
  ts.inter_correct
  ts.image_correct
  ts.ins_dj_correct
  ts.delete_correct
  ts.ball_correct
  ts.ins_correct
  ts.memb_correct
  ts.to_list_correct
  ts.to_set_correct
  ts.isEmpty_correct
  ts.size_correct
  ts.empty_correct

subsection "Code Generation"

export_code
  ts_iteratei
  ts_iterate
  ts_inj_image_filter
  ts_image_filter
  ts_inj_image
  ts_union_dj
  ts_union
  ts_inter
  ts_image
  ts_sel
  ts_sel'
  ts_ins_dj
  ts_delete
  ts_ball
  ts_ins
  ts_memb
  ts_to_list
  list_to_ts
  ts_isEmpty
  ts_size
  ts_empty
  in SML
  module_name TrieSet
  file -

end
