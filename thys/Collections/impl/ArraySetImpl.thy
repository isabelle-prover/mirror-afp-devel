header {* \isaheader{Set Implementation by Arrays} *}
theory ArraySetImpl
imports 
  "../spec/SetSpec" 
  "ArrayMapImpl" 
  "../gen_algo/SetByMap" 
  "../gen_algo/SetGA"
begin
text_raw {*\label{thy:ArraySetImpl}*}

(*@impl Set
  @type ias
  @abbrv ias,is
  Sets of natural numbers implemented by arrays.
*)

subsection "Definitions"
type_synonym ias = "(unit) iam"

definition ias_\<alpha> :: "ias \<Rightarrow> nat set" where "ias_\<alpha> == s_\<alpha> iam_\<alpha>"
abbreviation (input) ias_invar :: "ias \<Rightarrow> bool" where "ias_invar == iam_invar"
definition ias_empty :: "unit \<Rightarrow> ias" where "ias_empty == s_empty iam_empty"
definition ias_memb :: "nat \<Rightarrow> ias \<Rightarrow> bool" 
  where "ias_memb == s_memb iam_lookup"
definition ias_ins :: "nat \<Rightarrow> ias \<Rightarrow> ias" 
  where "ias_ins == s_ins iam_update"
definition ias_ins_dj :: "nat \<Rightarrow> ias \<Rightarrow> ias" where
  "ias_ins_dj == s_ins_dj iam_update_dj"
definition ias_delete :: "nat \<Rightarrow> ias \<Rightarrow> ias" 
  where "ias_delete == s_delete iam_delete"
definition ias_sel :: "ias \<Rightarrow> (nat \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "ias_sel == s_sel iam_sel"
definition "ias_sel' = sel_sel' ias_sel"
definition ias_isEmpty :: "ias \<Rightarrow> bool"
  where "ias_isEmpty == s_isEmpty iam_isEmpty"

definition ias_iteratei :: "ias \<Rightarrow> (nat,'\<sigma>) set_iterator" 
  where "ias_iteratei == s_iteratei iam_iteratei"

definition ias_union :: "ias \<Rightarrow> ias \<Rightarrow> ias" 
  where "ias_union == s_union iam_add"
definition ias_union_dj :: "ias \<Rightarrow> ias \<Rightarrow> ias" 
  where "ias_union_dj == s_union_dj iam_add_dj"
definition ias_inter :: "ias \<Rightarrow> ias \<Rightarrow> ias" 
  where "ias_inter == it_inter ias_iteratei ias_memb ias_empty ias_ins_dj"

definition ias_image_filter 
  where "ias_image_filter == it_image_filter ias_iteratei ias_empty ias_ins"
definition ias_inj_image_filter 
  where "ias_inj_image_filter == it_inj_image_filter ias_iteratei ias_empty ias_ins_dj"

definition ias_image where "ias_image == iflt_image ias_image_filter"
definition ias_inj_image where "ias_inj_image == iflt_inj_image ias_inj_image_filter"

definition "ias_to_list == it_set_to_list ias_iteratei"
definition "list_to_ias == gen_list_to_set ias_empty ias_ins"

subsection "Correctness"

lemmas ias_defs =
  list_to_ias_def
  ias_\<alpha>_def
  ias_delete_def
  ias_empty_def
  ias_image_def
  ias_image_filter_def
  ias_inj_image_def
  ias_inj_image_filter_def
  ias_ins_def
  ias_ins_dj_def
  ias_inter_def
  ias_isEmpty_def
  ias_iteratei_def
  ias_memb_def
  ias_sel_def
  ias_sel'_def
  ias_to_list_def
  ias_union_def
  ias_union_dj_def


lemmas ias_empty_impl = s_empty_correct[OF iam_empty_impl, folded ias_defs]
lemmas ias_memb_impl = s_memb_correct[OF iam_lookup_impl, folded ias_defs]
lemmas ias_ins_impl = s_ins_correct[OF iam_update_impl, folded ias_defs]
lemmas ias_ins_dj_impl = s_ins_dj_correct[OF iam_update_dj_impl, folded ias_defs]
lemmas ias_delete_impl = s_delete_correct[OF iam_delete_impl, folded ias_defs]
lemmas ias_iteratei_impl = s_iteratei_correct[OF iam_iteratei_impl, folded ias_defs]
lemmas ias_isEmpty_impl = s_isEmpty_correct[OF iam_isEmpty_impl, folded ias_defs]
lemmas ias_union_impl = s_union_correct[OF iam_add_impl, folded ias_defs]
lemmas ias_union_dj_impl = s_union_dj_correct[OF iam_add_dj_impl, folded ias_defs]
lemmas ias_sel_impl = s_sel_correct[OF iam_sel_impl, folded ias_defs]
lemmas ias_sel'_impl = sel_sel'_correct[OF ias_sel_impl, folded ias_sel'_def]
lemmas ias_inter_impl = it_inter_correct[OF ias_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded ias_inter_def]
lemmas ias_image_filter_impl = it_image_filter_correct[OF ias_iteratei_impl ias_empty_impl ias_ins_impl, folded ias_image_filter_def]
lemmas ias_inj_image_filter_impl = it_inj_image_filter_correct[OF ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ias_inj_image_filter_def]
lemmas ias_image_impl = iflt_image_correct[OF ias_image_filter_impl, folded ias_image_def]
lemmas ias_inj_image_impl = iflt_inj_image_correct[OF ias_inj_image_filter_impl, folded ias_inj_image_def]
lemmas ias_to_list_impl = it_set_to_list_correct[OF ias_iteratei_impl, folded ias_to_list_def]
lemmas list_to_ias_impl = gen_list_to_set_correct[OF ias_empty_impl ias_ins_impl, folded list_to_ias_def]

interpretation ias: set_iteratei ias_\<alpha> ias_invar ias_iteratei using ias_iteratei_impl .                               

interpretation ias: set_inj_image_filter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_inj_image_filter using ias_inj_image_filter_impl .
interpretation ias: set_image_filter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_image_filter using ias_image_filter_impl .
interpretation ias: set_inj_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_inj_image using ias_inj_image_impl .
interpretation ias: set_union_dj ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_union_dj using ias_union_dj_impl .
interpretation ias: set_union ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_union using ias_union_impl .
interpretation ias: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_inter using ias_inter_impl .
interpretation ias: set_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_image using ias_image_impl .
interpretation ias: set_sel ias_\<alpha> ias_invar ias_sel using ias_sel_impl .
interpretation ias: set_sel' ias_\<alpha> ias_invar ias_sel' using ias_sel'_impl .
interpretation ias: set_ins_dj ias_\<alpha> ias_invar ias_ins_dj using ias_ins_dj_impl .
interpretation ias: set_delete ias_\<alpha> ias_invar ias_delete using ias_delete_impl .
interpretation ias: set_ins ias_\<alpha> ias_invar ias_ins using ias_ins_impl .
interpretation ias: set_memb ias_\<alpha> ias_invar ias_memb using ias_memb_impl .
interpretation ias: set_to_list ias_\<alpha> ias_invar ias_to_list using ias_to_list_impl .
interpretation ias: list_to_set ias_\<alpha> ias_invar list_to_ias using list_to_ias_impl .
interpretation ias: set_isEmpty ias_\<alpha> ias_invar ias_isEmpty using ias_isEmpty_impl .
interpretation ias: set_empty ias_\<alpha> ias_invar ias_empty using ias_empty_impl .


lemmas ias_correct = 
  ias.inj_image_filter_correct
  ias.image_filter_correct
  ias.inj_image_correct
  ias.union_dj_correct
  ias.union_correct
  ias.inter_correct
  ias.image_correct
  ias.ins_dj_correct
  ias.delete_correct
  ias.ins_correct
  ias.memb_correct
  ias.to_list_correct
  ias.to_set_correct
  ias.isEmpty_correct
  ias.empty_correct

subsection "Code Generation"
export_code
  ias_iteratei
  ias_inj_image_filter
  ias_image_filter
  ias_inj_image
  ias_union_dj
  ias_union
  ias_inter
  ias_image
  ias_sel
  ias_sel'
  ias_ins_dj
  ias_delete
  ias_ins
  ias_memb
  ias_to_list
  list_to_ias
  ias_isEmpty
  ias_empty
  in SML
  module_name ArraySet
  file -

end
