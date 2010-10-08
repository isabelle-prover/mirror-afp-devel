(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedSet, implemented iterators, min, max, to_sorted_list

*)

header {* \isaheader{Set Implementation by Red-Black-Tree} *}
theory RBTSetImpl
imports SetSpec RBTMapImpl SetByMap SetGA
begin
text_raw {*\label{thy:RBTSetImpl}*}

text {*
  This implementation is based on the corresponding map implementation.
  Abbreviations: rs,r
*}

subsection "Definitions"
types
  'a rs = "('a::linorder,unit) rm"

definition rs_\<alpha> :: "'a::linorder rs \<Rightarrow> 'a set" where "rs_\<alpha> == s_\<alpha> rm_\<alpha>"
abbreviation (input) rs_invar :: "'a::linorder rs \<Rightarrow> bool" where "rs_invar == rm_invar"
definition rs_empty :: "'a::linorder rs" where "rs_empty == s_empty rm_empty"
definition rs_memb :: "'a::linorder \<Rightarrow> 'a rs \<Rightarrow> bool" 
  where "rs_memb == s_memb rm_lookup"
definition rs_ins :: "'a::linorder \<Rightarrow> 'a rs \<Rightarrow> 'a rs" 
  where "rs_ins == s_ins rm_update"
definition rs_ins_dj :: "'a::linorder \<Rightarrow> 'a rs \<Rightarrow> 'a rs" where
  "rs_ins_dj == s_ins_dj rm_update_dj"
definition rs_delete :: "'a::linorder \<Rightarrow> 'a rs \<Rightarrow> 'a rs" 
  where "rs_delete == s_delete rm_delete"
definition rs_sel :: "'a::linorder rs \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "rs_sel == s_sel rm_sel"
definition rs_isEmpty :: "'a::linorder rs \<Rightarrow> bool"
  where "rs_isEmpty == s_isEmpty rm_isEmpty"

definition rs_iterate :: "('a::linorder rs,'a,'\<sigma>) iterator" 
  where "rs_iterate == s_iterate rm_iterate"
definition rs_iteratei :: "('a::linorder rs,'a,'\<sigma>) iteratori" 
  where "rs_iteratei == s_iteratei rm_iteratei"

definition rs_iterateo :: "('a::linorder rs,'a,'\<sigma>) iterator" 
  where "rs_iterateo == s_iterateo rm_iterateo"
definition rs_iterateoi :: "('a::linorder rs,'a,'\<sigma>) iteratori" 
  where "rs_iterateoi == s_iterateoi rm_iterateoi"

definition rs_reverse_iterateo :: "('a::linorder rs,'a,'\<sigma>) iterator" 
  where "rs_reverse_iterateo == s_reverse_iterateo rm_reverse_iterateo"
definition rs_reverse_iterateoi :: "('a::linorder rs,'a,'\<sigma>) iteratori" 
  where "rs_reverse_iterateoi == s_reverse_iterateoi rm_reverse_iterateoi"

definition rs_ball :: "'a::linorder rs \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "rs_ball == s_ball rm_ball"
definition rs_union :: "'a::linorder rs \<Rightarrow> 'a rs \<Rightarrow> 'a rs" 
  where "rs_union == s_union rm_add"
definition rs_union_dj :: "'a::linorder rs \<Rightarrow> 'a rs \<Rightarrow> 'a rs" 
  where "rs_union_dj == s_union_dj rm_add_dj"
definition rs_inter :: "'a::linorder rs \<Rightarrow> 'a rs \<Rightarrow> 'a rs" 
  where "rs_inter == it_inter rs_iterate rs_memb rs_empty rs_ins_dj"

definition "rs_size == it_size rs_iterate"

definition rs_image_filter 
  where "rs_image_filter == it_image_filter rs_iterate rs_empty rs_ins"
definition rs_inj_image_filter 
  where "rs_inj_image_filter == it_inj_image_filter rs_iterate rs_empty rs_ins_dj"

definition rs_image where "rs_image == iflt_image rs_image_filter"
definition rs_inj_image where "rs_inj_image == iflt_inj_image rs_inj_image_filter"

definition "rs_to_list == rito_set_to_sorted_list rs_reverse_iterateo"
definition "list_to_rs == gen_list_to_set rs_empty rs_ins"

definition "rs_min == itoi_min rs_iterateoi"
definition "rs_max == ritoi_max rs_reverse_iterateoi"

subsection "Correctness"

lemmas rs_defs =
  list_to_rs_def
  rs_\<alpha>_def
  rs_ball_def
  rs_delete_def
  rs_empty_def
  rs_image_def
  rs_image_filter_def
  rs_inj_image_def
  rs_inj_image_filter_def
  rs_ins_def
  rs_ins_dj_def
  rs_inter_def
  rs_isEmpty_def
  rs_iterate_def
  rs_iteratei_def
  rs_iterateo_def
  rs_iterateoi_def
  rs_reverse_iterateo_def
  rs_reverse_iterateoi_def
  rs_memb_def
  rs_sel_def
  rs_size_def
  rs_to_list_def
  rs_union_def
  rs_union_dj_def
  rs_min_def
  rs_max_def


lemmas rs_empty_impl = s_empty_correct[OF rm_empty_impl, folded rs_defs]
lemmas rs_memb_impl = s_memb_correct[OF rm_lookup_impl, folded rs_defs]
lemmas rs_ins_impl = s_ins_correct[OF rm_update_impl, folded rs_defs]
lemmas rs_ins_dj_impl = s_ins_dj_correct[OF rm_update_dj_impl, folded rs_defs]
lemmas rs_delete_impl = s_delete_correct[OF rm_delete_impl, folded rs_defs]
lemmas rs_iteratei_impl = s_iteratei_correct[OF rm_iteratei_impl, folded rs_defs]
lemmas rs_iterate_impl = s_iterate_correct[OF rm_iterate_impl, folded rs_defs]
lemmas rs_iterateoi_impl = s_iterateoi_correct[OF rm_iterateoi_impl, folded rs_defs]
lemmas rs_iterateo_impl = s_iterateo_correct[OF rm_iterateo_impl, folded rs_defs]
lemmas rs_reverse_iterateoi_impl = s_reverse_iterateoi_correct[OF rm_reverse_iterateoi_impl, folded rs_defs]
lemmas rs_reverse_iterateo_impl = s_reverse_iterateo_correct[OF rm_reverse_iterateo_impl, folded rs_defs]
lemmas rs_isEmpty_impl = s_isEmpty_correct[OF rm_isEmpty_impl, folded rs_defs]
lemmas rs_union_impl = s_union_correct[OF rm_add_impl, folded rs_defs]
lemmas rs_union_dj_impl = s_union_dj_correct[OF rm_add_dj_impl, folded rs_defs]
lemmas rs_ball_impl = s_ball_correct[OF rm_ball_impl, folded rs_defs]
lemmas rs_sel_impl = s_sel_correct[OF rm_sel_impl, folded rs_defs]
lemmas rs_inter_impl = it_inter_correct[OF rs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rs_inter_def]
lemmas rs_size_impl = it_size_correct[OF rs_iterate_impl, folded rs_size_def]
lemmas rs_image_filter_impl = it_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_impl, folded rs_image_filter_def]
lemmas rs_inj_image_filter_impl = it_inj_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rs_inj_image_filter_def]
lemmas rs_image_impl = iflt_image_correct[OF rs_image_filter_impl, folded rs_image_def]
lemmas rs_inj_image_impl = iflt_inj_image_correct[OF rs_inj_image_filter_impl, folded rs_inj_image_def]
lemmas rs_to_list_impl = rito_set_to_sorted_list_correct[OF rs_reverse_iterateo_impl, folded rs_to_list_def]
lemmas list_to_rs_impl = gen_list_to_set_correct[OF rs_empty_impl rs_ins_impl, folded list_to_rs_def]

lemmas rs_min_impl = itoi_min_correct[OF rs_iterateoi_impl, folded rs_defs]
lemmas rs_max_impl = ritoi_max_correct[OF rs_reverse_iterateoi_impl, folded rs_defs]

interpretation rs: set_iteratei rs_\<alpha> rs_invar rs_iteratei using rs_iteratei_impl .                               
interpretation rs: set_iterate rs_\<alpha> rs_invar rs_iterate using rs_iterate_impl .

interpretation rs: set_iterateoi rs_\<alpha> rs_invar rs_iterateoi using rs_iterateoi_impl .                               
interpretation rs: set_iterateo rs_\<alpha> rs_invar rs_iterateo using rs_iterateo_impl .

interpretation rs: set_reverse_iterateoi rs_\<alpha> rs_invar rs_reverse_iterateoi using rs_reverse_iterateoi_impl .                               
interpretation rs: set_reverse_iterateo rs_\<alpha> rs_invar rs_reverse_iterateo using rs_reverse_iterateo_impl .

interpretation rs: set_inj_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_inj_image_filter using rs_inj_image_filter_impl .
interpretation rs: set_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_image_filter using rs_image_filter_impl .
interpretation rs: set_inj_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_inj_image using rs_inj_image_impl .
interpretation rs: set_union_dj rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_union_dj using rs_union_dj_impl .
interpretation rs: set_union rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_union using rs_union_impl .
interpretation rs: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_inter using rs_inter_impl .
interpretation rs: set_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_image using rs_image_impl .
interpretation rs: set_sel rs_\<alpha> rs_invar rs_sel using rs_sel_impl .
interpretation rs: set_ins_dj rs_\<alpha> rs_invar rs_ins_dj using rs_ins_dj_impl .
interpretation rs: set_delete rs_\<alpha> rs_invar rs_delete using rs_delete_impl .
interpretation rs: set_ball rs_\<alpha> rs_invar rs_ball using rs_ball_impl .
interpretation rs: set_ins rs_\<alpha> rs_invar rs_ins using rs_ins_impl .
interpretation rs: set_memb rs_\<alpha> rs_invar rs_memb using rs_memb_impl .
interpretation rs: set_to_sorted_list rs_\<alpha> rs_invar rs_to_list using rs_to_list_impl .
interpretation rs: list_to_set rs_\<alpha> rs_invar list_to_rs using list_to_rs_impl .
interpretation rs: set_isEmpty rs_\<alpha> rs_invar rs_isEmpty using rs_isEmpty_impl .
interpretation rs: set_size rs_\<alpha> rs_invar rs_size using rs_size_impl .
interpretation rs: set_empty rs_\<alpha> rs_invar rs_empty using rs_empty_impl .
interpretation rs: set_min rs_\<alpha> rs_invar rs_min using rs_min_impl .
interpretation rs: set_max rs_\<alpha> rs_invar rs_max using rs_max_impl .


lemmas rs_correct = 
  rs.inj_image_filter_correct
  rs.image_filter_correct
  rs.inj_image_correct
  rs.union_dj_correct
  rs.union_correct
  rs.inter_correct
  rs.image_correct
  rs.ins_dj_correct
  rs.delete_correct
  rs.ball_correct
  rs.ins_correct
  rs.memb_correct
  rs.to_list_correct
  rs.to_set_correct
  rs.isEmpty_correct
  rs.size_correct
  rs.empty_correct





subsection "Code Generation"
export_code
  rs_iteratei
  rs_iterate
  rs_iterateoi
  rs_iterateo
  rs_reverse_iterateoi
  rs_reverse_iterateo
  rs_inj_image_filter
  rs_image_filter
  rs_inj_image
  rs_union_dj
  rs_union
  rs_inter
  rs_image
  rs_sel
  rs_ins_dj
  rs_delete
  rs_ball
  rs_ins
  rs_memb
  rs_to_list
  list_to_rs
  rs_isEmpty
  rs_size
  rs_empty
  rs_min
  rs_max
  in SML
  module_name RBTSet
  file -

end

