(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Set Implementation by List} *}
theory ListSetImpl
imports SetSpec SetGA "common/Dlist_add"
begin
text_raw {*\label{thy:ListSetImpl}*}

text {*
  In this theory, sets are implemented by distinct lists. Abbreviations: ls,l
*}

types
  'a ls = "'a dlist"

subsection "Definitions"

definition ls_\<alpha> :: "'a ls \<Rightarrow> 'a set" where "ls_\<alpha> == Dlist.member"
abbreviation (input) ls_invar :: "'a ls \<Rightarrow> bool" where "ls_invar == \<lambda>_. True"
definition ls_empty :: "'a ls" where "ls_empty == Dlist.empty"
definition ls_memb :: "'a \<Rightarrow> 'a ls \<Rightarrow> bool" where "ls_memb x l == Dlist.member l x"
definition ls_ins :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_ins == Dlist.insert"
text {* 
  Since we use the abstract type @{typ "'a dlist"} for distinct lists,
  to preserve the invariant of distinct lists, we cannot just use Cons for disjoint insert,
  but must resort to ordinary insert.  The same applies to @{text ls_union_dj} below.
  @{text "list_to_lm_dj"} below.
*}
definition ls_ins_dj :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_ins_dj == Dlist.insert"
definition ls_delete :: "'a \<Rightarrow> 'a ls \<Rightarrow> 'a ls" where "ls_delete == remove'"
definition ls_iteratei :: "('a ls,'a,'\<sigma>) iteratori" where "ls_iteratei == iteratei"
definition ls_iterate :: "('a ls,'a,'\<sigma>) iterator" 
  where "ls_iterate == iti_iterate ls_iteratei"

definition ls_isEmpty :: "'a ls \<Rightarrow> bool" where "ls_isEmpty == Dlist.null"

definition ls_union :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_union == it_union ls_iterate ls_ins"
definition ls_inter :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_inter == it_inter ls_iterate ls_memb ls_empty ls_ins_dj"
definition ls_union_dj :: "'a ls \<Rightarrow> 'a ls \<Rightarrow> 'a ls" 
  where "ls_union_dj == ls_union"

definition ls_image_filter 
  where "ls_image_filter == it_image_filter ls_iterate ls_empty ls_ins"

definition ls_inj_image_filter 
  where "ls_inj_image_filter == it_inj_image_filter ls_iterate ls_empty ls_ins_dj"

definition "ls_image == iflt_image ls_image_filter"
definition "ls_inj_image == iflt_inj_image ls_inj_image_filter"

definition ls_ball :: "'a ls \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "ls_ball == iti_ball ls_iteratei"
definition ls_sel :: "'a ls \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "ls_sel == iti_sel ls_iteratei"
definition "ls_sel' == SetGA.sel_sel' ls_sel"

definition ls_to_list :: "'a ls \<Rightarrow> 'a list" where "ls_to_list == list_of_dlist"
definition list_to_ls :: "'a list \<Rightarrow> 'a ls" where "list_to_ls == Dlist"

definition "ls_size == it_size ls_iterate"

subsection "Correctness"
lemmas ls_defs = 
  ls_\<alpha>_def
  ls_empty_def
  ls_memb_def
  ls_ins_def
  ls_ins_dj_def
  ls_delete_def
  ls_iteratei_def
  ls_iterate_def
  ls_isEmpty_def
  ls_union_def
  ls_inter_def
  ls_union_dj_def
  ls_image_filter_def
  ls_inj_image_filter_def
  ls_image_def
  ls_inj_image_def
  ls_ball_def
  ls_sel_def
  ls_sel'_def
  ls_to_list_def
  list_to_ls_def
  ls_size_def


lemma ls_empty_impl: "set_empty ls_\<alpha> ls_invar ls_empty"
by(unfold_locales)(auto simp add: ls_defs member_empty)

lemma ls_memb_impl: "set_memb ls_\<alpha> ls_invar ls_memb"
by(unfold_locales)(auto simp add: ls_defs mem_def)

lemma ls_ins_impl: "set_ins ls_\<alpha> ls_invar ls_ins"
by(unfold_locales)(auto simp add: ls_defs mem_def)

lemma ls_ins_dj_impl: "set_ins_dj ls_\<alpha> ls_invar ls_ins_dj"
by(unfold_locales)(auto simp add: ls_defs)

lemma ls_delete_impl: "set_delete ls_\<alpha> ls_invar ls_delete"
by(unfold_locales)(auto simp add: ls_defs remove'_correct split: split_if_asm)

lemma ls_\<alpha>_finite[simp, intro!]: "finite (ls_\<alpha> l)"
by (auto simp add: ls_defs)

lemma ls_is_finite_set: "finite_set ls_\<alpha> ls_invar"
by(unfold_locales)(auto simp add: ls_defs)

lemma ls_iteratei_impl: "set_iteratei ls_\<alpha> ls_invar ls_iteratei"
by(unfold_locales)(unfold ls_defs, simp, rule iteratei_correct)

lemmas ls_iterate_impl = set_iteratei.iti_iterate_correct[OF ls_iteratei_impl, folded ls_iterate_def]

lemma ls_isEmpty_impl: "set_isEmpty ls_\<alpha> ls_invar ls_isEmpty"
by (unfold_locales) (auto simp add: ls_defs null_def member_def List.null_def member_set)

lemmas ls_union_impl = it_union_correct[OF ls_iterate_impl ls_ins_impl, folded ls_union_def] 

lemmas ls_inter_impl = it_inter_correct[OF ls_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded ls_inter_def]

lemmas ls_union_dj_impl = set_union.union_dj_by_union[OF ls_union_impl, folded ls_union_dj_def]

lemmas ls_image_filter_impl = it_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_impl, folded ls_image_filter_def]
lemmas ls_inj_image_filter_impl = it_inj_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ls_inj_image_filter_def]

lemmas ls_image_impl = iflt_image_correct[OF ls_image_filter_impl, folded ls_image_def]
lemmas ls_inj_image_impl = iflt_inj_image_correct[OF ls_inj_image_filter_impl, folded ls_inj_image_def]

lemmas ls_ball_impl = iti_ball_correct[OF ls_iteratei_impl, folded ls_ball_def]

lemmas ls_sel_impl = iti_sel_correct[OF ls_iteratei_impl, folded ls_sel_def]
lemmas ls_sel'_impl = sel_sel'_correct[OF ls_sel_impl, folded ls_sel'_def]

lemma ls_to_list_impl: "set_to_list ls_\<alpha> ls_invar ls_to_list"
by(unfold_locales)(auto simp add: ls_defs Dlist.member_def member_set)

lemma list_to_ls_impl: "list_to_set ls_\<alpha> ls_invar list_to_ls"
by(unfold_locales)(auto simp add: ls_defs Dlist.member_def member_set)

lemmas ls_size_impl = it_size_correct[OF ls_iterate_impl, folded ls_size_def]


interpretation ls: set_empty ls_\<alpha> ls_invar ls_empty using ls_empty_impl .
interpretation ls: set_memb ls_\<alpha> ls_invar ls_memb using ls_memb_impl .   
interpretation ls: set_ins ls_\<alpha> ls_invar ls_ins using ls_ins_impl .      
interpretation ls: set_ins_dj ls_\<alpha> ls_invar ls_ins_dj using ls_ins_dj_impl .
interpretation ls: set_delete ls_\<alpha> ls_invar ls_delete using ls_delete_impl .
interpretation ls: finite_set ls_\<alpha> ls_invar using ls_is_finite_set .
interpretation ls: set_iteratei ls_\<alpha> ls_invar ls_iteratei using ls_iteratei_impl .
interpretation ls: set_iterate ls_\<alpha> ls_invar ls_iterate using ls_iterate_impl .
interpretation ls: set_isEmpty ls_\<alpha> ls_invar ls_isEmpty using ls_isEmpty_impl .
interpretation ls: set_union ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_union using ls_union_impl .
interpretation ls: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inter using ls_inter_impl .
interpretation ls: set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_union_dj using ls_union_dj_impl .
interpretation ls: set_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_image_filter using ls_image_filter_impl .
interpretation ls: set_inj_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inj_image_filter using ls_inj_image_filter_impl .
interpretation ls: set_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_image using ls_image_impl .
interpretation ls: set_inj_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_inj_image using ls_inj_image_impl .
interpretation ls: set_ball ls_\<alpha> ls_invar ls_ball using ls_ball_impl .
interpretation ls: set_sel ls_\<alpha> ls_invar ls_sel using ls_sel_impl .
interpretation ls: set_sel' ls_\<alpha> ls_invar ls_sel' using ls_sel'_impl .
interpretation ls: set_to_list ls_\<alpha> ls_invar ls_to_list using ls_to_list_impl .
interpretation ls: list_to_set ls_\<alpha> ls_invar list_to_ls using list_to_ls_impl .
interpretation ls: set_size ls_\<alpha> ls_invar ls_size using ls_size_impl .

declare ls.finite[simp del, rule del]

lemmas ls_correct =
  ls.empty_correct                                                                                                 
  ls.memb_correct                                                                                                  
  ls.ins_correct                                                                                                   
  ls.ins_dj_correct
  ls.delete_correct
  ls.isEmpty_correct
  ls.union_correct
  ls.inter_correct
  ls.union_dj_correct
  ls.image_filter_correct
  ls.inj_image_filter_correct
  ls.image_correct
  ls.inj_image_correct
  ls.ball_correct
  ls.to_list_correct
  ls.to_set_correct
  ls.size_correct




subsection "Code Generation"

lemma list_of_dlist_list_to_ls [code abstract]:
  "list_of_dlist (list_to_ls xs) = remdups xs"
by(simp add: list_to_ls_def)

export_code
  ls_empty
  ls_memb
  ls_ins
  ls_ins_dj
  ls_delete
  ls_iteratei
  ls_iterate
  ls_isEmpty
  ls_union
  ls_inter
  ls_union_dj
  ls_image_filter
  ls_inj_image_filter
  ls_image
  ls_inj_image
  ls_ball
  ls_sel
  ls_sel'
  ls_to_list
  list_to_ls
  ls_size
  in SML
  module_name ListSet
  file -

end
