(*  Title:       Isabelle Collections Library
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
header {* \isaheader{Set Implementation by non-distinct Lists} *}
theory ListSetImpl_NotDist
imports 
  "../spec/SetSpec"
  "../gen_algo/SetGA"
  "../common/Misc" 
  "../common/ListAdd"
begin
text_raw {*\label{thy:ListSetImpl_NotDist}*}

(*@impl Set
  @type 'a lsnd
  @abbrv lsnd
  Sets implemented by lists that may contain duplicate elements. 
  Insertion is quick, but other operations are less performant than on 
  lists with distinct elements.
*)

type_synonym
  'a lsnd = "'a list"

subsection "Definitions"

definition lsnd_\<alpha> :: "'a lsnd \<Rightarrow> 'a set" where "lsnd_\<alpha> == set"
definition lsnd_invar :: "'a lsnd \<Rightarrow> bool" where "lsnd_invar == (\<lambda>_. True)"
definition lsnd_empty :: "unit \<Rightarrow> 'a lsnd" where "lsnd_empty == (\<lambda>_::unit. [])"
definition lsnd_memb :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> bool" where "lsnd_memb x l == List.member l x"
definition lsnd_ins :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_ins x l == x#l"
definition lsnd_ins_dj :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_ins_dj x l == x#l"

definition lsnd_delete :: "'a \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" where "lsnd_delete x l == remove_rev [] x l"

definition lsnd_iteratei :: "'a lsnd \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lsnd_iteratei l = foldli (remdups l)"

definition lsnd_isEmpty :: "'a lsnd \<Rightarrow> bool" where "lsnd_isEmpty s == s=[]"

definition lsnd_union :: "'a lsnd \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" 
  where "lsnd_union s1 s2 == revg s1 s2"
definition lsnd_inter :: "'a lsnd \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" 
  where "lsnd_inter == it_inter lsnd_iteratei lsnd_memb lsnd_empty lsnd_ins_dj"
definition lsnd_union_dj :: "'a lsnd \<Rightarrow> 'a lsnd \<Rightarrow> 'a lsnd" 
  where "lsnd_union_dj s1 s2 == revg s1 s2" -- "Union of disjoint sets"

definition lsnd_image_filter 
  where "lsnd_image_filter == it_image_filter lsnd_iteratei lsnd_empty lsnd_ins"

definition lsnd_inj_image_filter 
  where "lsnd_inj_image_filter == it_inj_image_filter lsnd_iteratei lsnd_empty lsnd_ins_dj"

definition "lsnd_image == iflt_image lsnd_image_filter"
definition "lsnd_inj_image == iflt_inj_image lsnd_inj_image_filter"

definition lsnd_sel :: "'a lsnd \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "lsnd_sel == iti_sel lsnd_iteratei"
definition "lsnd_sel' == iti_sel_no_map lsnd_iteratei"

definition lsnd_to_list :: "'a lsnd \<Rightarrow> 'a list" where "lsnd_to_list == remdups"
definition list_to_lsnd :: "'a list \<Rightarrow> 'a lsnd" where "list_to_lsnd == id"

subsection "Correctness"
lemmas lsnd_defs = 
  lsnd_\<alpha>_def
  lsnd_invar_def
  lsnd_empty_def
  lsnd_memb_def
  lsnd_ins_def
  lsnd_ins_dj_def
  lsnd_delete_def
  lsnd_iteratei_def
  lsnd_isEmpty_def
  lsnd_union_def
  lsnd_inter_def
  lsnd_union_dj_def
  lsnd_image_filter_def
  lsnd_inj_image_filter_def
  lsnd_image_def
  lsnd_inj_image_def
  lsnd_sel_def
  lsnd_sel'_def
  lsnd_to_list_def
  list_to_lsnd_def

lemma lsnd_empty_impl: "set_empty lsnd_\<alpha> lsnd_invar lsnd_empty"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_memb_impl: "set_memb lsnd_\<alpha> lsnd_invar lsnd_memb"
by (unfold_locales)(auto simp add: lsnd_defs in_set_member)

lemma lsnd_ins_impl: "set_ins lsnd_\<alpha> lsnd_invar lsnd_ins"
by (unfold_locales) (auto simp add: lsnd_defs in_set_member)

lemma lsnd_ins_dj_impl: "set_ins_dj lsnd_\<alpha> lsnd_invar lsnd_ins_dj"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_delete_impl: "set_delete lsnd_\<alpha> lsnd_invar lsnd_delete"
by (unfold_locales) (auto simp add: lsnd_delete_def lsnd_\<alpha>_def lsnd_invar_def remove_rev_alt_def)

lemma lsnd_\<alpha>_finite[simp, intro!]: "finite (lsnd_\<alpha> l)"
  by (auto simp add: lsnd_defs)

lemma lsnd_is_finite_set: "finite_set lsnd_\<alpha> lsnd_invar"
by (unfold_locales) (auto simp add: lsnd_defs)

lemma lsnd_iteratei_impl: "set_iteratei lsnd_\<alpha> lsnd_invar lsnd_iteratei"
proof 
  fix l :: "'a list"
  show "finite (lsnd_\<alpha> l)"
    unfolding lsnd_\<alpha>_def by simp

  show "set_iterator (lsnd_iteratei l) (lsnd_\<alpha> l)"
    apply (rule set_iterator_I [of "remdups l"])
    apply (simp_all add: lsnd_\<alpha>_def lsnd_iteratei_def)
  done
qed

lemma lsnd_isEmpty_impl: "set_isEmpty lsnd_\<alpha> lsnd_invar lsnd_isEmpty"
by(unfold_locales)(auto simp add: lsnd_defs)

lemmas lsnd_inter_impl = it_inter_correct[OF lsnd_iteratei_impl lsnd_memb_impl lsnd_empty_impl lsnd_ins_dj_impl, folded lsnd_inter_def]

lemma lsnd_union_impl: "set_union lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma lsnd_union_dj_impl: "set_union_dj lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union_dj"
by(unfold_locales)(auto simp add: lsnd_defs)

lemmas lsnd_image_filter_impl = it_image_filter_correct[OF lsnd_iteratei_impl lsnd_empty_impl lsnd_ins_impl, folded lsnd_image_filter_def]
lemmas lsnd_inj_image_filter_impl = it_inj_image_filter_correct[OF lsnd_iteratei_impl lsnd_empty_impl lsnd_ins_dj_impl, folded lsnd_inj_image_filter_def]

lemmas lsnd_image_impl = iflt_image_correct[OF lsnd_image_filter_impl, folded lsnd_image_def]
lemmas lsnd_inj_image_impl = iflt_inj_image_correct[OF lsnd_inj_image_filter_impl, folded lsnd_inj_image_def]

lemmas lsnd_sel_impl = iti_sel_correct[OF lsnd_iteratei_impl, folded lsnd_sel_def]
lemmas lsnd_sel'_impl = iti_sel'_correct[OF lsnd_iteratei_impl, folded lsnd_sel'_def]

lemma lsnd_to_list_impl: "set_to_list lsnd_\<alpha> lsnd_invar lsnd_to_list"
by(unfold_locales)(auto simp add: lsnd_defs)

lemma list_to_lsnd_impl: "list_to_set lsnd_\<alpha> lsnd_invar list_to_lsnd"
by(unfold_locales)(auto simp add: lsnd_defs)

interpretation lsnd: set_empty lsnd_\<alpha> lsnd_invar lsnd_empty using lsnd_empty_impl .
interpretation lsnd: set_memb lsnd_\<alpha> lsnd_invar lsnd_memb using lsnd_memb_impl .   
interpretation lsnd: set_ins lsnd_\<alpha> lsnd_invar lsnd_ins using lsnd_ins_impl .      
interpretation lsnd: set_ins_dj lsnd_\<alpha> lsnd_invar lsnd_ins_dj using lsnd_ins_dj_impl .
interpretation lsnd: set_delete lsnd_\<alpha> lsnd_invar lsnd_delete using lsnd_delete_impl .
interpretation lsnd: finite_set lsnd_\<alpha> lsnd_invar using lsnd_is_finite_set .
interpretation lsnd: set_iteratei lsnd_\<alpha> lsnd_invar lsnd_iteratei using lsnd_iteratei_impl .
interpretation lsnd: set_isEmpty lsnd_\<alpha> lsnd_invar lsnd_isEmpty using lsnd_isEmpty_impl .
interpretation lsnd: set_union lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union using lsnd_union_impl .
interpretation lsnd: set_inter lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_inter using lsnd_inter_impl .
interpretation lsnd: set_union_dj lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_union_dj using lsnd_union_dj_impl .
interpretation lsnd: set_image_filter lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_image_filter using lsnd_image_filter_impl .
interpretation lsnd: set_inj_image_filter lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_inj_image_filter using lsnd_inj_image_filter_impl .
interpretation lsnd: set_image lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_image using lsnd_image_impl .
interpretation lsnd: set_inj_image lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_inj_image using lsnd_inj_image_impl .
interpretation lsnd: set_sel lsnd_\<alpha> lsnd_invar lsnd_sel using lsnd_sel_impl .
interpretation lsnd: set_sel' lsnd_\<alpha> lsnd_invar lsnd_sel' using lsnd_sel'_impl .
interpretation lsnd: set_to_list lsnd_\<alpha> lsnd_invar lsnd_to_list using lsnd_to_list_impl .
interpretation lsnd: list_to_set lsnd_\<alpha> lsnd_invar list_to_lsnd using list_to_lsnd_impl .

declare lsnd.finite[simp del, rule del]

lemmas lsnd_correct =
  lsnd.empty_correct                                                                                                 
  lsnd.memb_correct                                                                                                  
  lsnd.ins_correct                                                                                                   
  lsnd.ins_dj_correct
  lsnd.delete_correct
  lsnd.isEmpty_correct
  lsnd.union_correct
  lsnd.inter_correct
  lsnd.union_dj_correct
  lsnd.image_filter_correct
  lsnd.inj_image_filter_correct
  lsnd.image_correct
  lsnd.inj_image_correct
  lsnd.to_list_correct
  lsnd.to_set_correct


subsection "Code Generation"

export_code
  lsnd_empty
  lsnd_memb
  lsnd_ins
  lsnd_ins_dj
  lsnd_delete
  lsnd_iteratei
  lsnd_isEmpty
  lsnd_union
  lsnd_inter
  lsnd_union_dj
  lsnd_image_filter
  lsnd_inj_image_filter
  lsnd_image
  lsnd_inj_image
  lsnd_sel
  lsnd_sel'
  lsnd_to_list
  list_to_lsnd
  in SML
  module_name ListSet
  file -



subsection {* Things often defined in StdImpl *}

definition "lsnd_disjoint_witness == SetGA.sel_disjoint_witness lsnd_sel lsnd_memb"
lemmas lsnd_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsnd_sel_impl lsnd_memb_impl, folded lsnd_disjoint_witness_def]
interpretation lsnd: set_disjoint_witness lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar
 lsnd_disjoint_witness using lsnd_disjoint_witness_impl .

definition "lsnd_ball == SetGA.iti_ball lsnd_iteratei"
lemmas lsnd_ball_impl = SetGA.iti_ball_correct[OF lsnd_iteratei_impl, folded lsnd_ball_def]
interpretation lsnd: set_ball lsnd_\<alpha> lsnd_invar lsnd_ball using lsnd_ball_impl .

definition "lsnd_bexists == SetGA.iti_bexists lsnd_iteratei"
lemmas lsnd_bexists_impl = SetGA.iti_bexists_correct[OF lsnd_iteratei_impl, folded lsnd_bexists_def]
interpretation lsnd: set_bexists lsnd_\<alpha> lsnd_invar lsnd_bexists using lsnd_bexists_impl .

definition "lsnd_disjoint == SetGA.ball_disjoint lsnd_ball lsnd_memb"
lemmas lsnd_disjoint_impl = SetGA.ball_disjoint_correct[OF lsnd_ball_impl lsnd_memb_impl, folded lsnd_disjoint_def]
interpretation lsnd: set_disjoint lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_disjoint using lsnd_disjoint_impl .

definition "lsnd_size == SetGA.it_size lsnd_iteratei"
lemmas lsnd_size_impl = SetGA.it_size_correct[OF lsnd_iteratei_impl, folded lsnd_size_def]
interpretation lsnd: set_size lsnd_\<alpha> lsnd_invar lsnd_size using lsnd_size_impl .

definition "lsnd_size_abort == SetGA.iti_size_abort lsnd_iteratei"
lemmas lsnd_size_abort_impl = SetGA.iti_size_abort_correct[OF lsnd_iteratei_impl, folded lsnd_size_abort_def]
interpretation lsnd: set_size_abort lsnd_\<alpha> lsnd_invar lsnd_size_abort using lsnd_size_abort_impl .

definition "lsnd_isSng == SetGA.sza_isSng lsnd_iteratei"
lemmas lsnd_isSng_impl = SetGA.sza_isSng_correct[OF lsnd_iteratei_impl, folded lsnd_isSng_def]
interpretation lsnd: set_isSng lsnd_\<alpha> lsnd_invar lsnd_isSng using lsnd_isSng_impl .

definition "lsnd_sng x = [x]"
lemma lsnd_sng_impl : "set_sng lsnd_\<alpha> lsnd_invar lsnd_sng"
  unfolding set_sng_def lsnd_sng_def lsnd_invar_def lsnd_\<alpha>_def
  by simp
interpretation lsnd: set_sng lsnd_\<alpha> lsnd_invar lsnd_sng using lsnd_sng_impl .

definition "lsnd_diff == SetGA.it_diff lsnd_iteratei lsnd_delete"
lemmas lsnd_diff_impl = SetGA.it_diff_correct[OF lsnd_iteratei_impl lsnd_delete_impl, folded lsnd_diff_def]
interpretation lsnd: set_diff lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_diff 
   using lsnd_diff_impl .

definition "lsnd_subset == SetGA.ball_subset lsnd_ball lsnd_memb"
lemmas lsnd_subset_impl = SetGA.ball_subset_correct[OF lsnd_ball_impl lsnd_memb_impl, folded lsnd_subset_def]
interpretation lsnd: set_subset lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_subset 
   using lsnd_subset_impl .

definition "lsnd_equal == SetGA.subset_equal lsnd_subset lsnd_subset"
lemmas lsnd_equal_impl = SetGA.subset_equal_correct[OF lsnd_subset_impl lsnd_subset_impl, folded lsnd_equal_def]
interpretation lsnd: set_equal lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_equal 
   using lsnd_equal_impl .


definition "lsnd_filter == SetGA.iflt_filter lsnd_inj_image_filter"
lemmas lsnd_filter_impl = SetGA.iflt_filter_correct[OF lsnd_inj_image_filter_impl, folded lsnd_filter_def]
interpretation lsnd: set_filter lsnd_\<alpha> lsnd_invar lsnd_\<alpha> lsnd_invar lsnd_filter 
   using lsnd_filter_impl .

end
