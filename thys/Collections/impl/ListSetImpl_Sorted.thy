(*  Title:       Isabelle Collections Library
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
header {* \isaheader{Set Implementation by sorted Lists} *}
theory ListSetImpl_Sorted
imports 
  "../spec/SetSpec"
  "../gen_algo/SetGA"
  "../common/Misc" 
  "../common/ListAdd" 
  "../common/Dlist_add"
begin
text_raw {*\label{thy:ListSetImpl_Sorted}*}

(*@impl Set
  @type 'a::linorder lss
  @abbrv lss
  Sets implemented by sorted lists.
*)

type_synonym
  'a lss = "'a list"

subsection "Definitions"
definition lss_\<alpha> :: "'a lss \<Rightarrow> 'a set" where "lss_\<alpha> == set"
definition lss_invar :: "'a::{linorder} lss \<Rightarrow> bool" where "lss_invar l == distinct l \<and> sorted l"
definition lss_empty :: "unit \<Rightarrow> 'a lss" where "lss_empty == (\<lambda>_::unit. [])"
definition lss_memb :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> bool" where "lss_memb x l == ListAdd.memb_sorted l x"
definition lss_ins :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_ins x l == ListAdd.insertion_sort x l"
definition lss_ins_dj :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_ins_dj == lss_ins"

definition lss_delete :: "'a::{linorder} \<Rightarrow> 'a lss \<Rightarrow> 'a lss" where "lss_delete x l == delete_sorted x l"

definition lss_iterateoi :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_iterateoi l = foldli l"

definition lss_reverse_iterateoi :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_reverse_iterateoi l = foldli (rev l)"

definition lss_iteratei :: "'a lss \<Rightarrow> ('a,'\<sigma>) set_iterator" 
where "lss_iteratei l = foldli l"

definition lss_isEmpty :: "'a lss \<Rightarrow> bool" where "lss_isEmpty s == s=[]"

definition lss_union :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_union s1 s2 == merge s1 s2"
definition lss_union_list :: "'a::{linorder} lss list \<Rightarrow> 'a lss" 
  where "lss_union_list l == merge_list [] l"
definition lss_inter :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_inter == inter_sorted"
definition lss_union_dj :: "'a::{linorder} lss \<Rightarrow> 'a lss \<Rightarrow> 'a lss" 
  where "lss_union_dj == lss_union" -- "Union of disjoint sets"

definition lss_image_filter 
  where "lss_image_filter f l = 
         mergesort (List.map_filter f l)"

definition lss_filter where [code_unfold]: "lss_filter = List.filter"

definition lss_inj_image_filter 
  where "lss_inj_image_filter == lss_image_filter"

definition "lss_image == iflt_image lss_image_filter"
definition "lss_inj_image == iflt_inj_image lss_inj_image_filter"

definition lss_sel :: "'a lss \<Rightarrow> ('a \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "lss_sel == iti_sel lss_iteratei"
definition "lss_sel' == iti_sel_no_map lss_iteratei"

definition lss_to_list :: "'a lss \<Rightarrow> 'a list" where "lss_to_list == id"
definition list_to_lss :: "'a::{linorder} list \<Rightarrow> 'a lss" where "list_to_lss == mergesort"

subsection "Correctness"
lemmas lss_defs = 
  lss_\<alpha>_def
  lss_invar_def
  lss_empty_def
  lss_memb_def
  lss_ins_def
  lss_ins_dj_def
  lss_delete_def
  lss_iteratei_def
  lss_isEmpty_def
  lss_union_def
  lss_union_list_def
  lss_inter_def
  lss_union_dj_def
  lss_image_filter_def
  lss_inj_image_filter_def
  lss_image_def
  lss_inj_image_def
  lss_sel_def
  lss_sel'_def
  lss_to_list_def
  list_to_lss_def

lemma lss_empty_impl: "set_empty lss_\<alpha> lss_invar lss_empty"
by (unfold_locales) (auto simp add: lss_defs)

lemma lss_memb_impl: "set_memb lss_\<alpha> lss_invar lss_memb"
by (unfold_locales) (auto simp add: lss_defs memb_sorted_correct)

lemma lss_ins_impl: "set_ins lss_\<alpha> lss_invar lss_ins"
by (unfold_locales) (auto simp add: lss_defs insertion_sort_correct)

lemma lss_ins_dj_impl: "set_ins_dj lss_\<alpha> lss_invar lss_ins_dj"
by (unfold_locales) (auto simp add: lss_defs insertion_sort_correct)

lemma lss_delete_impl: "set_delete lss_\<alpha> lss_invar lss_delete"
by(unfold_locales)(auto simp add: lss_delete_def lss_\<alpha>_def lss_invar_def delete_sorted_correct)

lemma lss_\<alpha>_finite[simp, intro!]: "finite (lss_\<alpha> l)"
  by (auto simp add: lss_defs)

lemma lss_is_finite_set: "finite_set lss_\<alpha> lss_invar"
by (unfold_locales) (auto simp add: lss_defs)

lemma lss_iterateoi_impl: "set_iterateoi lss_\<alpha> lss_invar lss_iterateoi"
proof 
  fix l :: "'a::{linorder} list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator_linord (lss_iterateoi l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_linord_I [of "l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_iterateoi_def)
  done
qed

lemma lss_reverse_iterateoi_impl: "set_reverse_iterateoi lss_\<alpha> lss_invar lss_reverse_iterateoi"
proof 
  fix l :: "'a list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator_rev_linord (lss_reverse_iterateoi l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_rev_linord_I [of "rev l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_reverse_iterateoi_def)
  done
qed

lemma lss_iteratei_impl: "set_iteratei lss_\<alpha> lss_invar lss_iteratei"
proof 
  fix l :: "'a list"
  assume invar_l: "lss_invar l"
  show "finite (lss_\<alpha> l)"
    unfolding lss_\<alpha>_def by simp

  from invar_l
  show "set_iterator (lss_iteratei l) (lss_\<alpha> l)"
    apply (rule_tac set_iterator_I [of "l"])
    apply (simp_all add: lss_\<alpha>_def lss_invar_def lss_iteratei_def)
  done
qed

lemma lss_isEmpty_impl: "set_isEmpty lss_\<alpha> lss_invar lss_isEmpty"
by(unfold_locales)(auto simp add: lss_defs)

lemma lss_inter_impl: "set_inter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inter"
by (unfold_locales) (auto simp add: lss_defs inter_sorted_correct)

lemma lss_union_impl: "set_union lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union"
by (unfold_locales) (auto simp add: lss_defs merge_correct)

lemma lss_union_list_impl: "set_union_list lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_list"
proof 
  fix l :: "'a::{linorder} lss list"
  assume "\<forall>s1\<in>set l. lss_invar s1"

  with merge_list_correct [of l "[]"]
  show "lss_\<alpha> (lss_union_list l) = \<Union>{lss_\<alpha> s1 |s1. s1 \<in> set l}"
       "lss_invar (lss_union_list l)"
    by (auto simp add: lss_defs)
qed

lemma lss_union_dj_impl: "set_union_dj lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_dj"
by (unfold_locales) (auto simp add: lss_defs merge_correct)

lemma lss_image_filter_impl : "set_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_image_filter"
apply (unfold_locales)
apply (simp_all add: lss_invar_def lss_image_filter_def mergesort_correct lss_\<alpha>_def
                     set_map_filter Bex_def)
done

lemma lss_inj_image_filter_impl : "set_inj_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inj_image_filter"
apply (unfold_locales)
apply (simp_all add: lss_invar_def lss_inj_image_filter_def lss_image_filter_def
                     mergesort_correct lss_\<alpha>_def
                     set_map_filter Bex_def)
done

lemma lss_filter_impl : "set_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_filter"
apply (unfold_locales)
apply (simp_all add: lss_invar_def lss_filter_def sorted_filter lss_\<alpha>_def
                     set_map_filter Bex_def)
done

lemmas lss_image_impl = iflt_image_correct[OF lss_image_filter_impl, folded lss_image_def]
lemmas lss_inj_image_impl = iflt_inj_image_correct[OF lss_inj_image_filter_impl, folded lss_inj_image_def]

lemmas lss_sel_impl = iti_sel_correct[OF lss_iteratei_impl, folded lss_sel_def]
lemmas lss_sel'_impl = iti_sel'_correct[OF lss_iteratei_impl, folded lss_sel'_def]

lemma lss_to_list_impl: "set_to_list lss_\<alpha> lss_invar lss_to_list"
by(unfold_locales)(auto simp add: lss_defs)

lemma list_to_lss_impl: "list_to_set lss_\<alpha> lss_invar list_to_lss"
by(unfold_locales)(auto simp add: lss_defs mergesort_correct)

interpretation lss: set_empty lss_\<alpha> lss_invar lss_empty using lss_empty_impl .
interpretation lss: set_memb lss_\<alpha> lss_invar lss_memb using lss_memb_impl .   
interpretation lss: set_ins lss_\<alpha> lss_invar lss_ins using lss_ins_impl .      
interpretation lss: set_ins_dj lss_\<alpha> lss_invar lss_ins_dj using lss_ins_dj_impl .
interpretation lss: set_delete lss_\<alpha> lss_invar lss_delete using lss_delete_impl .
interpretation lss: finite_set lss_\<alpha> lss_invar using lss_is_finite_set .
interpretation lss: set_iteratei lss_\<alpha> lss_invar lss_iteratei using lss_iteratei_impl .
interpretation lss: set_isEmpty lss_\<alpha> lss_invar lss_isEmpty using lss_isEmpty_impl .
interpretation lss: set_union lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union using lss_union_impl .
interpretation lss: set_union_list lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_list using lss_union_list_impl .
interpretation lss: set_inter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inter using lss_inter_impl .
interpretation lss: set_union_dj lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_union_dj using lss_union_dj_impl .
interpretation lss: set_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_image_filter using lss_image_filter_impl .
interpretation lss: set_inj_image_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inj_image_filter using lss_inj_image_filter_impl .
interpretation lss: set_filter lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_filter using lss_filter_impl .
interpretation lss: set_image lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_image using lss_image_impl .
interpretation lss: set_inj_image lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_inj_image using lss_inj_image_impl .
interpretation lss: set_sel lss_\<alpha> lss_invar lss_sel using lss_sel_impl .
interpretation lss: set_sel' lss_\<alpha> lss_invar lss_sel' using lss_sel'_impl .
interpretation lss: set_to_list lss_\<alpha> lss_invar lss_to_list using lss_to_list_impl .
interpretation lss: list_to_set lss_\<alpha> lss_invar list_to_lss using list_to_lss_impl .

declare lss.finite[simp del, rule del]

lemmas lss_correct =
  lss.empty_correct                                                                                                 
  lss.memb_correct                                                                                                  
  lss.ins_correct                                                                                                   
  lss.ins_dj_correct
  lss.delete_correct
  lss.isEmpty_correct
  lss.union_correct
  lss.union_list_correct
  lss.inter_correct
  lss.union_dj_correct
  lss.image_filter_correct
  lss.inj_image_filter_correct
  lss.image_correct
  lss.inj_image_correct
  lss.to_list_correct
  lss.to_set_correct


subsection "Code Generation"

export_code
  lss_empty
  lss_memb
  lss_ins
  lss_ins_dj
  lss_delete
  lss_iteratei
  lss_isEmpty
  lss_union
  lss_inter
  lss_union
  lss_union_list
  lss_image_filter
  lss_inj_image_filter
  lss_image
  lss_inj_image
  lss_sel
  lss_sel'
  lss_to_list
  list_to_lss
  in SML
  module_name ListSet
  file -

subsection {* Things often defined in StdImpl *}

definition lss_min where "lss_min = iti_sel_no_map lss_iterateoi" 
lemmas lss_min_impl = itoi_min_correct[OF lss_iterateoi_impl, folded lss_min_def]
interpretation lss: set_min lss_\<alpha> lss_invar lss_min using lss_min_impl .

definition lss_max where "lss_max = iti_sel_no_map lss_reverse_iterateoi" 
lemmas lss_max_impl = ritoi_max_correct[OF lss_reverse_iterateoi_impl, folded lss_max_def]
interpretation lss: set_max lss_\<alpha> lss_invar lss_max using lss_max_impl .

definition "lss_disjoint_witness == SetGA.sel_disjoint_witness lss_sel lss_memb"
lemmas lss_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lss_sel_impl lss_memb_impl, folded lss_disjoint_witness_def]
interpretation lss: set_disjoint_witness lss_\<alpha> lss_invar lss_\<alpha> lss_invar
 lss_disjoint_witness using lss_disjoint_witness_impl .

definition "lss_ball == SetGA.iti_ball lss_iteratei"
lemmas lss_ball_impl = SetGA.iti_ball_correct[OF lss_iteratei_impl, folded lss_ball_def]
interpretation lss: set_ball lss_\<alpha> lss_invar lss_ball using lss_ball_impl .

definition "lss_bexists == SetGA.iti_bexists lss_iteratei"
lemmas lss_bexists_impl = SetGA.iti_bexists_correct[OF lss_iteratei_impl, folded lss_bexists_def]
interpretation lss: set_bexists lss_\<alpha> lss_invar lss_bexists using lss_bexists_impl .

definition "lss_disjoint == SetGA.ball_disjoint lss_ball lss_memb"
lemmas lss_disjoint_impl = SetGA.ball_disjoint_correct[OF lss_ball_impl lss_memb_impl, folded lss_disjoint_def]
interpretation lss: set_disjoint lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_disjoint using lss_disjoint_impl .

definition "lss_size == SetGA.it_size lss_iteratei"
lemmas lss_size_impl = SetGA.it_size_correct[OF lss_iteratei_impl, folded lss_size_def]
interpretation lss: set_size lss_\<alpha> lss_invar lss_size using lss_size_impl .

definition "lss_size_abort == SetGA.iti_size_abort lss_iteratei"
lemmas lss_size_abort_impl = SetGA.iti_size_abort_correct[OF lss_iteratei_impl, folded lss_size_abort_def]
interpretation lss: set_size_abort lss_\<alpha> lss_invar lss_size_abort using lss_size_abort_impl .

definition "lss_isSng == SetGA.sza_isSng lss_iteratei"
lemmas lss_isSng_impl = SetGA.sza_isSng_correct[OF lss_iteratei_impl, folded lss_isSng_def]
interpretation lss: set_isSng lss_\<alpha> lss_invar lss_isSng using lss_isSng_impl .

definition "lss_sng x = [x]"
lemma lss_sng_impl : "set_sng lss_\<alpha> lss_invar lss_sng"
  unfolding set_sng_def lss_sng_def lss_invar_def lss_\<alpha>_def
  by simp
interpretation lss: set_sng lss_\<alpha> lss_invar lss_sng using lss_sng_impl .

definition "lss_equal l1 l2 = (l1 = l2)"
lemma lss_equal_impl : "set_equal lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_equal"
  unfolding set_equal_def lss_equal_def lss_\<alpha>_def lss_invar_def
  by (simp add: set_eq_sorted_correct)
interpretation lss: set_equal lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_equal using lss_equal_impl .

definition [code_unfold]: "lss_subset = subset_sorted"
lemma lss_subset_impl : "set_subset lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_subset"
  unfolding set_subset_def lss_subset_def lss_\<alpha>_def lss_invar_def
  by (simp add: subset_sorted_correct)
interpretation lss: set_subset lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_subset using lss_subset_impl .

definition [code_unfold]: "lss_diff = diff_sorted"
lemma lss_diff_impl : "set_diff lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_diff"
  unfolding set_diff_def lss_diff_def lss_\<alpha>_def lss_invar_def
  by (simp add: diff_sorted_correct)
interpretation lss: set_diff lss_\<alpha> lss_invar lss_\<alpha> lss_invar lss_diff using lss_diff_impl .

end
