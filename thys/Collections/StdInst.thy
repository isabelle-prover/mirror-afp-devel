(* Generated file *)
(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Standard Instantiations *}
theory StdInst
imports 
  MapStdImpl SetStdImpl Fifo
  SetIndex Algos 
  SetGA MapGA

begin
text_raw {*\label{thy:StdInst}*}
(* We use a small ad-hoc hack to generate the actual instantiations from this file: *)

text {*
  This theory provides standard instantiations of some abstract algorithms
  for rb-trees, lists and hashsets/maps.
*}


(* TODO: A bit dirty: We partially instantiate the it_set_to_list_enqueue generic algorithm here.
  The other parameter (the set class) is instantiated below using the automatic instantiation *)
definition "it_set_to_fifo it == it_set_to_List_enq it fifo_empty fifo_enqueue"

lemmas it_set_to_fifo_correct = it_set_to_List_enq_correct[OF _ fifo_empty_impl fifo_enqueue_impl, folded it_set_to_fifo_def]

(*  map TrieMap tm t TODO: @Peter: Keine Kombination (trie, rbt) generieren *)
(*  set TrieSet ts t TODO: @Peter: Keine Kombination (trie, rbt) generieren *)




(*#begin_generated*)

  definition "lsi_sel' == SetGA.sel_sel' lsi_sel"
  lemmas lsi_sel'_impl = SetGA.sel_sel'_correct[OF lsi_sel_impl, folded lsi_sel'_def]
  interpretation lsi: set_sel' lsi_\<alpha> lsi_invar lsi_sel' using lsi_sel'_impl .
  definition "ls_sel' == SetGA.sel_sel' ls_sel"
  lemmas ls_sel'_impl = SetGA.sel_sel'_correct[OF ls_sel_impl, folded ls_sel'_def]
  interpretation ls: set_sel' ls_\<alpha> ls_invar ls_sel' using ls_sel'_impl .
  definition "rs_sel' == SetGA.sel_sel' rs_sel"
  lemmas rs_sel'_impl = SetGA.sel_sel'_correct[OF rs_sel_impl, folded rs_sel'_def]
  interpretation rs: set_sel' rs_\<alpha> rs_invar rs_sel' using rs_sel'_impl .
  definition "hs_sel' == SetGA.sel_sel' hs_sel"
  lemmas hs_sel'_impl = SetGA.sel_sel'_correct[OF hs_sel_impl, folded hs_sel'_def]
  interpretation hs: set_sel' hs_\<alpha> hs_invar hs_sel' using hs_sel'_impl .
  definition "ahs_sel' == SetGA.sel_sel' ahs_sel"
  lemmas ahs_sel'_impl = SetGA.sel_sel'_correct[OF ahs_sel_impl, folded ahs_sel'_def]
  interpretation ahs: set_sel' ahs_\<alpha> ahs_invar ahs_sel' using ahs_sel'_impl .

  definition "lmi_sel' == MapGA.sel_sel' lmi_sel"
  lemmas lmi_sel'_impl = MapGA.sel_sel'_correct[OF lmi_sel_impl, folded lmi_sel'_def]
  interpretation lmi: map_sel' lmi_\<alpha> lmi_invar lmi_sel' using lmi_sel'_impl .
  definition "lm_sel' == MapGA.sel_sel' lm_sel"
  lemmas lm_sel'_impl = MapGA.sel_sel'_correct[OF lm_sel_impl, folded lm_sel'_def]
  interpretation lm: map_sel' lm_\<alpha> lm_invar lm_sel' using lm_sel'_impl .
  definition "rm_sel' == MapGA.sel_sel' rm_sel"
  lemmas rm_sel'_impl = MapGA.sel_sel'_correct[OF rm_sel_impl, folded rm_sel'_def]
  interpretation rm: map_sel' rm_\<alpha> rm_invar rm_sel' using rm_sel'_impl .
  definition "hm_sel' == MapGA.sel_sel' hm_sel"
  lemmas hm_sel'_impl = MapGA.sel_sel'_correct[OF hm_sel_impl, folded hm_sel'_def]
  interpretation hm: map_sel' hm_\<alpha> hm_invar hm_sel' using hm_sel'_impl .
  definition "ahm_sel' == MapGA.sel_sel' ahm_sel"
  lemmas ahm_sel'_impl = MapGA.sel_sel'_correct[OF ahm_sel_impl, folded ahm_sel'_def]
  interpretation ahm: map_sel' ahm_\<alpha> ahm_invar ahm_sel' using ahm_sel'_impl .

  definition "lili_copy == SetGA.it_copy lsi_iterate lsi_empty lsi_ins"
  lemmas lili_copy_impl = SetGA.it_copy_correct[OF lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded lili_copy_def]
  interpretation lili: set_copy lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_copy using lili_copy_impl .
  definition "lil_copy == SetGA.it_copy lsi_iterate ls_empty ls_ins"
  lemmas lil_copy_impl = SetGA.it_copy_correct[OF lsi_iterate_impl ls_empty_impl ls_ins_impl, folded lil_copy_def]
  interpretation lil: set_copy lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_copy using lil_copy_impl .
  definition "lir_copy == SetGA.it_copy lsi_iterate rs_empty rs_ins"
  lemmas lir_copy_impl = SetGA.it_copy_correct[OF lsi_iterate_impl rs_empty_impl rs_ins_impl, folded lir_copy_def]
  interpretation lir: set_copy lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_copy using lir_copy_impl .
  definition "lih_copy == SetGA.it_copy lsi_iterate hs_empty hs_ins"
  lemmas lih_copy_impl = SetGA.it_copy_correct[OF lsi_iterate_impl hs_empty_impl hs_ins_impl, folded lih_copy_def]
  interpretation lih: set_copy lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_copy using lih_copy_impl .
  definition "lia_copy == SetGA.it_copy lsi_iterate ahs_empty ahs_ins"
  lemmas lia_copy_impl = SetGA.it_copy_correct[OF lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded lia_copy_def]
  interpretation lia: set_copy lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_copy using lia_copy_impl .
  definition "lli_copy == SetGA.it_copy ls_iterate lsi_empty lsi_ins"
  lemmas lli_copy_impl = SetGA.it_copy_correct[OF ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded lli_copy_def]
  interpretation lli: set_copy ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_copy using lli_copy_impl .
  definition "ll_copy == SetGA.it_copy ls_iterate ls_empty ls_ins"
  lemmas ll_copy_impl = SetGA.it_copy_correct[OF ls_iterate_impl ls_empty_impl ls_ins_impl, folded ll_copy_def]
  interpretation ll: set_copy ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_copy using ll_copy_impl .
  definition "lr_copy == SetGA.it_copy ls_iterate rs_empty rs_ins"
  lemmas lr_copy_impl = SetGA.it_copy_correct[OF ls_iterate_impl rs_empty_impl rs_ins_impl, folded lr_copy_def]
  interpretation lr: set_copy ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_copy using lr_copy_impl .
  definition "lh_copy == SetGA.it_copy ls_iterate hs_empty hs_ins"
  lemmas lh_copy_impl = SetGA.it_copy_correct[OF ls_iterate_impl hs_empty_impl hs_ins_impl, folded lh_copy_def]
  interpretation lh: set_copy ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_copy using lh_copy_impl .
  definition "la_copy == SetGA.it_copy ls_iterate ahs_empty ahs_ins"
  lemmas la_copy_impl = SetGA.it_copy_correct[OF ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded la_copy_def]
  interpretation la: set_copy ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_copy using la_copy_impl .
  definition "rli_copy == SetGA.it_copy rs_iterate lsi_empty lsi_ins"
  lemmas rli_copy_impl = SetGA.it_copy_correct[OF rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded rli_copy_def]
  interpretation rli: set_copy rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_copy using rli_copy_impl .
  definition "rl_copy == SetGA.it_copy rs_iterate ls_empty ls_ins"
  lemmas rl_copy_impl = SetGA.it_copy_correct[OF rs_iterate_impl ls_empty_impl ls_ins_impl, folded rl_copy_def]
  interpretation rl: set_copy rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_copy using rl_copy_impl .
  definition "rr_copy == SetGA.it_copy rs_iterate rs_empty rs_ins"
  lemmas rr_copy_impl = SetGA.it_copy_correct[OF rs_iterate_impl rs_empty_impl rs_ins_impl, folded rr_copy_def]
  interpretation rr: set_copy rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_copy using rr_copy_impl .
  definition "rh_copy == SetGA.it_copy rs_iterate hs_empty hs_ins"
  lemmas rh_copy_impl = SetGA.it_copy_correct[OF rs_iterate_impl hs_empty_impl hs_ins_impl, folded rh_copy_def]
  interpretation rh: set_copy rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_copy using rh_copy_impl .
  definition "ra_copy == SetGA.it_copy rs_iterate ahs_empty ahs_ins"
  lemmas ra_copy_impl = SetGA.it_copy_correct[OF rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ra_copy_def]
  interpretation ra: set_copy rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_copy using ra_copy_impl .
  definition "hli_copy == SetGA.it_copy hs_iterate lsi_empty lsi_ins"
  lemmas hli_copy_impl = SetGA.it_copy_correct[OF hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded hli_copy_def]
  interpretation hli: set_copy hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_copy using hli_copy_impl .
  definition "hl_copy == SetGA.it_copy hs_iterate ls_empty ls_ins"
  lemmas hl_copy_impl = SetGA.it_copy_correct[OF hs_iterate_impl ls_empty_impl ls_ins_impl, folded hl_copy_def]
  interpretation hl: set_copy hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_copy using hl_copy_impl .
  definition "hr_copy == SetGA.it_copy hs_iterate rs_empty rs_ins"
  lemmas hr_copy_impl = SetGA.it_copy_correct[OF hs_iterate_impl rs_empty_impl rs_ins_impl, folded hr_copy_def]
  interpretation hr: set_copy hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_copy using hr_copy_impl .
  definition "hh_copy == SetGA.it_copy hs_iterate hs_empty hs_ins"
  lemmas hh_copy_impl = SetGA.it_copy_correct[OF hs_iterate_impl hs_empty_impl hs_ins_impl, folded hh_copy_def]
  interpretation hh: set_copy hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_copy using hh_copy_impl .
  definition "ha_copy == SetGA.it_copy hs_iterate ahs_empty ahs_ins"
  lemmas ha_copy_impl = SetGA.it_copy_correct[OF hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ha_copy_def]
  interpretation ha: set_copy hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_copy using ha_copy_impl .
  definition "ali_copy == SetGA.it_copy ahs_iterate lsi_empty lsi_ins"
  lemmas ali_copy_impl = SetGA.it_copy_correct[OF ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded ali_copy_def]
  interpretation ali: set_copy ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_copy using ali_copy_impl .
  definition "al_copy == SetGA.it_copy ahs_iterate ls_empty ls_ins"
  lemmas al_copy_impl = SetGA.it_copy_correct[OF ahs_iterate_impl ls_empty_impl ls_ins_impl, folded al_copy_def]
  interpretation al: set_copy ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_copy using al_copy_impl .
  definition "ar_copy == SetGA.it_copy ahs_iterate rs_empty rs_ins"
  lemmas ar_copy_impl = SetGA.it_copy_correct[OF ahs_iterate_impl rs_empty_impl rs_ins_impl, folded ar_copy_def]
  interpretation ar: set_copy ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_copy using ar_copy_impl .
  definition "ah_copy == SetGA.it_copy ahs_iterate hs_empty hs_ins"
  lemmas ah_copy_impl = SetGA.it_copy_correct[OF ahs_iterate_impl hs_empty_impl hs_ins_impl, folded ah_copy_def]
  interpretation ah: set_copy ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_copy using ah_copy_impl .
  definition "aa_copy == SetGA.it_copy ahs_iterate ahs_empty ahs_ins"
  lemmas aa_copy_impl = SetGA.it_copy_correct[OF ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded aa_copy_def]
  interpretation aa: set_copy ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_copy using aa_copy_impl .

  definition "lilili_union == SetGA.it_union lsi_iterate lsi_ins"
  lemmas lilili_union_impl = SetGA.it_union_correct[OF lsi_iterate_impl lsi_ins_impl, folded lilili_union_def]
  interpretation lilili: set_union lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_union using lilili_union_impl .
  definition "lill_union == SetGA.it_union lsi_iterate ls_ins"
  lemmas lill_union_impl = SetGA.it_union_correct[OF lsi_iterate_impl ls_ins_impl, folded lill_union_def]
  interpretation lill: set_union lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_union using lill_union_impl .
  definition "lirr_union == SetGA.it_union lsi_iterate rs_ins"
  lemmas lirr_union_impl = SetGA.it_union_correct[OF lsi_iterate_impl rs_ins_impl, folded lirr_union_def]
  interpretation lirr: set_union lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_union using lirr_union_impl .
  definition "lihh_union == SetGA.it_union lsi_iterate hs_ins"
  lemmas lihh_union_impl = SetGA.it_union_correct[OF lsi_iterate_impl hs_ins_impl, folded lihh_union_def]
  interpretation lihh: set_union lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_union using lihh_union_impl .
  definition "liaa_union == SetGA.it_union lsi_iterate ahs_ins"
  lemmas liaa_union_impl = SetGA.it_union_correct[OF lsi_iterate_impl ahs_ins_impl, folded liaa_union_def]
  interpretation liaa: set_union lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_union using liaa_union_impl .
  definition "llili_union == SetGA.it_union ls_iterate lsi_ins"
  lemmas llili_union_impl = SetGA.it_union_correct[OF ls_iterate_impl lsi_ins_impl, folded llili_union_def]
  interpretation llili: set_union ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_union using llili_union_impl .
  definition "lll_union == SetGA.it_union ls_iterate ls_ins"
  lemmas lll_union_impl = SetGA.it_union_correct[OF ls_iterate_impl ls_ins_impl, folded lll_union_def]
  interpretation lll: set_union ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union using lll_union_impl .
  definition "lrr_union == SetGA.it_union ls_iterate rs_ins"
  lemmas lrr_union_impl = SetGA.it_union_correct[OF ls_iterate_impl rs_ins_impl, folded lrr_union_def]
  interpretation lrr: set_union ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union using lrr_union_impl .
  definition "lhh_union == SetGA.it_union ls_iterate hs_ins"
  lemmas lhh_union_impl = SetGA.it_union_correct[OF ls_iterate_impl hs_ins_impl, folded lhh_union_def]
  interpretation lhh: set_union ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union using lhh_union_impl .
  definition "laa_union == SetGA.it_union ls_iterate ahs_ins"
  lemmas laa_union_impl = SetGA.it_union_correct[OF ls_iterate_impl ahs_ins_impl, folded laa_union_def]
  interpretation laa: set_union ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_union using laa_union_impl .
  definition "rlili_union == SetGA.it_union rs_iterate lsi_ins"
  lemmas rlili_union_impl = SetGA.it_union_correct[OF rs_iterate_impl lsi_ins_impl, folded rlili_union_def]
  interpretation rlili: set_union rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_union using rlili_union_impl .
  definition "rll_union == SetGA.it_union rs_iterate ls_ins"
  lemmas rll_union_impl = SetGA.it_union_correct[OF rs_iterate_impl ls_ins_impl, folded rll_union_def]
  interpretation rll: set_union rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union using rll_union_impl .
  definition "rrr_union == SetGA.it_union rs_iterate rs_ins"
  lemmas rrr_union_impl = SetGA.it_union_correct[OF rs_iterate_impl rs_ins_impl, folded rrr_union_def]
  interpretation rrr: set_union rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union using rrr_union_impl .
  definition "rhh_union == SetGA.it_union rs_iterate hs_ins"
  lemmas rhh_union_impl = SetGA.it_union_correct[OF rs_iterate_impl hs_ins_impl, folded rhh_union_def]
  interpretation rhh: set_union rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union using rhh_union_impl .
  definition "raa_union == SetGA.it_union rs_iterate ahs_ins"
  lemmas raa_union_impl = SetGA.it_union_correct[OF rs_iterate_impl ahs_ins_impl, folded raa_union_def]
  interpretation raa: set_union rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_union using raa_union_impl .
  definition "hlili_union == SetGA.it_union hs_iterate lsi_ins"
  lemmas hlili_union_impl = SetGA.it_union_correct[OF hs_iterate_impl lsi_ins_impl, folded hlili_union_def]
  interpretation hlili: set_union hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_union using hlili_union_impl .
  definition "hll_union == SetGA.it_union hs_iterate ls_ins"
  lemmas hll_union_impl = SetGA.it_union_correct[OF hs_iterate_impl ls_ins_impl, folded hll_union_def]
  interpretation hll: set_union hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union using hll_union_impl .
  definition "hrr_union == SetGA.it_union hs_iterate rs_ins"
  lemmas hrr_union_impl = SetGA.it_union_correct[OF hs_iterate_impl rs_ins_impl, folded hrr_union_def]
  interpretation hrr: set_union hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union using hrr_union_impl .
  definition "hhh_union == SetGA.it_union hs_iterate hs_ins"
  lemmas hhh_union_impl = SetGA.it_union_correct[OF hs_iterate_impl hs_ins_impl, folded hhh_union_def]
  interpretation hhh: set_union hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union using hhh_union_impl .
  definition "haa_union == SetGA.it_union hs_iterate ahs_ins"
  lemmas haa_union_impl = SetGA.it_union_correct[OF hs_iterate_impl ahs_ins_impl, folded haa_union_def]
  interpretation haa: set_union hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_union using haa_union_impl .
  definition "alili_union == SetGA.it_union ahs_iterate lsi_ins"
  lemmas alili_union_impl = SetGA.it_union_correct[OF ahs_iterate_impl lsi_ins_impl, folded alili_union_def]
  interpretation alili: set_union ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_union using alili_union_impl .
  definition "all_union == SetGA.it_union ahs_iterate ls_ins"
  lemmas all_union_impl = SetGA.it_union_correct[OF ahs_iterate_impl ls_ins_impl, folded all_union_def]
  interpretation all: set_union ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_union using all_union_impl .
  definition "arr_union == SetGA.it_union ahs_iterate rs_ins"
  lemmas arr_union_impl = SetGA.it_union_correct[OF ahs_iterate_impl rs_ins_impl, folded arr_union_def]
  interpretation arr: set_union ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_union using arr_union_impl .
  definition "ahh_union == SetGA.it_union ahs_iterate hs_ins"
  lemmas ahh_union_impl = SetGA.it_union_correct[OF ahs_iterate_impl hs_ins_impl, folded ahh_union_def]
  interpretation ahh: set_union ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_union using ahh_union_impl .
  definition "aaa_union == SetGA.it_union ahs_iterate ahs_ins"
  lemmas aaa_union_impl = SetGA.it_union_correct[OF ahs_iterate_impl ahs_ins_impl, folded aaa_union_def]
  interpretation aaa: set_union ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_union using aaa_union_impl .

  definition "lilili_union_dj == SetGA.it_union_dj lsi_iterate lsi_ins_dj"
  lemmas lilili_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iterate_impl lsi_ins_dj_impl, folded lilili_union_dj_def]
  interpretation lilili: set_union_dj lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_union_dj using lilili_union_dj_impl .
  definition "lill_union_dj == SetGA.it_union_dj lsi_iterate ls_ins_dj"
  lemmas lill_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iterate_impl ls_ins_dj_impl, folded lill_union_dj_def]
  interpretation lill: set_union_dj lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_union_dj using lill_union_dj_impl .
  definition "lirr_union_dj == SetGA.it_union_dj lsi_iterate rs_ins_dj"
  lemmas lirr_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iterate_impl rs_ins_dj_impl, folded lirr_union_dj_def]
  interpretation lirr: set_union_dj lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_union_dj using lirr_union_dj_impl .
  definition "lihh_union_dj == SetGA.it_union_dj lsi_iterate hs_ins_dj"
  lemmas lihh_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iterate_impl hs_ins_dj_impl, folded lihh_union_dj_def]
  interpretation lihh: set_union_dj lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_union_dj using lihh_union_dj_impl .
  definition "liaa_union_dj == SetGA.it_union_dj lsi_iterate ahs_ins_dj"
  lemmas liaa_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iterate_impl ahs_ins_dj_impl, folded liaa_union_dj_def]
  interpretation liaa: set_union_dj lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_union_dj using liaa_union_dj_impl .
  definition "llili_union_dj == SetGA.it_union_dj ls_iterate lsi_ins_dj"
  lemmas llili_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iterate_impl lsi_ins_dj_impl, folded llili_union_dj_def]
  interpretation llili: set_union_dj ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_union_dj using llili_union_dj_impl .
  definition "lll_union_dj == SetGA.it_union_dj ls_iterate ls_ins_dj"
  lemmas lll_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iterate_impl ls_ins_dj_impl, folded lll_union_dj_def]
  interpretation lll: set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union_dj using lll_union_dj_impl .
  definition "lrr_union_dj == SetGA.it_union_dj ls_iterate rs_ins_dj"
  lemmas lrr_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iterate_impl rs_ins_dj_impl, folded lrr_union_dj_def]
  interpretation lrr: set_union_dj ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union_dj using lrr_union_dj_impl .
  definition "lhh_union_dj == SetGA.it_union_dj ls_iterate hs_ins_dj"
  lemmas lhh_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iterate_impl hs_ins_dj_impl, folded lhh_union_dj_def]
  interpretation lhh: set_union_dj ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union_dj using lhh_union_dj_impl .
  definition "laa_union_dj == SetGA.it_union_dj ls_iterate ahs_ins_dj"
  lemmas laa_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iterate_impl ahs_ins_dj_impl, folded laa_union_dj_def]
  interpretation laa: set_union_dj ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_union_dj using laa_union_dj_impl .
  definition "rlili_union_dj == SetGA.it_union_dj rs_iterate lsi_ins_dj"
  lemmas rlili_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iterate_impl lsi_ins_dj_impl, folded rlili_union_dj_def]
  interpretation rlili: set_union_dj rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_union_dj using rlili_union_dj_impl .
  definition "rll_union_dj == SetGA.it_union_dj rs_iterate ls_ins_dj"
  lemmas rll_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iterate_impl ls_ins_dj_impl, folded rll_union_dj_def]
  interpretation rll: set_union_dj rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union_dj using rll_union_dj_impl .
  definition "rrr_union_dj == SetGA.it_union_dj rs_iterate rs_ins_dj"
  lemmas rrr_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iterate_impl rs_ins_dj_impl, folded rrr_union_dj_def]
  interpretation rrr: set_union_dj rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union_dj using rrr_union_dj_impl .
  definition "rhh_union_dj == SetGA.it_union_dj rs_iterate hs_ins_dj"
  lemmas rhh_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iterate_impl hs_ins_dj_impl, folded rhh_union_dj_def]
  interpretation rhh: set_union_dj rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union_dj using rhh_union_dj_impl .
  definition "raa_union_dj == SetGA.it_union_dj rs_iterate ahs_ins_dj"
  lemmas raa_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iterate_impl ahs_ins_dj_impl, folded raa_union_dj_def]
  interpretation raa: set_union_dj rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_union_dj using raa_union_dj_impl .
  definition "hlili_union_dj == SetGA.it_union_dj hs_iterate lsi_ins_dj"
  lemmas hlili_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iterate_impl lsi_ins_dj_impl, folded hlili_union_dj_def]
  interpretation hlili: set_union_dj hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_union_dj using hlili_union_dj_impl .
  definition "hll_union_dj == SetGA.it_union_dj hs_iterate ls_ins_dj"
  lemmas hll_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iterate_impl ls_ins_dj_impl, folded hll_union_dj_def]
  interpretation hll: set_union_dj hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union_dj using hll_union_dj_impl .
  definition "hrr_union_dj == SetGA.it_union_dj hs_iterate rs_ins_dj"
  lemmas hrr_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iterate_impl rs_ins_dj_impl, folded hrr_union_dj_def]
  interpretation hrr: set_union_dj hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union_dj using hrr_union_dj_impl .
  definition "hhh_union_dj == SetGA.it_union_dj hs_iterate hs_ins_dj"
  lemmas hhh_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iterate_impl hs_ins_dj_impl, folded hhh_union_dj_def]
  interpretation hhh: set_union_dj hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union_dj using hhh_union_dj_impl .
  definition "haa_union_dj == SetGA.it_union_dj hs_iterate ahs_ins_dj"
  lemmas haa_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iterate_impl ahs_ins_dj_impl, folded haa_union_dj_def]
  interpretation haa: set_union_dj hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_union_dj using haa_union_dj_impl .
  definition "alili_union_dj == SetGA.it_union_dj ahs_iterate lsi_ins_dj"
  lemmas alili_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iterate_impl lsi_ins_dj_impl, folded alili_union_dj_def]
  interpretation alili: set_union_dj ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_union_dj using alili_union_dj_impl .
  definition "all_union_dj == SetGA.it_union_dj ahs_iterate ls_ins_dj"
  lemmas all_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iterate_impl ls_ins_dj_impl, folded all_union_dj_def]
  interpretation all: set_union_dj ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_union_dj using all_union_dj_impl .
  definition "arr_union_dj == SetGA.it_union_dj ahs_iterate rs_ins_dj"
  lemmas arr_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iterate_impl rs_ins_dj_impl, folded arr_union_dj_def]
  interpretation arr: set_union_dj ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_union_dj using arr_union_dj_impl .
  definition "ahh_union_dj == SetGA.it_union_dj ahs_iterate hs_ins_dj"
  lemmas ahh_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iterate_impl hs_ins_dj_impl, folded ahh_union_dj_def]
  interpretation ahh: set_union_dj ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_union_dj using ahh_union_dj_impl .
  definition "aaa_union_dj == SetGA.it_union_dj ahs_iterate ahs_ins_dj"
  lemmas aaa_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iterate_impl ahs_ins_dj_impl, folded aaa_union_dj_def]
  interpretation aaa: set_union_dj ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_union_dj using aaa_union_dj_impl .

  definition "lilili_inter == SetGA.it_inter lsi_iterate lsi_memb lsi_empty lsi_ins_dj"
  lemmas lilili_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_inter_def]
  interpretation lilili: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_inter using lilili_inter_impl .
  definition "lilil_inter == SetGA.it_inter lsi_iterate lsi_memb ls_empty ls_ins_dj"
  lemmas lilil_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded lilil_inter_def]
  interpretation lilil: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lilil_inter using lilil_inter_impl .
  definition "lilir_inter == SetGA.it_inter lsi_iterate lsi_memb rs_empty rs_ins_dj"
  lemmas lilir_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded lilir_inter_def]
  interpretation lilir: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lilir_inter using lilir_inter_impl .
  definition "lilih_inter == SetGA.it_inter lsi_iterate lsi_memb hs_empty hs_ins_dj"
  lemmas lilih_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded lilih_inter_def]
  interpretation lilih: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lilih_inter using lilih_inter_impl .
  definition "lilia_inter == SetGA.it_inter lsi_iterate lsi_memb ahs_empty ahs_ins_dj"
  lemmas lilia_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_inter_def]
  interpretation lilia: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lilia_inter using lilia_inter_impl .
  definition "lilli_inter == SetGA.it_inter lsi_iterate ls_memb lsi_empty lsi_ins_dj"
  lemmas lilli_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_inter_def]
  interpretation lilli: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lilli_inter using lilli_inter_impl .
  definition "lill_inter == SetGA.it_inter lsi_iterate ls_memb ls_empty ls_ins_dj"
  lemmas lill_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded lill_inter_def]
  interpretation lill: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_inter using lill_inter_impl .
  definition "lilr_inter == SetGA.it_inter lsi_iterate ls_memb rs_empty rs_ins_dj"
  lemmas lilr_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded lilr_inter_def]
  interpretation lilr: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar lilr_inter using lilr_inter_impl .
  definition "lilh_inter == SetGA.it_inter lsi_iterate ls_memb hs_empty hs_ins_dj"
  lemmas lilh_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded lilh_inter_def]
  interpretation lilh: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar lilh_inter using lilh_inter_impl .
  definition "lila_inter == SetGA.it_inter lsi_iterate ls_memb ahs_empty ahs_ins_dj"
  lemmas lila_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_inter_def]
  interpretation lila: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lila_inter using lila_inter_impl .
  definition "lirli_inter == SetGA.it_inter lsi_iterate rs_memb lsi_empty lsi_ins_dj"
  lemmas lirli_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_inter_def]
  interpretation lirli: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lirli_inter using lirli_inter_impl .
  definition "lirl_inter == SetGA.it_inter lsi_iterate rs_memb ls_empty ls_ins_dj"
  lemmas lirl_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lirl_inter_def]
  interpretation lirl: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lirl_inter using lirl_inter_impl .
  definition "lirr_inter == SetGA.it_inter lsi_iterate rs_memb rs_empty rs_ins_dj"
  lemmas lirr_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lirr_inter_def]
  interpretation lirr: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_inter using lirr_inter_impl .
  definition "lirh_inter == SetGA.it_inter lsi_iterate rs_memb hs_empty hs_ins_dj"
  lemmas lirh_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lirh_inter_def]
  interpretation lirh: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lirh_inter using lirh_inter_impl .
  definition "lira_inter == SetGA.it_inter lsi_iterate rs_memb ahs_empty ahs_ins_dj"
  lemmas lira_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_inter_def]
  interpretation lira: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lira_inter using lira_inter_impl .
  definition "lihli_inter == SetGA.it_inter lsi_iterate hs_memb lsi_empty lsi_ins_dj"
  lemmas lihli_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_inter_def]
  interpretation lihli: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lihli_inter using lihli_inter_impl .
  definition "lihl_inter == SetGA.it_inter lsi_iterate hs_memb ls_empty ls_ins_dj"
  lemmas lihl_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lihl_inter_def]
  interpretation lihl: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lihl_inter using lihl_inter_impl .
  definition "lihr_inter == SetGA.it_inter lsi_iterate hs_memb rs_empty rs_ins_dj"
  lemmas lihr_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lihr_inter_def]
  interpretation lihr: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lihr_inter using lihr_inter_impl .
  definition "lihh_inter == SetGA.it_inter lsi_iterate hs_memb hs_empty hs_ins_dj"
  lemmas lihh_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lihh_inter_def]
  interpretation lihh: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_inter using lihh_inter_impl .
  definition "liha_inter == SetGA.it_inter lsi_iterate hs_memb ahs_empty ahs_ins_dj"
  lemmas liha_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_inter_def]
  interpretation liha: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar liha_inter using liha_inter_impl .
  definition "liali_inter == SetGA.it_inter lsi_iterate ahs_memb lsi_empty lsi_ins_dj"
  lemmas liali_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_inter_def]
  interpretation liali: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar liali_inter using liali_inter_impl .
  definition "lial_inter == SetGA.it_inter lsi_iterate ahs_memb ls_empty ls_ins_dj"
  lemmas lial_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lial_inter_def]
  interpretation lial: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lial_inter using lial_inter_impl .
  definition "liar_inter == SetGA.it_inter lsi_iterate ahs_memb rs_empty rs_ins_dj"
  lemmas liar_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded liar_inter_def]
  interpretation liar: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar liar_inter using liar_inter_impl .
  definition "liah_inter == SetGA.it_inter lsi_iterate ahs_memb hs_empty hs_ins_dj"
  lemmas liah_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded liah_inter_def]
  interpretation liah: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar liah_inter using liah_inter_impl .
  definition "liaa_inter == SetGA.it_inter lsi_iterate ahs_memb ahs_empty ahs_ins_dj"
  lemmas liaa_inter_impl = SetGA.it_inter_correct[OF lsi_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_inter_def]
  interpretation liaa: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_inter using liaa_inter_impl .
  definition "llili_inter == SetGA.it_inter ls_iterate lsi_memb lsi_empty lsi_ins_dj"
  lemmas llili_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_inter_def]
  interpretation llili: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_inter using llili_inter_impl .
  definition "llil_inter == SetGA.it_inter ls_iterate lsi_memb ls_empty ls_ins_dj"
  lemmas llil_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded llil_inter_def]
  interpretation llil: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar llil_inter using llil_inter_impl .
  definition "llir_inter == SetGA.it_inter ls_iterate lsi_memb rs_empty rs_ins_dj"
  lemmas llir_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded llir_inter_def]
  interpretation llir: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar llir_inter using llir_inter_impl .
  definition "llih_inter == SetGA.it_inter ls_iterate lsi_memb hs_empty hs_ins_dj"
  lemmas llih_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded llih_inter_def]
  interpretation llih: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar llih_inter using llih_inter_impl .
  definition "llia_inter == SetGA.it_inter ls_iterate lsi_memb ahs_empty ahs_ins_dj"
  lemmas llia_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_inter_def]
  interpretation llia: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar llia_inter using llia_inter_impl .
  definition "llli_inter == SetGA.it_inter ls_iterate ls_memb lsi_empty lsi_ins_dj"
  lemmas llli_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_inter_def]
  interpretation llli: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar llli_inter using llli_inter_impl .
  definition "lll_inter == SetGA.it_inter ls_iterate ls_memb ls_empty ls_ins_dj"
  lemmas lll_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded lll_inter_def]
  interpretation lll: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_inter using lll_inter_impl .
  definition "llr_inter == SetGA.it_inter ls_iterate ls_memb rs_empty rs_ins_dj"
  lemmas llr_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded llr_inter_def]
  interpretation llr: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_inter using llr_inter_impl .
  definition "llh_inter == SetGA.it_inter ls_iterate ls_memb hs_empty hs_ins_dj"
  lemmas llh_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded llh_inter_def]
  interpretation llh: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_inter using llh_inter_impl .
  definition "lla_inter == SetGA.it_inter ls_iterate ls_memb ahs_empty ahs_ins_dj"
  lemmas lla_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_inter_def]
  interpretation lla: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lla_inter using lla_inter_impl .
  definition "lrli_inter == SetGA.it_inter ls_iterate rs_memb lsi_empty lsi_ins_dj"
  lemmas lrli_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_inter_def]
  interpretation lrli: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lrli_inter using lrli_inter_impl .
  definition "lrl_inter == SetGA.it_inter ls_iterate rs_memb ls_empty ls_ins_dj"
  lemmas lrl_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inter_def]
  interpretation lrl: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_inter using lrl_inter_impl .
  definition "lrr_inter == SetGA.it_inter ls_iterate rs_memb rs_empty rs_ins_dj"
  lemmas lrr_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inter_def]
  interpretation lrr: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_inter using lrr_inter_impl .
  definition "lrh_inter == SetGA.it_inter ls_iterate rs_memb hs_empty hs_ins_dj"
  lemmas lrh_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inter_def]
  interpretation lrh: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_inter using lrh_inter_impl .
  definition "lra_inter == SetGA.it_inter ls_iterate rs_memb ahs_empty ahs_ins_dj"
  lemmas lra_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_inter_def]
  interpretation lra: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lra_inter using lra_inter_impl .
  definition "lhli_inter == SetGA.it_inter ls_iterate hs_memb lsi_empty lsi_ins_dj"
  lemmas lhli_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_inter_def]
  interpretation lhli: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lhli_inter using lhli_inter_impl .
  definition "lhl_inter == SetGA.it_inter ls_iterate hs_memb ls_empty ls_ins_dj"
  lemmas lhl_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inter_def]
  interpretation lhl: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_inter using lhl_inter_impl .
  definition "lhr_inter == SetGA.it_inter ls_iterate hs_memb rs_empty rs_ins_dj"
  lemmas lhr_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inter_def]
  interpretation lhr: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_inter using lhr_inter_impl .
  definition "lhh_inter == SetGA.it_inter ls_iterate hs_memb hs_empty hs_ins_dj"
  lemmas lhh_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inter_def]
  interpretation lhh: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_inter using lhh_inter_impl .
  definition "lha_inter == SetGA.it_inter ls_iterate hs_memb ahs_empty ahs_ins_dj"
  lemmas lha_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_inter_def]
  interpretation lha: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lha_inter using lha_inter_impl .
  definition "lali_inter == SetGA.it_inter ls_iterate ahs_memb lsi_empty lsi_ins_dj"
  lemmas lali_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_inter_def]
  interpretation lali: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lali_inter using lali_inter_impl .
  definition "lal_inter == SetGA.it_inter ls_iterate ahs_memb ls_empty ls_ins_dj"
  lemmas lal_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lal_inter_def]
  interpretation lal: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lal_inter using lal_inter_impl .
  definition "lar_inter == SetGA.it_inter ls_iterate ahs_memb rs_empty rs_ins_dj"
  lemmas lar_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lar_inter_def]
  interpretation lar: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lar_inter using lar_inter_impl .
  definition "lah_inter == SetGA.it_inter ls_iterate ahs_memb hs_empty hs_ins_dj"
  lemmas lah_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lah_inter_def]
  interpretation lah: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lah_inter using lah_inter_impl .
  definition "laa_inter == SetGA.it_inter ls_iterate ahs_memb ahs_empty ahs_ins_dj"
  lemmas laa_inter_impl = SetGA.it_inter_correct[OF ls_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_inter_def]
  interpretation laa: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_inter using laa_inter_impl .
  definition "rlili_inter == SetGA.it_inter rs_iterate lsi_memb lsi_empty lsi_ins_dj"
  lemmas rlili_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_inter_def]
  interpretation rlili: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_inter using rlili_inter_impl .
  definition "rlil_inter == SetGA.it_inter rs_iterate lsi_memb ls_empty ls_ins_dj"
  lemmas rlil_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded rlil_inter_def]
  interpretation rlil: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rlil_inter using rlil_inter_impl .
  definition "rlir_inter == SetGA.it_inter rs_iterate lsi_memb rs_empty rs_ins_dj"
  lemmas rlir_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded rlir_inter_def]
  interpretation rlir: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rlir_inter using rlir_inter_impl .
  definition "rlih_inter == SetGA.it_inter rs_iterate lsi_memb hs_empty hs_ins_dj"
  lemmas rlih_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded rlih_inter_def]
  interpretation rlih: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rlih_inter using rlih_inter_impl .
  definition "rlia_inter == SetGA.it_inter rs_iterate lsi_memb ahs_empty ahs_ins_dj"
  lemmas rlia_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_inter_def]
  interpretation rlia: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rlia_inter using rlia_inter_impl .
  definition "rlli_inter == SetGA.it_inter rs_iterate ls_memb lsi_empty lsi_ins_dj"
  lemmas rlli_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_inter_def]
  interpretation rlli: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rlli_inter using rlli_inter_impl .
  definition "rll_inter == SetGA.it_inter rs_iterate ls_memb ls_empty ls_ins_dj"
  lemmas rll_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded rll_inter_def]
  interpretation rll: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_inter using rll_inter_impl .
  definition "rlr_inter == SetGA.it_inter rs_iterate ls_memb rs_empty rs_ins_dj"
  lemmas rlr_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inter_def]
  interpretation rlr: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_inter using rlr_inter_impl .
  definition "rlh_inter == SetGA.it_inter rs_iterate ls_memb hs_empty hs_ins_dj"
  lemmas rlh_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inter_def]
  interpretation rlh: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_inter using rlh_inter_impl .
  definition "rla_inter == SetGA.it_inter rs_iterate ls_memb ahs_empty ahs_ins_dj"
  lemmas rla_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_inter_def]
  interpretation rla: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rla_inter using rla_inter_impl .
  definition "rrli_inter == SetGA.it_inter rs_iterate rs_memb lsi_empty lsi_ins_dj"
  lemmas rrli_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_inter_def]
  interpretation rrli: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rrli_inter using rrli_inter_impl .
  definition "rrl_inter == SetGA.it_inter rs_iterate rs_memb ls_empty ls_ins_dj"
  lemmas rrl_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inter_def]
  interpretation rrl: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_inter using rrl_inter_impl .
  definition "rrr_inter == SetGA.it_inter rs_iterate rs_memb rs_empty rs_ins_dj"
  lemmas rrr_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inter_def]
  interpretation rrr: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_inter using rrr_inter_impl .
  definition "rrh_inter == SetGA.it_inter rs_iterate rs_memb hs_empty hs_ins_dj"
  lemmas rrh_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inter_def]
  interpretation rrh: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_inter using rrh_inter_impl .
  definition "rra_inter == SetGA.it_inter rs_iterate rs_memb ahs_empty ahs_ins_dj"
  lemmas rra_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_inter_def]
  interpretation rra: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rra_inter using rra_inter_impl .
  definition "rhli_inter == SetGA.it_inter rs_iterate hs_memb lsi_empty lsi_ins_dj"
  lemmas rhli_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_inter_def]
  interpretation rhli: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rhli_inter using rhli_inter_impl .
  definition "rhl_inter == SetGA.it_inter rs_iterate hs_memb ls_empty ls_ins_dj"
  lemmas rhl_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inter_def]
  interpretation rhl: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_inter using rhl_inter_impl .
  definition "rhr_inter == SetGA.it_inter rs_iterate hs_memb rs_empty rs_ins_dj"
  lemmas rhr_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inter_def]
  interpretation rhr: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_inter using rhr_inter_impl .
  definition "rhh_inter == SetGA.it_inter rs_iterate hs_memb hs_empty hs_ins_dj"
  lemmas rhh_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inter_def]
  interpretation rhh: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_inter using rhh_inter_impl .
  definition "rha_inter == SetGA.it_inter rs_iterate hs_memb ahs_empty ahs_ins_dj"
  lemmas rha_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_inter_def]
  interpretation rha: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rha_inter using rha_inter_impl .
  definition "rali_inter == SetGA.it_inter rs_iterate ahs_memb lsi_empty lsi_ins_dj"
  lemmas rali_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_inter_def]
  interpretation rali: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rali_inter using rali_inter_impl .
  definition "ral_inter == SetGA.it_inter rs_iterate ahs_memb ls_empty ls_ins_dj"
  lemmas ral_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded ral_inter_def]
  interpretation ral: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ral_inter using ral_inter_impl .
  definition "rar_inter == SetGA.it_inter rs_iterate ahs_memb rs_empty rs_ins_dj"
  lemmas rar_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rar_inter_def]
  interpretation rar: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rar_inter using rar_inter_impl .
  definition "rah_inter == SetGA.it_inter rs_iterate ahs_memb hs_empty hs_ins_dj"
  lemmas rah_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rah_inter_def]
  interpretation rah: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rah_inter using rah_inter_impl .
  definition "raa_inter == SetGA.it_inter rs_iterate ahs_memb ahs_empty ahs_ins_dj"
  lemmas raa_inter_impl = SetGA.it_inter_correct[OF rs_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_inter_def]
  interpretation raa: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_inter using raa_inter_impl .
  definition "hlili_inter == SetGA.it_inter hs_iterate lsi_memb lsi_empty lsi_ins_dj"
  lemmas hlili_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_inter_def]
  interpretation hlili: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_inter using hlili_inter_impl .
  definition "hlil_inter == SetGA.it_inter hs_iterate lsi_memb ls_empty ls_ins_dj"
  lemmas hlil_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded hlil_inter_def]
  interpretation hlil: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hlil_inter using hlil_inter_impl .
  definition "hlir_inter == SetGA.it_inter hs_iterate lsi_memb rs_empty rs_ins_dj"
  lemmas hlir_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded hlir_inter_def]
  interpretation hlir: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hlir_inter using hlir_inter_impl .
  definition "hlih_inter == SetGA.it_inter hs_iterate lsi_memb hs_empty hs_ins_dj"
  lemmas hlih_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded hlih_inter_def]
  interpretation hlih: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hlih_inter using hlih_inter_impl .
  definition "hlia_inter == SetGA.it_inter hs_iterate lsi_memb ahs_empty ahs_ins_dj"
  lemmas hlia_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_inter_def]
  interpretation hlia: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hlia_inter using hlia_inter_impl .
  definition "hlli_inter == SetGA.it_inter hs_iterate ls_memb lsi_empty lsi_ins_dj"
  lemmas hlli_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_inter_def]
  interpretation hlli: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hlli_inter using hlli_inter_impl .
  definition "hll_inter == SetGA.it_inter hs_iterate ls_memb ls_empty ls_ins_dj"
  lemmas hll_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded hll_inter_def]
  interpretation hll: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_inter using hll_inter_impl .
  definition "hlr_inter == SetGA.it_inter hs_iterate ls_memb rs_empty rs_ins_dj"
  lemmas hlr_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inter_def]
  interpretation hlr: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_inter using hlr_inter_impl .
  definition "hlh_inter == SetGA.it_inter hs_iterate ls_memb hs_empty hs_ins_dj"
  lemmas hlh_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inter_def]
  interpretation hlh: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_inter using hlh_inter_impl .
  definition "hla_inter == SetGA.it_inter hs_iterate ls_memb ahs_empty ahs_ins_dj"
  lemmas hla_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_inter_def]
  interpretation hla: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hla_inter using hla_inter_impl .
  definition "hrli_inter == SetGA.it_inter hs_iterate rs_memb lsi_empty lsi_ins_dj"
  lemmas hrli_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_inter_def]
  interpretation hrli: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hrli_inter using hrli_inter_impl .
  definition "hrl_inter == SetGA.it_inter hs_iterate rs_memb ls_empty ls_ins_dj"
  lemmas hrl_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inter_def]
  interpretation hrl: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_inter using hrl_inter_impl .
  definition "hrr_inter == SetGA.it_inter hs_iterate rs_memb rs_empty rs_ins_dj"
  lemmas hrr_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inter_def]
  interpretation hrr: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_inter using hrr_inter_impl .
  definition "hrh_inter == SetGA.it_inter hs_iterate rs_memb hs_empty hs_ins_dj"
  lemmas hrh_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inter_def]
  interpretation hrh: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_inter using hrh_inter_impl .
  definition "hra_inter == SetGA.it_inter hs_iterate rs_memb ahs_empty ahs_ins_dj"
  lemmas hra_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_inter_def]
  interpretation hra: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hra_inter using hra_inter_impl .
  definition "hhli_inter == SetGA.it_inter hs_iterate hs_memb lsi_empty lsi_ins_dj"
  lemmas hhli_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_inter_def]
  interpretation hhli: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hhli_inter using hhli_inter_impl .
  definition "hhl_inter == SetGA.it_inter hs_iterate hs_memb ls_empty ls_ins_dj"
  lemmas hhl_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inter_def]
  interpretation hhl: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_inter using hhl_inter_impl .
  definition "hhr_inter == SetGA.it_inter hs_iterate hs_memb rs_empty rs_ins_dj"
  lemmas hhr_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inter_def]
  interpretation hhr: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_inter using hhr_inter_impl .
  definition "hhh_inter == SetGA.it_inter hs_iterate hs_memb hs_empty hs_ins_dj"
  lemmas hhh_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inter_def]
  interpretation hhh: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_inter using hhh_inter_impl .
  definition "hha_inter == SetGA.it_inter hs_iterate hs_memb ahs_empty ahs_ins_dj"
  lemmas hha_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_inter_def]
  interpretation hha: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hha_inter using hha_inter_impl .
  definition "hali_inter == SetGA.it_inter hs_iterate ahs_memb lsi_empty lsi_ins_dj"
  lemmas hali_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_inter_def]
  interpretation hali: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hali_inter using hali_inter_impl .
  definition "hal_inter == SetGA.it_inter hs_iterate ahs_memb ls_empty ls_ins_dj"
  lemmas hal_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hal_inter_def]
  interpretation hal: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hal_inter using hal_inter_impl .
  definition "har_inter == SetGA.it_inter hs_iterate ahs_memb rs_empty rs_ins_dj"
  lemmas har_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded har_inter_def]
  interpretation har: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar har_inter using har_inter_impl .
  definition "hah_inter == SetGA.it_inter hs_iterate ahs_memb hs_empty hs_ins_dj"
  lemmas hah_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hah_inter_def]
  interpretation hah: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hah_inter using hah_inter_impl .
  definition "haa_inter == SetGA.it_inter hs_iterate ahs_memb ahs_empty ahs_ins_dj"
  lemmas haa_inter_impl = SetGA.it_inter_correct[OF hs_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_inter_def]
  interpretation haa: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_inter using haa_inter_impl .
  definition "alili_inter == SetGA.it_inter ahs_iterate lsi_memb lsi_empty lsi_ins_dj"
  lemmas alili_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_inter_def]
  interpretation alili: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_inter using alili_inter_impl .
  definition "alil_inter == SetGA.it_inter ahs_iterate lsi_memb ls_empty ls_ins_dj"
  lemmas alil_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded alil_inter_def]
  interpretation alil: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar alil_inter using alil_inter_impl .
  definition "alir_inter == SetGA.it_inter ahs_iterate lsi_memb rs_empty rs_ins_dj"
  lemmas alir_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded alir_inter_def]
  interpretation alir: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar alir_inter using alir_inter_impl .
  definition "alih_inter == SetGA.it_inter ahs_iterate lsi_memb hs_empty hs_ins_dj"
  lemmas alih_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded alih_inter_def]
  interpretation alih: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar alih_inter using alih_inter_impl .
  definition "alia_inter == SetGA.it_inter ahs_iterate lsi_memb ahs_empty ahs_ins_dj"
  lemmas alia_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_inter_def]
  interpretation alia: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar alia_inter using alia_inter_impl .
  definition "alli_inter == SetGA.it_inter ahs_iterate ls_memb lsi_empty lsi_ins_dj"
  lemmas alli_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_inter_def]
  interpretation alli: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar alli_inter using alli_inter_impl .
  definition "all_inter == SetGA.it_inter ahs_iterate ls_memb ls_empty ls_ins_dj"
  lemmas all_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded all_inter_def]
  interpretation all: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_inter using all_inter_impl .
  definition "alr_inter == SetGA.it_inter ahs_iterate ls_memb rs_empty rs_ins_dj"
  lemmas alr_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded alr_inter_def]
  interpretation alr: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar alr_inter using alr_inter_impl .
  definition "alh_inter == SetGA.it_inter ahs_iterate ls_memb hs_empty hs_ins_dj"
  lemmas alh_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded alh_inter_def]
  interpretation alh: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar alh_inter using alh_inter_impl .
  definition "ala_inter == SetGA.it_inter ahs_iterate ls_memb ahs_empty ahs_ins_dj"
  lemmas ala_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_inter_def]
  interpretation ala: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ala_inter using ala_inter_impl .
  definition "arli_inter == SetGA.it_inter ahs_iterate rs_memb lsi_empty lsi_ins_dj"
  lemmas arli_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_inter_def]
  interpretation arli: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar arli_inter using arli_inter_impl .
  definition "arl_inter == SetGA.it_inter ahs_iterate rs_memb ls_empty ls_ins_dj"
  lemmas arl_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded arl_inter_def]
  interpretation arl: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar arl_inter using arl_inter_impl .
  definition "arr_inter == SetGA.it_inter ahs_iterate rs_memb rs_empty rs_ins_dj"
  lemmas arr_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded arr_inter_def]
  interpretation arr: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_inter using arr_inter_impl .
  definition "arh_inter == SetGA.it_inter ahs_iterate rs_memb hs_empty hs_ins_dj"
  lemmas arh_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded arh_inter_def]
  interpretation arh: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar arh_inter using arh_inter_impl .
  definition "ara_inter == SetGA.it_inter ahs_iterate rs_memb ahs_empty ahs_ins_dj"
  lemmas ara_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_inter_def]
  interpretation ara: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ara_inter using ara_inter_impl .
  definition "ahli_inter == SetGA.it_inter ahs_iterate hs_memb lsi_empty lsi_ins_dj"
  lemmas ahli_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_inter_def]
  interpretation ahli: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahli_inter using ahli_inter_impl .
  definition "ahl_inter == SetGA.it_inter ahs_iterate hs_memb ls_empty ls_ins_dj"
  lemmas ahl_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded ahl_inter_def]
  interpretation ahl: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahl_inter using ahl_inter_impl .
  definition "ahr_inter == SetGA.it_inter ahs_iterate hs_memb rs_empty rs_ins_dj"
  lemmas ahr_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded ahr_inter_def]
  interpretation ahr: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahr_inter using ahr_inter_impl .
  definition "ahh_inter == SetGA.it_inter ahs_iterate hs_memb hs_empty hs_ins_dj"
  lemmas ahh_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded ahh_inter_def]
  interpretation ahh: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_inter using ahh_inter_impl .
  definition "aha_inter == SetGA.it_inter ahs_iterate hs_memb ahs_empty ahs_ins_dj"
  lemmas aha_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_inter_def]
  interpretation aha: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar aha_inter using aha_inter_impl .
  definition "aali_inter == SetGA.it_inter ahs_iterate ahs_memb lsi_empty lsi_ins_dj"
  lemmas aali_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_inter_def]
  interpretation aali: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar aali_inter using aali_inter_impl .
  definition "aal_inter == SetGA.it_inter ahs_iterate ahs_memb ls_empty ls_ins_dj"
  lemmas aal_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded aal_inter_def]
  interpretation aal: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar aal_inter using aal_inter_impl .
  definition "aar_inter == SetGA.it_inter ahs_iterate ahs_memb rs_empty rs_ins_dj"
  lemmas aar_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded aar_inter_def]
  interpretation aar: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar aar_inter using aar_inter_impl .
  definition "aah_inter == SetGA.it_inter ahs_iterate ahs_memb hs_empty hs_ins_dj"
  lemmas aah_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded aah_inter_def]
  interpretation aah: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar aah_inter using aah_inter_impl .
  definition "aaa_inter == SetGA.it_inter ahs_iterate ahs_memb ahs_empty ahs_ins_dj"
  lemmas aaa_inter_impl = SetGA.it_inter_correct[OF ahs_iterate_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_inter_def]
  interpretation aaa: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_inter using aaa_inter_impl .

  definition "lili_subset == SetGA.ball_subset lsi_ball lsi_memb"
  lemmas lili_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl lsi_memb_impl, folded lili_subset_def]
  interpretation lili: set_subset lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_subset using lili_subset_impl .
  definition "lil_subset == SetGA.ball_subset lsi_ball ls_memb"
  lemmas lil_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl ls_memb_impl, folded lil_subset_def]
  interpretation lil: set_subset lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_subset using lil_subset_impl .
  definition "lir_subset == SetGA.ball_subset lsi_ball rs_memb"
  lemmas lir_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl rs_memb_impl, folded lir_subset_def]
  interpretation lir: set_subset lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_subset using lir_subset_impl .
  definition "lih_subset == SetGA.ball_subset lsi_ball hs_memb"
  lemmas lih_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl hs_memb_impl, folded lih_subset_def]
  interpretation lih: set_subset lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_subset using lih_subset_impl .
  definition "lia_subset == SetGA.ball_subset lsi_ball ahs_memb"
  lemmas lia_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl ahs_memb_impl, folded lia_subset_def]
  interpretation lia: set_subset lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_subset using lia_subset_impl .
  definition "lli_subset == SetGA.ball_subset ls_ball lsi_memb"
  lemmas lli_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl lsi_memb_impl, folded lli_subset_def]
  interpretation lli: set_subset ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_subset using lli_subset_impl .
  definition "ll_subset == SetGA.ball_subset ls_ball ls_memb"
  lemmas ll_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl ls_memb_impl, folded ll_subset_def]
  interpretation ll: set_subset ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_subset using ll_subset_impl .
  definition "lr_subset == SetGA.ball_subset ls_ball rs_memb"
  lemmas lr_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl rs_memb_impl, folded lr_subset_def]
  interpretation lr: set_subset ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_subset using lr_subset_impl .
  definition "lh_subset == SetGA.ball_subset ls_ball hs_memb"
  lemmas lh_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl hs_memb_impl, folded lh_subset_def]
  interpretation lh: set_subset ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_subset using lh_subset_impl .
  definition "la_subset == SetGA.ball_subset ls_ball ahs_memb"
  lemmas la_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl ahs_memb_impl, folded la_subset_def]
  interpretation la: set_subset ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_subset using la_subset_impl .
  definition "rli_subset == SetGA.ball_subset rs_ball lsi_memb"
  lemmas rli_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl lsi_memb_impl, folded rli_subset_def]
  interpretation rli: set_subset rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_subset using rli_subset_impl .
  definition "rl_subset == SetGA.ball_subset rs_ball ls_memb"
  lemmas rl_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl ls_memb_impl, folded rl_subset_def]
  interpretation rl: set_subset rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_subset using rl_subset_impl .
  definition "rr_subset == SetGA.ball_subset rs_ball rs_memb"
  lemmas rr_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl rs_memb_impl, folded rr_subset_def]
  interpretation rr: set_subset rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_subset using rr_subset_impl .
  definition "rh_subset == SetGA.ball_subset rs_ball hs_memb"
  lemmas rh_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl hs_memb_impl, folded rh_subset_def]
  interpretation rh: set_subset rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_subset using rh_subset_impl .
  definition "ra_subset == SetGA.ball_subset rs_ball ahs_memb"
  lemmas ra_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl ahs_memb_impl, folded ra_subset_def]
  interpretation ra: set_subset rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_subset using ra_subset_impl .
  definition "hli_subset == SetGA.ball_subset hs_ball lsi_memb"
  lemmas hli_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl lsi_memb_impl, folded hli_subset_def]
  interpretation hli: set_subset hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_subset using hli_subset_impl .
  definition "hl_subset == SetGA.ball_subset hs_ball ls_memb"
  lemmas hl_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl ls_memb_impl, folded hl_subset_def]
  interpretation hl: set_subset hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_subset using hl_subset_impl .
  definition "hr_subset == SetGA.ball_subset hs_ball rs_memb"
  lemmas hr_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl rs_memb_impl, folded hr_subset_def]
  interpretation hr: set_subset hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_subset using hr_subset_impl .
  definition "hh_subset == SetGA.ball_subset hs_ball hs_memb"
  lemmas hh_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl hs_memb_impl, folded hh_subset_def]
  interpretation hh: set_subset hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_subset using hh_subset_impl .
  definition "ha_subset == SetGA.ball_subset hs_ball ahs_memb"
  lemmas ha_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl ahs_memb_impl, folded ha_subset_def]
  interpretation ha: set_subset hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_subset using ha_subset_impl .
  definition "ali_subset == SetGA.ball_subset ahs_ball lsi_memb"
  lemmas ali_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl lsi_memb_impl, folded ali_subset_def]
  interpretation ali: set_subset ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_subset using ali_subset_impl .
  definition "al_subset == SetGA.ball_subset ahs_ball ls_memb"
  lemmas al_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl ls_memb_impl, folded al_subset_def]
  interpretation al: set_subset ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_subset using al_subset_impl .
  definition "ar_subset == SetGA.ball_subset ahs_ball rs_memb"
  lemmas ar_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl rs_memb_impl, folded ar_subset_def]
  interpretation ar: set_subset ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_subset using ar_subset_impl .
  definition "ah_subset == SetGA.ball_subset ahs_ball hs_memb"
  lemmas ah_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl hs_memb_impl, folded ah_subset_def]
  interpretation ah: set_subset ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_subset using ah_subset_impl .
  definition "aa_subset == SetGA.ball_subset ahs_ball ahs_memb"
  lemmas aa_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl ahs_memb_impl, folded aa_subset_def]
  interpretation aa: set_subset ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_subset using aa_subset_impl .

  definition "lili_equal == SetGA.subset_equal lili_subset lili_subset"
  lemmas lili_equal_impl = SetGA.subset_equal_correct[OF lili_subset_impl lili_subset_impl, folded lili_equal_def]
  interpretation lili: set_equal lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_equal using lili_equal_impl .
  definition "lil_equal == SetGA.subset_equal lil_subset lli_subset"
  lemmas lil_equal_impl = SetGA.subset_equal_correct[OF lil_subset_impl lli_subset_impl, folded lil_equal_def]
  interpretation lil: set_equal lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_equal using lil_equal_impl .
  definition "lir_equal == SetGA.subset_equal lir_subset rli_subset"
  lemmas lir_equal_impl = SetGA.subset_equal_correct[OF lir_subset_impl rli_subset_impl, folded lir_equal_def]
  interpretation lir: set_equal lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_equal using lir_equal_impl .
  definition "lih_equal == SetGA.subset_equal lih_subset hli_subset"
  lemmas lih_equal_impl = SetGA.subset_equal_correct[OF lih_subset_impl hli_subset_impl, folded lih_equal_def]
  interpretation lih: set_equal lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_equal using lih_equal_impl .
  definition "lia_equal == SetGA.subset_equal lia_subset ali_subset"
  lemmas lia_equal_impl = SetGA.subset_equal_correct[OF lia_subset_impl ali_subset_impl, folded lia_equal_def]
  interpretation lia: set_equal lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_equal using lia_equal_impl .
  definition "lli_equal == SetGA.subset_equal lli_subset lil_subset"
  lemmas lli_equal_impl = SetGA.subset_equal_correct[OF lli_subset_impl lil_subset_impl, folded lli_equal_def]
  interpretation lli: set_equal ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_equal using lli_equal_impl .
  definition "ll_equal == SetGA.subset_equal ll_subset ll_subset"
  lemmas ll_equal_impl = SetGA.subset_equal_correct[OF ll_subset_impl ll_subset_impl, folded ll_equal_def]
  interpretation ll: set_equal ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_equal using ll_equal_impl .
  definition "lr_equal == SetGA.subset_equal lr_subset rl_subset"
  lemmas lr_equal_impl = SetGA.subset_equal_correct[OF lr_subset_impl rl_subset_impl, folded lr_equal_def]
  interpretation lr: set_equal ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_equal using lr_equal_impl .
  definition "lh_equal == SetGA.subset_equal lh_subset hl_subset"
  lemmas lh_equal_impl = SetGA.subset_equal_correct[OF lh_subset_impl hl_subset_impl, folded lh_equal_def]
  interpretation lh: set_equal ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_equal using lh_equal_impl .
  definition "la_equal == SetGA.subset_equal la_subset al_subset"
  lemmas la_equal_impl = SetGA.subset_equal_correct[OF la_subset_impl al_subset_impl, folded la_equal_def]
  interpretation la: set_equal ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_equal using la_equal_impl .
  definition "rli_equal == SetGA.subset_equal rli_subset lir_subset"
  lemmas rli_equal_impl = SetGA.subset_equal_correct[OF rli_subset_impl lir_subset_impl, folded rli_equal_def]
  interpretation rli: set_equal rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_equal using rli_equal_impl .
  definition "rl_equal == SetGA.subset_equal rl_subset lr_subset"
  lemmas rl_equal_impl = SetGA.subset_equal_correct[OF rl_subset_impl lr_subset_impl, folded rl_equal_def]
  interpretation rl: set_equal rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_equal using rl_equal_impl .
  definition "rr_equal == SetGA.subset_equal rr_subset rr_subset"
  lemmas rr_equal_impl = SetGA.subset_equal_correct[OF rr_subset_impl rr_subset_impl, folded rr_equal_def]
  interpretation rr: set_equal rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_equal using rr_equal_impl .
  definition "rh_equal == SetGA.subset_equal rh_subset hr_subset"
  lemmas rh_equal_impl = SetGA.subset_equal_correct[OF rh_subset_impl hr_subset_impl, folded rh_equal_def]
  interpretation rh: set_equal rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_equal using rh_equal_impl .
  definition "ra_equal == SetGA.subset_equal ra_subset ar_subset"
  lemmas ra_equal_impl = SetGA.subset_equal_correct[OF ra_subset_impl ar_subset_impl, folded ra_equal_def]
  interpretation ra: set_equal rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_equal using ra_equal_impl .
  definition "hli_equal == SetGA.subset_equal hli_subset lih_subset"
  lemmas hli_equal_impl = SetGA.subset_equal_correct[OF hli_subset_impl lih_subset_impl, folded hli_equal_def]
  interpretation hli: set_equal hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_equal using hli_equal_impl .
  definition "hl_equal == SetGA.subset_equal hl_subset lh_subset"
  lemmas hl_equal_impl = SetGA.subset_equal_correct[OF hl_subset_impl lh_subset_impl, folded hl_equal_def]
  interpretation hl: set_equal hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_equal using hl_equal_impl .
  definition "hr_equal == SetGA.subset_equal hr_subset rh_subset"
  lemmas hr_equal_impl = SetGA.subset_equal_correct[OF hr_subset_impl rh_subset_impl, folded hr_equal_def]
  interpretation hr: set_equal hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_equal using hr_equal_impl .
  definition "hh_equal == SetGA.subset_equal hh_subset hh_subset"
  lemmas hh_equal_impl = SetGA.subset_equal_correct[OF hh_subset_impl hh_subset_impl, folded hh_equal_def]
  interpretation hh: set_equal hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_equal using hh_equal_impl .
  definition "ha_equal == SetGA.subset_equal ha_subset ah_subset"
  lemmas ha_equal_impl = SetGA.subset_equal_correct[OF ha_subset_impl ah_subset_impl, folded ha_equal_def]
  interpretation ha: set_equal hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_equal using ha_equal_impl .
  definition "ali_equal == SetGA.subset_equal ali_subset lia_subset"
  lemmas ali_equal_impl = SetGA.subset_equal_correct[OF ali_subset_impl lia_subset_impl, folded ali_equal_def]
  interpretation ali: set_equal ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_equal using ali_equal_impl .
  definition "al_equal == SetGA.subset_equal al_subset la_subset"
  lemmas al_equal_impl = SetGA.subset_equal_correct[OF al_subset_impl la_subset_impl, folded al_equal_def]
  interpretation al: set_equal ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_equal using al_equal_impl .
  definition "ar_equal == SetGA.subset_equal ar_subset ra_subset"
  lemmas ar_equal_impl = SetGA.subset_equal_correct[OF ar_subset_impl ra_subset_impl, folded ar_equal_def]
  interpretation ar: set_equal ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_equal using ar_equal_impl .
  definition "ah_equal == SetGA.subset_equal ah_subset ha_subset"
  lemmas ah_equal_impl = SetGA.subset_equal_correct[OF ah_subset_impl ha_subset_impl, folded ah_equal_def]
  interpretation ah: set_equal ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_equal using ah_equal_impl .
  definition "aa_equal == SetGA.subset_equal aa_subset aa_subset"
  lemmas aa_equal_impl = SetGA.subset_equal_correct[OF aa_subset_impl aa_subset_impl, folded aa_equal_def]
  interpretation aa: set_equal ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_equal using aa_equal_impl .

  definition "lili_image_filter == SetGA.it_image_filter lsi_iterate lsi_empty lsi_ins"
  lemmas lili_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded lili_image_filter_def]
  interpretation lili: set_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_image_filter using lili_image_filter_impl .
  definition "lil_image_filter == SetGA.it_image_filter lsi_iterate ls_empty ls_ins"
  lemmas lil_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iterate_impl ls_empty_impl ls_ins_impl, folded lil_image_filter_def]
  interpretation lil: set_image_filter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_image_filter using lil_image_filter_impl .
  definition "lir_image_filter == SetGA.it_image_filter lsi_iterate rs_empty rs_ins"
  lemmas lir_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iterate_impl rs_empty_impl rs_ins_impl, folded lir_image_filter_def]
  interpretation lir: set_image_filter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_image_filter using lir_image_filter_impl .
  definition "lih_image_filter == SetGA.it_image_filter lsi_iterate hs_empty hs_ins"
  lemmas lih_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iterate_impl hs_empty_impl hs_ins_impl, folded lih_image_filter_def]
  interpretation lih: set_image_filter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_image_filter using lih_image_filter_impl .
  definition "lia_image_filter == SetGA.it_image_filter lsi_iterate ahs_empty ahs_ins"
  lemmas lia_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded lia_image_filter_def]
  interpretation lia: set_image_filter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_image_filter using lia_image_filter_impl .
  definition "lli_image_filter == SetGA.it_image_filter ls_iterate lsi_empty lsi_ins"
  lemmas lli_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded lli_image_filter_def]
  interpretation lli: set_image_filter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_image_filter using lli_image_filter_impl .
  definition "ll_image_filter == SetGA.it_image_filter ls_iterate ls_empty ls_ins"
  lemmas ll_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_impl, folded ll_image_filter_def]
  interpretation ll: set_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_image_filter using ll_image_filter_impl .
  definition "lr_image_filter == SetGA.it_image_filter ls_iterate rs_empty rs_ins"
  lemmas lr_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iterate_impl rs_empty_impl rs_ins_impl, folded lr_image_filter_def]
  interpretation lr: set_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_image_filter using lr_image_filter_impl .
  definition "lh_image_filter == SetGA.it_image_filter ls_iterate hs_empty hs_ins"
  lemmas lh_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iterate_impl hs_empty_impl hs_ins_impl, folded lh_image_filter_def]
  interpretation lh: set_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_image_filter using lh_image_filter_impl .
  definition "la_image_filter == SetGA.it_image_filter ls_iterate ahs_empty ahs_ins"
  lemmas la_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded la_image_filter_def]
  interpretation la: set_image_filter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_image_filter using la_image_filter_impl .
  definition "rli_image_filter == SetGA.it_image_filter rs_iterate lsi_empty lsi_ins"
  lemmas rli_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded rli_image_filter_def]
  interpretation rli: set_image_filter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_image_filter using rli_image_filter_impl .
  definition "rl_image_filter == SetGA.it_image_filter rs_iterate ls_empty ls_ins"
  lemmas rl_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iterate_impl ls_empty_impl ls_ins_impl, folded rl_image_filter_def]
  interpretation rl: set_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_image_filter using rl_image_filter_impl .
  definition "rr_image_filter == SetGA.it_image_filter rs_iterate rs_empty rs_ins"
  lemmas rr_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_impl, folded rr_image_filter_def]
  interpretation rr: set_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_image_filter using rr_image_filter_impl .
  definition "rh_image_filter == SetGA.it_image_filter rs_iterate hs_empty hs_ins"
  lemmas rh_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iterate_impl hs_empty_impl hs_ins_impl, folded rh_image_filter_def]
  interpretation rh: set_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_image_filter using rh_image_filter_impl .
  definition "ra_image_filter == SetGA.it_image_filter rs_iterate ahs_empty ahs_ins"
  lemmas ra_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ra_image_filter_def]
  interpretation ra: set_image_filter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_image_filter using ra_image_filter_impl .
  definition "hli_image_filter == SetGA.it_image_filter hs_iterate lsi_empty lsi_ins"
  lemmas hli_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded hli_image_filter_def]
  interpretation hli: set_image_filter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_image_filter using hli_image_filter_impl .
  definition "hl_image_filter == SetGA.it_image_filter hs_iterate ls_empty ls_ins"
  lemmas hl_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iterate_impl ls_empty_impl ls_ins_impl, folded hl_image_filter_def]
  interpretation hl: set_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_image_filter using hl_image_filter_impl .
  definition "hr_image_filter == SetGA.it_image_filter hs_iterate rs_empty rs_ins"
  lemmas hr_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iterate_impl rs_empty_impl rs_ins_impl, folded hr_image_filter_def]
  interpretation hr: set_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_image_filter using hr_image_filter_impl .
  definition "hh_image_filter == SetGA.it_image_filter hs_iterate hs_empty hs_ins"
  lemmas hh_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iterate_impl hs_empty_impl hs_ins_impl, folded hh_image_filter_def]
  interpretation hh: set_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_image_filter using hh_image_filter_impl .
  definition "ha_image_filter == SetGA.it_image_filter hs_iterate ahs_empty ahs_ins"
  lemmas ha_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ha_image_filter_def]
  interpretation ha: set_image_filter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_image_filter using ha_image_filter_impl .
  definition "ali_image_filter == SetGA.it_image_filter ahs_iterate lsi_empty lsi_ins"
  lemmas ali_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded ali_image_filter_def]
  interpretation ali: set_image_filter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_image_filter using ali_image_filter_impl .
  definition "al_image_filter == SetGA.it_image_filter ahs_iterate ls_empty ls_ins"
  lemmas al_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iterate_impl ls_empty_impl ls_ins_impl, folded al_image_filter_def]
  interpretation al: set_image_filter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_image_filter using al_image_filter_impl .
  definition "ar_image_filter == SetGA.it_image_filter ahs_iterate rs_empty rs_ins"
  lemmas ar_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iterate_impl rs_empty_impl rs_ins_impl, folded ar_image_filter_def]
  interpretation ar: set_image_filter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_image_filter using ar_image_filter_impl .
  definition "ah_image_filter == SetGA.it_image_filter ahs_iterate hs_empty hs_ins"
  lemmas ah_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iterate_impl hs_empty_impl hs_ins_impl, folded ah_image_filter_def]
  interpretation ah: set_image_filter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_image_filter using ah_image_filter_impl .
  definition "aa_image_filter == SetGA.it_image_filter ahs_iterate ahs_empty ahs_ins"
  lemmas aa_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded aa_image_filter_def]
  interpretation aa: set_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_image_filter using aa_image_filter_impl .

  definition "lili_inj_image_filter == SetGA.it_inj_image_filter lsi_iterate lsi_empty lsi_ins_dj"
  lemmas lili_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lili_inj_image_filter_def]
  interpretation lili: set_inj_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_inj_image_filter using lili_inj_image_filter_impl .
  definition "lil_inj_image_filter == SetGA.it_inj_image_filter lsi_iterate ls_empty ls_ins_dj"
  lemmas lil_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lil_inj_image_filter_def]
  interpretation lil: set_inj_image_filter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_inj_image_filter using lil_inj_image_filter_impl .
  definition "lir_inj_image_filter == SetGA.it_inj_image_filter lsi_iterate rs_empty rs_ins_dj"
  lemmas lir_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lir_inj_image_filter_def]
  interpretation lir: set_inj_image_filter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_inj_image_filter using lir_inj_image_filter_impl .
  definition "lih_inj_image_filter == SetGA.it_inj_image_filter lsi_iterate hs_empty hs_ins_dj"
  lemmas lih_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lih_inj_image_filter_def]
  interpretation lih: set_inj_image_filter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_inj_image_filter using lih_inj_image_filter_impl .
  definition "lia_inj_image_filter == SetGA.it_inj_image_filter lsi_iterate ahs_empty ahs_ins_dj"
  lemmas lia_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lia_inj_image_filter_def]
  interpretation lia: set_inj_image_filter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_inj_image_filter using lia_inj_image_filter_impl .
  definition "lli_inj_image_filter == SetGA.it_inj_image_filter ls_iterate lsi_empty lsi_ins_dj"
  lemmas lli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lli_inj_image_filter_def]
  interpretation lli: set_inj_image_filter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_inj_image_filter using lli_inj_image_filter_impl .
  definition "ll_inj_image_filter == SetGA.it_inj_image_filter ls_iterate ls_empty ls_ins_dj"
  lemmas ll_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ll_inj_image_filter_def]
  interpretation ll: set_inj_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_inj_image_filter using ll_inj_image_filter_impl .
  definition "lr_inj_image_filter == SetGA.it_inj_image_filter ls_iterate rs_empty rs_ins_dj"
  lemmas lr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lr_inj_image_filter_def]
  interpretation lr: set_inj_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_inj_image_filter using lr_inj_image_filter_impl .
  definition "lh_inj_image_filter == SetGA.it_inj_image_filter ls_iterate hs_empty hs_ins_dj"
  lemmas lh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lh_inj_image_filter_def]
  interpretation lh: set_inj_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_inj_image_filter using lh_inj_image_filter_impl .
  definition "la_inj_image_filter == SetGA.it_inj_image_filter ls_iterate ahs_empty ahs_ins_dj"
  lemmas la_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded la_inj_image_filter_def]
  interpretation la: set_inj_image_filter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_inj_image_filter using la_inj_image_filter_impl .
  definition "rli_inj_image_filter == SetGA.it_inj_image_filter rs_iterate lsi_empty lsi_ins_dj"
  lemmas rli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rli_inj_image_filter_def]
  interpretation rli: set_inj_image_filter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_inj_image_filter using rli_inj_image_filter_impl .
  definition "rl_inj_image_filter == SetGA.it_inj_image_filter rs_iterate ls_empty ls_ins_dj"
  lemmas rl_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rl_inj_image_filter_def]
  interpretation rl: set_inj_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_inj_image_filter using rl_inj_image_filter_impl .
  definition "rr_inj_image_filter == SetGA.it_inj_image_filter rs_iterate rs_empty rs_ins_dj"
  lemmas rr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rr_inj_image_filter_def]
  interpretation rr: set_inj_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_inj_image_filter using rr_inj_image_filter_impl .
  definition "rh_inj_image_filter == SetGA.it_inj_image_filter rs_iterate hs_empty hs_ins_dj"
  lemmas rh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rh_inj_image_filter_def]
  interpretation rh: set_inj_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_inj_image_filter using rh_inj_image_filter_impl .
  definition "ra_inj_image_filter == SetGA.it_inj_image_filter rs_iterate ahs_empty ahs_ins_dj"
  lemmas ra_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ra_inj_image_filter_def]
  interpretation ra: set_inj_image_filter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_inj_image_filter using ra_inj_image_filter_impl .
  definition "hli_inj_image_filter == SetGA.it_inj_image_filter hs_iterate lsi_empty lsi_ins_dj"
  lemmas hli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hli_inj_image_filter_def]
  interpretation hli: set_inj_image_filter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_inj_image_filter using hli_inj_image_filter_impl .
  definition "hl_inj_image_filter == SetGA.it_inj_image_filter hs_iterate ls_empty ls_ins_dj"
  lemmas hl_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hl_inj_image_filter_def]
  interpretation hl: set_inj_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_inj_image_filter using hl_inj_image_filter_impl .
  definition "hr_inj_image_filter == SetGA.it_inj_image_filter hs_iterate rs_empty rs_ins_dj"
  lemmas hr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hr_inj_image_filter_def]
  interpretation hr: set_inj_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_inj_image_filter using hr_inj_image_filter_impl .
  definition "hh_inj_image_filter == SetGA.it_inj_image_filter hs_iterate hs_empty hs_ins_dj"
  lemmas hh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hh_inj_image_filter_def]
  interpretation hh: set_inj_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_inj_image_filter using hh_inj_image_filter_impl .
  definition "ha_inj_image_filter == SetGA.it_inj_image_filter hs_iterate ahs_empty ahs_ins_dj"
  lemmas ha_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ha_inj_image_filter_def]
  interpretation ha: set_inj_image_filter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_inj_image_filter using ha_inj_image_filter_impl .
  definition "ali_inj_image_filter == SetGA.it_inj_image_filter ahs_iterate lsi_empty lsi_ins_dj"
  lemmas ali_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded ali_inj_image_filter_def]
  interpretation ali: set_inj_image_filter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_inj_image_filter using ali_inj_image_filter_impl .
  definition "al_inj_image_filter == SetGA.it_inj_image_filter ahs_iterate ls_empty ls_ins_dj"
  lemmas al_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded al_inj_image_filter_def]
  interpretation al: set_inj_image_filter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_inj_image_filter using al_inj_image_filter_impl .
  definition "ar_inj_image_filter == SetGA.it_inj_image_filter ahs_iterate rs_empty rs_ins_dj"
  lemmas ar_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded ar_inj_image_filter_def]
  interpretation ar: set_inj_image_filter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_inj_image_filter using ar_inj_image_filter_impl .
  definition "ah_inj_image_filter == SetGA.it_inj_image_filter ahs_iterate hs_empty hs_ins_dj"
  lemmas ah_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded ah_inj_image_filter_def]
  interpretation ah: set_inj_image_filter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_inj_image_filter using ah_inj_image_filter_impl .
  definition "aa_inj_image_filter == SetGA.it_inj_image_filter ahs_iterate ahs_empty ahs_ins_dj"
  lemmas aa_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded aa_inj_image_filter_def]
  interpretation aa: set_inj_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_inj_image_filter using aa_inj_image_filter_impl .

  definition "lili_image == SetGA.iflt_image lili_image_filter"
  lemmas lili_image_impl = SetGA.iflt_image_correct[OF lili_image_filter_impl, folded lili_image_def]
  interpretation lili: set_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_image using lili_image_impl .
  definition "lil_image == SetGA.iflt_image lil_image_filter"
  lemmas lil_image_impl = SetGA.iflt_image_correct[OF lil_image_filter_impl, folded lil_image_def]
  interpretation lil: set_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_image using lil_image_impl .
  definition "lir_image == SetGA.iflt_image lir_image_filter"
  lemmas lir_image_impl = SetGA.iflt_image_correct[OF lir_image_filter_impl, folded lir_image_def]
  interpretation lir: set_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_image using lir_image_impl .
  definition "lih_image == SetGA.iflt_image lih_image_filter"
  lemmas lih_image_impl = SetGA.iflt_image_correct[OF lih_image_filter_impl, folded lih_image_def]
  interpretation lih: set_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_image using lih_image_impl .
  definition "lia_image == SetGA.iflt_image lia_image_filter"
  lemmas lia_image_impl = SetGA.iflt_image_correct[OF lia_image_filter_impl, folded lia_image_def]
  interpretation lia: set_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_image using lia_image_impl .
  definition "lli_image == SetGA.iflt_image lli_image_filter"
  lemmas lli_image_impl = SetGA.iflt_image_correct[OF lli_image_filter_impl, folded lli_image_def]
  interpretation lli: set_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_image using lli_image_impl .
  definition "ll_image == SetGA.iflt_image ll_image_filter"
  lemmas ll_image_impl = SetGA.iflt_image_correct[OF ll_image_filter_impl, folded ll_image_def]
  interpretation ll: set_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_image using ll_image_impl .
  definition "lr_image == SetGA.iflt_image lr_image_filter"
  lemmas lr_image_impl = SetGA.iflt_image_correct[OF lr_image_filter_impl, folded lr_image_def]
  interpretation lr: set_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_image using lr_image_impl .
  definition "lh_image == SetGA.iflt_image lh_image_filter"
  lemmas lh_image_impl = SetGA.iflt_image_correct[OF lh_image_filter_impl, folded lh_image_def]
  interpretation lh: set_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_image using lh_image_impl .
  definition "la_image == SetGA.iflt_image la_image_filter"
  lemmas la_image_impl = SetGA.iflt_image_correct[OF la_image_filter_impl, folded la_image_def]
  interpretation la: set_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_image using la_image_impl .
  definition "rli_image == SetGA.iflt_image rli_image_filter"
  lemmas rli_image_impl = SetGA.iflt_image_correct[OF rli_image_filter_impl, folded rli_image_def]
  interpretation rli: set_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_image using rli_image_impl .
  definition "rl_image == SetGA.iflt_image rl_image_filter"
  lemmas rl_image_impl = SetGA.iflt_image_correct[OF rl_image_filter_impl, folded rl_image_def]
  interpretation rl: set_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_image using rl_image_impl .
  definition "rr_image == SetGA.iflt_image rr_image_filter"
  lemmas rr_image_impl = SetGA.iflt_image_correct[OF rr_image_filter_impl, folded rr_image_def]
  interpretation rr: set_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_image using rr_image_impl .
  definition "rh_image == SetGA.iflt_image rh_image_filter"
  lemmas rh_image_impl = SetGA.iflt_image_correct[OF rh_image_filter_impl, folded rh_image_def]
  interpretation rh: set_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_image using rh_image_impl .
  definition "ra_image == SetGA.iflt_image ra_image_filter"
  lemmas ra_image_impl = SetGA.iflt_image_correct[OF ra_image_filter_impl, folded ra_image_def]
  interpretation ra: set_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_image using ra_image_impl .
  definition "hli_image == SetGA.iflt_image hli_image_filter"
  lemmas hli_image_impl = SetGA.iflt_image_correct[OF hli_image_filter_impl, folded hli_image_def]
  interpretation hli: set_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_image using hli_image_impl .
  definition "hl_image == SetGA.iflt_image hl_image_filter"
  lemmas hl_image_impl = SetGA.iflt_image_correct[OF hl_image_filter_impl, folded hl_image_def]
  interpretation hl: set_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_image using hl_image_impl .
  definition "hr_image == SetGA.iflt_image hr_image_filter"
  lemmas hr_image_impl = SetGA.iflt_image_correct[OF hr_image_filter_impl, folded hr_image_def]
  interpretation hr: set_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_image using hr_image_impl .
  definition "hh_image == SetGA.iflt_image hh_image_filter"
  lemmas hh_image_impl = SetGA.iflt_image_correct[OF hh_image_filter_impl, folded hh_image_def]
  interpretation hh: set_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_image using hh_image_impl .
  definition "ha_image == SetGA.iflt_image ha_image_filter"
  lemmas ha_image_impl = SetGA.iflt_image_correct[OF ha_image_filter_impl, folded ha_image_def]
  interpretation ha: set_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_image using ha_image_impl .
  definition "ali_image == SetGA.iflt_image ali_image_filter"
  lemmas ali_image_impl = SetGA.iflt_image_correct[OF ali_image_filter_impl, folded ali_image_def]
  interpretation ali: set_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_image using ali_image_impl .
  definition "al_image == SetGA.iflt_image al_image_filter"
  lemmas al_image_impl = SetGA.iflt_image_correct[OF al_image_filter_impl, folded al_image_def]
  interpretation al: set_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_image using al_image_impl .
  definition "ar_image == SetGA.iflt_image ar_image_filter"
  lemmas ar_image_impl = SetGA.iflt_image_correct[OF ar_image_filter_impl, folded ar_image_def]
  interpretation ar: set_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_image using ar_image_impl .
  definition "ah_image == SetGA.iflt_image ah_image_filter"
  lemmas ah_image_impl = SetGA.iflt_image_correct[OF ah_image_filter_impl, folded ah_image_def]
  interpretation ah: set_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_image using ah_image_impl .
  definition "aa_image == SetGA.iflt_image aa_image_filter"
  lemmas aa_image_impl = SetGA.iflt_image_correct[OF aa_image_filter_impl, folded aa_image_def]
  interpretation aa: set_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_image using aa_image_impl .

  definition "lili_inj_image == SetGA.iflt_inj_image lili_inj_image_filter"
  lemmas lili_inj_image_impl = SetGA.iflt_inj_image_correct[OF lili_inj_image_filter_impl, folded lili_inj_image_def]
  interpretation lili: set_inj_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_inj_image using lili_inj_image_impl .
  definition "lil_inj_image == SetGA.iflt_inj_image lil_inj_image_filter"
  lemmas lil_inj_image_impl = SetGA.iflt_inj_image_correct[OF lil_inj_image_filter_impl, folded lil_inj_image_def]
  interpretation lil: set_inj_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_inj_image using lil_inj_image_impl .
  definition "lir_inj_image == SetGA.iflt_inj_image lir_inj_image_filter"
  lemmas lir_inj_image_impl = SetGA.iflt_inj_image_correct[OF lir_inj_image_filter_impl, folded lir_inj_image_def]
  interpretation lir: set_inj_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_inj_image using lir_inj_image_impl .
  definition "lih_inj_image == SetGA.iflt_inj_image lih_inj_image_filter"
  lemmas lih_inj_image_impl = SetGA.iflt_inj_image_correct[OF lih_inj_image_filter_impl, folded lih_inj_image_def]
  interpretation lih: set_inj_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_inj_image using lih_inj_image_impl .
  definition "lia_inj_image == SetGA.iflt_inj_image lia_inj_image_filter"
  lemmas lia_inj_image_impl = SetGA.iflt_inj_image_correct[OF lia_inj_image_filter_impl, folded lia_inj_image_def]
  interpretation lia: set_inj_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_inj_image using lia_inj_image_impl .
  definition "lli_inj_image == SetGA.iflt_inj_image lli_inj_image_filter"
  lemmas lli_inj_image_impl = SetGA.iflt_inj_image_correct[OF lli_inj_image_filter_impl, folded lli_inj_image_def]
  interpretation lli: set_inj_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_inj_image using lli_inj_image_impl .
  definition "ll_inj_image == SetGA.iflt_inj_image ll_inj_image_filter"
  lemmas ll_inj_image_impl = SetGA.iflt_inj_image_correct[OF ll_inj_image_filter_impl, folded ll_inj_image_def]
  interpretation ll: set_inj_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_inj_image using ll_inj_image_impl .
  definition "lr_inj_image == SetGA.iflt_inj_image lr_inj_image_filter"
  lemmas lr_inj_image_impl = SetGA.iflt_inj_image_correct[OF lr_inj_image_filter_impl, folded lr_inj_image_def]
  interpretation lr: set_inj_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_inj_image using lr_inj_image_impl .
  definition "lh_inj_image == SetGA.iflt_inj_image lh_inj_image_filter"
  lemmas lh_inj_image_impl = SetGA.iflt_inj_image_correct[OF lh_inj_image_filter_impl, folded lh_inj_image_def]
  interpretation lh: set_inj_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_inj_image using lh_inj_image_impl .
  definition "la_inj_image == SetGA.iflt_inj_image la_inj_image_filter"
  lemmas la_inj_image_impl = SetGA.iflt_inj_image_correct[OF la_inj_image_filter_impl, folded la_inj_image_def]
  interpretation la: set_inj_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_inj_image using la_inj_image_impl .
  definition "rli_inj_image == SetGA.iflt_inj_image rli_inj_image_filter"
  lemmas rli_inj_image_impl = SetGA.iflt_inj_image_correct[OF rli_inj_image_filter_impl, folded rli_inj_image_def]
  interpretation rli: set_inj_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_inj_image using rli_inj_image_impl .
  definition "rl_inj_image == SetGA.iflt_inj_image rl_inj_image_filter"
  lemmas rl_inj_image_impl = SetGA.iflt_inj_image_correct[OF rl_inj_image_filter_impl, folded rl_inj_image_def]
  interpretation rl: set_inj_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_inj_image using rl_inj_image_impl .
  definition "rr_inj_image == SetGA.iflt_inj_image rr_inj_image_filter"
  lemmas rr_inj_image_impl = SetGA.iflt_inj_image_correct[OF rr_inj_image_filter_impl, folded rr_inj_image_def]
  interpretation rr: set_inj_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_inj_image using rr_inj_image_impl .
  definition "rh_inj_image == SetGA.iflt_inj_image rh_inj_image_filter"
  lemmas rh_inj_image_impl = SetGA.iflt_inj_image_correct[OF rh_inj_image_filter_impl, folded rh_inj_image_def]
  interpretation rh: set_inj_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_inj_image using rh_inj_image_impl .
  definition "ra_inj_image == SetGA.iflt_inj_image ra_inj_image_filter"
  lemmas ra_inj_image_impl = SetGA.iflt_inj_image_correct[OF ra_inj_image_filter_impl, folded ra_inj_image_def]
  interpretation ra: set_inj_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_inj_image using ra_inj_image_impl .
  definition "hli_inj_image == SetGA.iflt_inj_image hli_inj_image_filter"
  lemmas hli_inj_image_impl = SetGA.iflt_inj_image_correct[OF hli_inj_image_filter_impl, folded hli_inj_image_def]
  interpretation hli: set_inj_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_inj_image using hli_inj_image_impl .
  definition "hl_inj_image == SetGA.iflt_inj_image hl_inj_image_filter"
  lemmas hl_inj_image_impl = SetGA.iflt_inj_image_correct[OF hl_inj_image_filter_impl, folded hl_inj_image_def]
  interpretation hl: set_inj_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_inj_image using hl_inj_image_impl .
  definition "hr_inj_image == SetGA.iflt_inj_image hr_inj_image_filter"
  lemmas hr_inj_image_impl = SetGA.iflt_inj_image_correct[OF hr_inj_image_filter_impl, folded hr_inj_image_def]
  interpretation hr: set_inj_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_inj_image using hr_inj_image_impl .
  definition "hh_inj_image == SetGA.iflt_inj_image hh_inj_image_filter"
  lemmas hh_inj_image_impl = SetGA.iflt_inj_image_correct[OF hh_inj_image_filter_impl, folded hh_inj_image_def]
  interpretation hh: set_inj_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_inj_image using hh_inj_image_impl .
  definition "ha_inj_image == SetGA.iflt_inj_image ha_inj_image_filter"
  lemmas ha_inj_image_impl = SetGA.iflt_inj_image_correct[OF ha_inj_image_filter_impl, folded ha_inj_image_def]
  interpretation ha: set_inj_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_inj_image using ha_inj_image_impl .
  definition "ali_inj_image == SetGA.iflt_inj_image ali_inj_image_filter"
  lemmas ali_inj_image_impl = SetGA.iflt_inj_image_correct[OF ali_inj_image_filter_impl, folded ali_inj_image_def]
  interpretation ali: set_inj_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_inj_image using ali_inj_image_impl .
  definition "al_inj_image == SetGA.iflt_inj_image al_inj_image_filter"
  lemmas al_inj_image_impl = SetGA.iflt_inj_image_correct[OF al_inj_image_filter_impl, folded al_inj_image_def]
  interpretation al: set_inj_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_inj_image using al_inj_image_impl .
  definition "ar_inj_image == SetGA.iflt_inj_image ar_inj_image_filter"
  lemmas ar_inj_image_impl = SetGA.iflt_inj_image_correct[OF ar_inj_image_filter_impl, folded ar_inj_image_def]
  interpretation ar: set_inj_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_inj_image using ar_inj_image_impl .
  definition "ah_inj_image == SetGA.iflt_inj_image ah_inj_image_filter"
  lemmas ah_inj_image_impl = SetGA.iflt_inj_image_correct[OF ah_inj_image_filter_impl, folded ah_inj_image_def]
  interpretation ah: set_inj_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_inj_image using ah_inj_image_impl .
  definition "aa_inj_image == SetGA.iflt_inj_image aa_inj_image_filter"
  lemmas aa_inj_image_impl = SetGA.iflt_inj_image_correct[OF aa_inj_image_filter_impl, folded aa_inj_image_def]
  interpretation aa: set_inj_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_inj_image using aa_inj_image_impl .

  definition "lilili_Union_image == SetGA.it_Union_image lsi_iterate lsi_empty lilili_union"
  lemmas lilili_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl lsi_empty_impl lilili_union_impl, folded lilili_Union_image_def]
  interpretation lilili: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_Union_image using lilili_Union_image_impl .
  definition "lilil_Union_image == SetGA.it_Union_image lsi_iterate ls_empty lill_union"
  lemmas lilil_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ls_empty_impl lill_union_impl, folded lilil_Union_image_def]
  interpretation lilil: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lilil_Union_image using lilil_Union_image_impl .
  definition "lilir_Union_image == SetGA.it_Union_image lsi_iterate rs_empty lirr_union"
  lemmas lilir_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl rs_empty_impl lirr_union_impl, folded lilir_Union_image_def]
  interpretation lilir: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lilir_Union_image using lilir_Union_image_impl .
  definition "lilih_Union_image == SetGA.it_Union_image lsi_iterate hs_empty lihh_union"
  lemmas lilih_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl hs_empty_impl lihh_union_impl, folded lilih_Union_image_def]
  interpretation lilih: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lilih_Union_image using lilih_Union_image_impl .
  definition "lilia_Union_image == SetGA.it_Union_image lsi_iterate ahs_empty liaa_union"
  lemmas lilia_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ahs_empty_impl liaa_union_impl, folded lilia_Union_image_def]
  interpretation lilia: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lilia_Union_image using lilia_Union_image_impl .
  definition "lilli_Union_image == SetGA.it_Union_image lsi_iterate lsi_empty llili_union"
  lemmas lilli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl lsi_empty_impl llili_union_impl, folded lilli_Union_image_def]
  interpretation lilli: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lilli_Union_image using lilli_Union_image_impl .
  definition "lill_Union_image == SetGA.it_Union_image lsi_iterate ls_empty lll_union"
  lemmas lill_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ls_empty_impl lll_union_impl, folded lill_Union_image_def]
  interpretation lill: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_Union_image using lill_Union_image_impl .
  definition "lilr_Union_image == SetGA.it_Union_image lsi_iterate rs_empty lrr_union"
  lemmas lilr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl rs_empty_impl lrr_union_impl, folded lilr_Union_image_def]
  interpretation lilr: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar lilr_Union_image using lilr_Union_image_impl .
  definition "lilh_Union_image == SetGA.it_Union_image lsi_iterate hs_empty lhh_union"
  lemmas lilh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl hs_empty_impl lhh_union_impl, folded lilh_Union_image_def]
  interpretation lilh: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar lilh_Union_image using lilh_Union_image_impl .
  definition "lila_Union_image == SetGA.it_Union_image lsi_iterate ahs_empty laa_union"
  lemmas lila_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ahs_empty_impl laa_union_impl, folded lila_Union_image_def]
  interpretation lila: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lila_Union_image using lila_Union_image_impl .
  definition "lirli_Union_image == SetGA.it_Union_image lsi_iterate lsi_empty rlili_union"
  lemmas lirli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl lsi_empty_impl rlili_union_impl, folded lirli_Union_image_def]
  interpretation lirli: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lirli_Union_image using lirli_Union_image_impl .
  definition "lirl_Union_image == SetGA.it_Union_image lsi_iterate ls_empty rll_union"
  lemmas lirl_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ls_empty_impl rll_union_impl, folded lirl_Union_image_def]
  interpretation lirl: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lirl_Union_image using lirl_Union_image_impl .
  definition "lirr_Union_image == SetGA.it_Union_image lsi_iterate rs_empty rrr_union"
  lemmas lirr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl rs_empty_impl rrr_union_impl, folded lirr_Union_image_def]
  interpretation lirr: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_Union_image using lirr_Union_image_impl .
  definition "lirh_Union_image == SetGA.it_Union_image lsi_iterate hs_empty rhh_union"
  lemmas lirh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl hs_empty_impl rhh_union_impl, folded lirh_Union_image_def]
  interpretation lirh: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lirh_Union_image using lirh_Union_image_impl .
  definition "lira_Union_image == SetGA.it_Union_image lsi_iterate ahs_empty raa_union"
  lemmas lira_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ahs_empty_impl raa_union_impl, folded lira_Union_image_def]
  interpretation lira: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lira_Union_image using lira_Union_image_impl .
  definition "lihli_Union_image == SetGA.it_Union_image lsi_iterate lsi_empty hlili_union"
  lemmas lihli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl lsi_empty_impl hlili_union_impl, folded lihli_Union_image_def]
  interpretation lihli: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lihli_Union_image using lihli_Union_image_impl .
  definition "lihl_Union_image == SetGA.it_Union_image lsi_iterate ls_empty hll_union"
  lemmas lihl_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ls_empty_impl hll_union_impl, folded lihl_Union_image_def]
  interpretation lihl: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lihl_Union_image using lihl_Union_image_impl .
  definition "lihr_Union_image == SetGA.it_Union_image lsi_iterate rs_empty hrr_union"
  lemmas lihr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl rs_empty_impl hrr_union_impl, folded lihr_Union_image_def]
  interpretation lihr: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lihr_Union_image using lihr_Union_image_impl .
  definition "lihh_Union_image == SetGA.it_Union_image lsi_iterate hs_empty hhh_union"
  lemmas lihh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl hs_empty_impl hhh_union_impl, folded lihh_Union_image_def]
  interpretation lihh: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_Union_image using lihh_Union_image_impl .
  definition "liha_Union_image == SetGA.it_Union_image lsi_iterate ahs_empty haa_union"
  lemmas liha_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ahs_empty_impl haa_union_impl, folded liha_Union_image_def]
  interpretation liha: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar liha_Union_image using liha_Union_image_impl .
  definition "liali_Union_image == SetGA.it_Union_image lsi_iterate lsi_empty alili_union"
  lemmas liali_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl lsi_empty_impl alili_union_impl, folded liali_Union_image_def]
  interpretation liali: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar liali_Union_image using liali_Union_image_impl .
  definition "lial_Union_image == SetGA.it_Union_image lsi_iterate ls_empty all_union"
  lemmas lial_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ls_empty_impl all_union_impl, folded lial_Union_image_def]
  interpretation lial: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lial_Union_image using lial_Union_image_impl .
  definition "liar_Union_image == SetGA.it_Union_image lsi_iterate rs_empty arr_union"
  lemmas liar_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl rs_empty_impl arr_union_impl, folded liar_Union_image_def]
  interpretation liar: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar liar_Union_image using liar_Union_image_impl .
  definition "liah_Union_image == SetGA.it_Union_image lsi_iterate hs_empty ahh_union"
  lemmas liah_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl hs_empty_impl ahh_union_impl, folded liah_Union_image_def]
  interpretation liah: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar liah_Union_image using liah_Union_image_impl .
  definition "liaa_Union_image == SetGA.it_Union_image lsi_iterate ahs_empty aaa_union"
  lemmas liaa_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iterate_impl ahs_empty_impl aaa_union_impl, folded liaa_Union_image_def]
  interpretation liaa: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_Union_image using liaa_Union_image_impl .
  definition "llili_Union_image == SetGA.it_Union_image ls_iterate lsi_empty lilili_union"
  lemmas llili_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl lsi_empty_impl lilili_union_impl, folded llili_Union_image_def]
  interpretation llili: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_Union_image using llili_Union_image_impl .
  definition "llil_Union_image == SetGA.it_Union_image ls_iterate ls_empty lill_union"
  lemmas llil_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ls_empty_impl lill_union_impl, folded llil_Union_image_def]
  interpretation llil: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar llil_Union_image using llil_Union_image_impl .
  definition "llir_Union_image == SetGA.it_Union_image ls_iterate rs_empty lirr_union"
  lemmas llir_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl rs_empty_impl lirr_union_impl, folded llir_Union_image_def]
  interpretation llir: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar llir_Union_image using llir_Union_image_impl .
  definition "llih_Union_image == SetGA.it_Union_image ls_iterate hs_empty lihh_union"
  lemmas llih_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl hs_empty_impl lihh_union_impl, folded llih_Union_image_def]
  interpretation llih: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar llih_Union_image using llih_Union_image_impl .
  definition "llia_Union_image == SetGA.it_Union_image ls_iterate ahs_empty liaa_union"
  lemmas llia_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ahs_empty_impl liaa_union_impl, folded llia_Union_image_def]
  interpretation llia: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar llia_Union_image using llia_Union_image_impl .
  definition "llli_Union_image == SetGA.it_Union_image ls_iterate lsi_empty llili_union"
  lemmas llli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl lsi_empty_impl llili_union_impl, folded llli_Union_image_def]
  interpretation llli: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar llli_Union_image using llli_Union_image_impl .
  definition "lll_Union_image == SetGA.it_Union_image ls_iterate ls_empty lll_union"
  lemmas lll_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ls_empty_impl lll_union_impl, folded lll_Union_image_def]
  interpretation lll: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_Union_image using lll_Union_image_impl .
  definition "llr_Union_image == SetGA.it_Union_image ls_iterate rs_empty lrr_union"
  lemmas llr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl rs_empty_impl lrr_union_impl, folded llr_Union_image_def]
  interpretation llr: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_Union_image using llr_Union_image_impl .
  definition "llh_Union_image == SetGA.it_Union_image ls_iterate hs_empty lhh_union"
  lemmas llh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl hs_empty_impl lhh_union_impl, folded llh_Union_image_def]
  interpretation llh: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_Union_image using llh_Union_image_impl .
  definition "lla_Union_image == SetGA.it_Union_image ls_iterate ahs_empty laa_union"
  lemmas lla_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ahs_empty_impl laa_union_impl, folded lla_Union_image_def]
  interpretation lla: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lla_Union_image using lla_Union_image_impl .
  definition "lrli_Union_image == SetGA.it_Union_image ls_iterate lsi_empty rlili_union"
  lemmas lrli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl lsi_empty_impl rlili_union_impl, folded lrli_Union_image_def]
  interpretation lrli: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lrli_Union_image using lrli_Union_image_impl .
  definition "lrl_Union_image == SetGA.it_Union_image ls_iterate ls_empty rll_union"
  lemmas lrl_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ls_empty_impl rll_union_impl, folded lrl_Union_image_def]
  interpretation lrl: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_Union_image using lrl_Union_image_impl .
  definition "lrr_Union_image == SetGA.it_Union_image ls_iterate rs_empty rrr_union"
  lemmas lrr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl rs_empty_impl rrr_union_impl, folded lrr_Union_image_def]
  interpretation lrr: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_Union_image using lrr_Union_image_impl .
  definition "lrh_Union_image == SetGA.it_Union_image ls_iterate hs_empty rhh_union"
  lemmas lrh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl hs_empty_impl rhh_union_impl, folded lrh_Union_image_def]
  interpretation lrh: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_Union_image using lrh_Union_image_impl .
  definition "lra_Union_image == SetGA.it_Union_image ls_iterate ahs_empty raa_union"
  lemmas lra_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ahs_empty_impl raa_union_impl, folded lra_Union_image_def]
  interpretation lra: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lra_Union_image using lra_Union_image_impl .
  definition "lhli_Union_image == SetGA.it_Union_image ls_iterate lsi_empty hlili_union"
  lemmas lhli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl lsi_empty_impl hlili_union_impl, folded lhli_Union_image_def]
  interpretation lhli: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lhli_Union_image using lhli_Union_image_impl .
  definition "lhl_Union_image == SetGA.it_Union_image ls_iterate ls_empty hll_union"
  lemmas lhl_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ls_empty_impl hll_union_impl, folded lhl_Union_image_def]
  interpretation lhl: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_Union_image using lhl_Union_image_impl .
  definition "lhr_Union_image == SetGA.it_Union_image ls_iterate rs_empty hrr_union"
  lemmas lhr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl rs_empty_impl hrr_union_impl, folded lhr_Union_image_def]
  interpretation lhr: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_Union_image using lhr_Union_image_impl .
  definition "lhh_Union_image == SetGA.it_Union_image ls_iterate hs_empty hhh_union"
  lemmas lhh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl hs_empty_impl hhh_union_impl, folded lhh_Union_image_def]
  interpretation lhh: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_Union_image using lhh_Union_image_impl .
  definition "lha_Union_image == SetGA.it_Union_image ls_iterate ahs_empty haa_union"
  lemmas lha_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ahs_empty_impl haa_union_impl, folded lha_Union_image_def]
  interpretation lha: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lha_Union_image using lha_Union_image_impl .
  definition "lali_Union_image == SetGA.it_Union_image ls_iterate lsi_empty alili_union"
  lemmas lali_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl lsi_empty_impl alili_union_impl, folded lali_Union_image_def]
  interpretation lali: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lali_Union_image using lali_Union_image_impl .
  definition "lal_Union_image == SetGA.it_Union_image ls_iterate ls_empty all_union"
  lemmas lal_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ls_empty_impl all_union_impl, folded lal_Union_image_def]
  interpretation lal: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lal_Union_image using lal_Union_image_impl .
  definition "lar_Union_image == SetGA.it_Union_image ls_iterate rs_empty arr_union"
  lemmas lar_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl rs_empty_impl arr_union_impl, folded lar_Union_image_def]
  interpretation lar: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lar_Union_image using lar_Union_image_impl .
  definition "lah_Union_image == SetGA.it_Union_image ls_iterate hs_empty ahh_union"
  lemmas lah_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl hs_empty_impl ahh_union_impl, folded lah_Union_image_def]
  interpretation lah: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lah_Union_image using lah_Union_image_impl .
  definition "laa_Union_image == SetGA.it_Union_image ls_iterate ahs_empty aaa_union"
  lemmas laa_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iterate_impl ahs_empty_impl aaa_union_impl, folded laa_Union_image_def]
  interpretation laa: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_Union_image using laa_Union_image_impl .
  definition "rlili_Union_image == SetGA.it_Union_image rs_iterate lsi_empty lilili_union"
  lemmas rlili_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl lsi_empty_impl lilili_union_impl, folded rlili_Union_image_def]
  interpretation rlili: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_Union_image using rlili_Union_image_impl .
  definition "rlil_Union_image == SetGA.it_Union_image rs_iterate ls_empty lill_union"
  lemmas rlil_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ls_empty_impl lill_union_impl, folded rlil_Union_image_def]
  interpretation rlil: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rlil_Union_image using rlil_Union_image_impl .
  definition "rlir_Union_image == SetGA.it_Union_image rs_iterate rs_empty lirr_union"
  lemmas rlir_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl rs_empty_impl lirr_union_impl, folded rlir_Union_image_def]
  interpretation rlir: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rlir_Union_image using rlir_Union_image_impl .
  definition "rlih_Union_image == SetGA.it_Union_image rs_iterate hs_empty lihh_union"
  lemmas rlih_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl hs_empty_impl lihh_union_impl, folded rlih_Union_image_def]
  interpretation rlih: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rlih_Union_image using rlih_Union_image_impl .
  definition "rlia_Union_image == SetGA.it_Union_image rs_iterate ahs_empty liaa_union"
  lemmas rlia_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ahs_empty_impl liaa_union_impl, folded rlia_Union_image_def]
  interpretation rlia: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rlia_Union_image using rlia_Union_image_impl .
  definition "rlli_Union_image == SetGA.it_Union_image rs_iterate lsi_empty llili_union"
  lemmas rlli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl lsi_empty_impl llili_union_impl, folded rlli_Union_image_def]
  interpretation rlli: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rlli_Union_image using rlli_Union_image_impl .
  definition "rll_Union_image == SetGA.it_Union_image rs_iterate ls_empty lll_union"
  lemmas rll_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ls_empty_impl lll_union_impl, folded rll_Union_image_def]
  interpretation rll: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_Union_image using rll_Union_image_impl .
  definition "rlr_Union_image == SetGA.it_Union_image rs_iterate rs_empty lrr_union"
  lemmas rlr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl rs_empty_impl lrr_union_impl, folded rlr_Union_image_def]
  interpretation rlr: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_Union_image using rlr_Union_image_impl .
  definition "rlh_Union_image == SetGA.it_Union_image rs_iterate hs_empty lhh_union"
  lemmas rlh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl hs_empty_impl lhh_union_impl, folded rlh_Union_image_def]
  interpretation rlh: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_Union_image using rlh_Union_image_impl .
  definition "rla_Union_image == SetGA.it_Union_image rs_iterate ahs_empty laa_union"
  lemmas rla_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ahs_empty_impl laa_union_impl, folded rla_Union_image_def]
  interpretation rla: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rla_Union_image using rla_Union_image_impl .
  definition "rrli_Union_image == SetGA.it_Union_image rs_iterate lsi_empty rlili_union"
  lemmas rrli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl lsi_empty_impl rlili_union_impl, folded rrli_Union_image_def]
  interpretation rrli: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rrli_Union_image using rrli_Union_image_impl .
  definition "rrl_Union_image == SetGA.it_Union_image rs_iterate ls_empty rll_union"
  lemmas rrl_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ls_empty_impl rll_union_impl, folded rrl_Union_image_def]
  interpretation rrl: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_Union_image using rrl_Union_image_impl .
  definition "rrr_Union_image == SetGA.it_Union_image rs_iterate rs_empty rrr_union"
  lemmas rrr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl rs_empty_impl rrr_union_impl, folded rrr_Union_image_def]
  interpretation rrr: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_Union_image using rrr_Union_image_impl .
  definition "rrh_Union_image == SetGA.it_Union_image rs_iterate hs_empty rhh_union"
  lemmas rrh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl hs_empty_impl rhh_union_impl, folded rrh_Union_image_def]
  interpretation rrh: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_Union_image using rrh_Union_image_impl .
  definition "rra_Union_image == SetGA.it_Union_image rs_iterate ahs_empty raa_union"
  lemmas rra_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ahs_empty_impl raa_union_impl, folded rra_Union_image_def]
  interpretation rra: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rra_Union_image using rra_Union_image_impl .
  definition "rhli_Union_image == SetGA.it_Union_image rs_iterate lsi_empty hlili_union"
  lemmas rhli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl lsi_empty_impl hlili_union_impl, folded rhli_Union_image_def]
  interpretation rhli: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rhli_Union_image using rhli_Union_image_impl .
  definition "rhl_Union_image == SetGA.it_Union_image rs_iterate ls_empty hll_union"
  lemmas rhl_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ls_empty_impl hll_union_impl, folded rhl_Union_image_def]
  interpretation rhl: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_Union_image using rhl_Union_image_impl .
  definition "rhr_Union_image == SetGA.it_Union_image rs_iterate rs_empty hrr_union"
  lemmas rhr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl rs_empty_impl hrr_union_impl, folded rhr_Union_image_def]
  interpretation rhr: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_Union_image using rhr_Union_image_impl .
  definition "rhh_Union_image == SetGA.it_Union_image rs_iterate hs_empty hhh_union"
  lemmas rhh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl hs_empty_impl hhh_union_impl, folded rhh_Union_image_def]
  interpretation rhh: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_Union_image using rhh_Union_image_impl .
  definition "rha_Union_image == SetGA.it_Union_image rs_iterate ahs_empty haa_union"
  lemmas rha_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ahs_empty_impl haa_union_impl, folded rha_Union_image_def]
  interpretation rha: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rha_Union_image using rha_Union_image_impl .
  definition "rali_Union_image == SetGA.it_Union_image rs_iterate lsi_empty alili_union"
  lemmas rali_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl lsi_empty_impl alili_union_impl, folded rali_Union_image_def]
  interpretation rali: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rali_Union_image using rali_Union_image_impl .
  definition "ral_Union_image == SetGA.it_Union_image rs_iterate ls_empty all_union"
  lemmas ral_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ls_empty_impl all_union_impl, folded ral_Union_image_def]
  interpretation ral: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ral_Union_image using ral_Union_image_impl .
  definition "rar_Union_image == SetGA.it_Union_image rs_iterate rs_empty arr_union"
  lemmas rar_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl rs_empty_impl arr_union_impl, folded rar_Union_image_def]
  interpretation rar: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rar_Union_image using rar_Union_image_impl .
  definition "rah_Union_image == SetGA.it_Union_image rs_iterate hs_empty ahh_union"
  lemmas rah_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl hs_empty_impl ahh_union_impl, folded rah_Union_image_def]
  interpretation rah: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rah_Union_image using rah_Union_image_impl .
  definition "raa_Union_image == SetGA.it_Union_image rs_iterate ahs_empty aaa_union"
  lemmas raa_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iterate_impl ahs_empty_impl aaa_union_impl, folded raa_Union_image_def]
  interpretation raa: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_Union_image using raa_Union_image_impl .
  definition "hlili_Union_image == SetGA.it_Union_image hs_iterate lsi_empty lilili_union"
  lemmas hlili_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl lsi_empty_impl lilili_union_impl, folded hlili_Union_image_def]
  interpretation hlili: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_Union_image using hlili_Union_image_impl .
  definition "hlil_Union_image == SetGA.it_Union_image hs_iterate ls_empty lill_union"
  lemmas hlil_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ls_empty_impl lill_union_impl, folded hlil_Union_image_def]
  interpretation hlil: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hlil_Union_image using hlil_Union_image_impl .
  definition "hlir_Union_image == SetGA.it_Union_image hs_iterate rs_empty lirr_union"
  lemmas hlir_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl rs_empty_impl lirr_union_impl, folded hlir_Union_image_def]
  interpretation hlir: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hlir_Union_image using hlir_Union_image_impl .
  definition "hlih_Union_image == SetGA.it_Union_image hs_iterate hs_empty lihh_union"
  lemmas hlih_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl hs_empty_impl lihh_union_impl, folded hlih_Union_image_def]
  interpretation hlih: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hlih_Union_image using hlih_Union_image_impl .
  definition "hlia_Union_image == SetGA.it_Union_image hs_iterate ahs_empty liaa_union"
  lemmas hlia_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ahs_empty_impl liaa_union_impl, folded hlia_Union_image_def]
  interpretation hlia: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hlia_Union_image using hlia_Union_image_impl .
  definition "hlli_Union_image == SetGA.it_Union_image hs_iterate lsi_empty llili_union"
  lemmas hlli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl lsi_empty_impl llili_union_impl, folded hlli_Union_image_def]
  interpretation hlli: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hlli_Union_image using hlli_Union_image_impl .
  definition "hll_Union_image == SetGA.it_Union_image hs_iterate ls_empty lll_union"
  lemmas hll_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ls_empty_impl lll_union_impl, folded hll_Union_image_def]
  interpretation hll: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_Union_image using hll_Union_image_impl .
  definition "hlr_Union_image == SetGA.it_Union_image hs_iterate rs_empty lrr_union"
  lemmas hlr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl rs_empty_impl lrr_union_impl, folded hlr_Union_image_def]
  interpretation hlr: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_Union_image using hlr_Union_image_impl .
  definition "hlh_Union_image == SetGA.it_Union_image hs_iterate hs_empty lhh_union"
  lemmas hlh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl hs_empty_impl lhh_union_impl, folded hlh_Union_image_def]
  interpretation hlh: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_Union_image using hlh_Union_image_impl .
  definition "hla_Union_image == SetGA.it_Union_image hs_iterate ahs_empty laa_union"
  lemmas hla_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ahs_empty_impl laa_union_impl, folded hla_Union_image_def]
  interpretation hla: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hla_Union_image using hla_Union_image_impl .
  definition "hrli_Union_image == SetGA.it_Union_image hs_iterate lsi_empty rlili_union"
  lemmas hrli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl lsi_empty_impl rlili_union_impl, folded hrli_Union_image_def]
  interpretation hrli: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hrli_Union_image using hrli_Union_image_impl .
  definition "hrl_Union_image == SetGA.it_Union_image hs_iterate ls_empty rll_union"
  lemmas hrl_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ls_empty_impl rll_union_impl, folded hrl_Union_image_def]
  interpretation hrl: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_Union_image using hrl_Union_image_impl .
  definition "hrr_Union_image == SetGA.it_Union_image hs_iterate rs_empty rrr_union"
  lemmas hrr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl rs_empty_impl rrr_union_impl, folded hrr_Union_image_def]
  interpretation hrr: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_Union_image using hrr_Union_image_impl .
  definition "hrh_Union_image == SetGA.it_Union_image hs_iterate hs_empty rhh_union"
  lemmas hrh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl hs_empty_impl rhh_union_impl, folded hrh_Union_image_def]
  interpretation hrh: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_Union_image using hrh_Union_image_impl .
  definition "hra_Union_image == SetGA.it_Union_image hs_iterate ahs_empty raa_union"
  lemmas hra_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ahs_empty_impl raa_union_impl, folded hra_Union_image_def]
  interpretation hra: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hra_Union_image using hra_Union_image_impl .
  definition "hhli_Union_image == SetGA.it_Union_image hs_iterate lsi_empty hlili_union"
  lemmas hhli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl lsi_empty_impl hlili_union_impl, folded hhli_Union_image_def]
  interpretation hhli: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hhli_Union_image using hhli_Union_image_impl .
  definition "hhl_Union_image == SetGA.it_Union_image hs_iterate ls_empty hll_union"
  lemmas hhl_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ls_empty_impl hll_union_impl, folded hhl_Union_image_def]
  interpretation hhl: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_Union_image using hhl_Union_image_impl .
  definition "hhr_Union_image == SetGA.it_Union_image hs_iterate rs_empty hrr_union"
  lemmas hhr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl rs_empty_impl hrr_union_impl, folded hhr_Union_image_def]
  interpretation hhr: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_Union_image using hhr_Union_image_impl .
  definition "hhh_Union_image == SetGA.it_Union_image hs_iterate hs_empty hhh_union"
  lemmas hhh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl hs_empty_impl hhh_union_impl, folded hhh_Union_image_def]
  interpretation hhh: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_Union_image using hhh_Union_image_impl .
  definition "hha_Union_image == SetGA.it_Union_image hs_iterate ahs_empty haa_union"
  lemmas hha_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ahs_empty_impl haa_union_impl, folded hha_Union_image_def]
  interpretation hha: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hha_Union_image using hha_Union_image_impl .
  definition "hali_Union_image == SetGA.it_Union_image hs_iterate lsi_empty alili_union"
  lemmas hali_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl lsi_empty_impl alili_union_impl, folded hali_Union_image_def]
  interpretation hali: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hali_Union_image using hali_Union_image_impl .
  definition "hal_Union_image == SetGA.it_Union_image hs_iterate ls_empty all_union"
  lemmas hal_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ls_empty_impl all_union_impl, folded hal_Union_image_def]
  interpretation hal: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hal_Union_image using hal_Union_image_impl .
  definition "har_Union_image == SetGA.it_Union_image hs_iterate rs_empty arr_union"
  lemmas har_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl rs_empty_impl arr_union_impl, folded har_Union_image_def]
  interpretation har: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar har_Union_image using har_Union_image_impl .
  definition "hah_Union_image == SetGA.it_Union_image hs_iterate hs_empty ahh_union"
  lemmas hah_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl hs_empty_impl ahh_union_impl, folded hah_Union_image_def]
  interpretation hah: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hah_Union_image using hah_Union_image_impl .
  definition "haa_Union_image == SetGA.it_Union_image hs_iterate ahs_empty aaa_union"
  lemmas haa_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iterate_impl ahs_empty_impl aaa_union_impl, folded haa_Union_image_def]
  interpretation haa: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_Union_image using haa_Union_image_impl .
  definition "alili_Union_image == SetGA.it_Union_image ahs_iterate lsi_empty lilili_union"
  lemmas alili_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl lsi_empty_impl lilili_union_impl, folded alili_Union_image_def]
  interpretation alili: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_Union_image using alili_Union_image_impl .
  definition "alil_Union_image == SetGA.it_Union_image ahs_iterate ls_empty lill_union"
  lemmas alil_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ls_empty_impl lill_union_impl, folded alil_Union_image_def]
  interpretation alil: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar alil_Union_image using alil_Union_image_impl .
  definition "alir_Union_image == SetGA.it_Union_image ahs_iterate rs_empty lirr_union"
  lemmas alir_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl rs_empty_impl lirr_union_impl, folded alir_Union_image_def]
  interpretation alir: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar alir_Union_image using alir_Union_image_impl .
  definition "alih_Union_image == SetGA.it_Union_image ahs_iterate hs_empty lihh_union"
  lemmas alih_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl hs_empty_impl lihh_union_impl, folded alih_Union_image_def]
  interpretation alih: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar alih_Union_image using alih_Union_image_impl .
  definition "alia_Union_image == SetGA.it_Union_image ahs_iterate ahs_empty liaa_union"
  lemmas alia_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ahs_empty_impl liaa_union_impl, folded alia_Union_image_def]
  interpretation alia: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar alia_Union_image using alia_Union_image_impl .
  definition "alli_Union_image == SetGA.it_Union_image ahs_iterate lsi_empty llili_union"
  lemmas alli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl lsi_empty_impl llili_union_impl, folded alli_Union_image_def]
  interpretation alli: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar alli_Union_image using alli_Union_image_impl .
  definition "all_Union_image == SetGA.it_Union_image ahs_iterate ls_empty lll_union"
  lemmas all_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ls_empty_impl lll_union_impl, folded all_Union_image_def]
  interpretation all: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_Union_image using all_Union_image_impl .
  definition "alr_Union_image == SetGA.it_Union_image ahs_iterate rs_empty lrr_union"
  lemmas alr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl rs_empty_impl lrr_union_impl, folded alr_Union_image_def]
  interpretation alr: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar alr_Union_image using alr_Union_image_impl .
  definition "alh_Union_image == SetGA.it_Union_image ahs_iterate hs_empty lhh_union"
  lemmas alh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl hs_empty_impl lhh_union_impl, folded alh_Union_image_def]
  interpretation alh: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar alh_Union_image using alh_Union_image_impl .
  definition "ala_Union_image == SetGA.it_Union_image ahs_iterate ahs_empty laa_union"
  lemmas ala_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ahs_empty_impl laa_union_impl, folded ala_Union_image_def]
  interpretation ala: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ala_Union_image using ala_Union_image_impl .
  definition "arli_Union_image == SetGA.it_Union_image ahs_iterate lsi_empty rlili_union"
  lemmas arli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl lsi_empty_impl rlili_union_impl, folded arli_Union_image_def]
  interpretation arli: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar arli_Union_image using arli_Union_image_impl .
  definition "arl_Union_image == SetGA.it_Union_image ahs_iterate ls_empty rll_union"
  lemmas arl_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ls_empty_impl rll_union_impl, folded arl_Union_image_def]
  interpretation arl: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar arl_Union_image using arl_Union_image_impl .
  definition "arr_Union_image == SetGA.it_Union_image ahs_iterate rs_empty rrr_union"
  lemmas arr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl rs_empty_impl rrr_union_impl, folded arr_Union_image_def]
  interpretation arr: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_Union_image using arr_Union_image_impl .
  definition "arh_Union_image == SetGA.it_Union_image ahs_iterate hs_empty rhh_union"
  lemmas arh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl hs_empty_impl rhh_union_impl, folded arh_Union_image_def]
  interpretation arh: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar arh_Union_image using arh_Union_image_impl .
  definition "ara_Union_image == SetGA.it_Union_image ahs_iterate ahs_empty raa_union"
  lemmas ara_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ahs_empty_impl raa_union_impl, folded ara_Union_image_def]
  interpretation ara: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ara_Union_image using ara_Union_image_impl .
  definition "ahli_Union_image == SetGA.it_Union_image ahs_iterate lsi_empty hlili_union"
  lemmas ahli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl lsi_empty_impl hlili_union_impl, folded ahli_Union_image_def]
  interpretation ahli: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahli_Union_image using ahli_Union_image_impl .
  definition "ahl_Union_image == SetGA.it_Union_image ahs_iterate ls_empty hll_union"
  lemmas ahl_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ls_empty_impl hll_union_impl, folded ahl_Union_image_def]
  interpretation ahl: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahl_Union_image using ahl_Union_image_impl .
  definition "ahr_Union_image == SetGA.it_Union_image ahs_iterate rs_empty hrr_union"
  lemmas ahr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl rs_empty_impl hrr_union_impl, folded ahr_Union_image_def]
  interpretation ahr: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahr_Union_image using ahr_Union_image_impl .
  definition "ahh_Union_image == SetGA.it_Union_image ahs_iterate hs_empty hhh_union"
  lemmas ahh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl hs_empty_impl hhh_union_impl, folded ahh_Union_image_def]
  interpretation ahh: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_Union_image using ahh_Union_image_impl .
  definition "aha_Union_image == SetGA.it_Union_image ahs_iterate ahs_empty haa_union"
  lemmas aha_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ahs_empty_impl haa_union_impl, folded aha_Union_image_def]
  interpretation aha: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar aha_Union_image using aha_Union_image_impl .
  definition "aali_Union_image == SetGA.it_Union_image ahs_iterate lsi_empty alili_union"
  lemmas aali_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl lsi_empty_impl alili_union_impl, folded aali_Union_image_def]
  interpretation aali: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar aali_Union_image using aali_Union_image_impl .
  definition "aal_Union_image == SetGA.it_Union_image ahs_iterate ls_empty all_union"
  lemmas aal_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ls_empty_impl all_union_impl, folded aal_Union_image_def]
  interpretation aal: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar aal_Union_image using aal_Union_image_impl .
  definition "aar_Union_image == SetGA.it_Union_image ahs_iterate rs_empty arr_union"
  lemmas aar_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl rs_empty_impl arr_union_impl, folded aar_Union_image_def]
  interpretation aar: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar aar_Union_image using aar_Union_image_impl .
  definition "aah_Union_image == SetGA.it_Union_image ahs_iterate hs_empty ahh_union"
  lemmas aah_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl hs_empty_impl ahh_union_impl, folded aah_Union_image_def]
  interpretation aah: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar aah_Union_image using aah_Union_image_impl .
  definition "aaa_Union_image == SetGA.it_Union_image ahs_iterate ahs_empty aaa_union"
  lemmas aaa_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iterate_impl ahs_empty_impl aaa_union_impl, folded aaa_Union_image_def]
  interpretation aaa: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_Union_image using aaa_Union_image_impl .

  definition "lili_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel lsi_memb"
  lemmas lili_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl lsi_memb_impl, folded lili_disjoint_witness_def]
  interpretation lili: set_disjoint_witness lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_disjoint_witness using lili_disjoint_witness_impl .
  definition "lil_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel ls_memb"
  lemmas lil_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl ls_memb_impl, folded lil_disjoint_witness_def]
  interpretation lil: set_disjoint_witness lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_disjoint_witness using lil_disjoint_witness_impl .
  definition "lir_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel rs_memb"
  lemmas lir_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl rs_memb_impl, folded lir_disjoint_witness_def]
  interpretation lir: set_disjoint_witness lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_disjoint_witness using lir_disjoint_witness_impl .
  definition "lih_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel hs_memb"
  lemmas lih_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl hs_memb_impl, folded lih_disjoint_witness_def]
  interpretation lih: set_disjoint_witness lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_disjoint_witness using lih_disjoint_witness_impl .
  definition "lia_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel ahs_memb"
  lemmas lia_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl ahs_memb_impl, folded lia_disjoint_witness_def]
  interpretation lia: set_disjoint_witness lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_disjoint_witness using lia_disjoint_witness_impl .
  definition "lli_disjoint_witness == SetGA.sel_disjoint_witness ls_sel lsi_memb"
  lemmas lli_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl lsi_memb_impl, folded lli_disjoint_witness_def]
  interpretation lli: set_disjoint_witness ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_disjoint_witness using lli_disjoint_witness_impl .
  definition "ll_disjoint_witness == SetGA.sel_disjoint_witness ls_sel ls_memb"
  lemmas ll_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl ls_memb_impl, folded ll_disjoint_witness_def]
  interpretation ll: set_disjoint_witness ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_disjoint_witness using ll_disjoint_witness_impl .
  definition "lr_disjoint_witness == SetGA.sel_disjoint_witness ls_sel rs_memb"
  lemmas lr_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl rs_memb_impl, folded lr_disjoint_witness_def]
  interpretation lr: set_disjoint_witness ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_disjoint_witness using lr_disjoint_witness_impl .
  definition "lh_disjoint_witness == SetGA.sel_disjoint_witness ls_sel hs_memb"
  lemmas lh_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl hs_memb_impl, folded lh_disjoint_witness_def]
  interpretation lh: set_disjoint_witness ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_disjoint_witness using lh_disjoint_witness_impl .
  definition "la_disjoint_witness == SetGA.sel_disjoint_witness ls_sel ahs_memb"
  lemmas la_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl ahs_memb_impl, folded la_disjoint_witness_def]
  interpretation la: set_disjoint_witness ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_disjoint_witness using la_disjoint_witness_impl .
  definition "rli_disjoint_witness == SetGA.sel_disjoint_witness rs_sel lsi_memb"
  lemmas rli_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl lsi_memb_impl, folded rli_disjoint_witness_def]
  interpretation rli: set_disjoint_witness rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_disjoint_witness using rli_disjoint_witness_impl .
  definition "rl_disjoint_witness == SetGA.sel_disjoint_witness rs_sel ls_memb"
  lemmas rl_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl ls_memb_impl, folded rl_disjoint_witness_def]
  interpretation rl: set_disjoint_witness rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_disjoint_witness using rl_disjoint_witness_impl .
  definition "rr_disjoint_witness == SetGA.sel_disjoint_witness rs_sel rs_memb"
  lemmas rr_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl rs_memb_impl, folded rr_disjoint_witness_def]
  interpretation rr: set_disjoint_witness rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_disjoint_witness using rr_disjoint_witness_impl .
  definition "rh_disjoint_witness == SetGA.sel_disjoint_witness rs_sel hs_memb"
  lemmas rh_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl hs_memb_impl, folded rh_disjoint_witness_def]
  interpretation rh: set_disjoint_witness rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_disjoint_witness using rh_disjoint_witness_impl .
  definition "ra_disjoint_witness == SetGA.sel_disjoint_witness rs_sel ahs_memb"
  lemmas ra_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl ahs_memb_impl, folded ra_disjoint_witness_def]
  interpretation ra: set_disjoint_witness rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_disjoint_witness using ra_disjoint_witness_impl .
  definition "hli_disjoint_witness == SetGA.sel_disjoint_witness hs_sel lsi_memb"
  lemmas hli_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl lsi_memb_impl, folded hli_disjoint_witness_def]
  interpretation hli: set_disjoint_witness hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_disjoint_witness using hli_disjoint_witness_impl .
  definition "hl_disjoint_witness == SetGA.sel_disjoint_witness hs_sel ls_memb"
  lemmas hl_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl ls_memb_impl, folded hl_disjoint_witness_def]
  interpretation hl: set_disjoint_witness hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_disjoint_witness using hl_disjoint_witness_impl .
  definition "hr_disjoint_witness == SetGA.sel_disjoint_witness hs_sel rs_memb"
  lemmas hr_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl rs_memb_impl, folded hr_disjoint_witness_def]
  interpretation hr: set_disjoint_witness hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_disjoint_witness using hr_disjoint_witness_impl .
  definition "hh_disjoint_witness == SetGA.sel_disjoint_witness hs_sel hs_memb"
  lemmas hh_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl hs_memb_impl, folded hh_disjoint_witness_def]
  interpretation hh: set_disjoint_witness hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_disjoint_witness using hh_disjoint_witness_impl .
  definition "ha_disjoint_witness == SetGA.sel_disjoint_witness hs_sel ahs_memb"
  lemmas ha_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl ahs_memb_impl, folded ha_disjoint_witness_def]
  interpretation ha: set_disjoint_witness hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_disjoint_witness using ha_disjoint_witness_impl .
  definition "ali_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel lsi_memb"
  lemmas ali_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl lsi_memb_impl, folded ali_disjoint_witness_def]
  interpretation ali: set_disjoint_witness ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_disjoint_witness using ali_disjoint_witness_impl .
  definition "al_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel ls_memb"
  lemmas al_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl ls_memb_impl, folded al_disjoint_witness_def]
  interpretation al: set_disjoint_witness ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_disjoint_witness using al_disjoint_witness_impl .
  definition "ar_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel rs_memb"
  lemmas ar_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl rs_memb_impl, folded ar_disjoint_witness_def]
  interpretation ar: set_disjoint_witness ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_disjoint_witness using ar_disjoint_witness_impl .
  definition "ah_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel hs_memb"
  lemmas ah_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl hs_memb_impl, folded ah_disjoint_witness_def]
  interpretation ah: set_disjoint_witness ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_disjoint_witness using ah_disjoint_witness_impl .
  definition "aa_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel ahs_memb"
  lemmas aa_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl ahs_memb_impl, folded aa_disjoint_witness_def]
  interpretation aa: set_disjoint_witness ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_disjoint_witness using aa_disjoint_witness_impl .

  definition "lili_disjoint == SetGA.ball_disjoint lsi_ball lsi_memb"
  lemmas lili_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl lsi_memb_impl, folded lili_disjoint_def]
  interpretation lili: set_disjoint lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_disjoint using lili_disjoint_impl .
  definition "lil_disjoint == SetGA.ball_disjoint lsi_ball ls_memb"
  lemmas lil_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl ls_memb_impl, folded lil_disjoint_def]
  interpretation lil: set_disjoint lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_disjoint using lil_disjoint_impl .
  definition "lir_disjoint == SetGA.ball_disjoint lsi_ball rs_memb"
  lemmas lir_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl rs_memb_impl, folded lir_disjoint_def]
  interpretation lir: set_disjoint lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_disjoint using lir_disjoint_impl .
  definition "lih_disjoint == SetGA.ball_disjoint lsi_ball hs_memb"
  lemmas lih_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl hs_memb_impl, folded lih_disjoint_def]
  interpretation lih: set_disjoint lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_disjoint using lih_disjoint_impl .
  definition "lia_disjoint == SetGA.ball_disjoint lsi_ball ahs_memb"
  lemmas lia_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl ahs_memb_impl, folded lia_disjoint_def]
  interpretation lia: set_disjoint lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_disjoint using lia_disjoint_impl .
  definition "lli_disjoint == SetGA.ball_disjoint ls_ball lsi_memb"
  lemmas lli_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl lsi_memb_impl, folded lli_disjoint_def]
  interpretation lli: set_disjoint ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_disjoint using lli_disjoint_impl .
  definition "ll_disjoint == SetGA.ball_disjoint ls_ball ls_memb"
  lemmas ll_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl ls_memb_impl, folded ll_disjoint_def]
  interpretation ll: set_disjoint ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_disjoint using ll_disjoint_impl .
  definition "lr_disjoint == SetGA.ball_disjoint ls_ball rs_memb"
  lemmas lr_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl rs_memb_impl, folded lr_disjoint_def]
  interpretation lr: set_disjoint ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_disjoint using lr_disjoint_impl .
  definition "lh_disjoint == SetGA.ball_disjoint ls_ball hs_memb"
  lemmas lh_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl hs_memb_impl, folded lh_disjoint_def]
  interpretation lh: set_disjoint ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_disjoint using lh_disjoint_impl .
  definition "la_disjoint == SetGA.ball_disjoint ls_ball ahs_memb"
  lemmas la_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl ahs_memb_impl, folded la_disjoint_def]
  interpretation la: set_disjoint ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_disjoint using la_disjoint_impl .
  definition "rli_disjoint == SetGA.ball_disjoint rs_ball lsi_memb"
  lemmas rli_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl lsi_memb_impl, folded rli_disjoint_def]
  interpretation rli: set_disjoint rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_disjoint using rli_disjoint_impl .
  definition "rl_disjoint == SetGA.ball_disjoint rs_ball ls_memb"
  lemmas rl_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl ls_memb_impl, folded rl_disjoint_def]
  interpretation rl: set_disjoint rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_disjoint using rl_disjoint_impl .
  definition "rr_disjoint == SetGA.ball_disjoint rs_ball rs_memb"
  lemmas rr_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl rs_memb_impl, folded rr_disjoint_def]
  interpretation rr: set_disjoint rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_disjoint using rr_disjoint_impl .
  definition "rh_disjoint == SetGA.ball_disjoint rs_ball hs_memb"
  lemmas rh_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl hs_memb_impl, folded rh_disjoint_def]
  interpretation rh: set_disjoint rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_disjoint using rh_disjoint_impl .
  definition "ra_disjoint == SetGA.ball_disjoint rs_ball ahs_memb"
  lemmas ra_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl ahs_memb_impl, folded ra_disjoint_def]
  interpretation ra: set_disjoint rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_disjoint using ra_disjoint_impl .
  definition "hli_disjoint == SetGA.ball_disjoint hs_ball lsi_memb"
  lemmas hli_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl lsi_memb_impl, folded hli_disjoint_def]
  interpretation hli: set_disjoint hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_disjoint using hli_disjoint_impl .
  definition "hl_disjoint == SetGA.ball_disjoint hs_ball ls_memb"
  lemmas hl_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl ls_memb_impl, folded hl_disjoint_def]
  interpretation hl: set_disjoint hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_disjoint using hl_disjoint_impl .
  definition "hr_disjoint == SetGA.ball_disjoint hs_ball rs_memb"
  lemmas hr_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl rs_memb_impl, folded hr_disjoint_def]
  interpretation hr: set_disjoint hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_disjoint using hr_disjoint_impl .
  definition "hh_disjoint == SetGA.ball_disjoint hs_ball hs_memb"
  lemmas hh_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl hs_memb_impl, folded hh_disjoint_def]
  interpretation hh: set_disjoint hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_disjoint using hh_disjoint_impl .
  definition "ha_disjoint == SetGA.ball_disjoint hs_ball ahs_memb"
  lemmas ha_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl ahs_memb_impl, folded ha_disjoint_def]
  interpretation ha: set_disjoint hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_disjoint using ha_disjoint_impl .
  definition "ali_disjoint == SetGA.ball_disjoint ahs_ball lsi_memb"
  lemmas ali_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl lsi_memb_impl, folded ali_disjoint_def]
  interpretation ali: set_disjoint ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_disjoint using ali_disjoint_impl .
  definition "al_disjoint == SetGA.ball_disjoint ahs_ball ls_memb"
  lemmas al_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl ls_memb_impl, folded al_disjoint_def]
  interpretation al: set_disjoint ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_disjoint using al_disjoint_impl .
  definition "ar_disjoint == SetGA.ball_disjoint ahs_ball rs_memb"
  lemmas ar_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl rs_memb_impl, folded ar_disjoint_def]
  interpretation ar: set_disjoint ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_disjoint using ar_disjoint_impl .
  definition "ah_disjoint == SetGA.ball_disjoint ahs_ball hs_memb"
  lemmas ah_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl hs_memb_impl, folded ah_disjoint_def]
  interpretation ah: set_disjoint ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_disjoint using ah_disjoint_impl .
  definition "aa_disjoint == SetGA.ball_disjoint ahs_ball ahs_memb"
  lemmas aa_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl ahs_memb_impl, folded aa_disjoint_def]
  interpretation aa: set_disjoint ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_disjoint using aa_disjoint_impl .

  definition "lilili_image_filter_cp == SetGA.image_filter_cp lsi_iterate lsi_iterate lsi_empty lsi_ins"
  lemmas lilili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded lilili_image_filter_cp_def]
  definition "lilil_image_filter_cp == SetGA.image_filter_cp lsi_iterate lsi_iterate ls_empty ls_ins"
  lemmas lilil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_impl, folded lilil_image_filter_cp_def]
  definition "lilir_image_filter_cp == SetGA.image_filter_cp lsi_iterate lsi_iterate rs_empty rs_ins"
  lemmas lilir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_impl, folded lilir_image_filter_cp_def]
  definition "lilih_image_filter_cp == SetGA.image_filter_cp lsi_iterate lsi_iterate hs_empty hs_ins"
  lemmas lilih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_impl, folded lilih_image_filter_cp_def]
  definition "lilia_image_filter_cp == SetGA.image_filter_cp lsi_iterate lsi_iterate ahs_empty ahs_ins"
  lemmas lilia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded lilia_image_filter_cp_def]
  definition "lilli_image_filter_cp == SetGA.image_filter_cp lsi_iterate ls_iterate lsi_empty lsi_ins"
  lemmas lilli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded lilli_image_filter_cp_def]
  definition "lill_image_filter_cp == SetGA.image_filter_cp lsi_iterate ls_iterate ls_empty ls_ins"
  lemmas lill_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded lill_image_filter_cp_def]
  definition "lilr_image_filter_cp == SetGA.image_filter_cp lsi_iterate ls_iterate rs_empty rs_ins"
  lemmas lilr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded lilr_image_filter_cp_def]
  definition "lilh_image_filter_cp == SetGA.image_filter_cp lsi_iterate ls_iterate hs_empty hs_ins"
  lemmas lilh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded lilh_image_filter_cp_def]
  definition "lila_image_filter_cp == SetGA.image_filter_cp lsi_iterate ls_iterate ahs_empty ahs_ins"
  lemmas lila_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded lila_image_filter_cp_def]
  definition "lirli_image_filter_cp == SetGA.image_filter_cp lsi_iterate rs_iterate lsi_empty lsi_ins"
  lemmas lirli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded lirli_image_filter_cp_def]
  definition "lirl_image_filter_cp == SetGA.image_filter_cp lsi_iterate rs_iterate ls_empty ls_ins"
  lemmas lirl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded lirl_image_filter_cp_def]
  definition "lirr_image_filter_cp == SetGA.image_filter_cp lsi_iterate rs_iterate rs_empty rs_ins"
  lemmas lirr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded lirr_image_filter_cp_def]
  definition "lirh_image_filter_cp == SetGA.image_filter_cp lsi_iterate rs_iterate hs_empty hs_ins"
  lemmas lirh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded lirh_image_filter_cp_def]
  definition "lira_image_filter_cp == SetGA.image_filter_cp lsi_iterate rs_iterate ahs_empty ahs_ins"
  lemmas lira_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded lira_image_filter_cp_def]
  definition "lihli_image_filter_cp == SetGA.image_filter_cp lsi_iterate hs_iterate lsi_empty lsi_ins"
  lemmas lihli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded lihli_image_filter_cp_def]
  definition "lihl_image_filter_cp == SetGA.image_filter_cp lsi_iterate hs_iterate ls_empty ls_ins"
  lemmas lihl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded lihl_image_filter_cp_def]
  definition "lihr_image_filter_cp == SetGA.image_filter_cp lsi_iterate hs_iterate rs_empty rs_ins"
  lemmas lihr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded lihr_image_filter_cp_def]
  definition "lihh_image_filter_cp == SetGA.image_filter_cp lsi_iterate hs_iterate hs_empty hs_ins"
  lemmas lihh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded lihh_image_filter_cp_def]
  definition "liha_image_filter_cp == SetGA.image_filter_cp lsi_iterate hs_iterate ahs_empty ahs_ins"
  lemmas liha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded liha_image_filter_cp_def]
  definition "liali_image_filter_cp == SetGA.image_filter_cp lsi_iterate ahs_iterate lsi_empty lsi_ins"
  lemmas liali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded liali_image_filter_cp_def]
  definition "lial_image_filter_cp == SetGA.image_filter_cp lsi_iterate ahs_iterate ls_empty ls_ins"
  lemmas lial_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_impl, folded lial_image_filter_cp_def]
  definition "liar_image_filter_cp == SetGA.image_filter_cp lsi_iterate ahs_iterate rs_empty rs_ins"
  lemmas liar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_impl, folded liar_image_filter_cp_def]
  definition "liah_image_filter_cp == SetGA.image_filter_cp lsi_iterate ahs_iterate hs_empty hs_ins"
  lemmas liah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_impl, folded liah_image_filter_cp_def]
  definition "liaa_image_filter_cp == SetGA.image_filter_cp lsi_iterate ahs_iterate ahs_empty ahs_ins"
  lemmas liaa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded liaa_image_filter_cp_def]
  definition "llili_image_filter_cp == SetGA.image_filter_cp ls_iterate lsi_iterate lsi_empty lsi_ins"
  lemmas llili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded llili_image_filter_cp_def]
  definition "llil_image_filter_cp == SetGA.image_filter_cp ls_iterate lsi_iterate ls_empty ls_ins"
  lemmas llil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_impl, folded llil_image_filter_cp_def]
  definition "llir_image_filter_cp == SetGA.image_filter_cp ls_iterate lsi_iterate rs_empty rs_ins"
  lemmas llir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_impl, folded llir_image_filter_cp_def]
  definition "llih_image_filter_cp == SetGA.image_filter_cp ls_iterate lsi_iterate hs_empty hs_ins"
  lemmas llih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_impl, folded llih_image_filter_cp_def]
  definition "llia_image_filter_cp == SetGA.image_filter_cp ls_iterate lsi_iterate ahs_empty ahs_ins"
  lemmas llia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded llia_image_filter_cp_def]
  definition "llli_image_filter_cp == SetGA.image_filter_cp ls_iterate ls_iterate lsi_empty lsi_ins"
  lemmas llli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded llli_image_filter_cp_def]
  definition "lll_image_filter_cp == SetGA.image_filter_cp ls_iterate ls_iterate ls_empty ls_ins"
  lemmas lll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded lll_image_filter_cp_def]
  definition "llr_image_filter_cp == SetGA.image_filter_cp ls_iterate ls_iterate rs_empty rs_ins"
  lemmas llr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded llr_image_filter_cp_def]
  definition "llh_image_filter_cp == SetGA.image_filter_cp ls_iterate ls_iterate hs_empty hs_ins"
  lemmas llh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded llh_image_filter_cp_def]
  definition "lla_image_filter_cp == SetGA.image_filter_cp ls_iterate ls_iterate ahs_empty ahs_ins"
  lemmas lla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded lla_image_filter_cp_def]
  definition "lrli_image_filter_cp == SetGA.image_filter_cp ls_iterate rs_iterate lsi_empty lsi_ins"
  lemmas lrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded lrli_image_filter_cp_def]
  definition "lrl_image_filter_cp == SetGA.image_filter_cp ls_iterate rs_iterate ls_empty ls_ins"
  lemmas lrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded lrl_image_filter_cp_def]
  definition "lrr_image_filter_cp == SetGA.image_filter_cp ls_iterate rs_iterate rs_empty rs_ins"
  lemmas lrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded lrr_image_filter_cp_def]
  definition "lrh_image_filter_cp == SetGA.image_filter_cp ls_iterate rs_iterate hs_empty hs_ins"
  lemmas lrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded lrh_image_filter_cp_def]
  definition "lra_image_filter_cp == SetGA.image_filter_cp ls_iterate rs_iterate ahs_empty ahs_ins"
  lemmas lra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded lra_image_filter_cp_def]
  definition "lhli_image_filter_cp == SetGA.image_filter_cp ls_iterate hs_iterate lsi_empty lsi_ins"
  lemmas lhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded lhli_image_filter_cp_def]
  definition "lhl_image_filter_cp == SetGA.image_filter_cp ls_iterate hs_iterate ls_empty ls_ins"
  lemmas lhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded lhl_image_filter_cp_def]
  definition "lhr_image_filter_cp == SetGA.image_filter_cp ls_iterate hs_iterate rs_empty rs_ins"
  lemmas lhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded lhr_image_filter_cp_def]
  definition "lhh_image_filter_cp == SetGA.image_filter_cp ls_iterate hs_iterate hs_empty hs_ins"
  lemmas lhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded lhh_image_filter_cp_def]
  definition "lha_image_filter_cp == SetGA.image_filter_cp ls_iterate hs_iterate ahs_empty ahs_ins"
  lemmas lha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded lha_image_filter_cp_def]
  definition "lali_image_filter_cp == SetGA.image_filter_cp ls_iterate ahs_iterate lsi_empty lsi_ins"
  lemmas lali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded lali_image_filter_cp_def]
  definition "lal_image_filter_cp == SetGA.image_filter_cp ls_iterate ahs_iterate ls_empty ls_ins"
  lemmas lal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_impl, folded lal_image_filter_cp_def]
  definition "lar_image_filter_cp == SetGA.image_filter_cp ls_iterate ahs_iterate rs_empty rs_ins"
  lemmas lar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_impl, folded lar_image_filter_cp_def]
  definition "lah_image_filter_cp == SetGA.image_filter_cp ls_iterate ahs_iterate hs_empty hs_ins"
  lemmas lah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_impl, folded lah_image_filter_cp_def]
  definition "laa_image_filter_cp == SetGA.image_filter_cp ls_iterate ahs_iterate ahs_empty ahs_ins"
  lemmas laa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded laa_image_filter_cp_def]
  definition "rlili_image_filter_cp == SetGA.image_filter_cp rs_iterate lsi_iterate lsi_empty lsi_ins"
  lemmas rlili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded rlili_image_filter_cp_def]
  definition "rlil_image_filter_cp == SetGA.image_filter_cp rs_iterate lsi_iterate ls_empty ls_ins"
  lemmas rlil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_impl, folded rlil_image_filter_cp_def]
  definition "rlir_image_filter_cp == SetGA.image_filter_cp rs_iterate lsi_iterate rs_empty rs_ins"
  lemmas rlir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_impl, folded rlir_image_filter_cp_def]
  definition "rlih_image_filter_cp == SetGA.image_filter_cp rs_iterate lsi_iterate hs_empty hs_ins"
  lemmas rlih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_impl, folded rlih_image_filter_cp_def]
  definition "rlia_image_filter_cp == SetGA.image_filter_cp rs_iterate lsi_iterate ahs_empty ahs_ins"
  lemmas rlia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded rlia_image_filter_cp_def]
  definition "rlli_image_filter_cp == SetGA.image_filter_cp rs_iterate ls_iterate lsi_empty lsi_ins"
  lemmas rlli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded rlli_image_filter_cp_def]
  definition "rll_image_filter_cp == SetGA.image_filter_cp rs_iterate ls_iterate ls_empty ls_ins"
  lemmas rll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded rll_image_filter_cp_def]
  definition "rlr_image_filter_cp == SetGA.image_filter_cp rs_iterate ls_iterate rs_empty rs_ins"
  lemmas rlr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded rlr_image_filter_cp_def]
  definition "rlh_image_filter_cp == SetGA.image_filter_cp rs_iterate ls_iterate hs_empty hs_ins"
  lemmas rlh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded rlh_image_filter_cp_def]
  definition "rla_image_filter_cp == SetGA.image_filter_cp rs_iterate ls_iterate ahs_empty ahs_ins"
  lemmas rla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded rla_image_filter_cp_def]
  definition "rrli_image_filter_cp == SetGA.image_filter_cp rs_iterate rs_iterate lsi_empty lsi_ins"
  lemmas rrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded rrli_image_filter_cp_def]
  definition "rrl_image_filter_cp == SetGA.image_filter_cp rs_iterate rs_iterate ls_empty ls_ins"
  lemmas rrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded rrl_image_filter_cp_def]
  definition "rrr_image_filter_cp == SetGA.image_filter_cp rs_iterate rs_iterate rs_empty rs_ins"
  lemmas rrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded rrr_image_filter_cp_def]
  definition "rrh_image_filter_cp == SetGA.image_filter_cp rs_iterate rs_iterate hs_empty hs_ins"
  lemmas rrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded rrh_image_filter_cp_def]
  definition "rra_image_filter_cp == SetGA.image_filter_cp rs_iterate rs_iterate ahs_empty ahs_ins"
  lemmas rra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded rra_image_filter_cp_def]
  definition "rhli_image_filter_cp == SetGA.image_filter_cp rs_iterate hs_iterate lsi_empty lsi_ins"
  lemmas rhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded rhli_image_filter_cp_def]
  definition "rhl_image_filter_cp == SetGA.image_filter_cp rs_iterate hs_iterate ls_empty ls_ins"
  lemmas rhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded rhl_image_filter_cp_def]
  definition "rhr_image_filter_cp == SetGA.image_filter_cp rs_iterate hs_iterate rs_empty rs_ins"
  lemmas rhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded rhr_image_filter_cp_def]
  definition "rhh_image_filter_cp == SetGA.image_filter_cp rs_iterate hs_iterate hs_empty hs_ins"
  lemmas rhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded rhh_image_filter_cp_def]
  definition "rha_image_filter_cp == SetGA.image_filter_cp rs_iterate hs_iterate ahs_empty ahs_ins"
  lemmas rha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded rha_image_filter_cp_def]
  definition "rali_image_filter_cp == SetGA.image_filter_cp rs_iterate ahs_iterate lsi_empty lsi_ins"
  lemmas rali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded rali_image_filter_cp_def]
  definition "ral_image_filter_cp == SetGA.image_filter_cp rs_iterate ahs_iterate ls_empty ls_ins"
  lemmas ral_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_impl, folded ral_image_filter_cp_def]
  definition "rar_image_filter_cp == SetGA.image_filter_cp rs_iterate ahs_iterate rs_empty rs_ins"
  lemmas rar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_impl, folded rar_image_filter_cp_def]
  definition "rah_image_filter_cp == SetGA.image_filter_cp rs_iterate ahs_iterate hs_empty hs_ins"
  lemmas rah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_impl, folded rah_image_filter_cp_def]
  definition "raa_image_filter_cp == SetGA.image_filter_cp rs_iterate ahs_iterate ahs_empty ahs_ins"
  lemmas raa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded raa_image_filter_cp_def]
  definition "hlili_image_filter_cp == SetGA.image_filter_cp hs_iterate lsi_iterate lsi_empty lsi_ins"
  lemmas hlili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded hlili_image_filter_cp_def]
  definition "hlil_image_filter_cp == SetGA.image_filter_cp hs_iterate lsi_iterate ls_empty ls_ins"
  lemmas hlil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_impl, folded hlil_image_filter_cp_def]
  definition "hlir_image_filter_cp == SetGA.image_filter_cp hs_iterate lsi_iterate rs_empty rs_ins"
  lemmas hlir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_impl, folded hlir_image_filter_cp_def]
  definition "hlih_image_filter_cp == SetGA.image_filter_cp hs_iterate lsi_iterate hs_empty hs_ins"
  lemmas hlih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_impl, folded hlih_image_filter_cp_def]
  definition "hlia_image_filter_cp == SetGA.image_filter_cp hs_iterate lsi_iterate ahs_empty ahs_ins"
  lemmas hlia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded hlia_image_filter_cp_def]
  definition "hlli_image_filter_cp == SetGA.image_filter_cp hs_iterate ls_iterate lsi_empty lsi_ins"
  lemmas hlli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded hlli_image_filter_cp_def]
  definition "hll_image_filter_cp == SetGA.image_filter_cp hs_iterate ls_iterate ls_empty ls_ins"
  lemmas hll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded hll_image_filter_cp_def]
  definition "hlr_image_filter_cp == SetGA.image_filter_cp hs_iterate ls_iterate rs_empty rs_ins"
  lemmas hlr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded hlr_image_filter_cp_def]
  definition "hlh_image_filter_cp == SetGA.image_filter_cp hs_iterate ls_iterate hs_empty hs_ins"
  lemmas hlh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded hlh_image_filter_cp_def]
  definition "hla_image_filter_cp == SetGA.image_filter_cp hs_iterate ls_iterate ahs_empty ahs_ins"
  lemmas hla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded hla_image_filter_cp_def]
  definition "hrli_image_filter_cp == SetGA.image_filter_cp hs_iterate rs_iterate lsi_empty lsi_ins"
  lemmas hrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded hrli_image_filter_cp_def]
  definition "hrl_image_filter_cp == SetGA.image_filter_cp hs_iterate rs_iterate ls_empty ls_ins"
  lemmas hrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded hrl_image_filter_cp_def]
  definition "hrr_image_filter_cp == SetGA.image_filter_cp hs_iterate rs_iterate rs_empty rs_ins"
  lemmas hrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded hrr_image_filter_cp_def]
  definition "hrh_image_filter_cp == SetGA.image_filter_cp hs_iterate rs_iterate hs_empty hs_ins"
  lemmas hrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded hrh_image_filter_cp_def]
  definition "hra_image_filter_cp == SetGA.image_filter_cp hs_iterate rs_iterate ahs_empty ahs_ins"
  lemmas hra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded hra_image_filter_cp_def]
  definition "hhli_image_filter_cp == SetGA.image_filter_cp hs_iterate hs_iterate lsi_empty lsi_ins"
  lemmas hhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded hhli_image_filter_cp_def]
  definition "hhl_image_filter_cp == SetGA.image_filter_cp hs_iterate hs_iterate ls_empty ls_ins"
  lemmas hhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded hhl_image_filter_cp_def]
  definition "hhr_image_filter_cp == SetGA.image_filter_cp hs_iterate hs_iterate rs_empty rs_ins"
  lemmas hhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded hhr_image_filter_cp_def]
  definition "hhh_image_filter_cp == SetGA.image_filter_cp hs_iterate hs_iterate hs_empty hs_ins"
  lemmas hhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded hhh_image_filter_cp_def]
  definition "hha_image_filter_cp == SetGA.image_filter_cp hs_iterate hs_iterate ahs_empty ahs_ins"
  lemmas hha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded hha_image_filter_cp_def]
  definition "hali_image_filter_cp == SetGA.image_filter_cp hs_iterate ahs_iterate lsi_empty lsi_ins"
  lemmas hali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded hali_image_filter_cp_def]
  definition "hal_image_filter_cp == SetGA.image_filter_cp hs_iterate ahs_iterate ls_empty ls_ins"
  lemmas hal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_impl, folded hal_image_filter_cp_def]
  definition "har_image_filter_cp == SetGA.image_filter_cp hs_iterate ahs_iterate rs_empty rs_ins"
  lemmas har_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_impl, folded har_image_filter_cp_def]
  definition "hah_image_filter_cp == SetGA.image_filter_cp hs_iterate ahs_iterate hs_empty hs_ins"
  lemmas hah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_impl, folded hah_image_filter_cp_def]
  definition "haa_image_filter_cp == SetGA.image_filter_cp hs_iterate ahs_iterate ahs_empty ahs_ins"
  lemmas haa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded haa_image_filter_cp_def]
  definition "alili_image_filter_cp == SetGA.image_filter_cp ahs_iterate lsi_iterate lsi_empty lsi_ins"
  lemmas alili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_impl, folded alili_image_filter_cp_def]
  definition "alil_image_filter_cp == SetGA.image_filter_cp ahs_iterate lsi_iterate ls_empty ls_ins"
  lemmas alil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_impl, folded alil_image_filter_cp_def]
  definition "alir_image_filter_cp == SetGA.image_filter_cp ahs_iterate lsi_iterate rs_empty rs_ins"
  lemmas alir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_impl, folded alir_image_filter_cp_def]
  definition "alih_image_filter_cp == SetGA.image_filter_cp ahs_iterate lsi_iterate hs_empty hs_ins"
  lemmas alih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_impl, folded alih_image_filter_cp_def]
  definition "alia_image_filter_cp == SetGA.image_filter_cp ahs_iterate lsi_iterate ahs_empty ahs_ins"
  lemmas alia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_impl, folded alia_image_filter_cp_def]
  definition "alli_image_filter_cp == SetGA.image_filter_cp ahs_iterate ls_iterate lsi_empty lsi_ins"
  lemmas alli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_impl, folded alli_image_filter_cp_def]
  definition "all_image_filter_cp == SetGA.image_filter_cp ahs_iterate ls_iterate ls_empty ls_ins"
  lemmas all_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded all_image_filter_cp_def]
  definition "alr_image_filter_cp == SetGA.image_filter_cp ahs_iterate ls_iterate rs_empty rs_ins"
  lemmas alr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded alr_image_filter_cp_def]
  definition "alh_image_filter_cp == SetGA.image_filter_cp ahs_iterate ls_iterate hs_empty hs_ins"
  lemmas alh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded alh_image_filter_cp_def]
  definition "ala_image_filter_cp == SetGA.image_filter_cp ahs_iterate ls_iterate ahs_empty ahs_ins"
  lemmas ala_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_impl, folded ala_image_filter_cp_def]
  definition "arli_image_filter_cp == SetGA.image_filter_cp ahs_iterate rs_iterate lsi_empty lsi_ins"
  lemmas arli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_impl, folded arli_image_filter_cp_def]
  definition "arl_image_filter_cp == SetGA.image_filter_cp ahs_iterate rs_iterate ls_empty ls_ins"
  lemmas arl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded arl_image_filter_cp_def]
  definition "arr_image_filter_cp == SetGA.image_filter_cp ahs_iterate rs_iterate rs_empty rs_ins"
  lemmas arr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded arr_image_filter_cp_def]
  definition "arh_image_filter_cp == SetGA.image_filter_cp ahs_iterate rs_iterate hs_empty hs_ins"
  lemmas arh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded arh_image_filter_cp_def]
  definition "ara_image_filter_cp == SetGA.image_filter_cp ahs_iterate rs_iterate ahs_empty ahs_ins"
  lemmas ara_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_impl, folded ara_image_filter_cp_def]
  definition "ahli_image_filter_cp == SetGA.image_filter_cp ahs_iterate hs_iterate lsi_empty lsi_ins"
  lemmas ahli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_impl, folded ahli_image_filter_cp_def]
  definition "ahl_image_filter_cp == SetGA.image_filter_cp ahs_iterate hs_iterate ls_empty ls_ins"
  lemmas ahl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded ahl_image_filter_cp_def]
  definition "ahr_image_filter_cp == SetGA.image_filter_cp ahs_iterate hs_iterate rs_empty rs_ins"
  lemmas ahr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded ahr_image_filter_cp_def]
  definition "ahh_image_filter_cp == SetGA.image_filter_cp ahs_iterate hs_iterate hs_empty hs_ins"
  lemmas ahh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded ahh_image_filter_cp_def]
  definition "aha_image_filter_cp == SetGA.image_filter_cp ahs_iterate hs_iterate ahs_empty ahs_ins"
  lemmas aha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_impl, folded aha_image_filter_cp_def]
  definition "aali_image_filter_cp == SetGA.image_filter_cp ahs_iterate ahs_iterate lsi_empty lsi_ins"
  lemmas aali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_impl, folded aali_image_filter_cp_def]
  definition "aal_image_filter_cp == SetGA.image_filter_cp ahs_iterate ahs_iterate ls_empty ls_ins"
  lemmas aal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_impl, folded aal_image_filter_cp_def]
  definition "aar_image_filter_cp == SetGA.image_filter_cp ahs_iterate ahs_iterate rs_empty rs_ins"
  lemmas aar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_impl, folded aar_image_filter_cp_def]
  definition "aah_image_filter_cp == SetGA.image_filter_cp ahs_iterate ahs_iterate hs_empty hs_ins"
  lemmas aah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_impl, folded aah_image_filter_cp_def]
  definition "aaa_image_filter_cp == SetGA.image_filter_cp ahs_iterate ahs_iterate ahs_empty ahs_ins"
  lemmas aaa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_impl, folded aaa_image_filter_cp_def]

  definition "lilili_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas lilili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_inj_image_filter_cp_def]
  definition "lilil_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas lilil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lilil_inj_image_filter_cp_def]
  definition "lilir_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas lilir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lilir_inj_image_filter_cp_def]
  definition "lilih_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas lilih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lilih_inj_image_filter_cp_def]
  definition "lilia_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas lilia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_inj_image_filter_cp_def]
  definition "lilli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas lilli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_inj_image_filter_cp_def]
  definition "lill_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lill_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lill_inj_image_filter_cp_def]
  definition "lilr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas lilr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lilr_inj_image_filter_cp_def]
  definition "lilh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas lilh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lilh_inj_image_filter_cp_def]
  definition "lila_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas lila_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_inj_image_filter_cp_def]
  definition "lirli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas lirli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_inj_image_filter_cp_def]
  definition "lirl_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lirl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lirl_inj_image_filter_cp_def]
  definition "lirr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lirr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lirr_inj_image_filter_cp_def]
  definition "lirh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lirh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lirh_inj_image_filter_cp_def]
  definition "lira_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas lira_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_inj_image_filter_cp_def]
  definition "lihli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas lihli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_inj_image_filter_cp_def]
  definition "lihl_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lihl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lihl_inj_image_filter_cp_def]
  definition "lihr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lihr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lihr_inj_image_filter_cp_def]
  definition "lihh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lihh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lihh_inj_image_filter_cp_def]
  definition "liha_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas liha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_inj_image_filter_cp_def]
  definition "liali_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas liali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_inj_image_filter_cp_def]
  definition "lial_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas lial_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lial_inj_image_filter_cp_def]
  definition "liar_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas liar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded liar_inj_image_filter_cp_def]
  definition "liah_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas liah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded liah_inj_image_filter_cp_def]
  definition "liaa_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas liaa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_inj_image_filter_cp_def]
  definition "llili_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas llili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_inj_image_filter_cp_def]
  definition "llil_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas llil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded llil_inj_image_filter_cp_def]
  definition "llir_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas llir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llir_inj_image_filter_cp_def]
  definition "llih_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas llih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llih_inj_image_filter_cp_def]
  definition "llia_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas llia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_inj_image_filter_cp_def]
  definition "llli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas llli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_inj_image_filter_cp_def]
  definition "lll_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lll_inj_image_filter_cp_def]
  definition "llr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas llr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llr_inj_image_filter_cp_def]
  definition "llh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas llh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llh_inj_image_filter_cp_def]
  definition "lla_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas lla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_inj_image_filter_cp_def]
  definition "lrli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas lrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_inj_image_filter_cp_def]
  definition "lrl_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inj_image_filter_cp_def]
  definition "lrr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inj_image_filter_cp_def]
  definition "lrh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inj_image_filter_cp_def]
  definition "lra_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas lra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_inj_image_filter_cp_def]
  definition "lhli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas lhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_inj_image_filter_cp_def]
  definition "lhl_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inj_image_filter_cp_def]
  definition "lhr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inj_image_filter_cp_def]
  definition "lhh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inj_image_filter_cp_def]
  definition "lha_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas lha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_inj_image_filter_cp_def]
  definition "lali_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas lali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_inj_image_filter_cp_def]
  definition "lal_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas lal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lal_inj_image_filter_cp_def]
  definition "lar_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas lar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lar_inj_image_filter_cp_def]
  definition "lah_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas lah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lah_inj_image_filter_cp_def]
  definition "laa_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas laa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_inj_image_filter_cp_def]
  definition "rlili_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas rlili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_inj_image_filter_cp_def]
  definition "rlil_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas rlil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rlil_inj_image_filter_cp_def]
  definition "rlir_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas rlir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlir_inj_image_filter_cp_def]
  definition "rlih_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas rlih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlih_inj_image_filter_cp_def]
  definition "rlia_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas rlia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_inj_image_filter_cp_def]
  definition "rlli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas rlli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_inj_image_filter_cp_def]
  definition "rll_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas rll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rll_inj_image_filter_cp_def]
  definition "rlr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas rlr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inj_image_filter_cp_def]
  definition "rlh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas rlh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inj_image_filter_cp_def]
  definition "rla_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas rla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_inj_image_filter_cp_def]
  definition "rrli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas rrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_inj_image_filter_cp_def]
  definition "rrl_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas rrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inj_image_filter_cp_def]
  definition "rrr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas rrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inj_image_filter_cp_def]
  definition "rrh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas rrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inj_image_filter_cp_def]
  definition "rra_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas rra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_inj_image_filter_cp_def]
  definition "rhli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas rhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_inj_image_filter_cp_def]
  definition "rhl_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas rhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inj_image_filter_cp_def]
  definition "rhr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas rhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inj_image_filter_cp_def]
  definition "rhh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas rhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inj_image_filter_cp_def]
  definition "rha_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas rha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_inj_image_filter_cp_def]
  definition "rali_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas rali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_inj_image_filter_cp_def]
  definition "ral_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas ral_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ral_inj_image_filter_cp_def]
  definition "rar_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas rar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rar_inj_image_filter_cp_def]
  definition "rah_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas rah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rah_inj_image_filter_cp_def]
  definition "raa_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas raa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_inj_image_filter_cp_def]
  definition "hlili_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas hlili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_inj_image_filter_cp_def]
  definition "hlil_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas hlil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hlil_inj_image_filter_cp_def]
  definition "hlir_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas hlir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlir_inj_image_filter_cp_def]
  definition "hlih_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas hlih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlih_inj_image_filter_cp_def]
  definition "hlia_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas hlia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_inj_image_filter_cp_def]
  definition "hlli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas hlli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_inj_image_filter_cp_def]
  definition "hll_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas hll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hll_inj_image_filter_cp_def]
  definition "hlr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas hlr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inj_image_filter_cp_def]
  definition "hlh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas hlh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inj_image_filter_cp_def]
  definition "hla_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas hla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_inj_image_filter_cp_def]
  definition "hrli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas hrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_inj_image_filter_cp_def]
  definition "hrl_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas hrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inj_image_filter_cp_def]
  definition "hrr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas hrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inj_image_filter_cp_def]
  definition "hrh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas hrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inj_image_filter_cp_def]
  definition "hra_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas hra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_inj_image_filter_cp_def]
  definition "hhli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas hhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_inj_image_filter_cp_def]
  definition "hhl_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas hhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inj_image_filter_cp_def]
  definition "hhr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas hhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inj_image_filter_cp_def]
  definition "hhh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas hhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inj_image_filter_cp_def]
  definition "hha_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas hha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_inj_image_filter_cp_def]
  definition "hali_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas hali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_inj_image_filter_cp_def]
  definition "hal_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas hal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hal_inj_image_filter_cp_def]
  definition "har_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas har_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded har_inj_image_filter_cp_def]
  definition "hah_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas hah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hah_inj_image_filter_cp_def]
  definition "haa_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas haa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_inj_image_filter_cp_def]
  definition "alili_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas alili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_inj_image_filter_cp_def]
  definition "alil_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas alil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded alil_inj_image_filter_cp_def]
  definition "alir_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas alir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded alir_inj_image_filter_cp_def]
  definition "alih_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas alih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded alih_inj_image_filter_cp_def]
  definition "alia_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas alia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_inj_image_filter_cp_def]
  definition "alli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas alli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_inj_image_filter_cp_def]
  definition "all_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas all_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded all_inj_image_filter_cp_def]
  definition "alr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas alr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded alr_inj_image_filter_cp_def]
  definition "alh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas alh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded alh_inj_image_filter_cp_def]
  definition "ala_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas ala_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_inj_image_filter_cp_def]
  definition "arli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas arli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_inj_image_filter_cp_def]
  definition "arl_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas arl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded arl_inj_image_filter_cp_def]
  definition "arr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas arr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded arr_inj_image_filter_cp_def]
  definition "arh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas arh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded arh_inj_image_filter_cp_def]
  definition "ara_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas ara_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_inj_image_filter_cp_def]
  definition "ahli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas ahli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_inj_image_filter_cp_def]
  definition "ahl_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas ahl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ahl_inj_image_filter_cp_def]
  definition "ahr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas ahr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded ahr_inj_image_filter_cp_def]
  definition "ahh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas ahh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded ahh_inj_image_filter_cp_def]
  definition "aha_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas aha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_inj_image_filter_cp_def]
  definition "aali_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas aali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_inj_image_filter_cp_def]
  definition "aal_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas aal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded aal_inj_image_filter_cp_def]
  definition "aar_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas aar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded aar_inj_image_filter_cp_def]
  definition "aah_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas aah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded aah_inj_image_filter_cp_def]
  definition "aaa_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas aaa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_inj_image_filter_cp_def]

  definition "lilili_cart == SetGA.cart lsi_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas lilili_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_cart_def]
  definition "lilil_cart == SetGA.cart lsi_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas lilil_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lilil_cart_def]
  definition "lilir_cart == SetGA.cart lsi_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas lilir_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lilir_cart_def]
  definition "lilih_cart == SetGA.cart lsi_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas lilih_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lilih_cart_def]
  definition "lilia_cart == SetGA.cart lsi_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas lilia_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_cart_def]
  definition "lilli_cart == SetGA.cart lsi_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas lilli_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_cart_def]
  definition "lill_cart == SetGA.cart lsi_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lill_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lill_cart_def]
  definition "lilr_cart == SetGA.cart lsi_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas lilr_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lilr_cart_def]
  definition "lilh_cart == SetGA.cart lsi_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas lilh_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lilh_cart_def]
  definition "lila_cart == SetGA.cart lsi_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas lila_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_cart_def]
  definition "lirli_cart == SetGA.cart lsi_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas lirli_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_cart_def]
  definition "lirl_cart == SetGA.cart lsi_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lirl_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lirl_cart_def]
  definition "lirr_cart == SetGA.cart lsi_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lirr_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lirr_cart_def]
  definition "lirh_cart == SetGA.cart lsi_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lirh_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lirh_cart_def]
  definition "lira_cart == SetGA.cart lsi_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas lira_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_cart_def]
  definition "lihli_cart == SetGA.cart lsi_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas lihli_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_cart_def]
  definition "lihl_cart == SetGA.cart lsi_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lihl_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lihl_cart_def]
  definition "lihr_cart == SetGA.cart lsi_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lihr_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lihr_cart_def]
  definition "lihh_cart == SetGA.cart lsi_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lihh_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lihh_cart_def]
  definition "liha_cart == SetGA.cart lsi_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas liha_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_cart_def]
  definition "liali_cart == SetGA.cart lsi_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas liali_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_cart_def]
  definition "lial_cart == SetGA.cart lsi_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas lial_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lial_cart_def]
  definition "liar_cart == SetGA.cart lsi_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas liar_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded liar_cart_def]
  definition "liah_cart == SetGA.cart lsi_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas liah_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded liah_cart_def]
  definition "liaa_cart == SetGA.cart lsi_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas liaa_cart_correct = SetGA.cart_correct[OF lsi_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_cart_def]
  definition "llili_cart == SetGA.cart ls_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas llili_cart_correct = SetGA.cart_correct[OF ls_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_cart_def]
  definition "llil_cart == SetGA.cart ls_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas llil_cart_correct = SetGA.cart_correct[OF ls_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded llil_cart_def]
  definition "llir_cart == SetGA.cart ls_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas llir_cart_correct = SetGA.cart_correct[OF ls_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llir_cart_def]
  definition "llih_cart == SetGA.cart ls_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas llih_cart_correct = SetGA.cart_correct[OF ls_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llih_cart_def]
  definition "llia_cart == SetGA.cart ls_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas llia_cart_correct = SetGA.cart_correct[OF ls_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_cart_def]
  definition "llli_cart == SetGA.cart ls_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas llli_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_cart_def]
  definition "lll_cart == SetGA.cart ls_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lll_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lll_cart_def]
  definition "llr_cart == SetGA.cart ls_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas llr_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llr_cart_def]
  definition "llh_cart == SetGA.cart ls_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas llh_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llh_cart_def]
  definition "lla_cart == SetGA.cart ls_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas lla_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_cart_def]
  definition "lrli_cart == SetGA.cart ls_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas lrli_cart_correct = SetGA.cart_correct[OF ls_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_cart_def]
  definition "lrl_cart == SetGA.cart ls_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lrl_cart_correct = SetGA.cart_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lrl_cart_def]
  definition "lrr_cart == SetGA.cart ls_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lrr_cart_correct = SetGA.cart_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lrr_cart_def]
  definition "lrh_cart == SetGA.cart ls_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lrh_cart_correct = SetGA.cart_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lrh_cart_def]
  definition "lra_cart == SetGA.cart ls_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas lra_cart_correct = SetGA.cart_correct[OF ls_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_cart_def]
  definition "lhli_cart == SetGA.cart ls_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas lhli_cart_correct = SetGA.cart_correct[OF ls_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_cart_def]
  definition "lhl_cart == SetGA.cart ls_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lhl_cart_correct = SetGA.cart_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lhl_cart_def]
  definition "lhr_cart == SetGA.cart ls_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lhr_cart_correct = SetGA.cart_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lhr_cart_def]
  definition "lhh_cart == SetGA.cart ls_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lhh_cart_correct = SetGA.cart_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lhh_cart_def]
  definition "lha_cart == SetGA.cart ls_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas lha_cart_correct = SetGA.cart_correct[OF ls_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_cart_def]
  definition "lali_cart == SetGA.cart ls_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas lali_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_cart_def]
  definition "lal_cart == SetGA.cart ls_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas lal_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lal_cart_def]
  definition "lar_cart == SetGA.cart ls_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas lar_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lar_cart_def]
  definition "lah_cart == SetGA.cart ls_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas lah_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lah_cart_def]
  definition "laa_cart == SetGA.cart ls_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas laa_cart_correct = SetGA.cart_correct[OF ls_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_cart_def]
  definition "rlili_cart == SetGA.cart rs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas rlili_cart_correct = SetGA.cart_correct[OF rs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_cart_def]
  definition "rlil_cart == SetGA.cart rs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas rlil_cart_correct = SetGA.cart_correct[OF rs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rlil_cart_def]
  definition "rlir_cart == SetGA.cart rs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas rlir_cart_correct = SetGA.cart_correct[OF rs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlir_cart_def]
  definition "rlih_cart == SetGA.cart rs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas rlih_cart_correct = SetGA.cart_correct[OF rs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlih_cart_def]
  definition "rlia_cart == SetGA.cart rs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas rlia_cart_correct = SetGA.cart_correct[OF rs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_cart_def]
  definition "rlli_cart == SetGA.cart rs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas rlli_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_cart_def]
  definition "rll_cart == SetGA.cart rs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas rll_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rll_cart_def]
  definition "rlr_cart == SetGA.cart rs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas rlr_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlr_cart_def]
  definition "rlh_cart == SetGA.cart rs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas rlh_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlh_cart_def]
  definition "rla_cart == SetGA.cart rs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas rla_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_cart_def]
  definition "rrli_cart == SetGA.cart rs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas rrli_cart_correct = SetGA.cart_correct[OF rs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_cart_def]
  definition "rrl_cart == SetGA.cart rs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas rrl_cart_correct = SetGA.cart_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rrl_cart_def]
  definition "rrr_cart == SetGA.cart rs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas rrr_cart_correct = SetGA.cart_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rrr_cart_def]
  definition "rrh_cart == SetGA.cart rs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas rrh_cart_correct = SetGA.cart_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rrh_cart_def]
  definition "rra_cart == SetGA.cart rs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas rra_cart_correct = SetGA.cart_correct[OF rs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_cart_def]
  definition "rhli_cart == SetGA.cart rs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas rhli_cart_correct = SetGA.cart_correct[OF rs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_cart_def]
  definition "rhl_cart == SetGA.cart rs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas rhl_cart_correct = SetGA.cart_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rhl_cart_def]
  definition "rhr_cart == SetGA.cart rs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas rhr_cart_correct = SetGA.cart_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rhr_cart_def]
  definition "rhh_cart == SetGA.cart rs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas rhh_cart_correct = SetGA.cart_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rhh_cart_def]
  definition "rha_cart == SetGA.cart rs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas rha_cart_correct = SetGA.cart_correct[OF rs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_cart_def]
  definition "rali_cart == SetGA.cart rs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas rali_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_cart_def]
  definition "ral_cart == SetGA.cart rs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas ral_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ral_cart_def]
  definition "rar_cart == SetGA.cart rs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas rar_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rar_cart_def]
  definition "rah_cart == SetGA.cart rs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas rah_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rah_cart_def]
  definition "raa_cart == SetGA.cart rs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas raa_cart_correct = SetGA.cart_correct[OF rs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_cart_def]
  definition "hlili_cart == SetGA.cart hs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas hlili_cart_correct = SetGA.cart_correct[OF hs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_cart_def]
  definition "hlil_cart == SetGA.cart hs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas hlil_cart_correct = SetGA.cart_correct[OF hs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hlil_cart_def]
  definition "hlir_cart == SetGA.cart hs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas hlir_cart_correct = SetGA.cart_correct[OF hs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlir_cart_def]
  definition "hlih_cart == SetGA.cart hs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas hlih_cart_correct = SetGA.cart_correct[OF hs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlih_cart_def]
  definition "hlia_cart == SetGA.cart hs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas hlia_cart_correct = SetGA.cart_correct[OF hs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_cart_def]
  definition "hlli_cart == SetGA.cart hs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas hlli_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_cart_def]
  definition "hll_cart == SetGA.cart hs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas hll_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hll_cart_def]
  definition "hlr_cart == SetGA.cart hs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas hlr_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlr_cart_def]
  definition "hlh_cart == SetGA.cart hs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas hlh_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlh_cart_def]
  definition "hla_cart == SetGA.cart hs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas hla_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_cart_def]
  definition "hrli_cart == SetGA.cart hs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas hrli_cart_correct = SetGA.cart_correct[OF hs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_cart_def]
  definition "hrl_cart == SetGA.cart hs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas hrl_cart_correct = SetGA.cart_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hrl_cart_def]
  definition "hrr_cart == SetGA.cart hs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas hrr_cart_correct = SetGA.cart_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hrr_cart_def]
  definition "hrh_cart == SetGA.cart hs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas hrh_cart_correct = SetGA.cart_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hrh_cart_def]
  definition "hra_cart == SetGA.cart hs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas hra_cart_correct = SetGA.cart_correct[OF hs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_cart_def]
  definition "hhli_cart == SetGA.cart hs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas hhli_cart_correct = SetGA.cart_correct[OF hs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_cart_def]
  definition "hhl_cart == SetGA.cart hs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas hhl_cart_correct = SetGA.cart_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hhl_cart_def]
  definition "hhr_cart == SetGA.cart hs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas hhr_cart_correct = SetGA.cart_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hhr_cart_def]
  definition "hhh_cart == SetGA.cart hs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas hhh_cart_correct = SetGA.cart_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hhh_cart_def]
  definition "hha_cart == SetGA.cart hs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas hha_cart_correct = SetGA.cart_correct[OF hs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_cart_def]
  definition "hali_cart == SetGA.cart hs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas hali_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_cart_def]
  definition "hal_cart == SetGA.cart hs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas hal_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hal_cart_def]
  definition "har_cart == SetGA.cart hs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas har_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded har_cart_def]
  definition "hah_cart == SetGA.cart hs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas hah_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hah_cart_def]
  definition "haa_cart == SetGA.cart hs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas haa_cart_correct = SetGA.cart_correct[OF hs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_cart_def]
  definition "alili_cart == SetGA.cart ahs_iterate lsi_iterate lsi_empty lsi_ins_dj"
  lemmas alili_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl lsi_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_cart_def]
  definition "alil_cart == SetGA.cart ahs_iterate lsi_iterate ls_empty ls_ins_dj"
  lemmas alil_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl lsi_iterate_impl ls_empty_impl ls_ins_dj_impl, folded alil_cart_def]
  definition "alir_cart == SetGA.cart ahs_iterate lsi_iterate rs_empty rs_ins_dj"
  lemmas alir_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl lsi_iterate_impl rs_empty_impl rs_ins_dj_impl, folded alir_cart_def]
  definition "alih_cart == SetGA.cart ahs_iterate lsi_iterate hs_empty hs_ins_dj"
  lemmas alih_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl lsi_iterate_impl hs_empty_impl hs_ins_dj_impl, folded alih_cart_def]
  definition "alia_cart == SetGA.cart ahs_iterate lsi_iterate ahs_empty ahs_ins_dj"
  lemmas alia_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl lsi_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_cart_def]
  definition "alli_cart == SetGA.cart ahs_iterate ls_iterate lsi_empty lsi_ins_dj"
  lemmas alli_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ls_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_cart_def]
  definition "all_cart == SetGA.cart ahs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas all_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded all_cart_def]
  definition "alr_cart == SetGA.cart ahs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas alr_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded alr_cart_def]
  definition "alh_cart == SetGA.cart ahs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas alh_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded alh_cart_def]
  definition "ala_cart == SetGA.cart ahs_iterate ls_iterate ahs_empty ahs_ins_dj"
  lemmas ala_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ls_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_cart_def]
  definition "arli_cart == SetGA.cart ahs_iterate rs_iterate lsi_empty lsi_ins_dj"
  lemmas arli_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl rs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_cart_def]
  definition "arl_cart == SetGA.cart ahs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas arl_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded arl_cart_def]
  definition "arr_cart == SetGA.cart ahs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas arr_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded arr_cart_def]
  definition "arh_cart == SetGA.cart ahs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas arh_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded arh_cart_def]
  definition "ara_cart == SetGA.cart ahs_iterate rs_iterate ahs_empty ahs_ins_dj"
  lemmas ara_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl rs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_cart_def]
  definition "ahli_cart == SetGA.cart ahs_iterate hs_iterate lsi_empty lsi_ins_dj"
  lemmas ahli_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl hs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_cart_def]
  definition "ahl_cart == SetGA.cart ahs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas ahl_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ahl_cart_def]
  definition "ahr_cart == SetGA.cart ahs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas ahr_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded ahr_cart_def]
  definition "ahh_cart == SetGA.cart ahs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas ahh_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded ahh_cart_def]
  definition "aha_cart == SetGA.cart ahs_iterate hs_iterate ahs_empty ahs_ins_dj"
  lemmas aha_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl hs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_cart_def]
  definition "aali_cart == SetGA.cart ahs_iterate ahs_iterate lsi_empty lsi_ins_dj"
  lemmas aali_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ahs_iterate_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_cart_def]
  definition "aal_cart == SetGA.cart ahs_iterate ahs_iterate ls_empty ls_ins_dj"
  lemmas aal_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ahs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded aal_cart_def]
  definition "aar_cart == SetGA.cart ahs_iterate ahs_iterate rs_empty rs_ins_dj"
  lemmas aar_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ahs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded aar_cart_def]
  definition "aah_cart == SetGA.cart ahs_iterate ahs_iterate hs_empty hs_ins_dj"
  lemmas aah_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ahs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded aah_cart_def]
  definition "aaa_cart == SetGA.cart ahs_iterate ahs_iterate ahs_empty ahs_ins_dj"
  lemmas aaa_cart_correct = SetGA.cart_correct[OF ahs_iterate_impl ahs_iterate_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_cart_def]

  definition "lsi_to_fifo == it_set_to_fifo lsi_iterate"
  lemmas lsi_to_fifo_correct = it_set_to_fifo_correct[OF lsi_iterate_impl, folded lsi_to_fifo_def]
  definition "ls_to_fifo == it_set_to_fifo ls_iterate"
  lemmas ls_to_fifo_correct = it_set_to_fifo_correct[OF ls_iterate_impl, folded ls_to_fifo_def]
  definition "rs_to_fifo == it_set_to_fifo rs_iterate"
  lemmas rs_to_fifo_correct = it_set_to_fifo_correct[OF rs_iterate_impl, folded rs_to_fifo_def]
  definition "hs_to_fifo == it_set_to_fifo hs_iterate"
  lemmas hs_to_fifo_correct = it_set_to_fifo_correct[OF hs_iterate_impl, folded hs_to_fifo_def]
  definition "ahs_to_fifo == it_set_to_fifo ahs_iterate"
  lemmas ahs_to_fifo_correct = it_set_to_fifo_correct[OF ahs_iterate_impl, folded ahs_to_fifo_def]

  definition "lili_map_to_nat == map_to_nat lsi_iterate lmi_empty lmi_update"
  lemmas lili_map_to_nat_correct = map_to_nat_correct[OF lsi_iterate_impl lmi_empty_impl lmi_update_impl, folded lili_map_to_nat_def]
  definition "lil_map_to_nat == map_to_nat lsi_iterate lm_empty lm_update"
  lemmas lil_map_to_nat_correct = map_to_nat_correct[OF lsi_iterate_impl lm_empty_impl lm_update_impl, folded lil_map_to_nat_def]
  definition "lir_map_to_nat == map_to_nat lsi_iterate rm_empty rm_update"
  lemmas lir_map_to_nat_correct = map_to_nat_correct[OF lsi_iterate_impl rm_empty_impl rm_update_impl, folded lir_map_to_nat_def]
  definition "lih_map_to_nat == map_to_nat lsi_iterate hm_empty hm_update"
  lemmas lih_map_to_nat_correct = map_to_nat_correct[OF lsi_iterate_impl hm_empty_impl hm_update_impl, folded lih_map_to_nat_def]
  definition "lia_map_to_nat == map_to_nat lsi_iterate ahm_empty ahm_update"
  lemmas lia_map_to_nat_correct = map_to_nat_correct[OF lsi_iterate_impl ahm_empty_impl ahm_update_impl, folded lia_map_to_nat_def]
  definition "lli_map_to_nat == map_to_nat ls_iterate lmi_empty lmi_update"
  lemmas lli_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl lmi_empty_impl lmi_update_impl, folded lli_map_to_nat_def]
  definition "ll_map_to_nat == map_to_nat ls_iterate lm_empty lm_update"
  lemmas ll_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl lm_empty_impl lm_update_impl, folded ll_map_to_nat_def]
  definition "lr_map_to_nat == map_to_nat ls_iterate rm_empty rm_update"
  lemmas lr_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl rm_empty_impl rm_update_impl, folded lr_map_to_nat_def]
  definition "lh_map_to_nat == map_to_nat ls_iterate hm_empty hm_update"
  lemmas lh_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl hm_empty_impl hm_update_impl, folded lh_map_to_nat_def]
  definition "la_map_to_nat == map_to_nat ls_iterate ahm_empty ahm_update"
  lemmas la_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl ahm_empty_impl ahm_update_impl, folded la_map_to_nat_def]
  definition "rli_map_to_nat == map_to_nat rs_iterate lmi_empty lmi_update"
  lemmas rli_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl lmi_empty_impl lmi_update_impl, folded rli_map_to_nat_def]
  definition "rl_map_to_nat == map_to_nat rs_iterate lm_empty lm_update"
  lemmas rl_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl lm_empty_impl lm_update_impl, folded rl_map_to_nat_def]
  definition "rr_map_to_nat == map_to_nat rs_iterate rm_empty rm_update"
  lemmas rr_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl rm_empty_impl rm_update_impl, folded rr_map_to_nat_def]
  definition "rh_map_to_nat == map_to_nat rs_iterate hm_empty hm_update"
  lemmas rh_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl hm_empty_impl hm_update_impl, folded rh_map_to_nat_def]
  definition "ra_map_to_nat == map_to_nat rs_iterate ahm_empty ahm_update"
  lemmas ra_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl ahm_empty_impl ahm_update_impl, folded ra_map_to_nat_def]
  definition "hli_map_to_nat == map_to_nat hs_iterate lmi_empty lmi_update"
  lemmas hli_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl lmi_empty_impl lmi_update_impl, folded hli_map_to_nat_def]
  definition "hl_map_to_nat == map_to_nat hs_iterate lm_empty lm_update"
  lemmas hl_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl lm_empty_impl lm_update_impl, folded hl_map_to_nat_def]
  definition "hr_map_to_nat == map_to_nat hs_iterate rm_empty rm_update"
  lemmas hr_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl rm_empty_impl rm_update_impl, folded hr_map_to_nat_def]
  definition "hh_map_to_nat == map_to_nat hs_iterate hm_empty hm_update"
  lemmas hh_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl hm_empty_impl hm_update_impl, folded hh_map_to_nat_def]
  definition "ha_map_to_nat == map_to_nat hs_iterate ahm_empty ahm_update"
  lemmas ha_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl ahm_empty_impl ahm_update_impl, folded ha_map_to_nat_def]
  definition "ali_map_to_nat == map_to_nat ahs_iterate lmi_empty lmi_update"
  lemmas ali_map_to_nat_correct = map_to_nat_correct[OF ahs_iterate_impl lmi_empty_impl lmi_update_impl, folded ali_map_to_nat_def]
  definition "al_map_to_nat == map_to_nat ahs_iterate lm_empty lm_update"
  lemmas al_map_to_nat_correct = map_to_nat_correct[OF ahs_iterate_impl lm_empty_impl lm_update_impl, folded al_map_to_nat_def]
  definition "ar_map_to_nat == map_to_nat ahs_iterate rm_empty rm_update"
  lemmas ar_map_to_nat_correct = map_to_nat_correct[OF ahs_iterate_impl rm_empty_impl rm_update_impl, folded ar_map_to_nat_def]
  definition "ah_map_to_nat == map_to_nat ahs_iterate hm_empty hm_update"
  lemmas ah_map_to_nat_correct = map_to_nat_correct[OF ahs_iterate_impl hm_empty_impl hm_update_impl, folded ah_map_to_nat_def]
  definition "aa_map_to_nat == map_to_nat ahs_iterate ahm_empty ahm_update"
  lemmas aa_map_to_nat_correct = map_to_nat_correct[OF ahs_iterate_impl ahm_empty_impl ahm_update_impl, folded aa_map_to_nat_def]
(*#end_generated*)


(*#begin_generated*)
definition "lili_idx_invar == idx_invar lmi_\<alpha> lmi_invar lsi_\<alpha> lsi_invar"
definition "lili_idx_lookup == idx_lookup lmi_lookup lsi_empty"
lemmas lili_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl lsi_empty_impl, folded lili_idx_invar_def lili_idx_lookup_def]
definition "lil_idx_invar == idx_invar lmi_\<alpha> lmi_invar ls_\<alpha> ls_invar"
definition "lil_idx_lookup == idx_lookup lmi_lookup ls_empty"
lemmas lil_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl ls_empty_impl, folded lil_idx_invar_def lil_idx_lookup_def]
definition "lir_idx_invar == idx_invar lmi_\<alpha> lmi_invar rs_\<alpha> rs_invar"
definition "lir_idx_lookup == idx_lookup lmi_lookup rs_empty"
lemmas lir_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl rs_empty_impl, folded lir_idx_invar_def lir_idx_lookup_def]
definition "lih_idx_invar == idx_invar lmi_\<alpha> lmi_invar hs_\<alpha> hs_invar"
definition "lih_idx_lookup == idx_lookup lmi_lookup hs_empty"
lemmas lih_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl hs_empty_impl, folded lih_idx_invar_def lih_idx_lookup_def]
definition "lia_idx_invar == idx_invar lmi_\<alpha> lmi_invar ahs_\<alpha> ahs_invar"
definition "lia_idx_lookup == idx_lookup lmi_lookup ahs_empty"
lemmas lia_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl ahs_empty_impl, folded lia_idx_invar_def lia_idx_lookup_def]
definition "lli_idx_invar == idx_invar lm_\<alpha> lm_invar lsi_\<alpha> lsi_invar"
definition "lli_idx_lookup == idx_lookup lm_lookup lsi_empty"
lemmas lli_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl lsi_empty_impl, folded lli_idx_invar_def lli_idx_lookup_def]
definition "ll_idx_invar == idx_invar lm_\<alpha> lm_invar ls_\<alpha> ls_invar"
definition "ll_idx_lookup == idx_lookup lm_lookup ls_empty"
lemmas ll_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl ls_empty_impl, folded ll_idx_invar_def ll_idx_lookup_def]
definition "lr_idx_invar == idx_invar lm_\<alpha> lm_invar rs_\<alpha> rs_invar"
definition "lr_idx_lookup == idx_lookup lm_lookup rs_empty"
lemmas lr_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl rs_empty_impl, folded lr_idx_invar_def lr_idx_lookup_def]
definition "lh_idx_invar == idx_invar lm_\<alpha> lm_invar hs_\<alpha> hs_invar"
definition "lh_idx_lookup == idx_lookup lm_lookup hs_empty"
lemmas lh_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl hs_empty_impl, folded lh_idx_invar_def lh_idx_lookup_def]
definition "la_idx_invar == idx_invar lm_\<alpha> lm_invar ahs_\<alpha> ahs_invar"
definition "la_idx_lookup == idx_lookup lm_lookup ahs_empty"
lemmas la_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl ahs_empty_impl, folded la_idx_invar_def la_idx_lookup_def]
definition "rli_idx_invar == idx_invar rm_\<alpha> rm_invar lsi_\<alpha> lsi_invar"
definition "rli_idx_lookup == idx_lookup rm_lookup lsi_empty"
lemmas rli_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl lsi_empty_impl, folded rli_idx_invar_def rli_idx_lookup_def]
definition "rl_idx_invar == idx_invar rm_\<alpha> rm_invar ls_\<alpha> ls_invar"
definition "rl_idx_lookup == idx_lookup rm_lookup ls_empty"
lemmas rl_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl ls_empty_impl, folded rl_idx_invar_def rl_idx_lookup_def]
definition "rr_idx_invar == idx_invar rm_\<alpha> rm_invar rs_\<alpha> rs_invar"
definition "rr_idx_lookup == idx_lookup rm_lookup rs_empty"
lemmas rr_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl rs_empty_impl, folded rr_idx_invar_def rr_idx_lookup_def]
definition "rh_idx_invar == idx_invar rm_\<alpha> rm_invar hs_\<alpha> hs_invar"
definition "rh_idx_lookup == idx_lookup rm_lookup hs_empty"
lemmas rh_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl hs_empty_impl, folded rh_idx_invar_def rh_idx_lookup_def]
definition "ra_idx_invar == idx_invar rm_\<alpha> rm_invar ahs_\<alpha> ahs_invar"
definition "ra_idx_lookup == idx_lookup rm_lookup ahs_empty"
lemmas ra_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl ahs_empty_impl, folded ra_idx_invar_def ra_idx_lookup_def]
definition "hli_idx_invar == idx_invar hm_\<alpha> hm_invar lsi_\<alpha> lsi_invar"
definition "hli_idx_lookup == idx_lookup hm_lookup lsi_empty"
lemmas hli_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl lsi_empty_impl, folded hli_idx_invar_def hli_idx_lookup_def]
definition "hl_idx_invar == idx_invar hm_\<alpha> hm_invar ls_\<alpha> ls_invar"
definition "hl_idx_lookup == idx_lookup hm_lookup ls_empty"
lemmas hl_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl ls_empty_impl, folded hl_idx_invar_def hl_idx_lookup_def]
definition "hr_idx_invar == idx_invar hm_\<alpha> hm_invar rs_\<alpha> rs_invar"
definition "hr_idx_lookup == idx_lookup hm_lookup rs_empty"
lemmas hr_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl rs_empty_impl, folded hr_idx_invar_def hr_idx_lookup_def]
definition "hh_idx_invar == idx_invar hm_\<alpha> hm_invar hs_\<alpha> hs_invar"
definition "hh_idx_lookup == idx_lookup hm_lookup hs_empty"
lemmas hh_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl hs_empty_impl, folded hh_idx_invar_def hh_idx_lookup_def]
definition "ha_idx_invar == idx_invar hm_\<alpha> hm_invar ahs_\<alpha> ahs_invar"
definition "ha_idx_lookup == idx_lookup hm_lookup ahs_empty"
lemmas ha_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl ahs_empty_impl, folded ha_idx_invar_def ha_idx_lookup_def]
definition "ali_idx_invar == idx_invar ahm_\<alpha> ahm_invar lsi_\<alpha> lsi_invar"
definition "ali_idx_lookup == idx_lookup ahm_lookup lsi_empty"
lemmas ali_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl lsi_empty_impl, folded ali_idx_invar_def ali_idx_lookup_def]
definition "al_idx_invar == idx_invar ahm_\<alpha> ahm_invar ls_\<alpha> ls_invar"
definition "al_idx_lookup == idx_lookup ahm_lookup ls_empty"
lemmas al_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl ls_empty_impl, folded al_idx_invar_def al_idx_lookup_def]
definition "ar_idx_invar == idx_invar ahm_\<alpha> ahm_invar rs_\<alpha> rs_invar"
definition "ar_idx_lookup == idx_lookup ahm_lookup rs_empty"
lemmas ar_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl rs_empty_impl, folded ar_idx_invar_def ar_idx_lookup_def]
definition "ah_idx_invar == idx_invar ahm_\<alpha> ahm_invar hs_\<alpha> hs_invar"
definition "ah_idx_lookup == idx_lookup ahm_lookup hs_empty"
lemmas ah_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl hs_empty_impl, folded ah_idx_invar_def ah_idx_lookup_def]
definition "aa_idx_invar == idx_invar ahm_\<alpha> ahm_invar ahs_\<alpha> ahs_invar"
definition "aa_idx_lookup == idx_lookup ahm_lookup ahs_empty"
lemmas aa_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl ahs_empty_impl, folded aa_idx_invar_def aa_idx_lookup_def]
(*#end_generated*)

(*#begin_generated*)
definition "lilili_idx_build == idx_build lmi_empty lmi_lookup lmi_update   lsi_empty lsi_ins    lsi_iterate"
lemmas lilili_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   lsi_empty_impl lsi_ins_impl   lsi_iterate_impl,
  folded lili_idx_invar_def lilili_idx_build_def]
definition "lilil_idx_build == idx_build lmi_empty lmi_lookup lmi_update   lsi_empty lsi_ins    ls_iterate"
lemmas lilil_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   lsi_empty_impl lsi_ins_impl   ls_iterate_impl,
  folded lili_idx_invar_def lilil_idx_build_def]
definition "lilir_idx_build == idx_build lmi_empty lmi_lookup lmi_update   lsi_empty lsi_ins    rs_iterate"
lemmas lilir_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   lsi_empty_impl lsi_ins_impl   rs_iterate_impl,
  folded lili_idx_invar_def lilir_idx_build_def]
definition "lilih_idx_build == idx_build lmi_empty lmi_lookup lmi_update   lsi_empty lsi_ins    hs_iterate"
lemmas lilih_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   lsi_empty_impl lsi_ins_impl   hs_iterate_impl,
  folded lili_idx_invar_def lilih_idx_build_def]
definition "lilia_idx_build == idx_build lmi_empty lmi_lookup lmi_update   lsi_empty lsi_ins    ahs_iterate"
lemmas lilia_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   lsi_empty_impl lsi_ins_impl   ahs_iterate_impl,
  folded lili_idx_invar_def lilia_idx_build_def]
definition "lilli_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ls_empty ls_ins    lsi_iterate"
lemmas lilli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ls_empty_impl ls_ins_impl   lsi_iterate_impl,
  folded lil_idx_invar_def lilli_idx_build_def]
definition "lill_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ls_empty ls_ins    ls_iterate"
lemmas lill_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded lil_idx_invar_def lill_idx_build_def]
definition "lilr_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ls_empty ls_ins    rs_iterate"
lemmas lilr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded lil_idx_invar_def lilr_idx_build_def]
definition "lilh_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ls_empty ls_ins    hs_iterate"
lemmas lilh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded lil_idx_invar_def lilh_idx_build_def]
definition "lila_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ls_empty ls_ins    ahs_iterate"
lemmas lila_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ls_empty_impl ls_ins_impl   ahs_iterate_impl,
  folded lil_idx_invar_def lila_idx_build_def]
definition "lirli_idx_build == idx_build lmi_empty lmi_lookup lmi_update   rs_empty rs_ins    lsi_iterate"
lemmas lirli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   rs_empty_impl rs_ins_impl   lsi_iterate_impl,
  folded lir_idx_invar_def lirli_idx_build_def]
definition "lirl_idx_build == idx_build lmi_empty lmi_lookup lmi_update   rs_empty rs_ins    ls_iterate"
lemmas lirl_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded lir_idx_invar_def lirl_idx_build_def]
definition "lirr_idx_build == idx_build lmi_empty lmi_lookup lmi_update   rs_empty rs_ins    rs_iterate"
lemmas lirr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded lir_idx_invar_def lirr_idx_build_def]
definition "lirh_idx_build == idx_build lmi_empty lmi_lookup lmi_update   rs_empty rs_ins    hs_iterate"
lemmas lirh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded lir_idx_invar_def lirh_idx_build_def]
definition "lira_idx_build == idx_build lmi_empty lmi_lookup lmi_update   rs_empty rs_ins    ahs_iterate"
lemmas lira_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   rs_empty_impl rs_ins_impl   ahs_iterate_impl,
  folded lir_idx_invar_def lira_idx_build_def]
definition "lihli_idx_build == idx_build lmi_empty lmi_lookup lmi_update   hs_empty hs_ins    lsi_iterate"
lemmas lihli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   hs_empty_impl hs_ins_impl   lsi_iterate_impl,
  folded lih_idx_invar_def lihli_idx_build_def]
definition "lihl_idx_build == idx_build lmi_empty lmi_lookup lmi_update   hs_empty hs_ins    ls_iterate"
lemmas lihl_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded lih_idx_invar_def lihl_idx_build_def]
definition "lihr_idx_build == idx_build lmi_empty lmi_lookup lmi_update   hs_empty hs_ins    rs_iterate"
lemmas lihr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded lih_idx_invar_def lihr_idx_build_def]
definition "lihh_idx_build == idx_build lmi_empty lmi_lookup lmi_update   hs_empty hs_ins    hs_iterate"
lemmas lihh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded lih_idx_invar_def lihh_idx_build_def]
definition "liha_idx_build == idx_build lmi_empty lmi_lookup lmi_update   hs_empty hs_ins    ahs_iterate"
lemmas liha_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   hs_empty_impl hs_ins_impl   ahs_iterate_impl,
  folded lih_idx_invar_def liha_idx_build_def]
definition "liali_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ahs_empty ahs_ins    lsi_iterate"
lemmas liali_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ahs_empty_impl ahs_ins_impl   lsi_iterate_impl,
  folded lia_idx_invar_def liali_idx_build_def]
definition "lial_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ahs_empty ahs_ins    ls_iterate"
lemmas lial_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ahs_empty_impl ahs_ins_impl   ls_iterate_impl,
  folded lia_idx_invar_def lial_idx_build_def]
definition "liar_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ahs_empty ahs_ins    rs_iterate"
lemmas liar_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ahs_empty_impl ahs_ins_impl   rs_iterate_impl,
  folded lia_idx_invar_def liar_idx_build_def]
definition "liah_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ahs_empty ahs_ins    hs_iterate"
lemmas liah_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ahs_empty_impl ahs_ins_impl   hs_iterate_impl,
  folded lia_idx_invar_def liah_idx_build_def]
definition "liaa_idx_build == idx_build lmi_empty lmi_lookup lmi_update   ahs_empty ahs_ins    ahs_iterate"
lemmas liaa_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl   ahs_empty_impl ahs_ins_impl   ahs_iterate_impl,
  folded lia_idx_invar_def liaa_idx_build_def]
definition "llili_idx_build == idx_build lm_empty lm_lookup lm_update   lsi_empty lsi_ins    lsi_iterate"
lemmas llili_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   lsi_empty_impl lsi_ins_impl   lsi_iterate_impl,
  folded lli_idx_invar_def llili_idx_build_def]
definition "llil_idx_build == idx_build lm_empty lm_lookup lm_update   lsi_empty lsi_ins    ls_iterate"
lemmas llil_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   lsi_empty_impl lsi_ins_impl   ls_iterate_impl,
  folded lli_idx_invar_def llil_idx_build_def]
definition "llir_idx_build == idx_build lm_empty lm_lookup lm_update   lsi_empty lsi_ins    rs_iterate"
lemmas llir_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   lsi_empty_impl lsi_ins_impl   rs_iterate_impl,
  folded lli_idx_invar_def llir_idx_build_def]
definition "llih_idx_build == idx_build lm_empty lm_lookup lm_update   lsi_empty lsi_ins    hs_iterate"
lemmas llih_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   lsi_empty_impl lsi_ins_impl   hs_iterate_impl,
  folded lli_idx_invar_def llih_idx_build_def]
definition "llia_idx_build == idx_build lm_empty lm_lookup lm_update   lsi_empty lsi_ins    ahs_iterate"
lemmas llia_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   lsi_empty_impl lsi_ins_impl   ahs_iterate_impl,
  folded lli_idx_invar_def llia_idx_build_def]
definition "llli_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    lsi_iterate"
lemmas llli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   lsi_iterate_impl,
  folded ll_idx_invar_def llli_idx_build_def]
definition "lll_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    ls_iterate"
lemmas lll_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded ll_idx_invar_def lll_idx_build_def]
definition "llr_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    rs_iterate"
lemmas llr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded ll_idx_invar_def llr_idx_build_def]
definition "llh_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    hs_iterate"
lemmas llh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded ll_idx_invar_def llh_idx_build_def]
definition "lla_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    ahs_iterate"
lemmas lla_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   ahs_iterate_impl,
  folded ll_idx_invar_def lla_idx_build_def]
definition "lrli_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    lsi_iterate"
lemmas lrli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   lsi_iterate_impl,
  folded lr_idx_invar_def lrli_idx_build_def]
definition "lrl_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    ls_iterate"
lemmas lrl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded lr_idx_invar_def lrl_idx_build_def]
definition "lrr_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    rs_iterate"
lemmas lrr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded lr_idx_invar_def lrr_idx_build_def]
definition "lrh_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    hs_iterate"
lemmas lrh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded lr_idx_invar_def lrh_idx_build_def]
definition "lra_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    ahs_iterate"
lemmas lra_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   ahs_iterate_impl,
  folded lr_idx_invar_def lra_idx_build_def]
definition "lhli_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    lsi_iterate"
lemmas lhli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   lsi_iterate_impl,
  folded lh_idx_invar_def lhli_idx_build_def]
definition "lhl_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    ls_iterate"
lemmas lhl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded lh_idx_invar_def lhl_idx_build_def]
definition "lhr_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    rs_iterate"
lemmas lhr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded lh_idx_invar_def lhr_idx_build_def]
definition "lhh_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    hs_iterate"
lemmas lhh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded lh_idx_invar_def lhh_idx_build_def]
definition "lha_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    ahs_iterate"
lemmas lha_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   ahs_iterate_impl,
  folded lh_idx_invar_def lha_idx_build_def]
definition "lali_idx_build == idx_build lm_empty lm_lookup lm_update   ahs_empty ahs_ins    lsi_iterate"
lemmas lali_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ahs_empty_impl ahs_ins_impl   lsi_iterate_impl,
  folded la_idx_invar_def lali_idx_build_def]
definition "lal_idx_build == idx_build lm_empty lm_lookup lm_update   ahs_empty ahs_ins    ls_iterate"
lemmas lal_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ahs_empty_impl ahs_ins_impl   ls_iterate_impl,
  folded la_idx_invar_def lal_idx_build_def]
definition "lar_idx_build == idx_build lm_empty lm_lookup lm_update   ahs_empty ahs_ins    rs_iterate"
lemmas lar_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ahs_empty_impl ahs_ins_impl   rs_iterate_impl,
  folded la_idx_invar_def lar_idx_build_def]
definition "lah_idx_build == idx_build lm_empty lm_lookup lm_update   ahs_empty ahs_ins    hs_iterate"
lemmas lah_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ahs_empty_impl ahs_ins_impl   hs_iterate_impl,
  folded la_idx_invar_def lah_idx_build_def]
definition "laa_idx_build == idx_build lm_empty lm_lookup lm_update   ahs_empty ahs_ins    ahs_iterate"
lemmas laa_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ahs_empty_impl ahs_ins_impl   ahs_iterate_impl,
  folded la_idx_invar_def laa_idx_build_def]
definition "rlili_idx_build == idx_build rm_empty rm_lookup rm_update   lsi_empty lsi_ins    lsi_iterate"
lemmas rlili_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   lsi_empty_impl lsi_ins_impl   lsi_iterate_impl,
  folded rli_idx_invar_def rlili_idx_build_def]
definition "rlil_idx_build == idx_build rm_empty rm_lookup rm_update   lsi_empty lsi_ins    ls_iterate"
lemmas rlil_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   lsi_empty_impl lsi_ins_impl   ls_iterate_impl,
  folded rli_idx_invar_def rlil_idx_build_def]
definition "rlir_idx_build == idx_build rm_empty rm_lookup rm_update   lsi_empty lsi_ins    rs_iterate"
lemmas rlir_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   lsi_empty_impl lsi_ins_impl   rs_iterate_impl,
  folded rli_idx_invar_def rlir_idx_build_def]
definition "rlih_idx_build == idx_build rm_empty rm_lookup rm_update   lsi_empty lsi_ins    hs_iterate"
lemmas rlih_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   lsi_empty_impl lsi_ins_impl   hs_iterate_impl,
  folded rli_idx_invar_def rlih_idx_build_def]
definition "rlia_idx_build == idx_build rm_empty rm_lookup rm_update   lsi_empty lsi_ins    ahs_iterate"
lemmas rlia_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   lsi_empty_impl lsi_ins_impl   ahs_iterate_impl,
  folded rli_idx_invar_def rlia_idx_build_def]
definition "rlli_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    lsi_iterate"
lemmas rlli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   lsi_iterate_impl,
  folded rl_idx_invar_def rlli_idx_build_def]
definition "rll_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    ls_iterate"
lemmas rll_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded rl_idx_invar_def rll_idx_build_def]
definition "rlr_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    rs_iterate"
lemmas rlr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded rl_idx_invar_def rlr_idx_build_def]
definition "rlh_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    hs_iterate"
lemmas rlh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded rl_idx_invar_def rlh_idx_build_def]
definition "rla_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    ahs_iterate"
lemmas rla_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   ahs_iterate_impl,
  folded rl_idx_invar_def rla_idx_build_def]
definition "rrli_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    lsi_iterate"
lemmas rrli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   lsi_iterate_impl,
  folded rr_idx_invar_def rrli_idx_build_def]
definition "rrl_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    ls_iterate"
lemmas rrl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded rr_idx_invar_def rrl_idx_build_def]
definition "rrr_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    rs_iterate"
lemmas rrr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded rr_idx_invar_def rrr_idx_build_def]
definition "rrh_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    hs_iterate"
lemmas rrh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded rr_idx_invar_def rrh_idx_build_def]
definition "rra_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    ahs_iterate"
lemmas rra_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   ahs_iterate_impl,
  folded rr_idx_invar_def rra_idx_build_def]
definition "rhli_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    lsi_iterate"
lemmas rhli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   lsi_iterate_impl,
  folded rh_idx_invar_def rhli_idx_build_def]
definition "rhl_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    ls_iterate"
lemmas rhl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded rh_idx_invar_def rhl_idx_build_def]
definition "rhr_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    rs_iterate"
lemmas rhr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded rh_idx_invar_def rhr_idx_build_def]
definition "rhh_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    hs_iterate"
lemmas rhh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded rh_idx_invar_def rhh_idx_build_def]
definition "rha_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    ahs_iterate"
lemmas rha_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   ahs_iterate_impl,
  folded rh_idx_invar_def rha_idx_build_def]
definition "rali_idx_build == idx_build rm_empty rm_lookup rm_update   ahs_empty ahs_ins    lsi_iterate"
lemmas rali_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ahs_empty_impl ahs_ins_impl   lsi_iterate_impl,
  folded ra_idx_invar_def rali_idx_build_def]
definition "ral_idx_build == idx_build rm_empty rm_lookup rm_update   ahs_empty ahs_ins    ls_iterate"
lemmas ral_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ahs_empty_impl ahs_ins_impl   ls_iterate_impl,
  folded ra_idx_invar_def ral_idx_build_def]
definition "rar_idx_build == idx_build rm_empty rm_lookup rm_update   ahs_empty ahs_ins    rs_iterate"
lemmas rar_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ahs_empty_impl ahs_ins_impl   rs_iterate_impl,
  folded ra_idx_invar_def rar_idx_build_def]
definition "rah_idx_build == idx_build rm_empty rm_lookup rm_update   ahs_empty ahs_ins    hs_iterate"
lemmas rah_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ahs_empty_impl ahs_ins_impl   hs_iterate_impl,
  folded ra_idx_invar_def rah_idx_build_def]
definition "raa_idx_build == idx_build rm_empty rm_lookup rm_update   ahs_empty ahs_ins    ahs_iterate"
lemmas raa_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ahs_empty_impl ahs_ins_impl   ahs_iterate_impl,
  folded ra_idx_invar_def raa_idx_build_def]
definition "hlili_idx_build == idx_build hm_empty hm_lookup hm_update   lsi_empty lsi_ins    lsi_iterate"
lemmas hlili_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   lsi_empty_impl lsi_ins_impl   lsi_iterate_impl,
  folded hli_idx_invar_def hlili_idx_build_def]
definition "hlil_idx_build == idx_build hm_empty hm_lookup hm_update   lsi_empty lsi_ins    ls_iterate"
lemmas hlil_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   lsi_empty_impl lsi_ins_impl   ls_iterate_impl,
  folded hli_idx_invar_def hlil_idx_build_def]
definition "hlir_idx_build == idx_build hm_empty hm_lookup hm_update   lsi_empty lsi_ins    rs_iterate"
lemmas hlir_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   lsi_empty_impl lsi_ins_impl   rs_iterate_impl,
  folded hli_idx_invar_def hlir_idx_build_def]
definition "hlih_idx_build == idx_build hm_empty hm_lookup hm_update   lsi_empty lsi_ins    hs_iterate"
lemmas hlih_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   lsi_empty_impl lsi_ins_impl   hs_iterate_impl,
  folded hli_idx_invar_def hlih_idx_build_def]
definition "hlia_idx_build == idx_build hm_empty hm_lookup hm_update   lsi_empty lsi_ins    ahs_iterate"
lemmas hlia_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   lsi_empty_impl lsi_ins_impl   ahs_iterate_impl,
  folded hli_idx_invar_def hlia_idx_build_def]
definition "hlli_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    lsi_iterate"
lemmas hlli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   lsi_iterate_impl,
  folded hl_idx_invar_def hlli_idx_build_def]
definition "hll_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    ls_iterate"
lemmas hll_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded hl_idx_invar_def hll_idx_build_def]
definition "hlr_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    rs_iterate"
lemmas hlr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded hl_idx_invar_def hlr_idx_build_def]
definition "hlh_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    hs_iterate"
lemmas hlh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded hl_idx_invar_def hlh_idx_build_def]
definition "hla_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    ahs_iterate"
lemmas hla_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   ahs_iterate_impl,
  folded hl_idx_invar_def hla_idx_build_def]
definition "hrli_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    lsi_iterate"
lemmas hrli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   lsi_iterate_impl,
  folded hr_idx_invar_def hrli_idx_build_def]
definition "hrl_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    ls_iterate"
lemmas hrl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded hr_idx_invar_def hrl_idx_build_def]
definition "hrr_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    rs_iterate"
lemmas hrr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded hr_idx_invar_def hrr_idx_build_def]
definition "hrh_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    hs_iterate"
lemmas hrh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded hr_idx_invar_def hrh_idx_build_def]
definition "hra_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    ahs_iterate"
lemmas hra_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   ahs_iterate_impl,
  folded hr_idx_invar_def hra_idx_build_def]
definition "hhli_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    lsi_iterate"
lemmas hhli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   lsi_iterate_impl,
  folded hh_idx_invar_def hhli_idx_build_def]
definition "hhl_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    ls_iterate"
lemmas hhl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded hh_idx_invar_def hhl_idx_build_def]
definition "hhr_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    rs_iterate"
lemmas hhr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded hh_idx_invar_def hhr_idx_build_def]
definition "hhh_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    hs_iterate"
lemmas hhh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded hh_idx_invar_def hhh_idx_build_def]
definition "hha_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    ahs_iterate"
lemmas hha_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   ahs_iterate_impl,
  folded hh_idx_invar_def hha_idx_build_def]
definition "hali_idx_build == idx_build hm_empty hm_lookup hm_update   ahs_empty ahs_ins    lsi_iterate"
lemmas hali_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ahs_empty_impl ahs_ins_impl   lsi_iterate_impl,
  folded ha_idx_invar_def hali_idx_build_def]
definition "hal_idx_build == idx_build hm_empty hm_lookup hm_update   ahs_empty ahs_ins    ls_iterate"
lemmas hal_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ahs_empty_impl ahs_ins_impl   ls_iterate_impl,
  folded ha_idx_invar_def hal_idx_build_def]
definition "har_idx_build == idx_build hm_empty hm_lookup hm_update   ahs_empty ahs_ins    rs_iterate"
lemmas har_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ahs_empty_impl ahs_ins_impl   rs_iterate_impl,
  folded ha_idx_invar_def har_idx_build_def]
definition "hah_idx_build == idx_build hm_empty hm_lookup hm_update   ahs_empty ahs_ins    hs_iterate"
lemmas hah_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ahs_empty_impl ahs_ins_impl   hs_iterate_impl,
  folded ha_idx_invar_def hah_idx_build_def]
definition "haa_idx_build == idx_build hm_empty hm_lookup hm_update   ahs_empty ahs_ins    ahs_iterate"
lemmas haa_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ahs_empty_impl ahs_ins_impl   ahs_iterate_impl,
  folded ha_idx_invar_def haa_idx_build_def]
definition "alili_idx_build == idx_build ahm_empty ahm_lookup ahm_update   lsi_empty lsi_ins    lsi_iterate"
lemmas alili_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   lsi_empty_impl lsi_ins_impl   lsi_iterate_impl,
  folded ali_idx_invar_def alili_idx_build_def]
definition "alil_idx_build == idx_build ahm_empty ahm_lookup ahm_update   lsi_empty lsi_ins    ls_iterate"
lemmas alil_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   lsi_empty_impl lsi_ins_impl   ls_iterate_impl,
  folded ali_idx_invar_def alil_idx_build_def]
definition "alir_idx_build == idx_build ahm_empty ahm_lookup ahm_update   lsi_empty lsi_ins    rs_iterate"
lemmas alir_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   lsi_empty_impl lsi_ins_impl   rs_iterate_impl,
  folded ali_idx_invar_def alir_idx_build_def]
definition "alih_idx_build == idx_build ahm_empty ahm_lookup ahm_update   lsi_empty lsi_ins    hs_iterate"
lemmas alih_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   lsi_empty_impl lsi_ins_impl   hs_iterate_impl,
  folded ali_idx_invar_def alih_idx_build_def]
definition "alia_idx_build == idx_build ahm_empty ahm_lookup ahm_update   lsi_empty lsi_ins    ahs_iterate"
lemmas alia_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   lsi_empty_impl lsi_ins_impl   ahs_iterate_impl,
  folded ali_idx_invar_def alia_idx_build_def]
definition "alli_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ls_empty ls_ins    lsi_iterate"
lemmas alli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ls_empty_impl ls_ins_impl   lsi_iterate_impl,
  folded al_idx_invar_def alli_idx_build_def]
definition "all_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ls_empty ls_ins    ls_iterate"
lemmas all_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded al_idx_invar_def all_idx_build_def]
definition "alr_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ls_empty ls_ins    rs_iterate"
lemmas alr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded al_idx_invar_def alr_idx_build_def]
definition "alh_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ls_empty ls_ins    hs_iterate"
lemmas alh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded al_idx_invar_def alh_idx_build_def]
definition "ala_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ls_empty ls_ins    ahs_iterate"
lemmas ala_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ls_empty_impl ls_ins_impl   ahs_iterate_impl,
  folded al_idx_invar_def ala_idx_build_def]
definition "arli_idx_build == idx_build ahm_empty ahm_lookup ahm_update   rs_empty rs_ins    lsi_iterate"
lemmas arli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   rs_empty_impl rs_ins_impl   lsi_iterate_impl,
  folded ar_idx_invar_def arli_idx_build_def]
definition "arl_idx_build == idx_build ahm_empty ahm_lookup ahm_update   rs_empty rs_ins    ls_iterate"
lemmas arl_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded ar_idx_invar_def arl_idx_build_def]
definition "arr_idx_build == idx_build ahm_empty ahm_lookup ahm_update   rs_empty rs_ins    rs_iterate"
lemmas arr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded ar_idx_invar_def arr_idx_build_def]
definition "arh_idx_build == idx_build ahm_empty ahm_lookup ahm_update   rs_empty rs_ins    hs_iterate"
lemmas arh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded ar_idx_invar_def arh_idx_build_def]
definition "ara_idx_build == idx_build ahm_empty ahm_lookup ahm_update   rs_empty rs_ins    ahs_iterate"
lemmas ara_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   rs_empty_impl rs_ins_impl   ahs_iterate_impl,
  folded ar_idx_invar_def ara_idx_build_def]
definition "ahli_idx_build == idx_build ahm_empty ahm_lookup ahm_update   hs_empty hs_ins    lsi_iterate"
lemmas ahli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   hs_empty_impl hs_ins_impl   lsi_iterate_impl,
  folded ah_idx_invar_def ahli_idx_build_def]
definition "ahl_idx_build == idx_build ahm_empty ahm_lookup ahm_update   hs_empty hs_ins    ls_iterate"
lemmas ahl_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded ah_idx_invar_def ahl_idx_build_def]
definition "ahr_idx_build == idx_build ahm_empty ahm_lookup ahm_update   hs_empty hs_ins    rs_iterate"
lemmas ahr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded ah_idx_invar_def ahr_idx_build_def]
definition "ahh_idx_build == idx_build ahm_empty ahm_lookup ahm_update   hs_empty hs_ins    hs_iterate"
lemmas ahh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded ah_idx_invar_def ahh_idx_build_def]
definition "aha_idx_build == idx_build ahm_empty ahm_lookup ahm_update   hs_empty hs_ins    ahs_iterate"
lemmas aha_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   hs_empty_impl hs_ins_impl   ahs_iterate_impl,
  folded ah_idx_invar_def aha_idx_build_def]
definition "aali_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ahs_empty ahs_ins    lsi_iterate"
lemmas aali_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ahs_empty_impl ahs_ins_impl   lsi_iterate_impl,
  folded aa_idx_invar_def aali_idx_build_def]
definition "aal_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ahs_empty ahs_ins    ls_iterate"
lemmas aal_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ahs_empty_impl ahs_ins_impl   ls_iterate_impl,
  folded aa_idx_invar_def aal_idx_build_def]
definition "aar_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ahs_empty ahs_ins    rs_iterate"
lemmas aar_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ahs_empty_impl ahs_ins_impl   rs_iterate_impl,
  folded aa_idx_invar_def aar_idx_build_def]
definition "aah_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ahs_empty ahs_ins    hs_iterate"
lemmas aah_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ahs_empty_impl ahs_ins_impl   hs_iterate_impl,
  folded aa_idx_invar_def aah_idx_build_def]
definition "aaa_idx_build == idx_build ahm_empty ahm_lookup ahm_update   ahs_empty ahs_ins    ahs_iterate"
lemmas aaa_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl   ahs_empty_impl ahs_ins_impl   ahs_iterate_impl,
  folded aa_idx_invar_def aaa_idx_build_def]
(*#end_generated*)

end
