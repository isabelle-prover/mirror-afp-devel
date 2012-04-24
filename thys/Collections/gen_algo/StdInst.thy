(* Generated file *)
(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Standard Instantiations *}
theory StdInst
imports 
  "../impl/MapStdImpl"
  "../impl/SetStdImpl" 
  "../impl/Fifo"
  SetIndex 
  Algos
  SetGA 
  MapGA
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

  definition "lili_copy == SetGA.it_copy lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas lili_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lili_copy_def]
  interpretation lili: set_copy lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_copy using lili_copy_impl .
  definition "lil_copy == SetGA.it_copy lsi_iteratei ls_empty ls_ins_dj"
  lemmas lil_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lil_copy_def]
  interpretation lil: set_copy lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_copy using lil_copy_impl .
  definition "lir_copy == SetGA.it_copy lsi_iteratei rs_empty rs_ins_dj"
  lemmas lir_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lir_copy_def]
  interpretation lir: set_copy lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_copy using lir_copy_impl .
  definition "lih_copy == SetGA.it_copy lsi_iteratei hs_empty hs_ins_dj"
  lemmas lih_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lih_copy_def]
  interpretation lih: set_copy lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_copy using lih_copy_impl .
  definition "lia_copy == SetGA.it_copy lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas lia_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lia_copy_def]
  interpretation lia: set_copy lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_copy using lia_copy_impl .
  definition "liis_copy == SetGA.it_copy lsi_iteratei ias_empty ias_ins_dj"
  lemmas liis_copy_impl = SetGA.it_copy_correct[OF lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liis_copy_def]
  interpretation liis: set_copy lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_copy using liis_copy_impl .
  definition "lli_copy == SetGA.it_copy ls_iteratei lsi_empty lsi_ins_dj"
  lemmas lli_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lli_copy_def]
  interpretation lli: set_copy ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_copy using lli_copy_impl .
  definition "ll_copy == SetGA.it_copy ls_iteratei ls_empty ls_ins_dj"
  lemmas ll_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ll_copy_def]
  interpretation ll: set_copy ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_copy using ll_copy_impl .
  definition "lr_copy == SetGA.it_copy ls_iteratei rs_empty rs_ins_dj"
  lemmas lr_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lr_copy_def]
  interpretation lr: set_copy ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_copy using lr_copy_impl .
  definition "lh_copy == SetGA.it_copy ls_iteratei hs_empty hs_ins_dj"
  lemmas lh_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lh_copy_def]
  interpretation lh: set_copy ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_copy using lh_copy_impl .
  definition "la_copy == SetGA.it_copy ls_iteratei ahs_empty ahs_ins_dj"
  lemmas la_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded la_copy_def]
  interpretation la: set_copy ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_copy using la_copy_impl .
  definition "lis_copy == SetGA.it_copy ls_iteratei ias_empty ias_ins_dj"
  lemmas lis_copy_impl = SetGA.it_copy_correct[OF ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lis_copy_def]
  interpretation lis: set_copy ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_copy using lis_copy_impl .
  definition "rli_copy == SetGA.it_copy rs_iteratei lsi_empty lsi_ins_dj"
  lemmas rli_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rli_copy_def]
  interpretation rli: set_copy rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_copy using rli_copy_impl .
  definition "rl_copy == SetGA.it_copy rs_iteratei ls_empty ls_ins_dj"
  lemmas rl_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rl_copy_def]
  interpretation rl: set_copy rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_copy using rl_copy_impl .
  definition "rr_copy == SetGA.it_copy rs_iteratei rs_empty rs_ins_dj"
  lemmas rr_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rr_copy_def]
  interpretation rr: set_copy rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_copy using rr_copy_impl .
  definition "rh_copy == SetGA.it_copy rs_iteratei hs_empty hs_ins_dj"
  lemmas rh_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rh_copy_def]
  interpretation rh: set_copy rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_copy using rh_copy_impl .
  definition "ra_copy == SetGA.it_copy rs_iteratei ahs_empty ahs_ins_dj"
  lemmas ra_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ra_copy_def]
  interpretation ra: set_copy rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_copy using ra_copy_impl .
  definition "ris_copy == SetGA.it_copy rs_iteratei ias_empty ias_ins_dj"
  lemmas ris_copy_impl = SetGA.it_copy_correct[OF rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ris_copy_def]
  interpretation ris: set_copy rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_copy using ris_copy_impl .
  definition "hli_copy == SetGA.it_copy hs_iteratei lsi_empty lsi_ins_dj"
  lemmas hli_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hli_copy_def]
  interpretation hli: set_copy hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_copy using hli_copy_impl .
  definition "hl_copy == SetGA.it_copy hs_iteratei ls_empty ls_ins_dj"
  lemmas hl_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hl_copy_def]
  interpretation hl: set_copy hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_copy using hl_copy_impl .
  definition "hr_copy == SetGA.it_copy hs_iteratei rs_empty rs_ins_dj"
  lemmas hr_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hr_copy_def]
  interpretation hr: set_copy hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_copy using hr_copy_impl .
  definition "hh_copy == SetGA.it_copy hs_iteratei hs_empty hs_ins_dj"
  lemmas hh_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hh_copy_def]
  interpretation hh: set_copy hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_copy using hh_copy_impl .
  definition "ha_copy == SetGA.it_copy hs_iteratei ahs_empty ahs_ins_dj"
  lemmas ha_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ha_copy_def]
  interpretation ha: set_copy hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_copy using ha_copy_impl .
  definition "his_copy == SetGA.it_copy hs_iteratei ias_empty ias_ins_dj"
  lemmas his_copy_impl = SetGA.it_copy_correct[OF hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded his_copy_def]
  interpretation his: set_copy hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_copy using his_copy_impl .
  definition "ali_copy == SetGA.it_copy ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas ali_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ali_copy_def]
  interpretation ali: set_copy ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_copy using ali_copy_impl .
  definition "al_copy == SetGA.it_copy ahs_iteratei ls_empty ls_ins_dj"
  lemmas al_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded al_copy_def]
  interpretation al: set_copy ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_copy using al_copy_impl .
  definition "ar_copy == SetGA.it_copy ahs_iteratei rs_empty rs_ins_dj"
  lemmas ar_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ar_copy_def]
  interpretation ar: set_copy ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_copy using ar_copy_impl .
  definition "ah_copy == SetGA.it_copy ahs_iteratei hs_empty hs_ins_dj"
  lemmas ah_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ah_copy_def]
  interpretation ah: set_copy ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_copy using ah_copy_impl .
  definition "aa_copy == SetGA.it_copy ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas aa_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aa_copy_def]
  interpretation aa: set_copy ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_copy using aa_copy_impl .
  definition "ais_copy == SetGA.it_copy ahs_iteratei ias_empty ias_ins_dj"
  lemmas ais_copy_impl = SetGA.it_copy_correct[OF ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ais_copy_def]
  interpretation ais: set_copy ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_copy using ais_copy_impl .
  definition "isli_copy == SetGA.it_copy ias_iteratei lsi_empty lsi_ins_dj"
  lemmas isli_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isli_copy_def]
  interpretation isli: set_copy ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_copy using isli_copy_impl .
  definition "isl_copy == SetGA.it_copy ias_iteratei ls_empty ls_ins_dj"
  lemmas isl_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isl_copy_def]
  interpretation isl: set_copy ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_copy using isl_copy_impl .
  definition "isr_copy == SetGA.it_copy ias_iteratei rs_empty rs_ins_dj"
  lemmas isr_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isr_copy_def]
  interpretation isr: set_copy ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_copy using isr_copy_impl .
  definition "ish_copy == SetGA.it_copy ias_iteratei hs_empty hs_ins_dj"
  lemmas ish_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ish_copy_def]
  interpretation ish: set_copy ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_copy using ish_copy_impl .
  definition "isa_copy == SetGA.it_copy ias_iteratei ahs_empty ahs_ins_dj"
  lemmas isa_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isa_copy_def]
  interpretation isa: set_copy ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_copy using isa_copy_impl .
  definition "isis_copy == SetGA.it_copy ias_iteratei ias_empty ias_ins_dj"
  lemmas isis_copy_impl = SetGA.it_copy_correct[OF ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isis_copy_def]
  interpretation isis: set_copy ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_copy using isis_copy_impl .

  definition "lilili_union == SetGA.it_union lsi_iteratei lsi_ins"
  lemmas lilili_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl lsi_ins_impl, folded lilili_union_def]
  interpretation lilili: set_union lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_union using lilili_union_impl .
  definition "lill_union == SetGA.it_union lsi_iteratei ls_ins"
  lemmas lill_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl ls_ins_impl, folded lill_union_def]
  interpretation lill: set_union lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_union using lill_union_impl .
  definition "lirr_union == SetGA.it_union lsi_iteratei rs_ins"
  lemmas lirr_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl rs_ins_impl, folded lirr_union_def]
  interpretation lirr: set_union lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_union using lirr_union_impl .
  definition "lihh_union == SetGA.it_union lsi_iteratei hs_ins"
  lemmas lihh_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl hs_ins_impl, folded lihh_union_def]
  interpretation lihh: set_union lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_union using lihh_union_impl .
  definition "liaa_union == SetGA.it_union lsi_iteratei ahs_ins"
  lemmas liaa_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl ahs_ins_impl, folded liaa_union_def]
  interpretation liaa: set_union lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_union using liaa_union_impl .
  definition "liisis_union == SetGA.it_union lsi_iteratei ias_ins"
  lemmas liisis_union_impl = SetGA.it_union_correct[OF lsi_iteratei_impl ias_ins_impl, folded liisis_union_def]
  interpretation liisis: set_union lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar liisis_union using liisis_union_impl .
  definition "llili_union == SetGA.it_union ls_iteratei lsi_ins"
  lemmas llili_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl lsi_ins_impl, folded llili_union_def]
  interpretation llili: set_union ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_union using llili_union_impl .
  definition "lll_union == SetGA.it_union ls_iteratei ls_ins"
  lemmas lll_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl ls_ins_impl, folded lll_union_def]
  interpretation lll: set_union ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union using lll_union_impl .
  definition "lrr_union == SetGA.it_union ls_iteratei rs_ins"
  lemmas lrr_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl rs_ins_impl, folded lrr_union_def]
  interpretation lrr: set_union ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union using lrr_union_impl .
  definition "lhh_union == SetGA.it_union ls_iteratei hs_ins"
  lemmas lhh_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl hs_ins_impl, folded lhh_union_def]
  interpretation lhh: set_union ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union using lhh_union_impl .
  definition "laa_union == SetGA.it_union ls_iteratei ahs_ins"
  lemmas laa_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl ahs_ins_impl, folded laa_union_def]
  interpretation laa: set_union ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_union using laa_union_impl .
  definition "lisis_union == SetGA.it_union ls_iteratei ias_ins"
  lemmas lisis_union_impl = SetGA.it_union_correct[OF ls_iteratei_impl ias_ins_impl, folded lisis_union_def]
  interpretation lisis: set_union ls_\<alpha> ls_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar lisis_union using lisis_union_impl .
  definition "rlili_union == SetGA.it_union rs_iteratei lsi_ins"
  lemmas rlili_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl lsi_ins_impl, folded rlili_union_def]
  interpretation rlili: set_union rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_union using rlili_union_impl .
  definition "rll_union == SetGA.it_union rs_iteratei ls_ins"
  lemmas rll_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl ls_ins_impl, folded rll_union_def]
  interpretation rll: set_union rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union using rll_union_impl .
  definition "rrr_union == SetGA.it_union rs_iteratei rs_ins"
  lemmas rrr_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl rs_ins_impl, folded rrr_union_def]
  interpretation rrr: set_union rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union using rrr_union_impl .
  definition "rhh_union == SetGA.it_union rs_iteratei hs_ins"
  lemmas rhh_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl hs_ins_impl, folded rhh_union_def]
  interpretation rhh: set_union rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union using rhh_union_impl .
  definition "raa_union == SetGA.it_union rs_iteratei ahs_ins"
  lemmas raa_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl ahs_ins_impl, folded raa_union_def]
  interpretation raa: set_union rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_union using raa_union_impl .
  definition "risis_union == SetGA.it_union rs_iteratei ias_ins"
  lemmas risis_union_impl = SetGA.it_union_correct[OF rs_iteratei_impl ias_ins_impl, folded risis_union_def]
  interpretation risis: set_union rs_\<alpha> rs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar risis_union using risis_union_impl .
  definition "hlili_union == SetGA.it_union hs_iteratei lsi_ins"
  lemmas hlili_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl lsi_ins_impl, folded hlili_union_def]
  interpretation hlili: set_union hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_union using hlili_union_impl .
  definition "hll_union == SetGA.it_union hs_iteratei ls_ins"
  lemmas hll_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl ls_ins_impl, folded hll_union_def]
  interpretation hll: set_union hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union using hll_union_impl .
  definition "hrr_union == SetGA.it_union hs_iteratei rs_ins"
  lemmas hrr_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl rs_ins_impl, folded hrr_union_def]
  interpretation hrr: set_union hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union using hrr_union_impl .
  definition "hhh_union == SetGA.it_union hs_iteratei hs_ins"
  lemmas hhh_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl hs_ins_impl, folded hhh_union_def]
  interpretation hhh: set_union hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union using hhh_union_impl .
  definition "haa_union == SetGA.it_union hs_iteratei ahs_ins"
  lemmas haa_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl ahs_ins_impl, folded haa_union_def]
  interpretation haa: set_union hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_union using haa_union_impl .
  definition "hisis_union == SetGA.it_union hs_iteratei ias_ins"
  lemmas hisis_union_impl = SetGA.it_union_correct[OF hs_iteratei_impl ias_ins_impl, folded hisis_union_def]
  interpretation hisis: set_union hs_\<alpha> hs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar hisis_union using hisis_union_impl .
  definition "alili_union == SetGA.it_union ahs_iteratei lsi_ins"
  lemmas alili_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl lsi_ins_impl, folded alili_union_def]
  interpretation alili: set_union ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_union using alili_union_impl .
  definition "all_union == SetGA.it_union ahs_iteratei ls_ins"
  lemmas all_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl ls_ins_impl, folded all_union_def]
  interpretation all: set_union ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_union using all_union_impl .
  definition "arr_union == SetGA.it_union ahs_iteratei rs_ins"
  lemmas arr_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl rs_ins_impl, folded arr_union_def]
  interpretation arr: set_union ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_union using arr_union_impl .
  definition "ahh_union == SetGA.it_union ahs_iteratei hs_ins"
  lemmas ahh_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl hs_ins_impl, folded ahh_union_def]
  interpretation ahh: set_union ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_union using ahh_union_impl .
  definition "aaa_union == SetGA.it_union ahs_iteratei ahs_ins"
  lemmas aaa_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl ahs_ins_impl, folded aaa_union_def]
  interpretation aaa: set_union ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_union using aaa_union_impl .
  definition "aisis_union == SetGA.it_union ahs_iteratei ias_ins"
  lemmas aisis_union_impl = SetGA.it_union_correct[OF ahs_iteratei_impl ias_ins_impl, folded aisis_union_def]
  interpretation aisis: set_union ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar aisis_union using aisis_union_impl .
  definition "islili_union == SetGA.it_union ias_iteratei lsi_ins"
  lemmas islili_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl lsi_ins_impl, folded islili_union_def]
  interpretation islili: set_union ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar islili_union using islili_union_impl .
  definition "isll_union == SetGA.it_union ias_iteratei ls_ins"
  lemmas isll_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl ls_ins_impl, folded isll_union_def]
  interpretation isll: set_union ias_\<alpha> ias_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar isll_union using isll_union_impl .
  definition "isrr_union == SetGA.it_union ias_iteratei rs_ins"
  lemmas isrr_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl rs_ins_impl, folded isrr_union_def]
  interpretation isrr: set_union ias_\<alpha> ias_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar isrr_union using isrr_union_impl .
  definition "ishh_union == SetGA.it_union ias_iteratei hs_ins"
  lemmas ishh_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl hs_ins_impl, folded ishh_union_def]
  interpretation ishh: set_union ias_\<alpha> ias_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ishh_union using ishh_union_impl .
  definition "isaa_union == SetGA.it_union ias_iteratei ahs_ins"
  lemmas isaa_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl ahs_ins_impl, folded isaa_union_def]
  interpretation isaa: set_union ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar isaa_union using isaa_union_impl .
  definition "isisis_union == SetGA.it_union ias_iteratei ias_ins"
  lemmas isisis_union_impl = SetGA.it_union_correct[OF ias_iteratei_impl ias_ins_impl, folded isisis_union_def]
  interpretation isisis: set_union ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar isisis_union using isisis_union_impl .

  definition "lilili_union_dj == SetGA.it_union_dj lsi_iteratei lsi_ins_dj"
  lemmas lilili_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl lsi_ins_dj_impl, folded lilili_union_dj_def]
  interpretation lilili: set_union_dj lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_union_dj using lilili_union_dj_impl .
  definition "lill_union_dj == SetGA.it_union_dj lsi_iteratei ls_ins_dj"
  lemmas lill_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl ls_ins_dj_impl, folded lill_union_dj_def]
  interpretation lill: set_union_dj lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_union_dj using lill_union_dj_impl .
  definition "lirr_union_dj == SetGA.it_union_dj lsi_iteratei rs_ins_dj"
  lemmas lirr_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl rs_ins_dj_impl, folded lirr_union_dj_def]
  interpretation lirr: set_union_dj lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_union_dj using lirr_union_dj_impl .
  definition "lihh_union_dj == SetGA.it_union_dj lsi_iteratei hs_ins_dj"
  lemmas lihh_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl hs_ins_dj_impl, folded lihh_union_dj_def]
  interpretation lihh: set_union_dj lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_union_dj using lihh_union_dj_impl .
  definition "liaa_union_dj == SetGA.it_union_dj lsi_iteratei ahs_ins_dj"
  lemmas liaa_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl ahs_ins_dj_impl, folded liaa_union_dj_def]
  interpretation liaa: set_union_dj lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_union_dj using liaa_union_dj_impl .
  definition "liisis_union_dj == SetGA.it_union_dj lsi_iteratei ias_ins_dj"
  lemmas liisis_union_dj_impl = SetGA.it_union_dj_correct[OF lsi_iteratei_impl ias_ins_dj_impl, folded liisis_union_dj_def]
  interpretation liisis: set_union_dj lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar liisis_union_dj using liisis_union_dj_impl .
  definition "llili_union_dj == SetGA.it_union_dj ls_iteratei lsi_ins_dj"
  lemmas llili_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl lsi_ins_dj_impl, folded llili_union_dj_def]
  interpretation llili: set_union_dj ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_union_dj using llili_union_dj_impl .
  definition "lll_union_dj == SetGA.it_union_dj ls_iteratei ls_ins_dj"
  lemmas lll_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl ls_ins_dj_impl, folded lll_union_dj_def]
  interpretation lll: set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union_dj using lll_union_dj_impl .
  definition "lrr_union_dj == SetGA.it_union_dj ls_iteratei rs_ins_dj"
  lemmas lrr_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl rs_ins_dj_impl, folded lrr_union_dj_def]
  interpretation lrr: set_union_dj ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union_dj using lrr_union_dj_impl .
  definition "lhh_union_dj == SetGA.it_union_dj ls_iteratei hs_ins_dj"
  lemmas lhh_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl hs_ins_dj_impl, folded lhh_union_dj_def]
  interpretation lhh: set_union_dj ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union_dj using lhh_union_dj_impl .
  definition "laa_union_dj == SetGA.it_union_dj ls_iteratei ahs_ins_dj"
  lemmas laa_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl ahs_ins_dj_impl, folded laa_union_dj_def]
  interpretation laa: set_union_dj ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_union_dj using laa_union_dj_impl .
  definition "lisis_union_dj == SetGA.it_union_dj ls_iteratei ias_ins_dj"
  lemmas lisis_union_dj_impl = SetGA.it_union_dj_correct[OF ls_iteratei_impl ias_ins_dj_impl, folded lisis_union_dj_def]
  interpretation lisis: set_union_dj ls_\<alpha> ls_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar lisis_union_dj using lisis_union_dj_impl .
  definition "rlili_union_dj == SetGA.it_union_dj rs_iteratei lsi_ins_dj"
  lemmas rlili_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl lsi_ins_dj_impl, folded rlili_union_dj_def]
  interpretation rlili: set_union_dj rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_union_dj using rlili_union_dj_impl .
  definition "rll_union_dj == SetGA.it_union_dj rs_iteratei ls_ins_dj"
  lemmas rll_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl ls_ins_dj_impl, folded rll_union_dj_def]
  interpretation rll: set_union_dj rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union_dj using rll_union_dj_impl .
  definition "rrr_union_dj == SetGA.it_union_dj rs_iteratei rs_ins_dj"
  lemmas rrr_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl rs_ins_dj_impl, folded rrr_union_dj_def]
  interpretation rrr: set_union_dj rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union_dj using rrr_union_dj_impl .
  definition "rhh_union_dj == SetGA.it_union_dj rs_iteratei hs_ins_dj"
  lemmas rhh_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl hs_ins_dj_impl, folded rhh_union_dj_def]
  interpretation rhh: set_union_dj rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union_dj using rhh_union_dj_impl .
  definition "raa_union_dj == SetGA.it_union_dj rs_iteratei ahs_ins_dj"
  lemmas raa_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl ahs_ins_dj_impl, folded raa_union_dj_def]
  interpretation raa: set_union_dj rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_union_dj using raa_union_dj_impl .
  definition "risis_union_dj == SetGA.it_union_dj rs_iteratei ias_ins_dj"
  lemmas risis_union_dj_impl = SetGA.it_union_dj_correct[OF rs_iteratei_impl ias_ins_dj_impl, folded risis_union_dj_def]
  interpretation risis: set_union_dj rs_\<alpha> rs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar risis_union_dj using risis_union_dj_impl .
  definition "hlili_union_dj == SetGA.it_union_dj hs_iteratei lsi_ins_dj"
  lemmas hlili_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl lsi_ins_dj_impl, folded hlili_union_dj_def]
  interpretation hlili: set_union_dj hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_union_dj using hlili_union_dj_impl .
  definition "hll_union_dj == SetGA.it_union_dj hs_iteratei ls_ins_dj"
  lemmas hll_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl ls_ins_dj_impl, folded hll_union_dj_def]
  interpretation hll: set_union_dj hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union_dj using hll_union_dj_impl .
  definition "hrr_union_dj == SetGA.it_union_dj hs_iteratei rs_ins_dj"
  lemmas hrr_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl rs_ins_dj_impl, folded hrr_union_dj_def]
  interpretation hrr: set_union_dj hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union_dj using hrr_union_dj_impl .
  definition "hhh_union_dj == SetGA.it_union_dj hs_iteratei hs_ins_dj"
  lemmas hhh_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl hs_ins_dj_impl, folded hhh_union_dj_def]
  interpretation hhh: set_union_dj hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union_dj using hhh_union_dj_impl .
  definition "haa_union_dj == SetGA.it_union_dj hs_iteratei ahs_ins_dj"
  lemmas haa_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl ahs_ins_dj_impl, folded haa_union_dj_def]
  interpretation haa: set_union_dj hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_union_dj using haa_union_dj_impl .
  definition "hisis_union_dj == SetGA.it_union_dj hs_iteratei ias_ins_dj"
  lemmas hisis_union_dj_impl = SetGA.it_union_dj_correct[OF hs_iteratei_impl ias_ins_dj_impl, folded hisis_union_dj_def]
  interpretation hisis: set_union_dj hs_\<alpha> hs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar hisis_union_dj using hisis_union_dj_impl .
  definition "alili_union_dj == SetGA.it_union_dj ahs_iteratei lsi_ins_dj"
  lemmas alili_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl lsi_ins_dj_impl, folded alili_union_dj_def]
  interpretation alili: set_union_dj ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_union_dj using alili_union_dj_impl .
  definition "all_union_dj == SetGA.it_union_dj ahs_iteratei ls_ins_dj"
  lemmas all_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl ls_ins_dj_impl, folded all_union_dj_def]
  interpretation all: set_union_dj ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_union_dj using all_union_dj_impl .
  definition "arr_union_dj == SetGA.it_union_dj ahs_iteratei rs_ins_dj"
  lemmas arr_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl rs_ins_dj_impl, folded arr_union_dj_def]
  interpretation arr: set_union_dj ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_union_dj using arr_union_dj_impl .
  definition "ahh_union_dj == SetGA.it_union_dj ahs_iteratei hs_ins_dj"
  lemmas ahh_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl hs_ins_dj_impl, folded ahh_union_dj_def]
  interpretation ahh: set_union_dj ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_union_dj using ahh_union_dj_impl .
  definition "aaa_union_dj == SetGA.it_union_dj ahs_iteratei ahs_ins_dj"
  lemmas aaa_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl ahs_ins_dj_impl, folded aaa_union_dj_def]
  interpretation aaa: set_union_dj ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_union_dj using aaa_union_dj_impl .
  definition "aisis_union_dj == SetGA.it_union_dj ahs_iteratei ias_ins_dj"
  lemmas aisis_union_dj_impl = SetGA.it_union_dj_correct[OF ahs_iteratei_impl ias_ins_dj_impl, folded aisis_union_dj_def]
  interpretation aisis: set_union_dj ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar aisis_union_dj using aisis_union_dj_impl .
  definition "islili_union_dj == SetGA.it_union_dj ias_iteratei lsi_ins_dj"
  lemmas islili_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl lsi_ins_dj_impl, folded islili_union_dj_def]
  interpretation islili: set_union_dj ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar islili_union_dj using islili_union_dj_impl .
  definition "isll_union_dj == SetGA.it_union_dj ias_iteratei ls_ins_dj"
  lemmas isll_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl ls_ins_dj_impl, folded isll_union_dj_def]
  interpretation isll: set_union_dj ias_\<alpha> ias_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar isll_union_dj using isll_union_dj_impl .
  definition "isrr_union_dj == SetGA.it_union_dj ias_iteratei rs_ins_dj"
  lemmas isrr_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl rs_ins_dj_impl, folded isrr_union_dj_def]
  interpretation isrr: set_union_dj ias_\<alpha> ias_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar isrr_union_dj using isrr_union_dj_impl .
  definition "ishh_union_dj == SetGA.it_union_dj ias_iteratei hs_ins_dj"
  lemmas ishh_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl hs_ins_dj_impl, folded ishh_union_dj_def]
  interpretation ishh: set_union_dj ias_\<alpha> ias_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ishh_union_dj using ishh_union_dj_impl .
  definition "isaa_union_dj == SetGA.it_union_dj ias_iteratei ahs_ins_dj"
  lemmas isaa_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl ahs_ins_dj_impl, folded isaa_union_dj_def]
  interpretation isaa: set_union_dj ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar isaa_union_dj using isaa_union_dj_impl .
  definition "isisis_union_dj == SetGA.it_union_dj ias_iteratei ias_ins_dj"
  lemmas isisis_union_dj_impl = SetGA.it_union_dj_correct[OF ias_iteratei_impl ias_ins_dj_impl, folded isisis_union_dj_def]
  interpretation isisis: set_union_dj ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar isisis_union_dj using isisis_union_dj_impl .

  definition "lili_diff == SetGA.it_diff lsi_iteratei lsi_delete"
  lemmas lili_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl lsi_delete_impl, folded lili_diff_def]
  interpretation lili: set_diff lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_diff using lili_diff_impl .
  definition "lli_diff == SetGA.it_diff lsi_iteratei ls_delete"
  lemmas lli_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl ls_delete_impl, folded lli_diff_def]
  interpretation lli: set_diff ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_diff using lli_diff_impl .
  definition "rli_diff == SetGA.it_diff lsi_iteratei rs_delete"
  lemmas rli_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl rs_delete_impl, folded rli_diff_def]
  interpretation rli: set_diff rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_diff using rli_diff_impl .
  definition "hli_diff == SetGA.it_diff lsi_iteratei hs_delete"
  lemmas hli_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl hs_delete_impl, folded hli_diff_def]
  interpretation hli: set_diff hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_diff using hli_diff_impl .
  definition "ali_diff == SetGA.it_diff lsi_iteratei ahs_delete"
  lemmas ali_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl ahs_delete_impl, folded ali_diff_def]
  interpretation ali: set_diff ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_diff using ali_diff_impl .
  definition "isli_diff == SetGA.it_diff lsi_iteratei ias_delete"
  lemmas isli_diff_impl = SetGA.it_diff_correct[OF lsi_iteratei_impl ias_delete_impl, folded isli_diff_def]
  interpretation isli: set_diff ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_diff using isli_diff_impl .
  definition "lil_diff == SetGA.it_diff ls_iteratei lsi_delete"
  lemmas lil_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl lsi_delete_impl, folded lil_diff_def]
  interpretation lil: set_diff lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_diff using lil_diff_impl .
  definition "ll_diff == SetGA.it_diff ls_iteratei ls_delete"
  lemmas ll_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl ls_delete_impl, folded ll_diff_def]
  interpretation ll: set_diff ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_diff using ll_diff_impl .
  definition "rl_diff == SetGA.it_diff ls_iteratei rs_delete"
  lemmas rl_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl rs_delete_impl, folded rl_diff_def]
  interpretation rl: set_diff rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_diff using rl_diff_impl .
  definition "hl_diff == SetGA.it_diff ls_iteratei hs_delete"
  lemmas hl_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl hs_delete_impl, folded hl_diff_def]
  interpretation hl: set_diff hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_diff using hl_diff_impl .
  definition "al_diff == SetGA.it_diff ls_iteratei ahs_delete"
  lemmas al_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl ahs_delete_impl, folded al_diff_def]
  interpretation al: set_diff ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_diff using al_diff_impl .
  definition "isl_diff == SetGA.it_diff ls_iteratei ias_delete"
  lemmas isl_diff_impl = SetGA.it_diff_correct[OF ls_iteratei_impl ias_delete_impl, folded isl_diff_def]
  interpretation isl: set_diff ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_diff using isl_diff_impl .
  definition "lir_diff == SetGA.it_diff rs_iteratei lsi_delete"
  lemmas lir_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl lsi_delete_impl, folded lir_diff_def]
  interpretation lir: set_diff lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_diff using lir_diff_impl .
  definition "lr_diff == SetGA.it_diff rs_iteratei ls_delete"
  lemmas lr_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl ls_delete_impl, folded lr_diff_def]
  interpretation lr: set_diff ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_diff using lr_diff_impl .
  definition "rr_diff == SetGA.it_diff rs_iteratei rs_delete"
  lemmas rr_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl rs_delete_impl, folded rr_diff_def]
  interpretation rr: set_diff rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_diff using rr_diff_impl .
  definition "hr_diff == SetGA.it_diff rs_iteratei hs_delete"
  lemmas hr_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl hs_delete_impl, folded hr_diff_def]
  interpretation hr: set_diff hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_diff using hr_diff_impl .
  definition "ar_diff == SetGA.it_diff rs_iteratei ahs_delete"
  lemmas ar_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl ahs_delete_impl, folded ar_diff_def]
  interpretation ar: set_diff ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_diff using ar_diff_impl .
  definition "isr_diff == SetGA.it_diff rs_iteratei ias_delete"
  lemmas isr_diff_impl = SetGA.it_diff_correct[OF rs_iteratei_impl ias_delete_impl, folded isr_diff_def]
  interpretation isr: set_diff ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_diff using isr_diff_impl .
  definition "lih_diff == SetGA.it_diff hs_iteratei lsi_delete"
  lemmas lih_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl lsi_delete_impl, folded lih_diff_def]
  interpretation lih: set_diff lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_diff using lih_diff_impl .
  definition "lh_diff == SetGA.it_diff hs_iteratei ls_delete"
  lemmas lh_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl ls_delete_impl, folded lh_diff_def]
  interpretation lh: set_diff ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_diff using lh_diff_impl .
  definition "rh_diff == SetGA.it_diff hs_iteratei rs_delete"
  lemmas rh_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl rs_delete_impl, folded rh_diff_def]
  interpretation rh: set_diff rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_diff using rh_diff_impl .
  definition "hh_diff == SetGA.it_diff hs_iteratei hs_delete"
  lemmas hh_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl hs_delete_impl, folded hh_diff_def]
  interpretation hh: set_diff hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_diff using hh_diff_impl .
  definition "ah_diff == SetGA.it_diff hs_iteratei ahs_delete"
  lemmas ah_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl ahs_delete_impl, folded ah_diff_def]
  interpretation ah: set_diff ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_diff using ah_diff_impl .
  definition "ish_diff == SetGA.it_diff hs_iteratei ias_delete"
  lemmas ish_diff_impl = SetGA.it_diff_correct[OF hs_iteratei_impl ias_delete_impl, folded ish_diff_def]
  interpretation ish: set_diff ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_diff using ish_diff_impl .
  definition "lia_diff == SetGA.it_diff ahs_iteratei lsi_delete"
  lemmas lia_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl lsi_delete_impl, folded lia_diff_def]
  interpretation lia: set_diff lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_diff using lia_diff_impl .
  definition "la_diff == SetGA.it_diff ahs_iteratei ls_delete"
  lemmas la_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl ls_delete_impl, folded la_diff_def]
  interpretation la: set_diff ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_diff using la_diff_impl .
  definition "ra_diff == SetGA.it_diff ahs_iteratei rs_delete"
  lemmas ra_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl rs_delete_impl, folded ra_diff_def]
  interpretation ra: set_diff rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_diff using ra_diff_impl .
  definition "ha_diff == SetGA.it_diff ahs_iteratei hs_delete"
  lemmas ha_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl hs_delete_impl, folded ha_diff_def]
  interpretation ha: set_diff hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_diff using ha_diff_impl .
  definition "aa_diff == SetGA.it_diff ahs_iteratei ahs_delete"
  lemmas aa_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl ahs_delete_impl, folded aa_diff_def]
  interpretation aa: set_diff ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_diff using aa_diff_impl .
  definition "isa_diff == SetGA.it_diff ahs_iteratei ias_delete"
  lemmas isa_diff_impl = SetGA.it_diff_correct[OF ahs_iteratei_impl ias_delete_impl, folded isa_diff_def]
  interpretation isa: set_diff ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_diff using isa_diff_impl .
  definition "liis_diff == SetGA.it_diff ias_iteratei lsi_delete"
  lemmas liis_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl lsi_delete_impl, folded liis_diff_def]
  interpretation liis: set_diff lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_diff using liis_diff_impl .
  definition "lis_diff == SetGA.it_diff ias_iteratei ls_delete"
  lemmas lis_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl ls_delete_impl, folded lis_diff_def]
  interpretation lis: set_diff ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_diff using lis_diff_impl .
  definition "ris_diff == SetGA.it_diff ias_iteratei rs_delete"
  lemmas ris_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl rs_delete_impl, folded ris_diff_def]
  interpretation ris: set_diff rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_diff using ris_diff_impl .
  definition "his_diff == SetGA.it_diff ias_iteratei hs_delete"
  lemmas his_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl hs_delete_impl, folded his_diff_def]
  interpretation his: set_diff hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_diff using his_diff_impl .
  definition "ais_diff == SetGA.it_diff ias_iteratei ahs_delete"
  lemmas ais_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl ahs_delete_impl, folded ais_diff_def]
  interpretation ais: set_diff ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_diff using ais_diff_impl .
  definition "isis_diff == SetGA.it_diff ias_iteratei ias_delete"
  lemmas isis_diff_impl = SetGA.it_diff_correct[OF ias_iteratei_impl ias_delete_impl, folded isis_diff_def]
  interpretation isis: set_diff ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_diff using isis_diff_impl .

  definition "lsi_sng == SetGA.ei_sng lsi_empty lsi_ins"
  lemmas lsi_sng_impl = SetGA.ei_sng_correct[OF lsi_empty_impl lsi_ins_impl, folded lsi_sng_def]
  interpretation lsi: set_sng lsi_\<alpha> lsi_invar lsi_sng using lsi_sng_impl .
  definition "ls_sng == SetGA.ei_sng ls_empty ls_ins"
  lemmas ls_sng_impl = SetGA.ei_sng_correct[OF ls_empty_impl ls_ins_impl, folded ls_sng_def]
  interpretation ls: set_sng ls_\<alpha> ls_invar ls_sng using ls_sng_impl .
  definition "rs_sng == SetGA.ei_sng rs_empty rs_ins"
  lemmas rs_sng_impl = SetGA.ei_sng_correct[OF rs_empty_impl rs_ins_impl, folded rs_sng_def]
  interpretation rs: set_sng rs_\<alpha> rs_invar rs_sng using rs_sng_impl .
  definition "hs_sng == SetGA.ei_sng hs_empty hs_ins"
  lemmas hs_sng_impl = SetGA.ei_sng_correct[OF hs_empty_impl hs_ins_impl, folded hs_sng_def]
  interpretation hs: set_sng hs_\<alpha> hs_invar hs_sng using hs_sng_impl .
  definition "ahs_sng == SetGA.ei_sng ahs_empty ahs_ins"
  lemmas ahs_sng_impl = SetGA.ei_sng_correct[OF ahs_empty_impl ahs_ins_impl, folded ahs_sng_def]
  interpretation ahs: set_sng ahs_\<alpha> ahs_invar ahs_sng using ahs_sng_impl .
  definition "ias_sng == SetGA.ei_sng ias_empty ias_ins"
  lemmas ias_sng_impl = SetGA.ei_sng_correct[OF ias_empty_impl ias_ins_impl, folded ias_sng_def]
  interpretation ias: set_sng ias_\<alpha> ias_invar ias_sng using ias_sng_impl .

  definition "lsi_size == SetGA.it_size lsi_iteratei"
  lemmas lsi_size_impl = SetGA.it_size_correct[OF lsi_iteratei_impl, folded lsi_size_def]
  interpretation lsi: set_size lsi_\<alpha> lsi_invar lsi_size using lsi_size_impl .
  definition "ls_size == SetGA.it_size ls_iteratei"
  lemmas ls_size_impl = SetGA.it_size_correct[OF ls_iteratei_impl, folded ls_size_def]
  interpretation ls: set_size ls_\<alpha> ls_invar ls_size using ls_size_impl .
  definition "rs_size == SetGA.it_size rs_iteratei"
  lemmas rs_size_impl = SetGA.it_size_correct[OF rs_iteratei_impl, folded rs_size_def]
  interpretation rs: set_size rs_\<alpha> rs_invar rs_size using rs_size_impl .
  definition "hs_size == SetGA.it_size hs_iteratei"
  lemmas hs_size_impl = SetGA.it_size_correct[OF hs_iteratei_impl, folded hs_size_def]
  interpretation hs: set_size hs_\<alpha> hs_invar hs_size using hs_size_impl .
  definition "ahs_size == SetGA.it_size ahs_iteratei"
  lemmas ahs_size_impl = SetGA.it_size_correct[OF ahs_iteratei_impl, folded ahs_size_def]
  interpretation ahs: set_size ahs_\<alpha> ahs_invar ahs_size using ahs_size_impl .
  definition "ias_size == SetGA.it_size ias_iteratei"
  lemmas ias_size_impl = SetGA.it_size_correct[OF ias_iteratei_impl, folded ias_size_def]
  interpretation ias: set_size ias_\<alpha> ias_invar ias_size using ias_size_impl .

  definition "lsi_size_abort == SetGA.iti_size_abort lsi_iteratei"
  lemmas lsi_size_abort_impl = SetGA.iti_size_abort_correct[OF lsi_iteratei_impl, folded lsi_size_abort_def]
  interpretation lsi: set_size_abort lsi_\<alpha> lsi_invar lsi_size_abort using lsi_size_abort_impl .
  definition "ls_size_abort == SetGA.iti_size_abort ls_iteratei"
  lemmas ls_size_abort_impl = SetGA.iti_size_abort_correct[OF ls_iteratei_impl, folded ls_size_abort_def]
  interpretation ls: set_size_abort ls_\<alpha> ls_invar ls_size_abort using ls_size_abort_impl .
  definition "rs_size_abort == SetGA.iti_size_abort rs_iteratei"
  lemmas rs_size_abort_impl = SetGA.iti_size_abort_correct[OF rs_iteratei_impl, folded rs_size_abort_def]
  interpretation rs: set_size_abort rs_\<alpha> rs_invar rs_size_abort using rs_size_abort_impl .
  definition "hs_size_abort == SetGA.iti_size_abort hs_iteratei"
  lemmas hs_size_abort_impl = SetGA.iti_size_abort_correct[OF hs_iteratei_impl, folded hs_size_abort_def]
  interpretation hs: set_size_abort hs_\<alpha> hs_invar hs_size_abort using hs_size_abort_impl .
  definition "ahs_size_abort == SetGA.iti_size_abort ahs_iteratei"
  lemmas ahs_size_abort_impl = SetGA.iti_size_abort_correct[OF ahs_iteratei_impl, folded ahs_size_abort_def]
  interpretation ahs: set_size_abort ahs_\<alpha> ahs_invar ahs_size_abort using ahs_size_abort_impl .
  definition "ias_size_abort == SetGA.iti_size_abort ias_iteratei"
  lemmas ias_size_abort_impl = SetGA.iti_size_abort_correct[OF ias_iteratei_impl, folded ias_size_abort_def]
  interpretation ias: set_size_abort ias_\<alpha> ias_invar ias_size_abort using ias_size_abort_impl .

  definition "lsi_isSng == SetGA.sza_isSng lsi_iteratei"
  lemmas lsi_isSng_impl = SetGA.sza_isSng_correct[OF lsi_iteratei_impl, folded lsi_isSng_def]
  interpretation lsi: set_isSng lsi_\<alpha> lsi_invar lsi_isSng using lsi_isSng_impl .
  definition "ls_isSng == SetGA.sza_isSng ls_iteratei"
  lemmas ls_isSng_impl = SetGA.sza_isSng_correct[OF ls_iteratei_impl, folded ls_isSng_def]
  interpretation ls: set_isSng ls_\<alpha> ls_invar ls_isSng using ls_isSng_impl .
  definition "rs_isSng == SetGA.sza_isSng rs_iteratei"
  lemmas rs_isSng_impl = SetGA.sza_isSng_correct[OF rs_iteratei_impl, folded rs_isSng_def]
  interpretation rs: set_isSng rs_\<alpha> rs_invar rs_isSng using rs_isSng_impl .
  definition "hs_isSng == SetGA.sza_isSng hs_iteratei"
  lemmas hs_isSng_impl = SetGA.sza_isSng_correct[OF hs_iteratei_impl, folded hs_isSng_def]
  interpretation hs: set_isSng hs_\<alpha> hs_invar hs_isSng using hs_isSng_impl .
  definition "ahs_isSng == SetGA.sza_isSng ahs_iteratei"
  lemmas ahs_isSng_impl = SetGA.sza_isSng_correct[OF ahs_iteratei_impl, folded ahs_isSng_def]
  interpretation ahs: set_isSng ahs_\<alpha> ahs_invar ahs_isSng using ahs_isSng_impl .
  definition "ias_isSng == SetGA.sza_isSng ias_iteratei"
  lemmas ias_isSng_impl = SetGA.sza_isSng_correct[OF ias_iteratei_impl, folded ias_isSng_def]
  interpretation ias: set_isSng ias_\<alpha> ias_invar ias_isSng using ias_isSng_impl .

  definition "lsi_ball == SetGA.iti_ball lsi_iteratei"
  lemmas lsi_ball_impl = SetGA.iti_ball_correct[OF lsi_iteratei_impl, folded lsi_ball_def]
  interpretation lsi: set_ball lsi_\<alpha> lsi_invar lsi_ball using lsi_ball_impl .
  definition "ls_ball == SetGA.iti_ball ls_iteratei"
  lemmas ls_ball_impl = SetGA.iti_ball_correct[OF ls_iteratei_impl, folded ls_ball_def]
  interpretation ls: set_ball ls_\<alpha> ls_invar ls_ball using ls_ball_impl .
  definition "rs_ball == SetGA.iti_ball rs_iteratei"
  lemmas rs_ball_impl = SetGA.iti_ball_correct[OF rs_iteratei_impl, folded rs_ball_def]
  interpretation rs: set_ball rs_\<alpha> rs_invar rs_ball using rs_ball_impl .
  definition "hs_ball == SetGA.iti_ball hs_iteratei"
  lemmas hs_ball_impl = SetGA.iti_ball_correct[OF hs_iteratei_impl, folded hs_ball_def]
  interpretation hs: set_ball hs_\<alpha> hs_invar hs_ball using hs_ball_impl .
  definition "ahs_ball == SetGA.iti_ball ahs_iteratei"
  lemmas ahs_ball_impl = SetGA.iti_ball_correct[OF ahs_iteratei_impl, folded ahs_ball_def]
  interpretation ahs: set_ball ahs_\<alpha> ahs_invar ahs_ball using ahs_ball_impl .
  definition "ias_ball == SetGA.iti_ball ias_iteratei"
  lemmas ias_ball_impl = SetGA.iti_ball_correct[OF ias_iteratei_impl, folded ias_ball_def]
  interpretation ias: set_ball ias_\<alpha> ias_invar ias_ball using ias_ball_impl .

  definition "lsi_bexists == SetGA.neg_ball_bexists lsi_ball"
  lemmas lsi_bexists_impl = SetGA.neg_ball_bexists_correct[OF lsi_ball_impl, folded lsi_bexists_def]
  interpretation lsi: set_bexists lsi_\<alpha> lsi_invar lsi_bexists using lsi_bexists_impl .
  definition "ls_bexists == SetGA.neg_ball_bexists ls_ball"
  lemmas ls_bexists_impl = SetGA.neg_ball_bexists_correct[OF ls_ball_impl, folded ls_bexists_def]
  interpretation ls: set_bexists ls_\<alpha> ls_invar ls_bexists using ls_bexists_impl .
  definition "rs_bexists == SetGA.neg_ball_bexists rs_ball"
  lemmas rs_bexists_impl = SetGA.neg_ball_bexists_correct[OF rs_ball_impl, folded rs_bexists_def]
  interpretation rs: set_bexists rs_\<alpha> rs_invar rs_bexists using rs_bexists_impl .
  definition "hs_bexists == SetGA.neg_ball_bexists hs_ball"
  lemmas hs_bexists_impl = SetGA.neg_ball_bexists_correct[OF hs_ball_impl, folded hs_bexists_def]
  interpretation hs: set_bexists hs_\<alpha> hs_invar hs_bexists using hs_bexists_impl .
  definition "ahs_bexists == SetGA.neg_ball_bexists ahs_ball"
  lemmas ahs_bexists_impl = SetGA.neg_ball_bexists_correct[OF ahs_ball_impl, folded ahs_bexists_def]
  interpretation ahs: set_bexists ahs_\<alpha> ahs_invar ahs_bexists using ahs_bexists_impl .
  definition "ias_bexists == SetGA.neg_ball_bexists ias_ball"
  lemmas ias_bexists_impl = SetGA.neg_ball_bexists_correct[OF ias_ball_impl, folded ias_bexists_def]
  interpretation ias: set_bexists ias_\<alpha> ias_invar ias_bexists using ias_bexists_impl .

  definition "lilili_inter == SetGA.it_inter lsi_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas lilili_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_inter_def]
  interpretation lilili: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_inter using lilili_inter_impl .
  definition "lilil_inter == SetGA.it_inter lsi_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas lilil_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded lilil_inter_def]
  interpretation lilil: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lilil_inter using lilil_inter_impl .
  definition "lilir_inter == SetGA.it_inter lsi_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas lilir_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded lilir_inter_def]
  interpretation lilir: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lilir_inter using lilir_inter_impl .
  definition "lilih_inter == SetGA.it_inter lsi_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas lilih_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded lilih_inter_def]
  interpretation lilih: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lilih_inter using lilih_inter_impl .
  definition "lilia_inter == SetGA.it_inter lsi_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas lilia_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_inter_def]
  interpretation lilia: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lilia_inter using lilia_inter_impl .
  definition "liliis_inter == SetGA.it_inter lsi_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas liliis_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded liliis_inter_def]
  interpretation liliis: set_inter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liliis_inter using liliis_inter_impl .
  definition "lilli_inter == SetGA.it_inter lsi_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas lilli_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_inter_def]
  interpretation lilli: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lilli_inter using lilli_inter_impl .
  definition "lill_inter == SetGA.it_inter lsi_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas lill_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded lill_inter_def]
  interpretation lill: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_inter using lill_inter_impl .
  definition "lilr_inter == SetGA.it_inter lsi_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas lilr_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded lilr_inter_def]
  interpretation lilr: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar lilr_inter using lilr_inter_impl .
  definition "lilh_inter == SetGA.it_inter lsi_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas lilh_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded lilh_inter_def]
  interpretation lilh: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar lilh_inter using lilh_inter_impl .
  definition "lila_inter == SetGA.it_inter lsi_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas lila_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_inter_def]
  interpretation lila: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lila_inter using lila_inter_impl .
  definition "lilis_inter == SetGA.it_inter lsi_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas lilis_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded lilis_inter_def]
  interpretation lilis: set_inter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar lilis_inter using lilis_inter_impl .
  definition "lirli_inter == SetGA.it_inter lsi_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas lirli_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_inter_def]
  interpretation lirli: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lirli_inter using lirli_inter_impl .
  definition "lirl_inter == SetGA.it_inter lsi_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas lirl_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lirl_inter_def]
  interpretation lirl: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lirl_inter using lirl_inter_impl .
  definition "lirr_inter == SetGA.it_inter lsi_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas lirr_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lirr_inter_def]
  interpretation lirr: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_inter using lirr_inter_impl .
  definition "lirh_inter == SetGA.it_inter lsi_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas lirh_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lirh_inter_def]
  interpretation lirh: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lirh_inter using lirh_inter_impl .
  definition "lira_inter == SetGA.it_inter lsi_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas lira_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_inter_def]
  interpretation lira: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lira_inter using lira_inter_impl .
  definition "liris_inter == SetGA.it_inter lsi_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas liris_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded liris_inter_def]
  interpretation liris: set_inter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar liris_inter using liris_inter_impl .
  definition "lihli_inter == SetGA.it_inter lsi_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas lihli_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_inter_def]
  interpretation lihli: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lihli_inter using lihli_inter_impl .
  definition "lihl_inter == SetGA.it_inter lsi_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas lihl_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lihl_inter_def]
  interpretation lihl: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lihl_inter using lihl_inter_impl .
  definition "lihr_inter == SetGA.it_inter lsi_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas lihr_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lihr_inter_def]
  interpretation lihr: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lihr_inter using lihr_inter_impl .
  definition "lihh_inter == SetGA.it_inter lsi_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas lihh_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lihh_inter_def]
  interpretation lihh: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_inter using lihh_inter_impl .
  definition "liha_inter == SetGA.it_inter lsi_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas liha_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_inter_def]
  interpretation liha: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar liha_inter using liha_inter_impl .
  definition "lihis_inter == SetGA.it_inter lsi_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas lihis_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded lihis_inter_def]
  interpretation lihis: set_inter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar lihis_inter using lihis_inter_impl .
  definition "liali_inter == SetGA.it_inter lsi_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas liali_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_inter_def]
  interpretation liali: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar liali_inter using liali_inter_impl .
  definition "lial_inter == SetGA.it_inter lsi_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas lial_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lial_inter_def]
  interpretation lial: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lial_inter using lial_inter_impl .
  definition "liar_inter == SetGA.it_inter lsi_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas liar_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded liar_inter_def]
  interpretation liar: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar liar_inter using liar_inter_impl .
  definition "liah_inter == SetGA.it_inter lsi_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas liah_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded liah_inter_def]
  interpretation liah: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar liah_inter using liah_inter_impl .
  definition "liaa_inter == SetGA.it_inter lsi_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas liaa_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_inter_def]
  interpretation liaa: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_inter using liaa_inter_impl .
  definition "liais_inter == SetGA.it_inter lsi_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas liais_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded liais_inter_def]
  interpretation liais: set_inter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar liais_inter using liais_inter_impl .
  definition "liisli_inter == SetGA.it_inter lsi_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas liisli_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded liisli_inter_def]
  interpretation liisli: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar liisli_inter using liisli_inter_impl .
  definition "liisl_inter == SetGA.it_inter lsi_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas liisl_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded liisl_inter_def]
  interpretation liisl: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar liisl_inter using liisl_inter_impl .
  definition "liisr_inter == SetGA.it_inter lsi_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas liisr_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded liisr_inter_def]
  interpretation liisr: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar liisr_inter using liisr_inter_impl .
  definition "liish_inter == SetGA.it_inter lsi_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas liish_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded liish_inter_def]
  interpretation liish: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar liish_inter using liish_inter_impl .
  definition "liisa_inter == SetGA.it_inter lsi_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas liisa_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded liisa_inter_def]
  interpretation liisa: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar liisa_inter using liisa_inter_impl .
  definition "liisis_inter == SetGA.it_inter lsi_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas liisis_inter_impl = SetGA.it_inter_correct[OF lsi_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded liisis_inter_def]
  interpretation liisis: set_inter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar liisis_inter using liisis_inter_impl .
  definition "llili_inter == SetGA.it_inter ls_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas llili_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_inter_def]
  interpretation llili: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_inter using llili_inter_impl .
  definition "llil_inter == SetGA.it_inter ls_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas llil_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded llil_inter_def]
  interpretation llil: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar llil_inter using llil_inter_impl .
  definition "llir_inter == SetGA.it_inter ls_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas llir_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded llir_inter_def]
  interpretation llir: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar llir_inter using llir_inter_impl .
  definition "llih_inter == SetGA.it_inter ls_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas llih_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded llih_inter_def]
  interpretation llih: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar llih_inter using llih_inter_impl .
  definition "llia_inter == SetGA.it_inter ls_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas llia_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_inter_def]
  interpretation llia: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar llia_inter using llia_inter_impl .
  definition "lliis_inter == SetGA.it_inter ls_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas lliis_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded lliis_inter_def]
  interpretation lliis: set_inter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar lliis_inter using lliis_inter_impl .
  definition "llli_inter == SetGA.it_inter ls_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas llli_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_inter_def]
  interpretation llli: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar llli_inter using llli_inter_impl .
  definition "lll_inter == SetGA.it_inter ls_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas lll_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded lll_inter_def]
  interpretation lll: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_inter using lll_inter_impl .
  definition "llr_inter == SetGA.it_inter ls_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas llr_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded llr_inter_def]
  interpretation llr: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_inter using llr_inter_impl .
  definition "llh_inter == SetGA.it_inter ls_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas llh_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded llh_inter_def]
  interpretation llh: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_inter using llh_inter_impl .
  definition "lla_inter == SetGA.it_inter ls_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas lla_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_inter_def]
  interpretation lla: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lla_inter using lla_inter_impl .
  definition "llis_inter == SetGA.it_inter ls_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas llis_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded llis_inter_def]
  interpretation llis: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar llis_inter using llis_inter_impl .
  definition "lrli_inter == SetGA.it_inter ls_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas lrli_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_inter_def]
  interpretation lrli: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lrli_inter using lrli_inter_impl .
  definition "lrl_inter == SetGA.it_inter ls_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas lrl_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inter_def]
  interpretation lrl: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_inter using lrl_inter_impl .
  definition "lrr_inter == SetGA.it_inter ls_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas lrr_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inter_def]
  interpretation lrr: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_inter using lrr_inter_impl .
  definition "lrh_inter == SetGA.it_inter ls_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas lrh_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inter_def]
  interpretation lrh: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_inter using lrh_inter_impl .
  definition "lra_inter == SetGA.it_inter ls_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas lra_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_inter_def]
  interpretation lra: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lra_inter using lra_inter_impl .
  definition "lris_inter == SetGA.it_inter ls_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas lris_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded lris_inter_def]
  interpretation lris: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar lris_inter using lris_inter_impl .
  definition "lhli_inter == SetGA.it_inter ls_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas lhli_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_inter_def]
  interpretation lhli: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lhli_inter using lhli_inter_impl .
  definition "lhl_inter == SetGA.it_inter ls_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas lhl_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inter_def]
  interpretation lhl: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_inter using lhl_inter_impl .
  definition "lhr_inter == SetGA.it_inter ls_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas lhr_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inter_def]
  interpretation lhr: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_inter using lhr_inter_impl .
  definition "lhh_inter == SetGA.it_inter ls_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas lhh_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inter_def]
  interpretation lhh: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_inter using lhh_inter_impl .
  definition "lha_inter == SetGA.it_inter ls_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas lha_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_inter_def]
  interpretation lha: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lha_inter using lha_inter_impl .
  definition "lhis_inter == SetGA.it_inter ls_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas lhis_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded lhis_inter_def]
  interpretation lhis: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar lhis_inter using lhis_inter_impl .
  definition "lali_inter == SetGA.it_inter ls_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas lali_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_inter_def]
  interpretation lali: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lali_inter using lali_inter_impl .
  definition "lal_inter == SetGA.it_inter ls_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas lal_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lal_inter_def]
  interpretation lal: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lal_inter using lal_inter_impl .
  definition "lar_inter == SetGA.it_inter ls_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas lar_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lar_inter_def]
  interpretation lar: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lar_inter using lar_inter_impl .
  definition "lah_inter == SetGA.it_inter ls_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas lah_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lah_inter_def]
  interpretation lah: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lah_inter using lah_inter_impl .
  definition "laa_inter == SetGA.it_inter ls_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas laa_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_inter_def]
  interpretation laa: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_inter using laa_inter_impl .
  definition "lais_inter == SetGA.it_inter ls_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas lais_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded lais_inter_def]
  interpretation lais: set_inter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar lais_inter using lais_inter_impl .
  definition "lisli_inter == SetGA.it_inter ls_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas lisli_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded lisli_inter_def]
  interpretation lisli: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lisli_inter using lisli_inter_impl .
  definition "lisl_inter == SetGA.it_inter ls_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas lisl_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded lisl_inter_def]
  interpretation lisl: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar lisl_inter using lisl_inter_impl .
  definition "lisr_inter == SetGA.it_inter ls_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas lisr_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded lisr_inter_def]
  interpretation lisr: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar lisr_inter using lisr_inter_impl .
  definition "lish_inter == SetGA.it_inter ls_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas lish_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded lish_inter_def]
  interpretation lish: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar lish_inter using lish_inter_impl .
  definition "lisa_inter == SetGA.it_inter ls_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas lisa_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded lisa_inter_def]
  interpretation lisa: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar lisa_inter using lisa_inter_impl .
  definition "lisis_inter == SetGA.it_inter ls_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas lisis_inter_impl = SetGA.it_inter_correct[OF ls_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded lisis_inter_def]
  interpretation lisis: set_inter ls_\<alpha> ls_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar lisis_inter using lisis_inter_impl .
  definition "rlili_inter == SetGA.it_inter rs_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas rlili_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_inter_def]
  interpretation rlili: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_inter using rlili_inter_impl .
  definition "rlil_inter == SetGA.it_inter rs_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas rlil_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded rlil_inter_def]
  interpretation rlil: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rlil_inter using rlil_inter_impl .
  definition "rlir_inter == SetGA.it_inter rs_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas rlir_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded rlir_inter_def]
  interpretation rlir: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rlir_inter using rlir_inter_impl .
  definition "rlih_inter == SetGA.it_inter rs_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas rlih_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded rlih_inter_def]
  interpretation rlih: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rlih_inter using rlih_inter_impl .
  definition "rlia_inter == SetGA.it_inter rs_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas rlia_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_inter_def]
  interpretation rlia: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rlia_inter using rlia_inter_impl .
  definition "rliis_inter == SetGA.it_inter rs_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas rliis_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded rliis_inter_def]
  interpretation rliis: set_inter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar rliis_inter using rliis_inter_impl .
  definition "rlli_inter == SetGA.it_inter rs_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas rlli_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_inter_def]
  interpretation rlli: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rlli_inter using rlli_inter_impl .
  definition "rll_inter == SetGA.it_inter rs_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas rll_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded rll_inter_def]
  interpretation rll: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_inter using rll_inter_impl .
  definition "rlr_inter == SetGA.it_inter rs_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas rlr_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inter_def]
  interpretation rlr: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_inter using rlr_inter_impl .
  definition "rlh_inter == SetGA.it_inter rs_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas rlh_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inter_def]
  interpretation rlh: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_inter using rlh_inter_impl .
  definition "rla_inter == SetGA.it_inter rs_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas rla_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_inter_def]
  interpretation rla: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rla_inter using rla_inter_impl .
  definition "rlis_inter == SetGA.it_inter rs_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas rlis_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded rlis_inter_def]
  interpretation rlis: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar rlis_inter using rlis_inter_impl .
  definition "rrli_inter == SetGA.it_inter rs_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas rrli_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_inter_def]
  interpretation rrli: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rrli_inter using rrli_inter_impl .
  definition "rrl_inter == SetGA.it_inter rs_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas rrl_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inter_def]
  interpretation rrl: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_inter using rrl_inter_impl .
  definition "rrr_inter == SetGA.it_inter rs_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas rrr_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inter_def]
  interpretation rrr: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_inter using rrr_inter_impl .
  definition "rrh_inter == SetGA.it_inter rs_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas rrh_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inter_def]
  interpretation rrh: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_inter using rrh_inter_impl .
  definition "rra_inter == SetGA.it_inter rs_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas rra_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_inter_def]
  interpretation rra: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rra_inter using rra_inter_impl .
  definition "rris_inter == SetGA.it_inter rs_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas rris_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded rris_inter_def]
  interpretation rris: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar rris_inter using rris_inter_impl .
  definition "rhli_inter == SetGA.it_inter rs_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas rhli_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_inter_def]
  interpretation rhli: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rhli_inter using rhli_inter_impl .
  definition "rhl_inter == SetGA.it_inter rs_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas rhl_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inter_def]
  interpretation rhl: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_inter using rhl_inter_impl .
  definition "rhr_inter == SetGA.it_inter rs_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas rhr_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inter_def]
  interpretation rhr: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_inter using rhr_inter_impl .
  definition "rhh_inter == SetGA.it_inter rs_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas rhh_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inter_def]
  interpretation rhh: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_inter using rhh_inter_impl .
  definition "rha_inter == SetGA.it_inter rs_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas rha_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_inter_def]
  interpretation rha: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rha_inter using rha_inter_impl .
  definition "rhis_inter == SetGA.it_inter rs_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas rhis_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded rhis_inter_def]
  interpretation rhis: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar rhis_inter using rhis_inter_impl .
  definition "rali_inter == SetGA.it_inter rs_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas rali_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_inter_def]
  interpretation rali: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rali_inter using rali_inter_impl .
  definition "ral_inter == SetGA.it_inter rs_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas ral_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded ral_inter_def]
  interpretation ral: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ral_inter using ral_inter_impl .
  definition "rar_inter == SetGA.it_inter rs_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas rar_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rar_inter_def]
  interpretation rar: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rar_inter using rar_inter_impl .
  definition "rah_inter == SetGA.it_inter rs_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas rah_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rah_inter_def]
  interpretation rah: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rah_inter using rah_inter_impl .
  definition "raa_inter == SetGA.it_inter rs_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas raa_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_inter_def]
  interpretation raa: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_inter using raa_inter_impl .
  definition "rais_inter == SetGA.it_inter rs_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas rais_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded rais_inter_def]
  interpretation rais: set_inter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar rais_inter using rais_inter_impl .
  definition "risli_inter == SetGA.it_inter rs_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas risli_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded risli_inter_def]
  interpretation risli: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar risli_inter using risli_inter_impl .
  definition "risl_inter == SetGA.it_inter rs_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas risl_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded risl_inter_def]
  interpretation risl: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar risl_inter using risl_inter_impl .
  definition "risr_inter == SetGA.it_inter rs_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas risr_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded risr_inter_def]
  interpretation risr: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar risr_inter using risr_inter_impl .
  definition "rish_inter == SetGA.it_inter rs_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas rish_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded rish_inter_def]
  interpretation rish: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar rish_inter using rish_inter_impl .
  definition "risa_inter == SetGA.it_inter rs_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas risa_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded risa_inter_def]
  interpretation risa: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar risa_inter using risa_inter_impl .
  definition "risis_inter == SetGA.it_inter rs_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas risis_inter_impl = SetGA.it_inter_correct[OF rs_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded risis_inter_def]
  interpretation risis: set_inter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar risis_inter using risis_inter_impl .
  definition "hlili_inter == SetGA.it_inter hs_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas hlili_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_inter_def]
  interpretation hlili: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_inter using hlili_inter_impl .
  definition "hlil_inter == SetGA.it_inter hs_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas hlil_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded hlil_inter_def]
  interpretation hlil: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hlil_inter using hlil_inter_impl .
  definition "hlir_inter == SetGA.it_inter hs_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas hlir_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded hlir_inter_def]
  interpretation hlir: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hlir_inter using hlir_inter_impl .
  definition "hlih_inter == SetGA.it_inter hs_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas hlih_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded hlih_inter_def]
  interpretation hlih: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hlih_inter using hlih_inter_impl .
  definition "hlia_inter == SetGA.it_inter hs_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas hlia_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_inter_def]
  interpretation hlia: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hlia_inter using hlia_inter_impl .
  definition "hliis_inter == SetGA.it_inter hs_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas hliis_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded hliis_inter_def]
  interpretation hliis: set_inter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar hliis_inter using hliis_inter_impl .
  definition "hlli_inter == SetGA.it_inter hs_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas hlli_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_inter_def]
  interpretation hlli: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hlli_inter using hlli_inter_impl .
  definition "hll_inter == SetGA.it_inter hs_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas hll_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded hll_inter_def]
  interpretation hll: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_inter using hll_inter_impl .
  definition "hlr_inter == SetGA.it_inter hs_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas hlr_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inter_def]
  interpretation hlr: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_inter using hlr_inter_impl .
  definition "hlh_inter == SetGA.it_inter hs_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas hlh_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inter_def]
  interpretation hlh: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_inter using hlh_inter_impl .
  definition "hla_inter == SetGA.it_inter hs_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas hla_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_inter_def]
  interpretation hla: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hla_inter using hla_inter_impl .
  definition "hlis_inter == SetGA.it_inter hs_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas hlis_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded hlis_inter_def]
  interpretation hlis: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar hlis_inter using hlis_inter_impl .
  definition "hrli_inter == SetGA.it_inter hs_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas hrli_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_inter_def]
  interpretation hrli: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hrli_inter using hrli_inter_impl .
  definition "hrl_inter == SetGA.it_inter hs_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas hrl_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inter_def]
  interpretation hrl: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_inter using hrl_inter_impl .
  definition "hrr_inter == SetGA.it_inter hs_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas hrr_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inter_def]
  interpretation hrr: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_inter using hrr_inter_impl .
  definition "hrh_inter == SetGA.it_inter hs_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas hrh_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inter_def]
  interpretation hrh: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_inter using hrh_inter_impl .
  definition "hra_inter == SetGA.it_inter hs_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas hra_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_inter_def]
  interpretation hra: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hra_inter using hra_inter_impl .
  definition "hris_inter == SetGA.it_inter hs_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas hris_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded hris_inter_def]
  interpretation hris: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar hris_inter using hris_inter_impl .
  definition "hhli_inter == SetGA.it_inter hs_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas hhli_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_inter_def]
  interpretation hhli: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hhli_inter using hhli_inter_impl .
  definition "hhl_inter == SetGA.it_inter hs_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas hhl_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inter_def]
  interpretation hhl: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_inter using hhl_inter_impl .
  definition "hhr_inter == SetGA.it_inter hs_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas hhr_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inter_def]
  interpretation hhr: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_inter using hhr_inter_impl .
  definition "hhh_inter == SetGA.it_inter hs_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas hhh_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inter_def]
  interpretation hhh: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_inter using hhh_inter_impl .
  definition "hha_inter == SetGA.it_inter hs_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas hha_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_inter_def]
  interpretation hha: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hha_inter using hha_inter_impl .
  definition "hhis_inter == SetGA.it_inter hs_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas hhis_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded hhis_inter_def]
  interpretation hhis: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar hhis_inter using hhis_inter_impl .
  definition "hali_inter == SetGA.it_inter hs_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas hali_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_inter_def]
  interpretation hali: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hali_inter using hali_inter_impl .
  definition "hal_inter == SetGA.it_inter hs_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas hal_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hal_inter_def]
  interpretation hal: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hal_inter using hal_inter_impl .
  definition "har_inter == SetGA.it_inter hs_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas har_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded har_inter_def]
  interpretation har: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar har_inter using har_inter_impl .
  definition "hah_inter == SetGA.it_inter hs_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas hah_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hah_inter_def]
  interpretation hah: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hah_inter using hah_inter_impl .
  definition "haa_inter == SetGA.it_inter hs_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas haa_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_inter_def]
  interpretation haa: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_inter using haa_inter_impl .
  definition "hais_inter == SetGA.it_inter hs_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas hais_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded hais_inter_def]
  interpretation hais: set_inter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar hais_inter using hais_inter_impl .
  definition "hisli_inter == SetGA.it_inter hs_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas hisli_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded hisli_inter_def]
  interpretation hisli: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar hisli_inter using hisli_inter_impl .
  definition "hisl_inter == SetGA.it_inter hs_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas hisl_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded hisl_inter_def]
  interpretation hisl: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar hisl_inter using hisl_inter_impl .
  definition "hisr_inter == SetGA.it_inter hs_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas hisr_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded hisr_inter_def]
  interpretation hisr: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar hisr_inter using hisr_inter_impl .
  definition "hish_inter == SetGA.it_inter hs_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas hish_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded hish_inter_def]
  interpretation hish: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar hish_inter using hish_inter_impl .
  definition "hisa_inter == SetGA.it_inter hs_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas hisa_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded hisa_inter_def]
  interpretation hisa: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar hisa_inter using hisa_inter_impl .
  definition "hisis_inter == SetGA.it_inter hs_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas hisis_inter_impl = SetGA.it_inter_correct[OF hs_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded hisis_inter_def]
  interpretation hisis: set_inter hs_\<alpha> hs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar hisis_inter using hisis_inter_impl .
  definition "alili_inter == SetGA.it_inter ahs_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas alili_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_inter_def]
  interpretation alili: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_inter using alili_inter_impl .
  definition "alil_inter == SetGA.it_inter ahs_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas alil_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded alil_inter_def]
  interpretation alil: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar alil_inter using alil_inter_impl .
  definition "alir_inter == SetGA.it_inter ahs_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas alir_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded alir_inter_def]
  interpretation alir: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar alir_inter using alir_inter_impl .
  definition "alih_inter == SetGA.it_inter ahs_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas alih_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded alih_inter_def]
  interpretation alih: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar alih_inter using alih_inter_impl .
  definition "alia_inter == SetGA.it_inter ahs_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas alia_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_inter_def]
  interpretation alia: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar alia_inter using alia_inter_impl .
  definition "aliis_inter == SetGA.it_inter ahs_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas aliis_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded aliis_inter_def]
  interpretation aliis: set_inter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar aliis_inter using aliis_inter_impl .
  definition "alli_inter == SetGA.it_inter ahs_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas alli_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_inter_def]
  interpretation alli: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar alli_inter using alli_inter_impl .
  definition "all_inter == SetGA.it_inter ahs_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas all_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded all_inter_def]
  interpretation all: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_inter using all_inter_impl .
  definition "alr_inter == SetGA.it_inter ahs_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas alr_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded alr_inter_def]
  interpretation alr: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar alr_inter using alr_inter_impl .
  definition "alh_inter == SetGA.it_inter ahs_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas alh_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded alh_inter_def]
  interpretation alh: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar alh_inter using alh_inter_impl .
  definition "ala_inter == SetGA.it_inter ahs_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas ala_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_inter_def]
  interpretation ala: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ala_inter using ala_inter_impl .
  definition "alis_inter == SetGA.it_inter ahs_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas alis_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded alis_inter_def]
  interpretation alis: set_inter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar alis_inter using alis_inter_impl .
  definition "arli_inter == SetGA.it_inter ahs_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas arli_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_inter_def]
  interpretation arli: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar arli_inter using arli_inter_impl .
  definition "arl_inter == SetGA.it_inter ahs_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas arl_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded arl_inter_def]
  interpretation arl: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar arl_inter using arl_inter_impl .
  definition "arr_inter == SetGA.it_inter ahs_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas arr_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded arr_inter_def]
  interpretation arr: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_inter using arr_inter_impl .
  definition "arh_inter == SetGA.it_inter ahs_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas arh_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded arh_inter_def]
  interpretation arh: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar arh_inter using arh_inter_impl .
  definition "ara_inter == SetGA.it_inter ahs_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas ara_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_inter_def]
  interpretation ara: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ara_inter using ara_inter_impl .
  definition "aris_inter == SetGA.it_inter ahs_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas aris_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded aris_inter_def]
  interpretation aris: set_inter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar aris_inter using aris_inter_impl .
  definition "ahli_inter == SetGA.it_inter ahs_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas ahli_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_inter_def]
  interpretation ahli: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahli_inter using ahli_inter_impl .
  definition "ahl_inter == SetGA.it_inter ahs_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas ahl_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded ahl_inter_def]
  interpretation ahl: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahl_inter using ahl_inter_impl .
  definition "ahr_inter == SetGA.it_inter ahs_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas ahr_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded ahr_inter_def]
  interpretation ahr: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahr_inter using ahr_inter_impl .
  definition "ahh_inter == SetGA.it_inter ahs_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas ahh_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded ahh_inter_def]
  interpretation ahh: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_inter using ahh_inter_impl .
  definition "aha_inter == SetGA.it_inter ahs_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas aha_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_inter_def]
  interpretation aha: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar aha_inter using aha_inter_impl .
  definition "ahis_inter == SetGA.it_inter ahs_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas ahis_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded ahis_inter_def]
  interpretation ahis: set_inter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar ahis_inter using ahis_inter_impl .
  definition "aali_inter == SetGA.it_inter ahs_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas aali_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_inter_def]
  interpretation aali: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar aali_inter using aali_inter_impl .
  definition "aal_inter == SetGA.it_inter ahs_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas aal_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded aal_inter_def]
  interpretation aal: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar aal_inter using aal_inter_impl .
  definition "aar_inter == SetGA.it_inter ahs_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas aar_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded aar_inter_def]
  interpretation aar: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar aar_inter using aar_inter_impl .
  definition "aah_inter == SetGA.it_inter ahs_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas aah_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded aah_inter_def]
  interpretation aah: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar aah_inter using aah_inter_impl .
  definition "aaa_inter == SetGA.it_inter ahs_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas aaa_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_inter_def]
  interpretation aaa: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_inter using aaa_inter_impl .
  definition "aais_inter == SetGA.it_inter ahs_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas aais_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded aais_inter_def]
  interpretation aais: set_inter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar aais_inter using aais_inter_impl .
  definition "aisli_inter == SetGA.it_inter ahs_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas aisli_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded aisli_inter_def]
  interpretation aisli: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar aisli_inter using aisli_inter_impl .
  definition "aisl_inter == SetGA.it_inter ahs_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas aisl_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded aisl_inter_def]
  interpretation aisl: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar aisl_inter using aisl_inter_impl .
  definition "aisr_inter == SetGA.it_inter ahs_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas aisr_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded aisr_inter_def]
  interpretation aisr: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar aisr_inter using aisr_inter_impl .
  definition "aish_inter == SetGA.it_inter ahs_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas aish_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded aish_inter_def]
  interpretation aish: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar aish_inter using aish_inter_impl .
  definition "aisa_inter == SetGA.it_inter ahs_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas aisa_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded aisa_inter_def]
  interpretation aisa: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar aisa_inter using aisa_inter_impl .
  definition "aisis_inter == SetGA.it_inter ahs_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas aisis_inter_impl = SetGA.it_inter_correct[OF ahs_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded aisis_inter_def]
  interpretation aisis: set_inter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar aisis_inter using aisis_inter_impl .
  definition "islili_inter == SetGA.it_inter ias_iteratei lsi_memb lsi_empty lsi_ins_dj"
  lemmas islili_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded islili_inter_def]
  interpretation islili: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar islili_inter using islili_inter_impl .
  definition "islil_inter == SetGA.it_inter ias_iteratei lsi_memb ls_empty ls_ins_dj"
  lemmas islil_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl ls_empty_impl ls_ins_dj_impl, folded islil_inter_def]
  interpretation islil: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar islil_inter using islil_inter_impl .
  definition "islir_inter == SetGA.it_inter ias_iteratei lsi_memb rs_empty rs_ins_dj"
  lemmas islir_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl rs_empty_impl rs_ins_dj_impl, folded islir_inter_def]
  interpretation islir: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar islir_inter using islir_inter_impl .
  definition "islih_inter == SetGA.it_inter ias_iteratei lsi_memb hs_empty hs_ins_dj"
  lemmas islih_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl hs_empty_impl hs_ins_dj_impl, folded islih_inter_def]
  interpretation islih: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar islih_inter using islih_inter_impl .
  definition "islia_inter == SetGA.it_inter ias_iteratei lsi_memb ahs_empty ahs_ins_dj"
  lemmas islia_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded islia_inter_def]
  interpretation islia: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar islia_inter using islia_inter_impl .
  definition "isliis_inter == SetGA.it_inter ias_iteratei lsi_memb ias_empty ias_ins_dj"
  lemmas isliis_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl lsi_memb_impl ias_empty_impl ias_ins_dj_impl, folded isliis_inter_def]
  interpretation isliis: set_inter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar isliis_inter using isliis_inter_impl .
  definition "islli_inter == SetGA.it_inter ias_iteratei ls_memb lsi_empty lsi_ins_dj"
  lemmas islli_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded islli_inter_def]
  interpretation islli: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar islli_inter using islli_inter_impl .
  definition "isll_inter == SetGA.it_inter ias_iteratei ls_memb ls_empty ls_ins_dj"
  lemmas isll_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded isll_inter_def]
  interpretation isll: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar isll_inter using isll_inter_impl .
  definition "islr_inter == SetGA.it_inter ias_iteratei ls_memb rs_empty rs_ins_dj"
  lemmas islr_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded islr_inter_def]
  interpretation islr: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar islr_inter using islr_inter_impl .
  definition "islh_inter == SetGA.it_inter ias_iteratei ls_memb hs_empty hs_ins_dj"
  lemmas islh_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded islh_inter_def]
  interpretation islh: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar islh_inter using islh_inter_impl .
  definition "isla_inter == SetGA.it_inter ias_iteratei ls_memb ahs_empty ahs_ins_dj"
  lemmas isla_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded isla_inter_def]
  interpretation isla: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar isla_inter using isla_inter_impl .
  definition "islis_inter == SetGA.it_inter ias_iteratei ls_memb ias_empty ias_ins_dj"
  lemmas islis_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ls_memb_impl ias_empty_impl ias_ins_dj_impl, folded islis_inter_def]
  interpretation islis: set_inter ias_\<alpha> ias_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar islis_inter using islis_inter_impl .
  definition "isrli_inter == SetGA.it_inter ias_iteratei rs_memb lsi_empty lsi_ins_dj"
  lemmas isrli_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded isrli_inter_def]
  interpretation isrli: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar isrli_inter using isrli_inter_impl .
  definition "isrl_inter == SetGA.it_inter ias_iteratei rs_memb ls_empty ls_ins_dj"
  lemmas isrl_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded isrl_inter_def]
  interpretation isrl: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar isrl_inter using isrl_inter_impl .
  definition "isrr_inter == SetGA.it_inter ias_iteratei rs_memb rs_empty rs_ins_dj"
  lemmas isrr_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded isrr_inter_def]
  interpretation isrr: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar isrr_inter using isrr_inter_impl .
  definition "isrh_inter == SetGA.it_inter ias_iteratei rs_memb hs_empty hs_ins_dj"
  lemmas isrh_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded isrh_inter_def]
  interpretation isrh: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar isrh_inter using isrh_inter_impl .
  definition "isra_inter == SetGA.it_inter ias_iteratei rs_memb ahs_empty ahs_ins_dj"
  lemmas isra_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded isra_inter_def]
  interpretation isra: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar isra_inter using isra_inter_impl .
  definition "isris_inter == SetGA.it_inter ias_iteratei rs_memb ias_empty ias_ins_dj"
  lemmas isris_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl rs_memb_impl ias_empty_impl ias_ins_dj_impl, folded isris_inter_def]
  interpretation isris: set_inter ias_\<alpha> ias_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar isris_inter using isris_inter_impl .
  definition "ishli_inter == SetGA.it_inter ias_iteratei hs_memb lsi_empty lsi_ins_dj"
  lemmas ishli_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded ishli_inter_def]
  interpretation ishli: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ishli_inter using ishli_inter_impl .
  definition "ishl_inter == SetGA.it_inter ias_iteratei hs_memb ls_empty ls_ins_dj"
  lemmas ishl_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded ishl_inter_def]
  interpretation ishl: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ishl_inter using ishl_inter_impl .
  definition "ishr_inter == SetGA.it_inter ias_iteratei hs_memb rs_empty rs_ins_dj"
  lemmas ishr_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded ishr_inter_def]
  interpretation ishr: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ishr_inter using ishr_inter_impl .
  definition "ishh_inter == SetGA.it_inter ias_iteratei hs_memb hs_empty hs_ins_dj"
  lemmas ishh_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded ishh_inter_def]
  interpretation ishh: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ishh_inter using ishh_inter_impl .
  definition "isha_inter == SetGA.it_inter ias_iteratei hs_memb ahs_empty ahs_ins_dj"
  lemmas isha_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded isha_inter_def]
  interpretation isha: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar isha_inter using isha_inter_impl .
  definition "ishis_inter == SetGA.it_inter ias_iteratei hs_memb ias_empty ias_ins_dj"
  lemmas ishis_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl hs_memb_impl ias_empty_impl ias_ins_dj_impl, folded ishis_inter_def]
  interpretation ishis: set_inter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar ishis_inter using ishis_inter_impl .
  definition "isali_inter == SetGA.it_inter ias_iteratei ahs_memb lsi_empty lsi_ins_dj"
  lemmas isali_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded isali_inter_def]
  interpretation isali: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar isali_inter using isali_inter_impl .
  definition "isal_inter == SetGA.it_inter ias_iteratei ahs_memb ls_empty ls_ins_dj"
  lemmas isal_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl ls_empty_impl ls_ins_dj_impl, folded isal_inter_def]
  interpretation isal: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar isal_inter using isal_inter_impl .
  definition "isar_inter == SetGA.it_inter ias_iteratei ahs_memb rs_empty rs_ins_dj"
  lemmas isar_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl rs_empty_impl rs_ins_dj_impl, folded isar_inter_def]
  interpretation isar: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar isar_inter using isar_inter_impl .
  definition "isah_inter == SetGA.it_inter ias_iteratei ahs_memb hs_empty hs_ins_dj"
  lemmas isah_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl hs_empty_impl hs_ins_dj_impl, folded isah_inter_def]
  interpretation isah: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar isah_inter using isah_inter_impl .
  definition "isaa_inter == SetGA.it_inter ias_iteratei ahs_memb ahs_empty ahs_ins_dj"
  lemmas isaa_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded isaa_inter_def]
  interpretation isaa: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar isaa_inter using isaa_inter_impl .
  definition "isais_inter == SetGA.it_inter ias_iteratei ahs_memb ias_empty ias_ins_dj"
  lemmas isais_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ahs_memb_impl ias_empty_impl ias_ins_dj_impl, folded isais_inter_def]
  interpretation isais: set_inter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar isais_inter using isais_inter_impl .
  definition "isisli_inter == SetGA.it_inter ias_iteratei ias_memb lsi_empty lsi_ins_dj"
  lemmas isisli_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl lsi_empty_impl lsi_ins_dj_impl, folded isisli_inter_def]
  interpretation isisli: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isisli_inter using isisli_inter_impl .
  definition "isisl_inter == SetGA.it_inter ias_iteratei ias_memb ls_empty ls_ins_dj"
  lemmas isisl_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl ls_empty_impl ls_ins_dj_impl, folded isisl_inter_def]
  interpretation isisl: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar isisl_inter using isisl_inter_impl .
  definition "isisr_inter == SetGA.it_inter ias_iteratei ias_memb rs_empty rs_ins_dj"
  lemmas isisr_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl rs_empty_impl rs_ins_dj_impl, folded isisr_inter_def]
  interpretation isisr: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar isisr_inter using isisr_inter_impl .
  definition "isish_inter == SetGA.it_inter ias_iteratei ias_memb hs_empty hs_ins_dj"
  lemmas isish_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl hs_empty_impl hs_ins_dj_impl, folded isish_inter_def]
  interpretation isish: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar isish_inter using isish_inter_impl .
  definition "isisa_inter == SetGA.it_inter ias_iteratei ias_memb ahs_empty ahs_ins_dj"
  lemmas isisa_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl ahs_empty_impl ahs_ins_dj_impl, folded isisa_inter_def]
  interpretation isisa: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isisa_inter using isisa_inter_impl .
  definition "isisis_inter == SetGA.it_inter ias_iteratei ias_memb ias_empty ias_ins_dj"
  lemmas isisis_inter_impl = SetGA.it_inter_correct[OF ias_iteratei_impl ias_memb_impl ias_empty_impl ias_ins_dj_impl, folded isisis_inter_def]
  interpretation isisis: set_inter ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar isisis_inter using isisis_inter_impl .

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
  definition "liis_subset == SetGA.ball_subset lsi_ball ias_memb"
  lemmas liis_subset_impl = SetGA.ball_subset_correct[OF lsi_ball_impl ias_memb_impl, folded liis_subset_def]
  interpretation liis: set_subset lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_subset using liis_subset_impl .
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
  definition "lis_subset == SetGA.ball_subset ls_ball ias_memb"
  lemmas lis_subset_impl = SetGA.ball_subset_correct[OF ls_ball_impl ias_memb_impl, folded lis_subset_def]
  interpretation lis: set_subset ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_subset using lis_subset_impl .
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
  definition "ris_subset == SetGA.ball_subset rs_ball ias_memb"
  lemmas ris_subset_impl = SetGA.ball_subset_correct[OF rs_ball_impl ias_memb_impl, folded ris_subset_def]
  interpretation ris: set_subset rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_subset using ris_subset_impl .
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
  definition "his_subset == SetGA.ball_subset hs_ball ias_memb"
  lemmas his_subset_impl = SetGA.ball_subset_correct[OF hs_ball_impl ias_memb_impl, folded his_subset_def]
  interpretation his: set_subset hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_subset using his_subset_impl .
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
  definition "ais_subset == SetGA.ball_subset ahs_ball ias_memb"
  lemmas ais_subset_impl = SetGA.ball_subset_correct[OF ahs_ball_impl ias_memb_impl, folded ais_subset_def]
  interpretation ais: set_subset ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_subset using ais_subset_impl .
  definition "isli_subset == SetGA.ball_subset ias_ball lsi_memb"
  lemmas isli_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl lsi_memb_impl, folded isli_subset_def]
  interpretation isli: set_subset ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_subset using isli_subset_impl .
  definition "isl_subset == SetGA.ball_subset ias_ball ls_memb"
  lemmas isl_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl ls_memb_impl, folded isl_subset_def]
  interpretation isl: set_subset ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_subset using isl_subset_impl .
  definition "isr_subset == SetGA.ball_subset ias_ball rs_memb"
  lemmas isr_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl rs_memb_impl, folded isr_subset_def]
  interpretation isr: set_subset ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_subset using isr_subset_impl .
  definition "ish_subset == SetGA.ball_subset ias_ball hs_memb"
  lemmas ish_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl hs_memb_impl, folded ish_subset_def]
  interpretation ish: set_subset ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_subset using ish_subset_impl .
  definition "isa_subset == SetGA.ball_subset ias_ball ahs_memb"
  lemmas isa_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl ahs_memb_impl, folded isa_subset_def]
  interpretation isa: set_subset ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_subset using isa_subset_impl .
  definition "isis_subset == SetGA.ball_subset ias_ball ias_memb"
  lemmas isis_subset_impl = SetGA.ball_subset_correct[OF ias_ball_impl ias_memb_impl, folded isis_subset_def]
  interpretation isis: set_subset ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_subset using isis_subset_impl .

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
  definition "liis_equal == SetGA.subset_equal liis_subset isli_subset"
  lemmas liis_equal_impl = SetGA.subset_equal_correct[OF liis_subset_impl isli_subset_impl, folded liis_equal_def]
  interpretation liis: set_equal lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_equal using liis_equal_impl .
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
  definition "lis_equal == SetGA.subset_equal lis_subset isl_subset"
  lemmas lis_equal_impl = SetGA.subset_equal_correct[OF lis_subset_impl isl_subset_impl, folded lis_equal_def]
  interpretation lis: set_equal ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_equal using lis_equal_impl .
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
  definition "ris_equal == SetGA.subset_equal ris_subset isr_subset"
  lemmas ris_equal_impl = SetGA.subset_equal_correct[OF ris_subset_impl isr_subset_impl, folded ris_equal_def]
  interpretation ris: set_equal rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_equal using ris_equal_impl .
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
  definition "his_equal == SetGA.subset_equal his_subset ish_subset"
  lemmas his_equal_impl = SetGA.subset_equal_correct[OF his_subset_impl ish_subset_impl, folded his_equal_def]
  interpretation his: set_equal hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_equal using his_equal_impl .
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
  definition "ais_equal == SetGA.subset_equal ais_subset isa_subset"
  lemmas ais_equal_impl = SetGA.subset_equal_correct[OF ais_subset_impl isa_subset_impl, folded ais_equal_def]
  interpretation ais: set_equal ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_equal using ais_equal_impl .
  definition "isli_equal == SetGA.subset_equal isli_subset liis_subset"
  lemmas isli_equal_impl = SetGA.subset_equal_correct[OF isli_subset_impl liis_subset_impl, folded isli_equal_def]
  interpretation isli: set_equal ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_equal using isli_equal_impl .
  definition "isl_equal == SetGA.subset_equal isl_subset lis_subset"
  lemmas isl_equal_impl = SetGA.subset_equal_correct[OF isl_subset_impl lis_subset_impl, folded isl_equal_def]
  interpretation isl: set_equal ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_equal using isl_equal_impl .
  definition "isr_equal == SetGA.subset_equal isr_subset ris_subset"
  lemmas isr_equal_impl = SetGA.subset_equal_correct[OF isr_subset_impl ris_subset_impl, folded isr_equal_def]
  interpretation isr: set_equal ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_equal using isr_equal_impl .
  definition "ish_equal == SetGA.subset_equal ish_subset his_subset"
  lemmas ish_equal_impl = SetGA.subset_equal_correct[OF ish_subset_impl his_subset_impl, folded ish_equal_def]
  interpretation ish: set_equal ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_equal using ish_equal_impl .
  definition "isa_equal == SetGA.subset_equal isa_subset ais_subset"
  lemmas isa_equal_impl = SetGA.subset_equal_correct[OF isa_subset_impl ais_subset_impl, folded isa_equal_def]
  interpretation isa: set_equal ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_equal using isa_equal_impl .
  definition "isis_equal == SetGA.subset_equal isis_subset isis_subset"
  lemmas isis_equal_impl = SetGA.subset_equal_correct[OF isis_subset_impl isis_subset_impl, folded isis_equal_def]
  interpretation isis: set_equal ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_equal using isis_equal_impl .

  definition "lili_image_filter == SetGA.it_image_filter lsi_iteratei lsi_empty lsi_ins"
  lemmas lili_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lili_image_filter_def]
  interpretation lili: set_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_image_filter using lili_image_filter_impl .
  definition "lil_image_filter == SetGA.it_image_filter lsi_iteratei ls_empty ls_ins"
  lemmas lil_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded lil_image_filter_def]
  interpretation lil: set_image_filter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_image_filter using lil_image_filter_impl .
  definition "lir_image_filter == SetGA.it_image_filter lsi_iteratei rs_empty rs_ins"
  lemmas lir_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded lir_image_filter_def]
  interpretation lir: set_image_filter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_image_filter using lir_image_filter_impl .
  definition "lih_image_filter == SetGA.it_image_filter lsi_iteratei hs_empty hs_ins"
  lemmas lih_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded lih_image_filter_def]
  interpretation lih: set_image_filter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_image_filter using lih_image_filter_impl .
  definition "lia_image_filter == SetGA.it_image_filter lsi_iteratei ahs_empty ahs_ins"
  lemmas lia_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lia_image_filter_def]
  interpretation lia: set_image_filter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_image_filter using lia_image_filter_impl .
  definition "liis_image_filter == SetGA.it_image_filter lsi_iteratei ias_empty ias_ins"
  lemmas liis_image_filter_impl = SetGA.it_image_filter_correct[OF lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded liis_image_filter_def]
  interpretation liis: set_image_filter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_image_filter using liis_image_filter_impl .
  definition "lli_image_filter == SetGA.it_image_filter ls_iteratei lsi_empty lsi_ins"
  lemmas lli_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lli_image_filter_def]
  interpretation lli: set_image_filter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_image_filter using lli_image_filter_impl .
  definition "ll_image_filter == SetGA.it_image_filter ls_iteratei ls_empty ls_ins"
  lemmas ll_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl ls_empty_impl ls_ins_impl, folded ll_image_filter_def]
  interpretation ll: set_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_image_filter using ll_image_filter_impl .
  definition "lr_image_filter == SetGA.it_image_filter ls_iteratei rs_empty rs_ins"
  lemmas lr_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl rs_empty_impl rs_ins_impl, folded lr_image_filter_def]
  interpretation lr: set_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_image_filter using lr_image_filter_impl .
  definition "lh_image_filter == SetGA.it_image_filter ls_iteratei hs_empty hs_ins"
  lemmas lh_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl hs_empty_impl hs_ins_impl, folded lh_image_filter_def]
  interpretation lh: set_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_image_filter using lh_image_filter_impl .
  definition "la_image_filter == SetGA.it_image_filter ls_iteratei ahs_empty ahs_ins"
  lemmas la_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded la_image_filter_def]
  interpretation la: set_image_filter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_image_filter using la_image_filter_impl .
  definition "lis_image_filter == SetGA.it_image_filter ls_iteratei ias_empty ias_ins"
  lemmas lis_image_filter_impl = SetGA.it_image_filter_correct[OF ls_iteratei_impl ias_empty_impl ias_ins_impl, folded lis_image_filter_def]
  interpretation lis: set_image_filter ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_image_filter using lis_image_filter_impl .
  definition "rli_image_filter == SetGA.it_image_filter rs_iteratei lsi_empty lsi_ins"
  lemmas rli_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rli_image_filter_def]
  interpretation rli: set_image_filter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_image_filter using rli_image_filter_impl .
  definition "rl_image_filter == SetGA.it_image_filter rs_iteratei ls_empty ls_ins"
  lemmas rl_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl ls_empty_impl ls_ins_impl, folded rl_image_filter_def]
  interpretation rl: set_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_image_filter using rl_image_filter_impl .
  definition "rr_image_filter == SetGA.it_image_filter rs_iteratei rs_empty rs_ins"
  lemmas rr_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl rs_empty_impl rs_ins_impl, folded rr_image_filter_def]
  interpretation rr: set_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_image_filter using rr_image_filter_impl .
  definition "rh_image_filter == SetGA.it_image_filter rs_iteratei hs_empty hs_ins"
  lemmas rh_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl hs_empty_impl hs_ins_impl, folded rh_image_filter_def]
  interpretation rh: set_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_image_filter using rh_image_filter_impl .
  definition "ra_image_filter == SetGA.it_image_filter rs_iteratei ahs_empty ahs_ins"
  lemmas ra_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ra_image_filter_def]
  interpretation ra: set_image_filter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_image_filter using ra_image_filter_impl .
  definition "ris_image_filter == SetGA.it_image_filter rs_iteratei ias_empty ias_ins"
  lemmas ris_image_filter_impl = SetGA.it_image_filter_correct[OF rs_iteratei_impl ias_empty_impl ias_ins_impl, folded ris_image_filter_def]
  interpretation ris: set_image_filter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_image_filter using ris_image_filter_impl .
  definition "hli_image_filter == SetGA.it_image_filter hs_iteratei lsi_empty lsi_ins"
  lemmas hli_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hli_image_filter_def]
  interpretation hli: set_image_filter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_image_filter using hli_image_filter_impl .
  definition "hl_image_filter == SetGA.it_image_filter hs_iteratei ls_empty ls_ins"
  lemmas hl_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl ls_empty_impl ls_ins_impl, folded hl_image_filter_def]
  interpretation hl: set_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_image_filter using hl_image_filter_impl .
  definition "hr_image_filter == SetGA.it_image_filter hs_iteratei rs_empty rs_ins"
  lemmas hr_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl rs_empty_impl rs_ins_impl, folded hr_image_filter_def]
  interpretation hr: set_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_image_filter using hr_image_filter_impl .
  definition "hh_image_filter == SetGA.it_image_filter hs_iteratei hs_empty hs_ins"
  lemmas hh_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl hs_empty_impl hs_ins_impl, folded hh_image_filter_def]
  interpretation hh: set_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_image_filter using hh_image_filter_impl .
  definition "ha_image_filter == SetGA.it_image_filter hs_iteratei ahs_empty ahs_ins"
  lemmas ha_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ha_image_filter_def]
  interpretation ha: set_image_filter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_image_filter using ha_image_filter_impl .
  definition "his_image_filter == SetGA.it_image_filter hs_iteratei ias_empty ias_ins"
  lemmas his_image_filter_impl = SetGA.it_image_filter_correct[OF hs_iteratei_impl ias_empty_impl ias_ins_impl, folded his_image_filter_def]
  interpretation his: set_image_filter hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_image_filter using his_image_filter_impl .
  definition "ali_image_filter == SetGA.it_image_filter ahs_iteratei lsi_empty lsi_ins"
  lemmas ali_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded ali_image_filter_def]
  interpretation ali: set_image_filter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_image_filter using ali_image_filter_impl .
  definition "al_image_filter == SetGA.it_image_filter ahs_iteratei ls_empty ls_ins"
  lemmas al_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded al_image_filter_def]
  interpretation al: set_image_filter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_image_filter using al_image_filter_impl .
  definition "ar_image_filter == SetGA.it_image_filter ahs_iteratei rs_empty rs_ins"
  lemmas ar_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded ar_image_filter_def]
  interpretation ar: set_image_filter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_image_filter using ar_image_filter_impl .
  definition "ah_image_filter == SetGA.it_image_filter ahs_iteratei hs_empty hs_ins"
  lemmas ah_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded ah_image_filter_def]
  interpretation ah: set_image_filter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_image_filter using ah_image_filter_impl .
  definition "aa_image_filter == SetGA.it_image_filter ahs_iteratei ahs_empty ahs_ins"
  lemmas aa_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aa_image_filter_def]
  interpretation aa: set_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_image_filter using aa_image_filter_impl .
  definition "ais_image_filter == SetGA.it_image_filter ahs_iteratei ias_empty ias_ins"
  lemmas ais_image_filter_impl = SetGA.it_image_filter_correct[OF ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded ais_image_filter_def]
  interpretation ais: set_image_filter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_image_filter using ais_image_filter_impl .
  definition "isli_image_filter == SetGA.it_image_filter ias_iteratei lsi_empty lsi_ins"
  lemmas isli_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isli_image_filter_def]
  interpretation isli: set_image_filter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_image_filter using isli_image_filter_impl .
  definition "isl_image_filter == SetGA.it_image_filter ias_iteratei ls_empty ls_ins"
  lemmas isl_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl ls_empty_impl ls_ins_impl, folded isl_image_filter_def]
  interpretation isl: set_image_filter ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_image_filter using isl_image_filter_impl .
  definition "isr_image_filter == SetGA.it_image_filter ias_iteratei rs_empty rs_ins"
  lemmas isr_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl rs_empty_impl rs_ins_impl, folded isr_image_filter_def]
  interpretation isr: set_image_filter ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_image_filter using isr_image_filter_impl .
  definition "ish_image_filter == SetGA.it_image_filter ias_iteratei hs_empty hs_ins"
  lemmas ish_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl hs_empty_impl hs_ins_impl, folded ish_image_filter_def]
  interpretation ish: set_image_filter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_image_filter using ish_image_filter_impl .
  definition "isa_image_filter == SetGA.it_image_filter ias_iteratei ahs_empty ahs_ins"
  lemmas isa_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isa_image_filter_def]
  interpretation isa: set_image_filter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_image_filter using isa_image_filter_impl .
  definition "isis_image_filter == SetGA.it_image_filter ias_iteratei ias_empty ias_ins"
  lemmas isis_image_filter_impl = SetGA.it_image_filter_correct[OF ias_iteratei_impl ias_empty_impl ias_ins_impl, folded isis_image_filter_def]
  interpretation isis: set_image_filter ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_image_filter using isis_image_filter_impl .

  definition "lili_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas lili_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lili_inj_image_filter_def]
  interpretation lili: set_inj_image_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_inj_image_filter using lili_inj_image_filter_impl .
  definition "lil_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei ls_empty ls_ins_dj"
  lemmas lil_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lil_inj_image_filter_def]
  interpretation lil: set_inj_image_filter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_inj_image_filter using lil_inj_image_filter_impl .
  definition "lir_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei rs_empty rs_ins_dj"
  lemmas lir_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lir_inj_image_filter_def]
  interpretation lir: set_inj_image_filter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_inj_image_filter using lir_inj_image_filter_impl .
  definition "lih_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei hs_empty hs_ins_dj"
  lemmas lih_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lih_inj_image_filter_def]
  interpretation lih: set_inj_image_filter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_inj_image_filter using lih_inj_image_filter_impl .
  definition "lia_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas lia_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lia_inj_image_filter_def]
  interpretation lia: set_inj_image_filter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_inj_image_filter using lia_inj_image_filter_impl .
  definition "liis_inj_image_filter == SetGA.it_inj_image_filter lsi_iteratei ias_empty ias_ins_dj"
  lemmas liis_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liis_inj_image_filter_def]
  interpretation liis: set_inj_image_filter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_inj_image_filter using liis_inj_image_filter_impl .
  definition "lli_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei lsi_empty lsi_ins_dj"
  lemmas lli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lli_inj_image_filter_def]
  interpretation lli: set_inj_image_filter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_inj_image_filter using lli_inj_image_filter_impl .
  definition "ll_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei ls_empty ls_ins_dj"
  lemmas ll_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ll_inj_image_filter_def]
  interpretation ll: set_inj_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_inj_image_filter using ll_inj_image_filter_impl .
  definition "lr_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei rs_empty rs_ins_dj"
  lemmas lr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lr_inj_image_filter_def]
  interpretation lr: set_inj_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_inj_image_filter using lr_inj_image_filter_impl .
  definition "lh_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei hs_empty hs_ins_dj"
  lemmas lh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lh_inj_image_filter_def]
  interpretation lh: set_inj_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_inj_image_filter using lh_inj_image_filter_impl .
  definition "la_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei ahs_empty ahs_ins_dj"
  lemmas la_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded la_inj_image_filter_def]
  interpretation la: set_inj_image_filter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_inj_image_filter using la_inj_image_filter_impl .
  definition "lis_inj_image_filter == SetGA.it_inj_image_filter ls_iteratei ias_empty ias_ins_dj"
  lemmas lis_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lis_inj_image_filter_def]
  interpretation lis: set_inj_image_filter ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_inj_image_filter using lis_inj_image_filter_impl .
  definition "rli_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei lsi_empty lsi_ins_dj"
  lemmas rli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rli_inj_image_filter_def]
  interpretation rli: set_inj_image_filter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_inj_image_filter using rli_inj_image_filter_impl .
  definition "rl_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei ls_empty ls_ins_dj"
  lemmas rl_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rl_inj_image_filter_def]
  interpretation rl: set_inj_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_inj_image_filter using rl_inj_image_filter_impl .
  definition "rr_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei rs_empty rs_ins_dj"
  lemmas rr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rr_inj_image_filter_def]
  interpretation rr: set_inj_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_inj_image_filter using rr_inj_image_filter_impl .
  definition "rh_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei hs_empty hs_ins_dj"
  lemmas rh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rh_inj_image_filter_def]
  interpretation rh: set_inj_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_inj_image_filter using rh_inj_image_filter_impl .
  definition "ra_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei ahs_empty ahs_ins_dj"
  lemmas ra_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ra_inj_image_filter_def]
  interpretation ra: set_inj_image_filter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_inj_image_filter using ra_inj_image_filter_impl .
  definition "ris_inj_image_filter == SetGA.it_inj_image_filter rs_iteratei ias_empty ias_ins_dj"
  lemmas ris_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ris_inj_image_filter_def]
  interpretation ris: set_inj_image_filter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_inj_image_filter using ris_inj_image_filter_impl .
  definition "hli_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei lsi_empty lsi_ins_dj"
  lemmas hli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hli_inj_image_filter_def]
  interpretation hli: set_inj_image_filter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_inj_image_filter using hli_inj_image_filter_impl .
  definition "hl_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei ls_empty ls_ins_dj"
  lemmas hl_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hl_inj_image_filter_def]
  interpretation hl: set_inj_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_inj_image_filter using hl_inj_image_filter_impl .
  definition "hr_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei rs_empty rs_ins_dj"
  lemmas hr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hr_inj_image_filter_def]
  interpretation hr: set_inj_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_inj_image_filter using hr_inj_image_filter_impl .
  definition "hh_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei hs_empty hs_ins_dj"
  lemmas hh_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hh_inj_image_filter_def]
  interpretation hh: set_inj_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_inj_image_filter using hh_inj_image_filter_impl .
  definition "ha_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei ahs_empty ahs_ins_dj"
  lemmas ha_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ha_inj_image_filter_def]
  interpretation ha: set_inj_image_filter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_inj_image_filter using ha_inj_image_filter_impl .
  definition "his_inj_image_filter == SetGA.it_inj_image_filter hs_iteratei ias_empty ias_ins_dj"
  lemmas his_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded his_inj_image_filter_def]
  interpretation his: set_inj_image_filter hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_inj_image_filter using his_inj_image_filter_impl .
  definition "ali_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas ali_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ali_inj_image_filter_def]
  interpretation ali: set_inj_image_filter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_inj_image_filter using ali_inj_image_filter_impl .
  definition "al_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei ls_empty ls_ins_dj"
  lemmas al_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded al_inj_image_filter_def]
  interpretation al: set_inj_image_filter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_inj_image_filter using al_inj_image_filter_impl .
  definition "ar_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei rs_empty rs_ins_dj"
  lemmas ar_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ar_inj_image_filter_def]
  interpretation ar: set_inj_image_filter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_inj_image_filter using ar_inj_image_filter_impl .
  definition "ah_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei hs_empty hs_ins_dj"
  lemmas ah_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ah_inj_image_filter_def]
  interpretation ah: set_inj_image_filter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_inj_image_filter using ah_inj_image_filter_impl .
  definition "aa_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas aa_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aa_inj_image_filter_def]
  interpretation aa: set_inj_image_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_inj_image_filter using aa_inj_image_filter_impl .
  definition "ais_inj_image_filter == SetGA.it_inj_image_filter ahs_iteratei ias_empty ias_ins_dj"
  lemmas ais_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ais_inj_image_filter_def]
  interpretation ais: set_inj_image_filter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_inj_image_filter using ais_inj_image_filter_impl .
  definition "isli_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei lsi_empty lsi_ins_dj"
  lemmas isli_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isli_inj_image_filter_def]
  interpretation isli: set_inj_image_filter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_inj_image_filter using isli_inj_image_filter_impl .
  definition "isl_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei ls_empty ls_ins_dj"
  lemmas isl_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isl_inj_image_filter_def]
  interpretation isl: set_inj_image_filter ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_inj_image_filter using isl_inj_image_filter_impl .
  definition "isr_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei rs_empty rs_ins_dj"
  lemmas isr_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isr_inj_image_filter_def]
  interpretation isr: set_inj_image_filter ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_inj_image_filter using isr_inj_image_filter_impl .
  definition "ish_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei hs_empty hs_ins_dj"
  lemmas ish_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ish_inj_image_filter_def]
  interpretation ish: set_inj_image_filter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_inj_image_filter using ish_inj_image_filter_impl .
  definition "isa_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei ahs_empty ahs_ins_dj"
  lemmas isa_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isa_inj_image_filter_def]
  interpretation isa: set_inj_image_filter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_inj_image_filter using isa_inj_image_filter_impl .
  definition "isis_inj_image_filter == SetGA.it_inj_image_filter ias_iteratei ias_empty ias_ins_dj"
  lemmas isis_inj_image_filter_impl = SetGA.it_inj_image_filter_correct[OF ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isis_inj_image_filter_def]
  interpretation isis: set_inj_image_filter ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_inj_image_filter using isis_inj_image_filter_impl .

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
  definition "liis_image == SetGA.iflt_image liis_image_filter"
  lemmas liis_image_impl = SetGA.iflt_image_correct[OF liis_image_filter_impl, folded liis_image_def]
  interpretation liis: set_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_image using liis_image_impl .
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
  definition "lis_image == SetGA.iflt_image lis_image_filter"
  lemmas lis_image_impl = SetGA.iflt_image_correct[OF lis_image_filter_impl, folded lis_image_def]
  interpretation lis: set_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_image using lis_image_impl .
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
  definition "ris_image == SetGA.iflt_image ris_image_filter"
  lemmas ris_image_impl = SetGA.iflt_image_correct[OF ris_image_filter_impl, folded ris_image_def]
  interpretation ris: set_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_image using ris_image_impl .
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
  definition "his_image == SetGA.iflt_image his_image_filter"
  lemmas his_image_impl = SetGA.iflt_image_correct[OF his_image_filter_impl, folded his_image_def]
  interpretation his: set_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_image using his_image_impl .
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
  definition "ais_image == SetGA.iflt_image ais_image_filter"
  lemmas ais_image_impl = SetGA.iflt_image_correct[OF ais_image_filter_impl, folded ais_image_def]
  interpretation ais: set_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_image using ais_image_impl .
  definition "isli_image == SetGA.iflt_image isli_image_filter"
  lemmas isli_image_impl = SetGA.iflt_image_correct[OF isli_image_filter_impl, folded isli_image_def]
  interpretation isli: set_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_image using isli_image_impl .
  definition "isl_image == SetGA.iflt_image isl_image_filter"
  lemmas isl_image_impl = SetGA.iflt_image_correct[OF isl_image_filter_impl, folded isl_image_def]
  interpretation isl: set_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_image using isl_image_impl .
  definition "isr_image == SetGA.iflt_image isr_image_filter"
  lemmas isr_image_impl = SetGA.iflt_image_correct[OF isr_image_filter_impl, folded isr_image_def]
  interpretation isr: set_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_image using isr_image_impl .
  definition "ish_image == SetGA.iflt_image ish_image_filter"
  lemmas ish_image_impl = SetGA.iflt_image_correct[OF ish_image_filter_impl, folded ish_image_def]
  interpretation ish: set_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_image using ish_image_impl .
  definition "isa_image == SetGA.iflt_image isa_image_filter"
  lemmas isa_image_impl = SetGA.iflt_image_correct[OF isa_image_filter_impl, folded isa_image_def]
  interpretation isa: set_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_image using isa_image_impl .
  definition "isis_image == SetGA.iflt_image isis_image_filter"
  lemmas isis_image_impl = SetGA.iflt_image_correct[OF isis_image_filter_impl, folded isis_image_def]
  interpretation isis: set_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_image using isis_image_impl .

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
  definition "liis_inj_image == SetGA.iflt_inj_image liis_inj_image_filter"
  lemmas liis_inj_image_impl = SetGA.iflt_inj_image_correct[OF liis_inj_image_filter_impl, folded liis_inj_image_def]
  interpretation liis: set_inj_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_inj_image using liis_inj_image_impl .
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
  definition "lis_inj_image == SetGA.iflt_inj_image lis_inj_image_filter"
  lemmas lis_inj_image_impl = SetGA.iflt_inj_image_correct[OF lis_inj_image_filter_impl, folded lis_inj_image_def]
  interpretation lis: set_inj_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_inj_image using lis_inj_image_impl .
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
  definition "ris_inj_image == SetGA.iflt_inj_image ris_inj_image_filter"
  lemmas ris_inj_image_impl = SetGA.iflt_inj_image_correct[OF ris_inj_image_filter_impl, folded ris_inj_image_def]
  interpretation ris: set_inj_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_inj_image using ris_inj_image_impl .
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
  definition "his_inj_image == SetGA.iflt_inj_image his_inj_image_filter"
  lemmas his_inj_image_impl = SetGA.iflt_inj_image_correct[OF his_inj_image_filter_impl, folded his_inj_image_def]
  interpretation his: set_inj_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_inj_image using his_inj_image_impl .
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
  definition "ais_inj_image == SetGA.iflt_inj_image ais_inj_image_filter"
  lemmas ais_inj_image_impl = SetGA.iflt_inj_image_correct[OF ais_inj_image_filter_impl, folded ais_inj_image_def]
  interpretation ais: set_inj_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_inj_image using ais_inj_image_impl .
  definition "isli_inj_image == SetGA.iflt_inj_image isli_inj_image_filter"
  lemmas isli_inj_image_impl = SetGA.iflt_inj_image_correct[OF isli_inj_image_filter_impl, folded isli_inj_image_def]
  interpretation isli: set_inj_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_inj_image using isli_inj_image_impl .
  definition "isl_inj_image == SetGA.iflt_inj_image isl_inj_image_filter"
  lemmas isl_inj_image_impl = SetGA.iflt_inj_image_correct[OF isl_inj_image_filter_impl, folded isl_inj_image_def]
  interpretation isl: set_inj_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_inj_image using isl_inj_image_impl .
  definition "isr_inj_image == SetGA.iflt_inj_image isr_inj_image_filter"
  lemmas isr_inj_image_impl = SetGA.iflt_inj_image_correct[OF isr_inj_image_filter_impl, folded isr_inj_image_def]
  interpretation isr: set_inj_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_inj_image using isr_inj_image_impl .
  definition "ish_inj_image == SetGA.iflt_inj_image ish_inj_image_filter"
  lemmas ish_inj_image_impl = SetGA.iflt_inj_image_correct[OF ish_inj_image_filter_impl, folded ish_inj_image_def]
  interpretation ish: set_inj_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_inj_image using ish_inj_image_impl .
  definition "isa_inj_image == SetGA.iflt_inj_image isa_inj_image_filter"
  lemmas isa_inj_image_impl = SetGA.iflt_inj_image_correct[OF isa_inj_image_filter_impl, folded isa_inj_image_def]
  interpretation isa: set_inj_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_inj_image using isa_inj_image_impl .
  definition "isis_inj_image == SetGA.iflt_inj_image isis_inj_image_filter"
  lemmas isis_inj_image_impl = SetGA.iflt_inj_image_correct[OF isis_inj_image_filter_impl, folded isis_inj_image_def]
  interpretation isis: set_inj_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_inj_image using isis_inj_image_impl .

  definition "lili_filter == SetGA.iflt_filter lili_inj_image_filter"
  lemmas lili_filter_impl = SetGA.iflt_filter_correct[OF lili_inj_image_filter_impl, folded lili_filter_def]
  interpretation lili: set_filter lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lili_filter using lili_filter_impl .
  definition "lil_filter == SetGA.iflt_filter lil_inj_image_filter"
  lemmas lil_filter_impl = SetGA.iflt_filter_correct[OF lil_inj_image_filter_impl, folded lil_filter_def]
  interpretation lil: set_filter lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lil_filter using lil_filter_impl .
  definition "lir_filter == SetGA.iflt_filter lir_inj_image_filter"
  lemmas lir_filter_impl = SetGA.iflt_filter_correct[OF lir_inj_image_filter_impl, folded lir_filter_def]
  interpretation lir: set_filter lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lir_filter using lir_filter_impl .
  definition "lih_filter == SetGA.iflt_filter lih_inj_image_filter"
  lemmas lih_filter_impl = SetGA.iflt_filter_correct[OF lih_inj_image_filter_impl, folded lih_filter_def]
  interpretation lih: set_filter lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lih_filter using lih_filter_impl .
  definition "lia_filter == SetGA.iflt_filter lia_inj_image_filter"
  lemmas lia_filter_impl = SetGA.iflt_filter_correct[OF lia_inj_image_filter_impl, folded lia_filter_def]
  interpretation lia: set_filter lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lia_filter using lia_filter_impl .
  definition "liis_filter == SetGA.iflt_filter liis_inj_image_filter"
  lemmas liis_filter_impl = SetGA.iflt_filter_correct[OF liis_inj_image_filter_impl, folded liis_filter_def]
  interpretation liis: set_filter lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_filter using liis_filter_impl .
  definition "lli_filter == SetGA.iflt_filter lli_inj_image_filter"
  lemmas lli_filter_impl = SetGA.iflt_filter_correct[OF lli_inj_image_filter_impl, folded lli_filter_def]
  interpretation lli: set_filter ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lli_filter using lli_filter_impl .
  definition "ll_filter == SetGA.iflt_filter ll_inj_image_filter"
  lemmas ll_filter_impl = SetGA.iflt_filter_correct[OF ll_inj_image_filter_impl, folded ll_filter_def]
  interpretation ll: set_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_filter using ll_filter_impl .
  definition "lr_filter == SetGA.iflt_filter lr_inj_image_filter"
  lemmas lr_filter_impl = SetGA.iflt_filter_correct[OF lr_inj_image_filter_impl, folded lr_filter_def]
  interpretation lr: set_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_filter using lr_filter_impl .
  definition "lh_filter == SetGA.iflt_filter lh_inj_image_filter"
  lemmas lh_filter_impl = SetGA.iflt_filter_correct[OF lh_inj_image_filter_impl, folded lh_filter_def]
  interpretation lh: set_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_filter using lh_filter_impl .
  definition "la_filter == SetGA.iflt_filter la_inj_image_filter"
  lemmas la_filter_impl = SetGA.iflt_filter_correct[OF la_inj_image_filter_impl, folded la_filter_def]
  interpretation la: set_filter ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar la_filter using la_filter_impl .
  definition "lis_filter == SetGA.iflt_filter lis_inj_image_filter"
  lemmas lis_filter_impl = SetGA.iflt_filter_correct[OF lis_inj_image_filter_impl, folded lis_filter_def]
  interpretation lis: set_filter ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_filter using lis_filter_impl .
  definition "rli_filter == SetGA.iflt_filter rli_inj_image_filter"
  lemmas rli_filter_impl = SetGA.iflt_filter_correct[OF rli_inj_image_filter_impl, folded rli_filter_def]
  interpretation rli: set_filter rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rli_filter using rli_filter_impl .
  definition "rl_filter == SetGA.iflt_filter rl_inj_image_filter"
  lemmas rl_filter_impl = SetGA.iflt_filter_correct[OF rl_inj_image_filter_impl, folded rl_filter_def]
  interpretation rl: set_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_filter using rl_filter_impl .
  definition "rr_filter == SetGA.iflt_filter rr_inj_image_filter"
  lemmas rr_filter_impl = SetGA.iflt_filter_correct[OF rr_inj_image_filter_impl, folded rr_filter_def]
  interpretation rr: set_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_filter using rr_filter_impl .
  definition "rh_filter == SetGA.iflt_filter rh_inj_image_filter"
  lemmas rh_filter_impl = SetGA.iflt_filter_correct[OF rh_inj_image_filter_impl, folded rh_filter_def]
  interpretation rh: set_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_filter using rh_filter_impl .
  definition "ra_filter == SetGA.iflt_filter ra_inj_image_filter"
  lemmas ra_filter_impl = SetGA.iflt_filter_correct[OF ra_inj_image_filter_impl, folded ra_filter_def]
  interpretation ra: set_filter rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ra_filter using ra_filter_impl .
  definition "ris_filter == SetGA.iflt_filter ris_inj_image_filter"
  lemmas ris_filter_impl = SetGA.iflt_filter_correct[OF ris_inj_image_filter_impl, folded ris_filter_def]
  interpretation ris: set_filter rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_filter using ris_filter_impl .
  definition "hli_filter == SetGA.iflt_filter hli_inj_image_filter"
  lemmas hli_filter_impl = SetGA.iflt_filter_correct[OF hli_inj_image_filter_impl, folded hli_filter_def]
  interpretation hli: set_filter hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hli_filter using hli_filter_impl .
  definition "hl_filter == SetGA.iflt_filter hl_inj_image_filter"
  lemmas hl_filter_impl = SetGA.iflt_filter_correct[OF hl_inj_image_filter_impl, folded hl_filter_def]
  interpretation hl: set_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_filter using hl_filter_impl .
  definition "hr_filter == SetGA.iflt_filter hr_inj_image_filter"
  lemmas hr_filter_impl = SetGA.iflt_filter_correct[OF hr_inj_image_filter_impl, folded hr_filter_def]
  interpretation hr: set_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_filter using hr_filter_impl .
  definition "hh_filter == SetGA.iflt_filter hh_inj_image_filter"
  lemmas hh_filter_impl = SetGA.iflt_filter_correct[OF hh_inj_image_filter_impl, folded hh_filter_def]
  interpretation hh: set_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_filter using hh_filter_impl .
  definition "ha_filter == SetGA.iflt_filter ha_inj_image_filter"
  lemmas ha_filter_impl = SetGA.iflt_filter_correct[OF ha_inj_image_filter_impl, folded ha_filter_def]
  interpretation ha: set_filter hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ha_filter using ha_filter_impl .
  definition "his_filter == SetGA.iflt_filter his_inj_image_filter"
  lemmas his_filter_impl = SetGA.iflt_filter_correct[OF his_inj_image_filter_impl, folded his_filter_def]
  interpretation his: set_filter hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_filter using his_filter_impl .
  definition "ali_filter == SetGA.iflt_filter ali_inj_image_filter"
  lemmas ali_filter_impl = SetGA.iflt_filter_correct[OF ali_inj_image_filter_impl, folded ali_filter_def]
  interpretation ali: set_filter ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ali_filter using ali_filter_impl .
  definition "al_filter == SetGA.iflt_filter al_inj_image_filter"
  lemmas al_filter_impl = SetGA.iflt_filter_correct[OF al_inj_image_filter_impl, folded al_filter_def]
  interpretation al: set_filter ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar al_filter using al_filter_impl .
  definition "ar_filter == SetGA.iflt_filter ar_inj_image_filter"
  lemmas ar_filter_impl = SetGA.iflt_filter_correct[OF ar_inj_image_filter_impl, folded ar_filter_def]
  interpretation ar: set_filter ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ar_filter using ar_filter_impl .
  definition "ah_filter == SetGA.iflt_filter ah_inj_image_filter"
  lemmas ah_filter_impl = SetGA.iflt_filter_correct[OF ah_inj_image_filter_impl, folded ah_filter_def]
  interpretation ah: set_filter ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ah_filter using ah_filter_impl .
  definition "aa_filter == SetGA.iflt_filter aa_inj_image_filter"
  lemmas aa_filter_impl = SetGA.iflt_filter_correct[OF aa_inj_image_filter_impl, folded aa_filter_def]
  interpretation aa: set_filter ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aa_filter using aa_filter_impl .
  definition "ais_filter == SetGA.iflt_filter ais_inj_image_filter"
  lemmas ais_filter_impl = SetGA.iflt_filter_correct[OF ais_inj_image_filter_impl, folded ais_filter_def]
  interpretation ais: set_filter ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_filter using ais_filter_impl .
  definition "isli_filter == SetGA.iflt_filter isli_inj_image_filter"
  lemmas isli_filter_impl = SetGA.iflt_filter_correct[OF isli_inj_image_filter_impl, folded isli_filter_def]
  interpretation isli: set_filter ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_filter using isli_filter_impl .
  definition "isl_filter == SetGA.iflt_filter isl_inj_image_filter"
  lemmas isl_filter_impl = SetGA.iflt_filter_correct[OF isl_inj_image_filter_impl, folded isl_filter_def]
  interpretation isl: set_filter ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_filter using isl_filter_impl .
  definition "isr_filter == SetGA.iflt_filter isr_inj_image_filter"
  lemmas isr_filter_impl = SetGA.iflt_filter_correct[OF isr_inj_image_filter_impl, folded isr_filter_def]
  interpretation isr: set_filter ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_filter using isr_filter_impl .
  definition "ish_filter == SetGA.iflt_filter ish_inj_image_filter"
  lemmas ish_filter_impl = SetGA.iflt_filter_correct[OF ish_inj_image_filter_impl, folded ish_filter_def]
  interpretation ish: set_filter ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_filter using ish_filter_impl .
  definition "isa_filter == SetGA.iflt_filter isa_inj_image_filter"
  lemmas isa_filter_impl = SetGA.iflt_filter_correct[OF isa_inj_image_filter_impl, folded isa_filter_def]
  interpretation isa: set_filter ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_filter using isa_filter_impl .
  definition "isis_filter == SetGA.iflt_filter isis_inj_image_filter"
  lemmas isis_filter_impl = SetGA.iflt_filter_correct[OF isis_inj_image_filter_impl, folded isis_filter_def]
  interpretation isis: set_filter ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_filter using isis_filter_impl .

  definition "lilili_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty lilili_union"
  lemmas lilili_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl lilili_union_impl, folded lilili_Union_image_def]
  interpretation lilili: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar lilili_Union_image using lilili_Union_image_impl .
  definition "lilli_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty llili_union"
  lemmas lilli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl llili_union_impl, folded lilli_Union_image_def]
  interpretation lilli: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lilli_Union_image using lilli_Union_image_impl .
  definition "lirli_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty rlili_union"
  lemmas lirli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl rlili_union_impl, folded lirli_Union_image_def]
  interpretation lirli: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lirli_Union_image using lirli_Union_image_impl .
  definition "lihli_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty hlili_union"
  lemmas lihli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl hlili_union_impl, folded lihli_Union_image_def]
  interpretation lihli: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lihli_Union_image using lihli_Union_image_impl .
  definition "liali_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty alili_union"
  lemmas liali_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl alili_union_impl, folded liali_Union_image_def]
  interpretation liali: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar liali_Union_image using liali_Union_image_impl .
  definition "liisli_Union_image == SetGA.it_Union_image lsi_iteratei lsi_empty islili_union"
  lemmas liisli_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl lsi_empty_impl islili_union_impl, folded liisli_Union_image_def]
  interpretation liisli: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar liisli_Union_image using liisli_Union_image_impl .
  definition "lilil_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty lill_union"
  lemmas lilil_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl lill_union_impl, folded lilil_Union_image_def]
  interpretation lilil: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar lilil_Union_image using lilil_Union_image_impl .
  definition "lill_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty lll_union"
  lemmas lill_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl lll_union_impl, folded lill_Union_image_def]
  interpretation lill: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lill_Union_image using lill_Union_image_impl .
  definition "lirl_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty rll_union"
  lemmas lirl_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl rll_union_impl, folded lirl_Union_image_def]
  interpretation lirl: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lirl_Union_image using lirl_Union_image_impl .
  definition "lihl_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty hll_union"
  lemmas lihl_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl hll_union_impl, folded lihl_Union_image_def]
  interpretation lihl: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lihl_Union_image using lihl_Union_image_impl .
  definition "lial_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty all_union"
  lemmas lial_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl all_union_impl, folded lial_Union_image_def]
  interpretation lial: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lial_Union_image using lial_Union_image_impl .
  definition "liisl_Union_image == SetGA.it_Union_image lsi_iteratei ls_empty isll_union"
  lemmas liisl_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ls_empty_impl isll_union_impl, folded liisl_Union_image_def]
  interpretation liisl: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar liisl_Union_image using liisl_Union_image_impl .
  definition "lilir_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty lirr_union"
  lemmas lilir_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl lirr_union_impl, folded lilir_Union_image_def]
  interpretation lilir: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar lilir_Union_image using lilir_Union_image_impl .
  definition "lilr_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty lrr_union"
  lemmas lilr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl lrr_union_impl, folded lilr_Union_image_def]
  interpretation lilr: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar lilr_Union_image using lilr_Union_image_impl .
  definition "lirr_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty rrr_union"
  lemmas lirr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl rrr_union_impl, folded lirr_Union_image_def]
  interpretation lirr: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lirr_Union_image using lirr_Union_image_impl .
  definition "lihr_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty hrr_union"
  lemmas lihr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl hrr_union_impl, folded lihr_Union_image_def]
  interpretation lihr: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lihr_Union_image using lihr_Union_image_impl .
  definition "liar_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty arr_union"
  lemmas liar_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl arr_union_impl, folded liar_Union_image_def]
  interpretation liar: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar liar_Union_image using liar_Union_image_impl .
  definition "liisr_Union_image == SetGA.it_Union_image lsi_iteratei rs_empty isrr_union"
  lemmas liisr_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl rs_empty_impl isrr_union_impl, folded liisr_Union_image_def]
  interpretation liisr: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar liisr_Union_image using liisr_Union_image_impl .
  definition "lilih_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty lihh_union"
  lemmas lilih_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl lihh_union_impl, folded lilih_Union_image_def]
  interpretation lilih: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar lilih_Union_image using lilih_Union_image_impl .
  definition "lilh_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty lhh_union"
  lemmas lilh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl lhh_union_impl, folded lilh_Union_image_def]
  interpretation lilh: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar lilh_Union_image using lilh_Union_image_impl .
  definition "lirh_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty rhh_union"
  lemmas lirh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl rhh_union_impl, folded lirh_Union_image_def]
  interpretation lirh: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lirh_Union_image using lirh_Union_image_impl .
  definition "lihh_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty hhh_union"
  lemmas lihh_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl hhh_union_impl, folded lihh_Union_image_def]
  interpretation lihh: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lihh_Union_image using lihh_Union_image_impl .
  definition "liah_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty ahh_union"
  lemmas liah_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl ahh_union_impl, folded liah_Union_image_def]
  interpretation liah: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar liah_Union_image using liah_Union_image_impl .
  definition "liish_Union_image == SetGA.it_Union_image lsi_iteratei hs_empty ishh_union"
  lemmas liish_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl hs_empty_impl ishh_union_impl, folded liish_Union_image_def]
  interpretation liish: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar liish_Union_image using liish_Union_image_impl .
  definition "lilia_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty liaa_union"
  lemmas lilia_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl liaa_union_impl, folded lilia_Union_image_def]
  interpretation lilia: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar lilia_Union_image using lilia_Union_image_impl .
  definition "lila_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty laa_union"
  lemmas lila_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl laa_union_impl, folded lila_Union_image_def]
  interpretation lila: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lila_Union_image using lila_Union_image_impl .
  definition "lira_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty raa_union"
  lemmas lira_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl raa_union_impl, folded lira_Union_image_def]
  interpretation lira: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lira_Union_image using lira_Union_image_impl .
  definition "liha_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty haa_union"
  lemmas liha_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl haa_union_impl, folded liha_Union_image_def]
  interpretation liha: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar liha_Union_image using liha_Union_image_impl .
  definition "liaa_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty aaa_union"
  lemmas liaa_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl aaa_union_impl, folded liaa_Union_image_def]
  interpretation liaa: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar liaa_Union_image using liaa_Union_image_impl .
  definition "liisa_Union_image == SetGA.it_Union_image lsi_iteratei ahs_empty isaa_union"
  lemmas liisa_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ahs_empty_impl isaa_union_impl, folded liisa_Union_image_def]
  interpretation liisa: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar liisa_Union_image using liisa_Union_image_impl .
  definition "liliis_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty liisis_union"
  lemmas liliis_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl liisis_union_impl, folded liliis_Union_image_def]
  interpretation liliis: set_Union_image lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liliis_Union_image using liliis_Union_image_impl .
  definition "lilis_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty lisis_union"
  lemmas lilis_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl lisis_union_impl, folded lilis_Union_image_def]
  interpretation lilis: set_Union_image lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar lilis_Union_image using lilis_Union_image_impl .
  definition "liris_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty risis_union"
  lemmas liris_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl risis_union_impl, folded liris_Union_image_def]
  interpretation liris: set_Union_image lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar liris_Union_image using liris_Union_image_impl .
  definition "lihis_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty hisis_union"
  lemmas lihis_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl hisis_union_impl, folded lihis_Union_image_def]
  interpretation lihis: set_Union_image lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar lihis_Union_image using lihis_Union_image_impl .
  definition "liais_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty aisis_union"
  lemmas liais_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl aisis_union_impl, folded liais_Union_image_def]
  interpretation liais: set_Union_image lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar liais_Union_image using liais_Union_image_impl .
  definition "liisis_Union_image == SetGA.it_Union_image lsi_iteratei ias_empty isisis_union"
  lemmas liisis_Union_image_impl = SetGA.it_Union_image_correct[OF lsi_iteratei_impl ias_empty_impl isisis_union_impl, folded liisis_Union_image_def]
  interpretation liisis: set_Union_image lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar liisis_Union_image using liisis_Union_image_impl .
  definition "llili_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty lilili_union"
  lemmas llili_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl lilili_union_impl, folded llili_Union_image_def]
  interpretation llili: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar llili_Union_image using llili_Union_image_impl .
  definition "llli_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty llili_union"
  lemmas llli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl llili_union_impl, folded llli_Union_image_def]
  interpretation llli: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar llli_Union_image using llli_Union_image_impl .
  definition "lrli_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty rlili_union"
  lemmas lrli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl rlili_union_impl, folded lrli_Union_image_def]
  interpretation lrli: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lrli_Union_image using lrli_Union_image_impl .
  definition "lhli_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty hlili_union"
  lemmas lhli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl hlili_union_impl, folded lhli_Union_image_def]
  interpretation lhli: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lhli_Union_image using lhli_Union_image_impl .
  definition "lali_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty alili_union"
  lemmas lali_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl alili_union_impl, folded lali_Union_image_def]
  interpretation lali: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lali_Union_image using lali_Union_image_impl .
  definition "lisli_Union_image == SetGA.it_Union_image ls_iteratei lsi_empty islili_union"
  lemmas lisli_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl lsi_empty_impl islili_union_impl, folded lisli_Union_image_def]
  interpretation lisli: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lisli_Union_image using lisli_Union_image_impl .
  definition "llil_Union_image == SetGA.it_Union_image ls_iteratei ls_empty lill_union"
  lemmas llil_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl lill_union_impl, folded llil_Union_image_def]
  interpretation llil: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar llil_Union_image using llil_Union_image_impl .
  definition "lll_Union_image == SetGA.it_Union_image ls_iteratei ls_empty lll_union"
  lemmas lll_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl lll_union_impl, folded lll_Union_image_def]
  interpretation lll: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_Union_image using lll_Union_image_impl .
  definition "lrl_Union_image == SetGA.it_Union_image ls_iteratei ls_empty rll_union"
  lemmas lrl_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl rll_union_impl, folded lrl_Union_image_def]
  interpretation lrl: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_Union_image using lrl_Union_image_impl .
  definition "lhl_Union_image == SetGA.it_Union_image ls_iteratei ls_empty hll_union"
  lemmas lhl_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl hll_union_impl, folded lhl_Union_image_def]
  interpretation lhl: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_Union_image using lhl_Union_image_impl .
  definition "lal_Union_image == SetGA.it_Union_image ls_iteratei ls_empty all_union"
  lemmas lal_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl all_union_impl, folded lal_Union_image_def]
  interpretation lal: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lal_Union_image using lal_Union_image_impl .
  definition "lisl_Union_image == SetGA.it_Union_image ls_iteratei ls_empty isll_union"
  lemmas lisl_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ls_empty_impl isll_union_impl, folded lisl_Union_image_def]
  interpretation lisl: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar lisl_Union_image using lisl_Union_image_impl .
  definition "llir_Union_image == SetGA.it_Union_image ls_iteratei rs_empty lirr_union"
  lemmas llir_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl lirr_union_impl, folded llir_Union_image_def]
  interpretation llir: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar llir_Union_image using llir_Union_image_impl .
  definition "llr_Union_image == SetGA.it_Union_image ls_iteratei rs_empty lrr_union"
  lemmas llr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl lrr_union_impl, folded llr_Union_image_def]
  interpretation llr: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_Union_image using llr_Union_image_impl .
  definition "lrr_Union_image == SetGA.it_Union_image ls_iteratei rs_empty rrr_union"
  lemmas lrr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl rrr_union_impl, folded lrr_Union_image_def]
  interpretation lrr: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_Union_image using lrr_Union_image_impl .
  definition "lhr_Union_image == SetGA.it_Union_image ls_iteratei rs_empty hrr_union"
  lemmas lhr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl hrr_union_impl, folded lhr_Union_image_def]
  interpretation lhr: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_Union_image using lhr_Union_image_impl .
  definition "lar_Union_image == SetGA.it_Union_image ls_iteratei rs_empty arr_union"
  lemmas lar_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl arr_union_impl, folded lar_Union_image_def]
  interpretation lar: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lar_Union_image using lar_Union_image_impl .
  definition "lisr_Union_image == SetGA.it_Union_image ls_iteratei rs_empty isrr_union"
  lemmas lisr_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl rs_empty_impl isrr_union_impl, folded lisr_Union_image_def]
  interpretation lisr: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar lisr_Union_image using lisr_Union_image_impl .
  definition "llih_Union_image == SetGA.it_Union_image ls_iteratei hs_empty lihh_union"
  lemmas llih_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl lihh_union_impl, folded llih_Union_image_def]
  interpretation llih: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar llih_Union_image using llih_Union_image_impl .
  definition "llh_Union_image == SetGA.it_Union_image ls_iteratei hs_empty lhh_union"
  lemmas llh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl lhh_union_impl, folded llh_Union_image_def]
  interpretation llh: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_Union_image using llh_Union_image_impl .
  definition "lrh_Union_image == SetGA.it_Union_image ls_iteratei hs_empty rhh_union"
  lemmas lrh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl rhh_union_impl, folded lrh_Union_image_def]
  interpretation lrh: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_Union_image using lrh_Union_image_impl .
  definition "lhh_Union_image == SetGA.it_Union_image ls_iteratei hs_empty hhh_union"
  lemmas lhh_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl hhh_union_impl, folded lhh_Union_image_def]
  interpretation lhh: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_Union_image using lhh_Union_image_impl .
  definition "lah_Union_image == SetGA.it_Union_image ls_iteratei hs_empty ahh_union"
  lemmas lah_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl ahh_union_impl, folded lah_Union_image_def]
  interpretation lah: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lah_Union_image using lah_Union_image_impl .
  definition "lish_Union_image == SetGA.it_Union_image ls_iteratei hs_empty ishh_union"
  lemmas lish_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl hs_empty_impl ishh_union_impl, folded lish_Union_image_def]
  interpretation lish: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar lish_Union_image using lish_Union_image_impl .
  definition "llia_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty liaa_union"
  lemmas llia_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl liaa_union_impl, folded llia_Union_image_def]
  interpretation llia: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar llia_Union_image using llia_Union_image_impl .
  definition "lla_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty laa_union"
  lemmas lla_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl laa_union_impl, folded lla_Union_image_def]
  interpretation lla: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar lla_Union_image using lla_Union_image_impl .
  definition "lra_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty raa_union"
  lemmas lra_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl raa_union_impl, folded lra_Union_image_def]
  interpretation lra: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lra_Union_image using lra_Union_image_impl .
  definition "lha_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty haa_union"
  lemmas lha_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl haa_union_impl, folded lha_Union_image_def]
  interpretation lha: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lha_Union_image using lha_Union_image_impl .
  definition "laa_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty aaa_union"
  lemmas laa_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl aaa_union_impl, folded laa_Union_image_def]
  interpretation laa: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar laa_Union_image using laa_Union_image_impl .
  definition "lisa_Union_image == SetGA.it_Union_image ls_iteratei ahs_empty isaa_union"
  lemmas lisa_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ahs_empty_impl isaa_union_impl, folded lisa_Union_image_def]
  interpretation lisa: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar lisa_Union_image using lisa_Union_image_impl .
  definition "lliis_Union_image == SetGA.it_Union_image ls_iteratei ias_empty liisis_union"
  lemmas lliis_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl liisis_union_impl, folded lliis_Union_image_def]
  interpretation lliis: set_Union_image ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar lliis_Union_image using lliis_Union_image_impl .
  definition "llis_Union_image == SetGA.it_Union_image ls_iteratei ias_empty lisis_union"
  lemmas llis_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl lisis_union_impl, folded llis_Union_image_def]
  interpretation llis: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar llis_Union_image using llis_Union_image_impl .
  definition "lris_Union_image == SetGA.it_Union_image ls_iteratei ias_empty risis_union"
  lemmas lris_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl risis_union_impl, folded lris_Union_image_def]
  interpretation lris: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar lris_Union_image using lris_Union_image_impl .
  definition "lhis_Union_image == SetGA.it_Union_image ls_iteratei ias_empty hisis_union"
  lemmas lhis_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl hisis_union_impl, folded lhis_Union_image_def]
  interpretation lhis: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar lhis_Union_image using lhis_Union_image_impl .
  definition "lais_Union_image == SetGA.it_Union_image ls_iteratei ias_empty aisis_union"
  lemmas lais_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl aisis_union_impl, folded lais_Union_image_def]
  interpretation lais: set_Union_image ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar lais_Union_image using lais_Union_image_impl .
  definition "lisis_Union_image == SetGA.it_Union_image ls_iteratei ias_empty isisis_union"
  lemmas lisis_Union_image_impl = SetGA.it_Union_image_correct[OF ls_iteratei_impl ias_empty_impl isisis_union_impl, folded lisis_Union_image_def]
  interpretation lisis: set_Union_image ls_\<alpha> ls_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar lisis_Union_image using lisis_Union_image_impl .
  definition "rlili_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty lilili_union"
  lemmas rlili_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl lilili_union_impl, folded rlili_Union_image_def]
  interpretation rlili: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar rlili_Union_image using rlili_Union_image_impl .
  definition "rlli_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty llili_union"
  lemmas rlli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl llili_union_impl, folded rlli_Union_image_def]
  interpretation rlli: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar rlli_Union_image using rlli_Union_image_impl .
  definition "rrli_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty rlili_union"
  lemmas rrli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl rlili_union_impl, folded rrli_Union_image_def]
  interpretation rrli: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rrli_Union_image using rrli_Union_image_impl .
  definition "rhli_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty hlili_union"
  lemmas rhli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl hlili_union_impl, folded rhli_Union_image_def]
  interpretation rhli: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rhli_Union_image using rhli_Union_image_impl .
  definition "rali_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty alili_union"
  lemmas rali_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl alili_union_impl, folded rali_Union_image_def]
  interpretation rali: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rali_Union_image using rali_Union_image_impl .
  definition "risli_Union_image == SetGA.it_Union_image rs_iteratei lsi_empty islili_union"
  lemmas risli_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl lsi_empty_impl islili_union_impl, folded risli_Union_image_def]
  interpretation risli: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar risli_Union_image using risli_Union_image_impl .
  definition "rlil_Union_image == SetGA.it_Union_image rs_iteratei ls_empty lill_union"
  lemmas rlil_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl lill_union_impl, folded rlil_Union_image_def]
  interpretation rlil: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar rlil_Union_image using rlil_Union_image_impl .
  definition "rll_Union_image == SetGA.it_Union_image rs_iteratei ls_empty lll_union"
  lemmas rll_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl lll_union_impl, folded rll_Union_image_def]
  interpretation rll: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_Union_image using rll_Union_image_impl .
  definition "rrl_Union_image == SetGA.it_Union_image rs_iteratei ls_empty rll_union"
  lemmas rrl_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl rll_union_impl, folded rrl_Union_image_def]
  interpretation rrl: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_Union_image using rrl_Union_image_impl .
  definition "rhl_Union_image == SetGA.it_Union_image rs_iteratei ls_empty hll_union"
  lemmas rhl_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl hll_union_impl, folded rhl_Union_image_def]
  interpretation rhl: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_Union_image using rhl_Union_image_impl .
  definition "ral_Union_image == SetGA.it_Union_image rs_iteratei ls_empty all_union"
  lemmas ral_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl all_union_impl, folded ral_Union_image_def]
  interpretation ral: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ral_Union_image using ral_Union_image_impl .
  definition "risl_Union_image == SetGA.it_Union_image rs_iteratei ls_empty isll_union"
  lemmas risl_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ls_empty_impl isll_union_impl, folded risl_Union_image_def]
  interpretation risl: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar risl_Union_image using risl_Union_image_impl .
  definition "rlir_Union_image == SetGA.it_Union_image rs_iteratei rs_empty lirr_union"
  lemmas rlir_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl lirr_union_impl, folded rlir_Union_image_def]
  interpretation rlir: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar rlir_Union_image using rlir_Union_image_impl .
  definition "rlr_Union_image == SetGA.it_Union_image rs_iteratei rs_empty lrr_union"
  lemmas rlr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl lrr_union_impl, folded rlr_Union_image_def]
  interpretation rlr: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_Union_image using rlr_Union_image_impl .
  definition "rrr_Union_image == SetGA.it_Union_image rs_iteratei rs_empty rrr_union"
  lemmas rrr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl rrr_union_impl, folded rrr_Union_image_def]
  interpretation rrr: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_Union_image using rrr_Union_image_impl .
  definition "rhr_Union_image == SetGA.it_Union_image rs_iteratei rs_empty hrr_union"
  lemmas rhr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl hrr_union_impl, folded rhr_Union_image_def]
  interpretation rhr: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_Union_image using rhr_Union_image_impl .
  definition "rar_Union_image == SetGA.it_Union_image rs_iteratei rs_empty arr_union"
  lemmas rar_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl arr_union_impl, folded rar_Union_image_def]
  interpretation rar: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rar_Union_image using rar_Union_image_impl .
  definition "risr_Union_image == SetGA.it_Union_image rs_iteratei rs_empty isrr_union"
  lemmas risr_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl rs_empty_impl isrr_union_impl, folded risr_Union_image_def]
  interpretation risr: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar risr_Union_image using risr_Union_image_impl .
  definition "rlih_Union_image == SetGA.it_Union_image rs_iteratei hs_empty lihh_union"
  lemmas rlih_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl lihh_union_impl, folded rlih_Union_image_def]
  interpretation rlih: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar rlih_Union_image using rlih_Union_image_impl .
  definition "rlh_Union_image == SetGA.it_Union_image rs_iteratei hs_empty lhh_union"
  lemmas rlh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl lhh_union_impl, folded rlh_Union_image_def]
  interpretation rlh: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_Union_image using rlh_Union_image_impl .
  definition "rrh_Union_image == SetGA.it_Union_image rs_iteratei hs_empty rhh_union"
  lemmas rrh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl rhh_union_impl, folded rrh_Union_image_def]
  interpretation rrh: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_Union_image using rrh_Union_image_impl .
  definition "rhh_Union_image == SetGA.it_Union_image rs_iteratei hs_empty hhh_union"
  lemmas rhh_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl hhh_union_impl, folded rhh_Union_image_def]
  interpretation rhh: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_Union_image using rhh_Union_image_impl .
  definition "rah_Union_image == SetGA.it_Union_image rs_iteratei hs_empty ahh_union"
  lemmas rah_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl ahh_union_impl, folded rah_Union_image_def]
  interpretation rah: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rah_Union_image using rah_Union_image_impl .
  definition "rish_Union_image == SetGA.it_Union_image rs_iteratei hs_empty ishh_union"
  lemmas rish_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl hs_empty_impl ishh_union_impl, folded rish_Union_image_def]
  interpretation rish: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar rish_Union_image using rish_Union_image_impl .
  definition "rlia_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty liaa_union"
  lemmas rlia_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl liaa_union_impl, folded rlia_Union_image_def]
  interpretation rlia: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar rlia_Union_image using rlia_Union_image_impl .
  definition "rla_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty laa_union"
  lemmas rla_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl laa_union_impl, folded rla_Union_image_def]
  interpretation rla: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar rla_Union_image using rla_Union_image_impl .
  definition "rra_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty raa_union"
  lemmas rra_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl raa_union_impl, folded rra_Union_image_def]
  interpretation rra: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar rra_Union_image using rra_Union_image_impl .
  definition "rha_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty haa_union"
  lemmas rha_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl haa_union_impl, folded rha_Union_image_def]
  interpretation rha: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rha_Union_image using rha_Union_image_impl .
  definition "raa_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty aaa_union"
  lemmas raa_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl aaa_union_impl, folded raa_Union_image_def]
  interpretation raa: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar raa_Union_image using raa_Union_image_impl .
  definition "risa_Union_image == SetGA.it_Union_image rs_iteratei ahs_empty isaa_union"
  lemmas risa_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ahs_empty_impl isaa_union_impl, folded risa_Union_image_def]
  interpretation risa: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar risa_Union_image using risa_Union_image_impl .
  definition "rliis_Union_image == SetGA.it_Union_image rs_iteratei ias_empty liisis_union"
  lemmas rliis_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl liisis_union_impl, folded rliis_Union_image_def]
  interpretation rliis: set_Union_image rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar rliis_Union_image using rliis_Union_image_impl .
  definition "rlis_Union_image == SetGA.it_Union_image rs_iteratei ias_empty lisis_union"
  lemmas rlis_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl lisis_union_impl, folded rlis_Union_image_def]
  interpretation rlis: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar rlis_Union_image using rlis_Union_image_impl .
  definition "rris_Union_image == SetGA.it_Union_image rs_iteratei ias_empty risis_union"
  lemmas rris_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl risis_union_impl, folded rris_Union_image_def]
  interpretation rris: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar rris_Union_image using rris_Union_image_impl .
  definition "rhis_Union_image == SetGA.it_Union_image rs_iteratei ias_empty hisis_union"
  lemmas rhis_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl hisis_union_impl, folded rhis_Union_image_def]
  interpretation rhis: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar rhis_Union_image using rhis_Union_image_impl .
  definition "rais_Union_image == SetGA.it_Union_image rs_iteratei ias_empty aisis_union"
  lemmas rais_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl aisis_union_impl, folded rais_Union_image_def]
  interpretation rais: set_Union_image rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar rais_Union_image using rais_Union_image_impl .
  definition "risis_Union_image == SetGA.it_Union_image rs_iteratei ias_empty isisis_union"
  lemmas risis_Union_image_impl = SetGA.it_Union_image_correct[OF rs_iteratei_impl ias_empty_impl isisis_union_impl, folded risis_Union_image_def]
  interpretation risis: set_Union_image rs_\<alpha> rs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar risis_Union_image using risis_Union_image_impl .
  definition "hlili_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty lilili_union"
  lemmas hlili_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl lilili_union_impl, folded hlili_Union_image_def]
  interpretation hlili: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar hlili_Union_image using hlili_Union_image_impl .
  definition "hlli_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty llili_union"
  lemmas hlli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl llili_union_impl, folded hlli_Union_image_def]
  interpretation hlli: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar hlli_Union_image using hlli_Union_image_impl .
  definition "hrli_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty rlili_union"
  lemmas hrli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl rlili_union_impl, folded hrli_Union_image_def]
  interpretation hrli: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar hrli_Union_image using hrli_Union_image_impl .
  definition "hhli_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty hlili_union"
  lemmas hhli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl hlili_union_impl, folded hhli_Union_image_def]
  interpretation hhli: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hhli_Union_image using hhli_Union_image_impl .
  definition "hali_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty alili_union"
  lemmas hali_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl alili_union_impl, folded hali_Union_image_def]
  interpretation hali: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hali_Union_image using hali_Union_image_impl .
  definition "hisli_Union_image == SetGA.it_Union_image hs_iteratei lsi_empty islili_union"
  lemmas hisli_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl lsi_empty_impl islili_union_impl, folded hisli_Union_image_def]
  interpretation hisli: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar hisli_Union_image using hisli_Union_image_impl .
  definition "hlil_Union_image == SetGA.it_Union_image hs_iteratei ls_empty lill_union"
  lemmas hlil_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl lill_union_impl, folded hlil_Union_image_def]
  interpretation hlil: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar hlil_Union_image using hlil_Union_image_impl .
  definition "hll_Union_image == SetGA.it_Union_image hs_iteratei ls_empty lll_union"
  lemmas hll_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl lll_union_impl, folded hll_Union_image_def]
  interpretation hll: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_Union_image using hll_Union_image_impl .
  definition "hrl_Union_image == SetGA.it_Union_image hs_iteratei ls_empty rll_union"
  lemmas hrl_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl rll_union_impl, folded hrl_Union_image_def]
  interpretation hrl: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_Union_image using hrl_Union_image_impl .
  definition "hhl_Union_image == SetGA.it_Union_image hs_iteratei ls_empty hll_union"
  lemmas hhl_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl hll_union_impl, folded hhl_Union_image_def]
  interpretation hhl: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_Union_image using hhl_Union_image_impl .
  definition "hal_Union_image == SetGA.it_Union_image hs_iteratei ls_empty all_union"
  lemmas hal_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl all_union_impl, folded hal_Union_image_def]
  interpretation hal: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hal_Union_image using hal_Union_image_impl .
  definition "hisl_Union_image == SetGA.it_Union_image hs_iteratei ls_empty isll_union"
  lemmas hisl_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ls_empty_impl isll_union_impl, folded hisl_Union_image_def]
  interpretation hisl: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar hisl_Union_image using hisl_Union_image_impl .
  definition "hlir_Union_image == SetGA.it_Union_image hs_iteratei rs_empty lirr_union"
  lemmas hlir_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl lirr_union_impl, folded hlir_Union_image_def]
  interpretation hlir: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar hlir_Union_image using hlir_Union_image_impl .
  definition "hlr_Union_image == SetGA.it_Union_image hs_iteratei rs_empty lrr_union"
  lemmas hlr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl lrr_union_impl, folded hlr_Union_image_def]
  interpretation hlr: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_Union_image using hlr_Union_image_impl .
  definition "hrr_Union_image == SetGA.it_Union_image hs_iteratei rs_empty rrr_union"
  lemmas hrr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl rrr_union_impl, folded hrr_Union_image_def]
  interpretation hrr: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_Union_image using hrr_Union_image_impl .
  definition "hhr_Union_image == SetGA.it_Union_image hs_iteratei rs_empty hrr_union"
  lemmas hhr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl hrr_union_impl, folded hhr_Union_image_def]
  interpretation hhr: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_Union_image using hhr_Union_image_impl .
  definition "har_Union_image == SetGA.it_Union_image hs_iteratei rs_empty arr_union"
  lemmas har_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl arr_union_impl, folded har_Union_image_def]
  interpretation har: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar har_Union_image using har_Union_image_impl .
  definition "hisr_Union_image == SetGA.it_Union_image hs_iteratei rs_empty isrr_union"
  lemmas hisr_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl rs_empty_impl isrr_union_impl, folded hisr_Union_image_def]
  interpretation hisr: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar hisr_Union_image using hisr_Union_image_impl .
  definition "hlih_Union_image == SetGA.it_Union_image hs_iteratei hs_empty lihh_union"
  lemmas hlih_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl lihh_union_impl, folded hlih_Union_image_def]
  interpretation hlih: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar hlih_Union_image using hlih_Union_image_impl .
  definition "hlh_Union_image == SetGA.it_Union_image hs_iteratei hs_empty lhh_union"
  lemmas hlh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl lhh_union_impl, folded hlh_Union_image_def]
  interpretation hlh: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_Union_image using hlh_Union_image_impl .
  definition "hrh_Union_image == SetGA.it_Union_image hs_iteratei hs_empty rhh_union"
  lemmas hrh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl rhh_union_impl, folded hrh_Union_image_def]
  interpretation hrh: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_Union_image using hrh_Union_image_impl .
  definition "hhh_Union_image == SetGA.it_Union_image hs_iteratei hs_empty hhh_union"
  lemmas hhh_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl hhh_union_impl, folded hhh_Union_image_def]
  interpretation hhh: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_Union_image using hhh_Union_image_impl .
  definition "hah_Union_image == SetGA.it_Union_image hs_iteratei hs_empty ahh_union"
  lemmas hah_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl ahh_union_impl, folded hah_Union_image_def]
  interpretation hah: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hah_Union_image using hah_Union_image_impl .
  definition "hish_Union_image == SetGA.it_Union_image hs_iteratei hs_empty ishh_union"
  lemmas hish_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl hs_empty_impl ishh_union_impl, folded hish_Union_image_def]
  interpretation hish: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar hish_Union_image using hish_Union_image_impl .
  definition "hlia_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty liaa_union"
  lemmas hlia_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl liaa_union_impl, folded hlia_Union_image_def]
  interpretation hlia: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar hlia_Union_image using hlia_Union_image_impl .
  definition "hla_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty laa_union"
  lemmas hla_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl laa_union_impl, folded hla_Union_image_def]
  interpretation hla: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar hla_Union_image using hla_Union_image_impl .
  definition "hra_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty raa_union"
  lemmas hra_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl raa_union_impl, folded hra_Union_image_def]
  interpretation hra: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar hra_Union_image using hra_Union_image_impl .
  definition "hha_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty haa_union"
  lemmas hha_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl haa_union_impl, folded hha_Union_image_def]
  interpretation hha: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar hha_Union_image using hha_Union_image_impl .
  definition "haa_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty aaa_union"
  lemmas haa_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl aaa_union_impl, folded haa_Union_image_def]
  interpretation haa: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar haa_Union_image using haa_Union_image_impl .
  definition "hisa_Union_image == SetGA.it_Union_image hs_iteratei ahs_empty isaa_union"
  lemmas hisa_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ahs_empty_impl isaa_union_impl, folded hisa_Union_image_def]
  interpretation hisa: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar hisa_Union_image using hisa_Union_image_impl .
  definition "hliis_Union_image == SetGA.it_Union_image hs_iteratei ias_empty liisis_union"
  lemmas hliis_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl liisis_union_impl, folded hliis_Union_image_def]
  interpretation hliis: set_Union_image hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar hliis_Union_image using hliis_Union_image_impl .
  definition "hlis_Union_image == SetGA.it_Union_image hs_iteratei ias_empty lisis_union"
  lemmas hlis_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl lisis_union_impl, folded hlis_Union_image_def]
  interpretation hlis: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar hlis_Union_image using hlis_Union_image_impl .
  definition "hris_Union_image == SetGA.it_Union_image hs_iteratei ias_empty risis_union"
  lemmas hris_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl risis_union_impl, folded hris_Union_image_def]
  interpretation hris: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar hris_Union_image using hris_Union_image_impl .
  definition "hhis_Union_image == SetGA.it_Union_image hs_iteratei ias_empty hisis_union"
  lemmas hhis_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl hisis_union_impl, folded hhis_Union_image_def]
  interpretation hhis: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar hhis_Union_image using hhis_Union_image_impl .
  definition "hais_Union_image == SetGA.it_Union_image hs_iteratei ias_empty aisis_union"
  lemmas hais_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl aisis_union_impl, folded hais_Union_image_def]
  interpretation hais: set_Union_image hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar hais_Union_image using hais_Union_image_impl .
  definition "hisis_Union_image == SetGA.it_Union_image hs_iteratei ias_empty isisis_union"
  lemmas hisis_Union_image_impl = SetGA.it_Union_image_correct[OF hs_iteratei_impl ias_empty_impl isisis_union_impl, folded hisis_Union_image_def]
  interpretation hisis: set_Union_image hs_\<alpha> hs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar hisis_Union_image using hisis_Union_image_impl .
  definition "alili_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty lilili_union"
  lemmas alili_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl lilili_union_impl, folded alili_Union_image_def]
  interpretation alili: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar alili_Union_image using alili_Union_image_impl .
  definition "alli_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty llili_union"
  lemmas alli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl llili_union_impl, folded alli_Union_image_def]
  interpretation alli: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar alli_Union_image using alli_Union_image_impl .
  definition "arli_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty rlili_union"
  lemmas arli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl rlili_union_impl, folded arli_Union_image_def]
  interpretation arli: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar arli_Union_image using arli_Union_image_impl .
  definition "ahli_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty hlili_union"
  lemmas ahli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl hlili_union_impl, folded ahli_Union_image_def]
  interpretation ahli: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ahli_Union_image using ahli_Union_image_impl .
  definition "aali_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty alili_union"
  lemmas aali_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl alili_union_impl, folded aali_Union_image_def]
  interpretation aali: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar aali_Union_image using aali_Union_image_impl .
  definition "aisli_Union_image == SetGA.it_Union_image ahs_iteratei lsi_empty islili_union"
  lemmas aisli_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl lsi_empty_impl islili_union_impl, folded aisli_Union_image_def]
  interpretation aisli: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar aisli_Union_image using aisli_Union_image_impl .
  definition "alil_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty lill_union"
  lemmas alil_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl lill_union_impl, folded alil_Union_image_def]
  interpretation alil: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar alil_Union_image using alil_Union_image_impl .
  definition "all_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty lll_union"
  lemmas all_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl lll_union_impl, folded all_Union_image_def]
  interpretation all: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar all_Union_image using all_Union_image_impl .
  definition "arl_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty rll_union"
  lemmas arl_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl rll_union_impl, folded arl_Union_image_def]
  interpretation arl: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar arl_Union_image using arl_Union_image_impl .
  definition "ahl_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty hll_union"
  lemmas ahl_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl hll_union_impl, folded ahl_Union_image_def]
  interpretation ahl: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ahl_Union_image using ahl_Union_image_impl .
  definition "aal_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty all_union"
  lemmas aal_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl all_union_impl, folded aal_Union_image_def]
  interpretation aal: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar aal_Union_image using aal_Union_image_impl .
  definition "aisl_Union_image == SetGA.it_Union_image ahs_iteratei ls_empty isll_union"
  lemmas aisl_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ls_empty_impl isll_union_impl, folded aisl_Union_image_def]
  interpretation aisl: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar aisl_Union_image using aisl_Union_image_impl .
  definition "alir_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty lirr_union"
  lemmas alir_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl lirr_union_impl, folded alir_Union_image_def]
  interpretation alir: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar alir_Union_image using alir_Union_image_impl .
  definition "alr_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty lrr_union"
  lemmas alr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl lrr_union_impl, folded alr_Union_image_def]
  interpretation alr: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar alr_Union_image using alr_Union_image_impl .
  definition "arr_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty rrr_union"
  lemmas arr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl rrr_union_impl, folded arr_Union_image_def]
  interpretation arr: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar arr_Union_image using arr_Union_image_impl .
  definition "ahr_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty hrr_union"
  lemmas ahr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl hrr_union_impl, folded ahr_Union_image_def]
  interpretation ahr: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ahr_Union_image using ahr_Union_image_impl .
  definition "aar_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty arr_union"
  lemmas aar_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl arr_union_impl, folded aar_Union_image_def]
  interpretation aar: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar aar_Union_image using aar_Union_image_impl .
  definition "aisr_Union_image == SetGA.it_Union_image ahs_iteratei rs_empty isrr_union"
  lemmas aisr_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl rs_empty_impl isrr_union_impl, folded aisr_Union_image_def]
  interpretation aisr: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar aisr_Union_image using aisr_Union_image_impl .
  definition "alih_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty lihh_union"
  lemmas alih_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl lihh_union_impl, folded alih_Union_image_def]
  interpretation alih: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar alih_Union_image using alih_Union_image_impl .
  definition "alh_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty lhh_union"
  lemmas alh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl lhh_union_impl, folded alh_Union_image_def]
  interpretation alh: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar alh_Union_image using alh_Union_image_impl .
  definition "arh_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty rhh_union"
  lemmas arh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl rhh_union_impl, folded arh_Union_image_def]
  interpretation arh: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar arh_Union_image using arh_Union_image_impl .
  definition "ahh_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty hhh_union"
  lemmas ahh_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl hhh_union_impl, folded ahh_Union_image_def]
  interpretation ahh: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ahh_Union_image using ahh_Union_image_impl .
  definition "aah_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty ahh_union"
  lemmas aah_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl ahh_union_impl, folded aah_Union_image_def]
  interpretation aah: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar aah_Union_image using aah_Union_image_impl .
  definition "aish_Union_image == SetGA.it_Union_image ahs_iteratei hs_empty ishh_union"
  lemmas aish_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl hs_empty_impl ishh_union_impl, folded aish_Union_image_def]
  interpretation aish: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar aish_Union_image using aish_Union_image_impl .
  definition "alia_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty liaa_union"
  lemmas alia_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl liaa_union_impl, folded alia_Union_image_def]
  interpretation alia: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar alia_Union_image using alia_Union_image_impl .
  definition "ala_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty laa_union"
  lemmas ala_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl laa_union_impl, folded ala_Union_image_def]
  interpretation ala: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar ala_Union_image using ala_Union_image_impl .
  definition "ara_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty raa_union"
  lemmas ara_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl raa_union_impl, folded ara_Union_image_def]
  interpretation ara: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar ara_Union_image using ara_Union_image_impl .
  definition "aha_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty haa_union"
  lemmas aha_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl haa_union_impl, folded aha_Union_image_def]
  interpretation aha: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar aha_Union_image using aha_Union_image_impl .
  definition "aaa_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty aaa_union"
  lemmas aaa_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl aaa_union_impl, folded aaa_Union_image_def]
  interpretation aaa: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar aaa_Union_image using aaa_Union_image_impl .
  definition "aisa_Union_image == SetGA.it_Union_image ahs_iteratei ahs_empty isaa_union"
  lemmas aisa_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ahs_empty_impl isaa_union_impl, folded aisa_Union_image_def]
  interpretation aisa: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar aisa_Union_image using aisa_Union_image_impl .
  definition "aliis_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty liisis_union"
  lemmas aliis_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl liisis_union_impl, folded aliis_Union_image_def]
  interpretation aliis: set_Union_image ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar aliis_Union_image using aliis_Union_image_impl .
  definition "alis_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty lisis_union"
  lemmas alis_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl lisis_union_impl, folded alis_Union_image_def]
  interpretation alis: set_Union_image ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar alis_Union_image using alis_Union_image_impl .
  definition "aris_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty risis_union"
  lemmas aris_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl risis_union_impl, folded aris_Union_image_def]
  interpretation aris: set_Union_image ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar aris_Union_image using aris_Union_image_impl .
  definition "ahis_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty hisis_union"
  lemmas ahis_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl hisis_union_impl, folded ahis_Union_image_def]
  interpretation ahis: set_Union_image ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar ahis_Union_image using ahis_Union_image_impl .
  definition "aais_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty aisis_union"
  lemmas aais_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl aisis_union_impl, folded aais_Union_image_def]
  interpretation aais: set_Union_image ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar aais_Union_image using aais_Union_image_impl .
  definition "aisis_Union_image == SetGA.it_Union_image ahs_iteratei ias_empty isisis_union"
  lemmas aisis_Union_image_impl = SetGA.it_Union_image_correct[OF ahs_iteratei_impl ias_empty_impl isisis_union_impl, folded aisis_Union_image_def]
  interpretation aisis: set_Union_image ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar aisis_Union_image using aisis_Union_image_impl .
  definition "islili_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty lilili_union"
  lemmas islili_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl lilili_union_impl, folded islili_Union_image_def]
  interpretation islili: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar lsi_\<alpha> lsi_invar islili_Union_image using islili_Union_image_impl .
  definition "islli_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty llili_union"
  lemmas islli_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl llili_union_impl, folded islli_Union_image_def]
  interpretation islli: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar lsi_\<alpha> lsi_invar islli_Union_image using islli_Union_image_impl .
  definition "isrli_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty rlili_union"
  lemmas isrli_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl rlili_union_impl, folded isrli_Union_image_def]
  interpretation isrli: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar lsi_\<alpha> lsi_invar isrli_Union_image using isrli_Union_image_impl .
  definition "ishli_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty hlili_union"
  lemmas ishli_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl hlili_union_impl, folded ishli_Union_image_def]
  interpretation ishli: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar lsi_\<alpha> lsi_invar ishli_Union_image using ishli_Union_image_impl .
  definition "isali_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty alili_union"
  lemmas isali_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl alili_union_impl, folded isali_Union_image_def]
  interpretation isali: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar lsi_\<alpha> lsi_invar isali_Union_image using isali_Union_image_impl .
  definition "isisli_Union_image == SetGA.it_Union_image ias_iteratei lsi_empty islili_union"
  lemmas isisli_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl lsi_empty_impl islili_union_impl, folded isisli_Union_image_def]
  interpretation isisli: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isisli_Union_image using isisli_Union_image_impl .
  definition "islil_Union_image == SetGA.it_Union_image ias_iteratei ls_empty lill_union"
  lemmas islil_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl lill_union_impl, folded islil_Union_image_def]
  interpretation islil: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ls_\<alpha> ls_invar islil_Union_image using islil_Union_image_impl .
  definition "isll_Union_image == SetGA.it_Union_image ias_iteratei ls_empty lll_union"
  lemmas isll_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl lll_union_impl, folded isll_Union_image_def]
  interpretation isll: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar isll_Union_image using isll_Union_image_impl .
  definition "isrl_Union_image == SetGA.it_Union_image ias_iteratei ls_empty rll_union"
  lemmas isrl_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl rll_union_impl, folded isrl_Union_image_def]
  interpretation isrl: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar isrl_Union_image using isrl_Union_image_impl .
  definition "ishl_Union_image == SetGA.it_Union_image ias_iteratei ls_empty hll_union"
  lemmas ishl_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl hll_union_impl, folded ishl_Union_image_def]
  interpretation ishl: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar ishl_Union_image using ishl_Union_image_impl .
  definition "isal_Union_image == SetGA.it_Union_image ias_iteratei ls_empty all_union"
  lemmas isal_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl all_union_impl, folded isal_Union_image_def]
  interpretation isal: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ls_\<alpha> ls_invar isal_Union_image using isal_Union_image_impl .
  definition "isisl_Union_image == SetGA.it_Union_image ias_iteratei ls_empty isll_union"
  lemmas isisl_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ls_empty_impl isll_union_impl, folded isisl_Union_image_def]
  interpretation isisl: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar ls_\<alpha> ls_invar isisl_Union_image using isisl_Union_image_impl .
  definition "islir_Union_image == SetGA.it_Union_image ias_iteratei rs_empty lirr_union"
  lemmas islir_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl lirr_union_impl, folded islir_Union_image_def]
  interpretation islir: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar rs_\<alpha> rs_invar islir_Union_image using islir_Union_image_impl .
  definition "islr_Union_image == SetGA.it_Union_image ias_iteratei rs_empty lrr_union"
  lemmas islr_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl lrr_union_impl, folded islr_Union_image_def]
  interpretation islr: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar islr_Union_image using islr_Union_image_impl .
  definition "isrr_Union_image == SetGA.it_Union_image ias_iteratei rs_empty rrr_union"
  lemmas isrr_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl rrr_union_impl, folded isrr_Union_image_def]
  interpretation isrr: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar isrr_Union_image using isrr_Union_image_impl .
  definition "ishr_Union_image == SetGA.it_Union_image ias_iteratei rs_empty hrr_union"
  lemmas ishr_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl hrr_union_impl, folded ishr_Union_image_def]
  interpretation ishr: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar ishr_Union_image using ishr_Union_image_impl .
  definition "isar_Union_image == SetGA.it_Union_image ias_iteratei rs_empty arr_union"
  lemmas isar_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl arr_union_impl, folded isar_Union_image_def]
  interpretation isar: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar rs_\<alpha> rs_invar isar_Union_image using isar_Union_image_impl .
  definition "isisr_Union_image == SetGA.it_Union_image ias_iteratei rs_empty isrr_union"
  lemmas isisr_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl rs_empty_impl isrr_union_impl, folded isisr_Union_image_def]
  interpretation isisr: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar rs_\<alpha> rs_invar isisr_Union_image using isisr_Union_image_impl .
  definition "islih_Union_image == SetGA.it_Union_image ias_iteratei hs_empty lihh_union"
  lemmas islih_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl lihh_union_impl, folded islih_Union_image_def]
  interpretation islih: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar hs_\<alpha> hs_invar islih_Union_image using islih_Union_image_impl .
  definition "islh_Union_image == SetGA.it_Union_image ias_iteratei hs_empty lhh_union"
  lemmas islh_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl lhh_union_impl, folded islh_Union_image_def]
  interpretation islh: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar islh_Union_image using islh_Union_image_impl .
  definition "isrh_Union_image == SetGA.it_Union_image ias_iteratei hs_empty rhh_union"
  lemmas isrh_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl rhh_union_impl, folded isrh_Union_image_def]
  interpretation isrh: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar isrh_Union_image using isrh_Union_image_impl .
  definition "ishh_Union_image == SetGA.it_Union_image ias_iteratei hs_empty hhh_union"
  lemmas ishh_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl hhh_union_impl, folded ishh_Union_image_def]
  interpretation ishh: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar ishh_Union_image using ishh_Union_image_impl .
  definition "isah_Union_image == SetGA.it_Union_image ias_iteratei hs_empty ahh_union"
  lemmas isah_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl ahh_union_impl, folded isah_Union_image_def]
  interpretation isah: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar hs_\<alpha> hs_invar isah_Union_image using isah_Union_image_impl .
  definition "isish_Union_image == SetGA.it_Union_image ias_iteratei hs_empty ishh_union"
  lemmas isish_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl hs_empty_impl ishh_union_impl, folded isish_Union_image_def]
  interpretation isish: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar hs_\<alpha> hs_invar isish_Union_image using isish_Union_image_impl .
  definition "islia_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty liaa_union"
  lemmas islia_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl liaa_union_impl, folded islia_Union_image_def]
  interpretation islia: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ahs_\<alpha> ahs_invar islia_Union_image using islia_Union_image_impl .
  definition "isla_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty laa_union"
  lemmas isla_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl laa_union_impl, folded isla_Union_image_def]
  interpretation isla: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar ahs_\<alpha> ahs_invar isla_Union_image using isla_Union_image_impl .
  definition "isra_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty raa_union"
  lemmas isra_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl raa_union_impl, folded isra_Union_image_def]
  interpretation isra: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar ahs_\<alpha> ahs_invar isra_Union_image using isra_Union_image_impl .
  definition "isha_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty haa_union"
  lemmas isha_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl haa_union_impl, folded isha_Union_image_def]
  interpretation isha: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar ahs_\<alpha> ahs_invar isha_Union_image using isha_Union_image_impl .
  definition "isaa_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty aaa_union"
  lemmas isaa_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl aaa_union_impl, folded isaa_Union_image_def]
  interpretation isaa: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ahs_\<alpha> ahs_invar isaa_Union_image using isaa_Union_image_impl .
  definition "isisa_Union_image == SetGA.it_Union_image ias_iteratei ahs_empty isaa_union"
  lemmas isisa_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ahs_empty_impl isaa_union_impl, folded isisa_Union_image_def]
  interpretation isisa: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isisa_Union_image using isisa_Union_image_impl .
  definition "isliis_Union_image == SetGA.it_Union_image ias_iteratei ias_empty liisis_union"
  lemmas isliis_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl liisis_union_impl, folded isliis_Union_image_def]
  interpretation isliis: set_Union_image ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar isliis_Union_image using isliis_Union_image_impl .
  definition "islis_Union_image == SetGA.it_Union_image ias_iteratei ias_empty lisis_union"
  lemmas islis_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl lisis_union_impl, folded islis_Union_image_def]
  interpretation islis: set_Union_image ias_\<alpha> ias_invar ls_\<alpha> ls_invar ias_\<alpha> ias_invar islis_Union_image using islis_Union_image_impl .
  definition "isris_Union_image == SetGA.it_Union_image ias_iteratei ias_empty risis_union"
  lemmas isris_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl risis_union_impl, folded isris_Union_image_def]
  interpretation isris: set_Union_image ias_\<alpha> ias_invar rs_\<alpha> rs_invar ias_\<alpha> ias_invar isris_Union_image using isris_Union_image_impl .
  definition "ishis_Union_image == SetGA.it_Union_image ias_iteratei ias_empty hisis_union"
  lemmas ishis_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl hisis_union_impl, folded ishis_Union_image_def]
  interpretation ishis: set_Union_image ias_\<alpha> ias_invar hs_\<alpha> hs_invar ias_\<alpha> ias_invar ishis_Union_image using ishis_Union_image_impl .
  definition "isais_Union_image == SetGA.it_Union_image ias_iteratei ias_empty aisis_union"
  lemmas isais_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl aisis_union_impl, folded isais_Union_image_def]
  interpretation isais: set_Union_image ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar isais_Union_image using isais_Union_image_impl .
  definition "isisis_Union_image == SetGA.it_Union_image ias_iteratei ias_empty isisis_union"
  lemmas isisis_Union_image_impl = SetGA.it_Union_image_correct[OF ias_iteratei_impl ias_empty_impl isisis_union_impl, folded isisis_Union_image_def]
  interpretation isisis: set_Union_image ias_\<alpha> ias_invar ias_\<alpha> ias_invar ias_\<alpha> ias_invar isisis_Union_image using isisis_Union_image_impl .

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
  definition "liis_disjoint_witness == SetGA.sel_disjoint_witness lsi_sel ias_memb"
  lemmas liis_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF lsi_sel_impl ias_memb_impl, folded liis_disjoint_witness_def]
  interpretation liis: set_disjoint_witness lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_disjoint_witness using liis_disjoint_witness_impl .
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
  definition "lis_disjoint_witness == SetGA.sel_disjoint_witness ls_sel ias_memb"
  lemmas lis_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ls_sel_impl ias_memb_impl, folded lis_disjoint_witness_def]
  interpretation lis: set_disjoint_witness ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_disjoint_witness using lis_disjoint_witness_impl .
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
  definition "ris_disjoint_witness == SetGA.sel_disjoint_witness rs_sel ias_memb"
  lemmas ris_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF rs_sel_impl ias_memb_impl, folded ris_disjoint_witness_def]
  interpretation ris: set_disjoint_witness rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_disjoint_witness using ris_disjoint_witness_impl .
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
  definition "his_disjoint_witness == SetGA.sel_disjoint_witness hs_sel ias_memb"
  lemmas his_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF hs_sel_impl ias_memb_impl, folded his_disjoint_witness_def]
  interpretation his: set_disjoint_witness hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_disjoint_witness using his_disjoint_witness_impl .
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
  definition "ais_disjoint_witness == SetGA.sel_disjoint_witness ahs_sel ias_memb"
  lemmas ais_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ahs_sel_impl ias_memb_impl, folded ais_disjoint_witness_def]
  interpretation ais: set_disjoint_witness ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_disjoint_witness using ais_disjoint_witness_impl .
  definition "isli_disjoint_witness == SetGA.sel_disjoint_witness ias_sel lsi_memb"
  lemmas isli_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl lsi_memb_impl, folded isli_disjoint_witness_def]
  interpretation isli: set_disjoint_witness ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_disjoint_witness using isli_disjoint_witness_impl .
  definition "isl_disjoint_witness == SetGA.sel_disjoint_witness ias_sel ls_memb"
  lemmas isl_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl ls_memb_impl, folded isl_disjoint_witness_def]
  interpretation isl: set_disjoint_witness ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_disjoint_witness using isl_disjoint_witness_impl .
  definition "isr_disjoint_witness == SetGA.sel_disjoint_witness ias_sel rs_memb"
  lemmas isr_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl rs_memb_impl, folded isr_disjoint_witness_def]
  interpretation isr: set_disjoint_witness ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_disjoint_witness using isr_disjoint_witness_impl .
  definition "ish_disjoint_witness == SetGA.sel_disjoint_witness ias_sel hs_memb"
  lemmas ish_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl hs_memb_impl, folded ish_disjoint_witness_def]
  interpretation ish: set_disjoint_witness ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_disjoint_witness using ish_disjoint_witness_impl .
  definition "isa_disjoint_witness == SetGA.sel_disjoint_witness ias_sel ahs_memb"
  lemmas isa_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl ahs_memb_impl, folded isa_disjoint_witness_def]
  interpretation isa: set_disjoint_witness ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_disjoint_witness using isa_disjoint_witness_impl .
  definition "isis_disjoint_witness == SetGA.sel_disjoint_witness ias_sel ias_memb"
  lemmas isis_disjoint_witness_impl = SetGA.sel_disjoint_witness_correct[OF ias_sel_impl ias_memb_impl, folded isis_disjoint_witness_def]
  interpretation isis: set_disjoint_witness ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_disjoint_witness using isis_disjoint_witness_impl .

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
  definition "liis_disjoint == SetGA.ball_disjoint lsi_ball ias_memb"
  lemmas liis_disjoint_impl = SetGA.ball_disjoint_correct[OF lsi_ball_impl ias_memb_impl, folded liis_disjoint_def]
  interpretation liis: set_disjoint lsi_\<alpha> lsi_invar ias_\<alpha> ias_invar liis_disjoint using liis_disjoint_impl .
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
  definition "lis_disjoint == SetGA.ball_disjoint ls_ball ias_memb"
  lemmas lis_disjoint_impl = SetGA.ball_disjoint_correct[OF ls_ball_impl ias_memb_impl, folded lis_disjoint_def]
  interpretation lis: set_disjoint ls_\<alpha> ls_invar ias_\<alpha> ias_invar lis_disjoint using lis_disjoint_impl .
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
  definition "ris_disjoint == SetGA.ball_disjoint rs_ball ias_memb"
  lemmas ris_disjoint_impl = SetGA.ball_disjoint_correct[OF rs_ball_impl ias_memb_impl, folded ris_disjoint_def]
  interpretation ris: set_disjoint rs_\<alpha> rs_invar ias_\<alpha> ias_invar ris_disjoint using ris_disjoint_impl .
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
  definition "his_disjoint == SetGA.ball_disjoint hs_ball ias_memb"
  lemmas his_disjoint_impl = SetGA.ball_disjoint_correct[OF hs_ball_impl ias_memb_impl, folded his_disjoint_def]
  interpretation his: set_disjoint hs_\<alpha> hs_invar ias_\<alpha> ias_invar his_disjoint using his_disjoint_impl .
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
  definition "ais_disjoint == SetGA.ball_disjoint ahs_ball ias_memb"
  lemmas ais_disjoint_impl = SetGA.ball_disjoint_correct[OF ahs_ball_impl ias_memb_impl, folded ais_disjoint_def]
  interpretation ais: set_disjoint ahs_\<alpha> ahs_invar ias_\<alpha> ias_invar ais_disjoint using ais_disjoint_impl .
  definition "isli_disjoint == SetGA.ball_disjoint ias_ball lsi_memb"
  lemmas isli_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl lsi_memb_impl, folded isli_disjoint_def]
  interpretation isli: set_disjoint ias_\<alpha> ias_invar lsi_\<alpha> lsi_invar isli_disjoint using isli_disjoint_impl .
  definition "isl_disjoint == SetGA.ball_disjoint ias_ball ls_memb"
  lemmas isl_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl ls_memb_impl, folded isl_disjoint_def]
  interpretation isl: set_disjoint ias_\<alpha> ias_invar ls_\<alpha> ls_invar isl_disjoint using isl_disjoint_impl .
  definition "isr_disjoint == SetGA.ball_disjoint ias_ball rs_memb"
  lemmas isr_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl rs_memb_impl, folded isr_disjoint_def]
  interpretation isr: set_disjoint ias_\<alpha> ias_invar rs_\<alpha> rs_invar isr_disjoint using isr_disjoint_impl .
  definition "ish_disjoint == SetGA.ball_disjoint ias_ball hs_memb"
  lemmas ish_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl hs_memb_impl, folded ish_disjoint_def]
  interpretation ish: set_disjoint ias_\<alpha> ias_invar hs_\<alpha> hs_invar ish_disjoint using ish_disjoint_impl .
  definition "isa_disjoint == SetGA.ball_disjoint ias_ball ahs_memb"
  lemmas isa_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl ahs_memb_impl, folded isa_disjoint_def]
  interpretation isa: set_disjoint ias_\<alpha> ias_invar ahs_\<alpha> ahs_invar isa_disjoint using isa_disjoint_impl .
  definition "isis_disjoint == SetGA.ball_disjoint ias_ball ias_memb"
  lemmas isis_disjoint_impl = SetGA.ball_disjoint_correct[OF ias_ball_impl ias_memb_impl, folded isis_disjoint_def]
  interpretation isis: set_disjoint ias_\<alpha> ias_invar ias_\<alpha> ias_invar isis_disjoint using isis_disjoint_impl .

  definition "lilili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas lilili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lilili_image_filter_cartesian_product_def]
  definition "lilil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas lilil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded lilil_image_filter_cartesian_product_def]
  definition "lilir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas lilir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded lilir_image_filter_cartesian_product_def]
  definition "lilih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas lilih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded lilih_image_filter_cartesian_product_def]
  definition "lilia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas lilia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lilia_image_filter_cartesian_product_def]
  definition "liliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas liliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded liliis_image_filter_cartesian_product_def]
  definition "lilli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas lilli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lilli_image_filter_cartesian_product_def]
  definition "lill_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei ls_empty ls_ins"
  lemmas lill_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded lill_image_filter_cartesian_product_def]
  definition "lilr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei rs_empty rs_ins"
  lemmas lilr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded lilr_image_filter_cartesian_product_def]
  definition "lilh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei hs_empty hs_ins"
  lemmas lilh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded lilh_image_filter_cartesian_product_def]
  definition "lila_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas lila_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lila_image_filter_cartesian_product_def]
  definition "lilis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ls_iteratei ias_empty ias_ins"
  lemmas lilis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded lilis_image_filter_cartesian_product_def]
  definition "lirli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas lirli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lirli_image_filter_cartesian_product_def]
  definition "lirl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei ls_empty ls_ins"
  lemmas lirl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded lirl_image_filter_cartesian_product_def]
  definition "lirr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei rs_empty rs_ins"
  lemmas lirr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded lirr_image_filter_cartesian_product_def]
  definition "lirh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei hs_empty hs_ins"
  lemmas lirh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded lirh_image_filter_cartesian_product_def]
  definition "lira_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas lira_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lira_image_filter_cartesian_product_def]
  definition "liris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei rs_iteratei ias_empty ias_ins"
  lemmas liris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded liris_image_filter_cartesian_product_def]
  definition "lihli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas lihli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lihli_image_filter_cartesian_product_def]
  definition "lihl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei ls_empty ls_ins"
  lemmas lihl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded lihl_image_filter_cartesian_product_def]
  definition "lihr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei rs_empty rs_ins"
  lemmas lihr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded lihr_image_filter_cartesian_product_def]
  definition "lihh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei hs_empty hs_ins"
  lemmas lihh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded lihh_image_filter_cartesian_product_def]
  definition "liha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas liha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liha_image_filter_cartesian_product_def]
  definition "lihis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei hs_iteratei ias_empty ias_ins"
  lemmas lihis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded lihis_image_filter_cartesian_product_def]
  definition "liali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas liali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded liali_image_filter_cartesian_product_def]
  definition "lial_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas lial_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded lial_image_filter_cartesian_product_def]
  definition "liar_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas liar_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded liar_image_filter_cartesian_product_def]
  definition "liah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas liah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded liah_image_filter_cartesian_product_def]
  definition "liaa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas liaa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liaa_image_filter_cartesian_product_def]
  definition "liais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas liais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded liais_image_filter_cartesian_product_def]
  definition "liisli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas liisli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded liisli_image_filter_cartesian_product_def]
  definition "liisl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei ls_empty ls_ins"
  lemmas liisl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded liisl_image_filter_cartesian_product_def]
  definition "liisr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei rs_empty rs_ins"
  lemmas liisr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded liisr_image_filter_cartesian_product_def]
  definition "liish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei hs_empty hs_ins"
  lemmas liish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded liish_image_filter_cartesian_product_def]
  definition "liisa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas liisa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liisa_image_filter_cartesian_product_def]
  definition "liisis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product lsi_iteratei ias_iteratei ias_empty ias_ins"
  lemmas liisis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded liisis_image_filter_cartesian_product_def]
  definition "llili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas llili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded llili_image_filter_cartesian_product_def]
  definition "llil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas llil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded llil_image_filter_cartesian_product_def]
  definition "llir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas llir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded llir_image_filter_cartesian_product_def]
  definition "llih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas llih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded llih_image_filter_cartesian_product_def]
  definition "llia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas llia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded llia_image_filter_cartesian_product_def]
  definition "lliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas lliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded lliis_image_filter_cartesian_product_def]
  definition "llli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas llli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded llli_image_filter_cartesian_product_def]
  definition "lll_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei ls_empty ls_ins"
  lemmas lll_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded lll_image_filter_cartesian_product_def]
  definition "llr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei rs_empty rs_ins"
  lemmas llr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded llr_image_filter_cartesian_product_def]
  definition "llh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei hs_empty hs_ins"
  lemmas llh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded llh_image_filter_cartesian_product_def]
  definition "lla_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas lla_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lla_image_filter_cartesian_product_def]
  definition "llis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ls_iteratei ias_empty ias_ins"
  lemmas llis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded llis_image_filter_cartesian_product_def]
  definition "lrli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas lrli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lrli_image_filter_cartesian_product_def]
  definition "lrl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei ls_empty ls_ins"
  lemmas lrl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded lrl_image_filter_cartesian_product_def]
  definition "lrr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei rs_empty rs_ins"
  lemmas lrr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded lrr_image_filter_cartesian_product_def]
  definition "lrh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei hs_empty hs_ins"
  lemmas lrh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded lrh_image_filter_cartesian_product_def]
  definition "lra_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas lra_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lra_image_filter_cartesian_product_def]
  definition "lris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei rs_iteratei ias_empty ias_ins"
  lemmas lris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded lris_image_filter_cartesian_product_def]
  definition "lhli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas lhli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lhli_image_filter_cartesian_product_def]
  definition "lhl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei ls_empty ls_ins"
  lemmas lhl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded lhl_image_filter_cartesian_product_def]
  definition "lhr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei rs_empty rs_ins"
  lemmas lhr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded lhr_image_filter_cartesian_product_def]
  definition "lhh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei hs_empty hs_ins"
  lemmas lhh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded lhh_image_filter_cartesian_product_def]
  definition "lha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas lha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lha_image_filter_cartesian_product_def]
  definition "lhis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei hs_iteratei ias_empty ias_ins"
  lemmas lhis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded lhis_image_filter_cartesian_product_def]
  definition "lali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas lali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lali_image_filter_cartesian_product_def]
  definition "lal_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas lal_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded lal_image_filter_cartesian_product_def]
  definition "lar_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas lar_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded lar_image_filter_cartesian_product_def]
  definition "lah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas lah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded lah_image_filter_cartesian_product_def]
  definition "laa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas laa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded laa_image_filter_cartesian_product_def]
  definition "lais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas lais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded lais_image_filter_cartesian_product_def]
  definition "lisli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas lisli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lisli_image_filter_cartesian_product_def]
  definition "lisl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei ls_empty ls_ins"
  lemmas lisl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded lisl_image_filter_cartesian_product_def]
  definition "lisr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei rs_empty rs_ins"
  lemmas lisr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded lisr_image_filter_cartesian_product_def]
  definition "lish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei hs_empty hs_ins"
  lemmas lish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded lish_image_filter_cartesian_product_def]
  definition "lisa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas lisa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lisa_image_filter_cartesian_product_def]
  definition "lisis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ls_iteratei ias_iteratei ias_empty ias_ins"
  lemmas lisis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded lisis_image_filter_cartesian_product_def]
  definition "rlili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas rlili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rlili_image_filter_cartesian_product_def]
  definition "rlil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas rlil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded rlil_image_filter_cartesian_product_def]
  definition "rlir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas rlir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded rlir_image_filter_cartesian_product_def]
  definition "rlih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas rlih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded rlih_image_filter_cartesian_product_def]
  definition "rlia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas rlia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rlia_image_filter_cartesian_product_def]
  definition "rliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas rliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded rliis_image_filter_cartesian_product_def]
  definition "rlli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas rlli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rlli_image_filter_cartesian_product_def]
  definition "rll_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas rll_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded rll_image_filter_cartesian_product_def]
  definition "rlr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas rlr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded rlr_image_filter_cartesian_product_def]
  definition "rlh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas rlh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded rlh_image_filter_cartesian_product_def]
  definition "rla_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas rla_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rla_image_filter_cartesian_product_def]
  definition "rlis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas rlis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded rlis_image_filter_cartesian_product_def]
  definition "rrli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas rrli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rrli_image_filter_cartesian_product_def]
  definition "rrl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas rrl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded rrl_image_filter_cartesian_product_def]
  definition "rrr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas rrr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded rrr_image_filter_cartesian_product_def]
  definition "rrh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas rrh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded rrh_image_filter_cartesian_product_def]
  definition "rra_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas rra_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rra_image_filter_cartesian_product_def]
  definition "rris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas rris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded rris_image_filter_cartesian_product_def]
  definition "rhli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas rhli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rhli_image_filter_cartesian_product_def]
  definition "rhl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas rhl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded rhl_image_filter_cartesian_product_def]
  definition "rhr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas rhr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded rhr_image_filter_cartesian_product_def]
  definition "rhh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas rhh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded rhh_image_filter_cartesian_product_def]
  definition "rha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas rha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rha_image_filter_cartesian_product_def]
  definition "rhis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas rhis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded rhis_image_filter_cartesian_product_def]
  definition "rali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas rali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rali_image_filter_cartesian_product_def]
  definition "ral_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas ral_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded ral_image_filter_cartesian_product_def]
  definition "rar_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas rar_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded rar_image_filter_cartesian_product_def]
  definition "rah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas rah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded rah_image_filter_cartesian_product_def]
  definition "raa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas raa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded raa_image_filter_cartesian_product_def]
  definition "rais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas rais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded rais_image_filter_cartesian_product_def]
  definition "risli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas risli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded risli_image_filter_cartesian_product_def]
  definition "risl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas risl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded risl_image_filter_cartesian_product_def]
  definition "risr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas risr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded risr_image_filter_cartesian_product_def]
  definition "rish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas rish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded rish_image_filter_cartesian_product_def]
  definition "risa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas risa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded risa_image_filter_cartesian_product_def]
  definition "risis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product rs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas risis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded risis_image_filter_cartesian_product_def]
  definition "hlili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas hlili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hlili_image_filter_cartesian_product_def]
  definition "hlil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas hlil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded hlil_image_filter_cartesian_product_def]
  definition "hlir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas hlir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded hlir_image_filter_cartesian_product_def]
  definition "hlih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas hlih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded hlih_image_filter_cartesian_product_def]
  definition "hlia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas hlia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hlia_image_filter_cartesian_product_def]
  definition "hliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas hliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded hliis_image_filter_cartesian_product_def]
  definition "hlli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas hlli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hlli_image_filter_cartesian_product_def]
  definition "hll_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas hll_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded hll_image_filter_cartesian_product_def]
  definition "hlr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas hlr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded hlr_image_filter_cartesian_product_def]
  definition "hlh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas hlh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded hlh_image_filter_cartesian_product_def]
  definition "hla_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas hla_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hla_image_filter_cartesian_product_def]
  definition "hlis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas hlis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded hlis_image_filter_cartesian_product_def]
  definition "hrli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas hrli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hrli_image_filter_cartesian_product_def]
  definition "hrl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas hrl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded hrl_image_filter_cartesian_product_def]
  definition "hrr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas hrr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded hrr_image_filter_cartesian_product_def]
  definition "hrh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas hrh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded hrh_image_filter_cartesian_product_def]
  definition "hra_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas hra_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hra_image_filter_cartesian_product_def]
  definition "hris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas hris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded hris_image_filter_cartesian_product_def]
  definition "hhli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas hhli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hhli_image_filter_cartesian_product_def]
  definition "hhl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas hhl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded hhl_image_filter_cartesian_product_def]
  definition "hhr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas hhr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded hhr_image_filter_cartesian_product_def]
  definition "hhh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas hhh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded hhh_image_filter_cartesian_product_def]
  definition "hha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas hha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hha_image_filter_cartesian_product_def]
  definition "hhis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas hhis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded hhis_image_filter_cartesian_product_def]
  definition "hali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas hali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hali_image_filter_cartesian_product_def]
  definition "hal_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas hal_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded hal_image_filter_cartesian_product_def]
  definition "har_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas har_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded har_image_filter_cartesian_product_def]
  definition "hah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas hah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded hah_image_filter_cartesian_product_def]
  definition "haa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas haa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded haa_image_filter_cartesian_product_def]
  definition "hais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas hais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded hais_image_filter_cartesian_product_def]
  definition "hisli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas hisli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hisli_image_filter_cartesian_product_def]
  definition "hisl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas hisl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded hisl_image_filter_cartesian_product_def]
  definition "hisr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas hisr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded hisr_image_filter_cartesian_product_def]
  definition "hish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas hish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded hish_image_filter_cartesian_product_def]
  definition "hisa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas hisa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hisa_image_filter_cartesian_product_def]
  definition "hisis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product hs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas hisis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded hisis_image_filter_cartesian_product_def]
  definition "alili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas alili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded alili_image_filter_cartesian_product_def]
  definition "alil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas alil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded alil_image_filter_cartesian_product_def]
  definition "alir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas alir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded alir_image_filter_cartesian_product_def]
  definition "alih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas alih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded alih_image_filter_cartesian_product_def]
  definition "alia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas alia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded alia_image_filter_cartesian_product_def]
  definition "aliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas aliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded aliis_image_filter_cartesian_product_def]
  definition "alli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas alli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded alli_image_filter_cartesian_product_def]
  definition "all_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas all_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded all_image_filter_cartesian_product_def]
  definition "alr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas alr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded alr_image_filter_cartesian_product_def]
  definition "alh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas alh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded alh_image_filter_cartesian_product_def]
  definition "ala_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas ala_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ala_image_filter_cartesian_product_def]
  definition "alis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas alis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded alis_image_filter_cartesian_product_def]
  definition "arli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas arli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded arli_image_filter_cartesian_product_def]
  definition "arl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas arl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded arl_image_filter_cartesian_product_def]
  definition "arr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas arr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded arr_image_filter_cartesian_product_def]
  definition "arh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas arh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded arh_image_filter_cartesian_product_def]
  definition "ara_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas ara_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ara_image_filter_cartesian_product_def]
  definition "aris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas aris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded aris_image_filter_cartesian_product_def]
  definition "ahli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas ahli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded ahli_image_filter_cartesian_product_def]
  definition "ahl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas ahl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded ahl_image_filter_cartesian_product_def]
  definition "ahr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas ahr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded ahr_image_filter_cartesian_product_def]
  definition "ahh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas ahh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded ahh_image_filter_cartesian_product_def]
  definition "aha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas aha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aha_image_filter_cartesian_product_def]
  definition "ahis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas ahis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded ahis_image_filter_cartesian_product_def]
  definition "aali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas aali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded aali_image_filter_cartesian_product_def]
  definition "aal_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas aal_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded aal_image_filter_cartesian_product_def]
  definition "aar_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas aar_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded aar_image_filter_cartesian_product_def]
  definition "aah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas aah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded aah_image_filter_cartesian_product_def]
  definition "aaa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas aaa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aaa_image_filter_cartesian_product_def]
  definition "aais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas aais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded aais_image_filter_cartesian_product_def]
  definition "aisli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas aisli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded aisli_image_filter_cartesian_product_def]
  definition "aisl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas aisl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded aisl_image_filter_cartesian_product_def]
  definition "aisr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas aisr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded aisr_image_filter_cartesian_product_def]
  definition "aish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas aish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded aish_image_filter_cartesian_product_def]
  definition "aisa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas aisa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aisa_image_filter_cartesian_product_def]
  definition "aisis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ahs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas aisis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded aisis_image_filter_cartesian_product_def]
  definition "islili_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas islili_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded islili_image_filter_cartesian_product_def]
  definition "islil_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas islil_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded islil_image_filter_cartesian_product_def]
  definition "islir_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas islir_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded islir_image_filter_cartesian_product_def]
  definition "islih_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas islih_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded islih_image_filter_cartesian_product_def]
  definition "islia_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas islia_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded islia_image_filter_cartesian_product_def]
  definition "isliis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas isliis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded isliis_image_filter_cartesian_product_def]
  definition "islli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas islli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded islli_image_filter_cartesian_product_def]
  definition "isll_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei ls_empty ls_ins"
  lemmas isll_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded isll_image_filter_cartesian_product_def]
  definition "islr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei rs_empty rs_ins"
  lemmas islr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded islr_image_filter_cartesian_product_def]
  definition "islh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei hs_empty hs_ins"
  lemmas islh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded islh_image_filter_cartesian_product_def]
  definition "isla_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas isla_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isla_image_filter_cartesian_product_def]
  definition "islis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ls_iteratei ias_empty ias_ins"
  lemmas islis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded islis_image_filter_cartesian_product_def]
  definition "isrli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas isrli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isrli_image_filter_cartesian_product_def]
  definition "isrl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei ls_empty ls_ins"
  lemmas isrl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded isrl_image_filter_cartesian_product_def]
  definition "isrr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei rs_empty rs_ins"
  lemmas isrr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded isrr_image_filter_cartesian_product_def]
  definition "isrh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei hs_empty hs_ins"
  lemmas isrh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded isrh_image_filter_cartesian_product_def]
  definition "isra_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas isra_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isra_image_filter_cartesian_product_def]
  definition "isris_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei rs_iteratei ias_empty ias_ins"
  lemmas isris_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded isris_image_filter_cartesian_product_def]
  definition "ishli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas ishli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded ishli_image_filter_cartesian_product_def]
  definition "ishl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei ls_empty ls_ins"
  lemmas ishl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded ishl_image_filter_cartesian_product_def]
  definition "ishr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei rs_empty rs_ins"
  lemmas ishr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded ishr_image_filter_cartesian_product_def]
  definition "ishh_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei hs_empty hs_ins"
  lemmas ishh_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded ishh_image_filter_cartesian_product_def]
  definition "isha_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas isha_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isha_image_filter_cartesian_product_def]
  definition "ishis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei hs_iteratei ias_empty ias_ins"
  lemmas ishis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded ishis_image_filter_cartesian_product_def]
  definition "isali_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas isali_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isali_image_filter_cartesian_product_def]
  definition "isal_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas isal_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded isal_image_filter_cartesian_product_def]
  definition "isar_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas isar_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded isar_image_filter_cartesian_product_def]
  definition "isah_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas isah_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded isah_image_filter_cartesian_product_def]
  definition "isaa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas isaa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isaa_image_filter_cartesian_product_def]
  definition "isais_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas isais_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded isais_image_filter_cartesian_product_def]
  definition "isisli_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas isisli_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isisli_image_filter_cartesian_product_def]
  definition "isisl_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei ls_empty ls_ins"
  lemmas isisl_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded isisl_image_filter_cartesian_product_def]
  definition "isisr_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei rs_empty rs_ins"
  lemmas isisr_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded isisr_image_filter_cartesian_product_def]
  definition "isish_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei hs_empty hs_ins"
  lemmas isish_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded isish_image_filter_cartesian_product_def]
  definition "isisa_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas isisa_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isisa_image_filter_cartesian_product_def]
  definition "isisis_image_filter_cartesian_product == SetGA.image_filter_cartesian_product ias_iteratei ias_iteratei ias_empty ias_ins"
  lemmas isisis_image_filter_cartesian_product_correct = SetGA.image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded isisis_image_filter_cartesian_product_def]

  definition "lilili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas lilili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_inj_image_filter_cartesian_product_def]
  definition "lilil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas lilil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lilil_inj_image_filter_cartesian_product_def]
  definition "lilir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas lilir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilir_inj_image_filter_cartesian_product_def]
  definition "lilih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas lilih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilih_inj_image_filter_cartesian_product_def]
  definition "lilia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas lilia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_inj_image_filter_cartesian_product_def]
  definition "liliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas liliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liliis_inj_image_filter_cartesian_product_def]
  definition "lilli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas lilli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_inj_image_filter_cartesian_product_def]
  definition "lill_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lill_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lill_inj_image_filter_cartesian_product_def]
  definition "lilr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas lilr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilr_inj_image_filter_cartesian_product_def]
  definition "lilh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas lilh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilh_inj_image_filter_cartesian_product_def]
  definition "lila_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lila_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_inj_image_filter_cartesian_product_def]
  definition "lilis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas lilis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lilis_inj_image_filter_cartesian_product_def]
  definition "lirli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lirli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_inj_image_filter_cartesian_product_def]
  definition "lirl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lirl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lirl_inj_image_filter_cartesian_product_def]
  definition "lirr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lirr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lirr_inj_image_filter_cartesian_product_def]
  definition "lirh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lirh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lirh_inj_image_filter_cartesian_product_def]
  definition "lira_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lira_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_inj_image_filter_cartesian_product_def]
  definition "liris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas liris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liris_inj_image_filter_cartesian_product_def]
  definition "lihli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lihli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_inj_image_filter_cartesian_product_def]
  definition "lihl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lihl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lihl_inj_image_filter_cartesian_product_def]
  definition "lihr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lihr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lihr_inj_image_filter_cartesian_product_def]
  definition "lihh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lihh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lihh_inj_image_filter_cartesian_product_def]
  definition "liha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas liha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_inj_image_filter_cartesian_product_def]
  definition "lihis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas lihis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lihis_inj_image_filter_cartesian_product_def]
  definition "liali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas liali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_inj_image_filter_cartesian_product_def]
  definition "lial_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lial_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lial_inj_image_filter_cartesian_product_def]
  definition "liar_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas liar_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liar_inj_image_filter_cartesian_product_def]
  definition "liah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas liah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liah_inj_image_filter_cartesian_product_def]
  definition "liaa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas liaa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_inj_image_filter_cartesian_product_def]
  definition "liais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas liais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liais_inj_image_filter_cartesian_product_def]
  definition "liisli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas liisli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liisli_inj_image_filter_cartesian_product_def]
  definition "liisl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas liisl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded liisl_inj_image_filter_cartesian_product_def]
  definition "liisr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas liisr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liisr_inj_image_filter_cartesian_product_def]
  definition "liish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas liish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liish_inj_image_filter_cartesian_product_def]
  definition "liisa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas liisa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liisa_inj_image_filter_cartesian_product_def]
  definition "liisis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product lsi_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas liisis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF lsi_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liisis_inj_image_filter_cartesian_product_def]
  definition "llili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas llili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_inj_image_filter_cartesian_product_def]
  definition "llil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas llil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded llil_inj_image_filter_cartesian_product_def]
  definition "llir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas llir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llir_inj_image_filter_cartesian_product_def]
  definition "llih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas llih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llih_inj_image_filter_cartesian_product_def]
  definition "llia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas llia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_inj_image_filter_cartesian_product_def]
  definition "lliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas lliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lliis_inj_image_filter_cartesian_product_def]
  definition "llli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas llli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_inj_image_filter_cartesian_product_def]
  definition "lll_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lll_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lll_inj_image_filter_cartesian_product_def]
  definition "llr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas llr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llr_inj_image_filter_cartesian_product_def]
  definition "llh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas llh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llh_inj_image_filter_cartesian_product_def]
  definition "lla_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lla_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_inj_image_filter_cartesian_product_def]
  definition "llis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas llis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded llis_inj_image_filter_cartesian_product_def]
  definition "lrli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lrli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_inj_image_filter_cartesian_product_def]
  definition "lrl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lrl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inj_image_filter_cartesian_product_def]
  definition "lrr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lrr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inj_image_filter_cartesian_product_def]
  definition "lrh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lrh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inj_image_filter_cartesian_product_def]
  definition "lra_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lra_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_inj_image_filter_cartesian_product_def]
  definition "lris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas lris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lris_inj_image_filter_cartesian_product_def]
  definition "lhli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lhli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_inj_image_filter_cartesian_product_def]
  definition "lhl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lhl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inj_image_filter_cartesian_product_def]
  definition "lhr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lhr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inj_image_filter_cartesian_product_def]
  definition "lhh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lhh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inj_image_filter_cartesian_product_def]
  definition "lha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas lha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_inj_image_filter_cartesian_product_def]
  definition "lhis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas lhis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lhis_inj_image_filter_cartesian_product_def]
  definition "lali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas lali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_inj_image_filter_cartesian_product_def]
  definition "lal_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lal_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lal_inj_image_filter_cartesian_product_def]
  definition "lar_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas lar_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lar_inj_image_filter_cartesian_product_def]
  definition "lah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas lah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lah_inj_image_filter_cartesian_product_def]
  definition "laa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas laa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_inj_image_filter_cartesian_product_def]
  definition "lais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas lais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lais_inj_image_filter_cartesian_product_def]
  definition "lisli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas lisli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lisli_inj_image_filter_cartesian_product_def]
  definition "lisl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas lisl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lisl_inj_image_filter_cartesian_product_def]
  definition "lisr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas lisr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lisr_inj_image_filter_cartesian_product_def]
  definition "lish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas lish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lish_inj_image_filter_cartesian_product_def]
  definition "lisa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas lisa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lisa_inj_image_filter_cartesian_product_def]
  definition "lisis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ls_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas lisis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ls_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lisis_inj_image_filter_cartesian_product_def]
  definition "rlili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas rlili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_inj_image_filter_cartesian_product_def]
  definition "rlil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas rlil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rlil_inj_image_filter_cartesian_product_def]
  definition "rlir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas rlir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlir_inj_image_filter_cartesian_product_def]
  definition "rlih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas rlih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlih_inj_image_filter_cartesian_product_def]
  definition "rlia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas rlia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_inj_image_filter_cartesian_product_def]
  definition "rliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas rliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rliis_inj_image_filter_cartesian_product_def]
  definition "rlli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas rlli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_inj_image_filter_cartesian_product_def]
  definition "rll_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas rll_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rll_inj_image_filter_cartesian_product_def]
  definition "rlr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas rlr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inj_image_filter_cartesian_product_def]
  definition "rlh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas rlh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inj_image_filter_cartesian_product_def]
  definition "rla_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas rla_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_inj_image_filter_cartesian_product_def]
  definition "rlis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas rlis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rlis_inj_image_filter_cartesian_product_def]
  definition "rrli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas rrli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_inj_image_filter_cartesian_product_def]
  definition "rrl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas rrl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inj_image_filter_cartesian_product_def]
  definition "rrr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas rrr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inj_image_filter_cartesian_product_def]
  definition "rrh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas rrh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inj_image_filter_cartesian_product_def]
  definition "rra_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas rra_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_inj_image_filter_cartesian_product_def]
  definition "rris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas rris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rris_inj_image_filter_cartesian_product_def]
  definition "rhli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas rhli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_inj_image_filter_cartesian_product_def]
  definition "rhl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas rhl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inj_image_filter_cartesian_product_def]
  definition "rhr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas rhr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inj_image_filter_cartesian_product_def]
  definition "rhh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas rhh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inj_image_filter_cartesian_product_def]
  definition "rha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas rha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_inj_image_filter_cartesian_product_def]
  definition "rhis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas rhis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rhis_inj_image_filter_cartesian_product_def]
  definition "rali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas rali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_inj_image_filter_cartesian_product_def]
  definition "ral_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas ral_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ral_inj_image_filter_cartesian_product_def]
  definition "rar_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas rar_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rar_inj_image_filter_cartesian_product_def]
  definition "rah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas rah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rah_inj_image_filter_cartesian_product_def]
  definition "raa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas raa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_inj_image_filter_cartesian_product_def]
  definition "rais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas rais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rais_inj_image_filter_cartesian_product_def]
  definition "risli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas risli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded risli_inj_image_filter_cartesian_product_def]
  definition "risl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas risl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded risl_inj_image_filter_cartesian_product_def]
  definition "risr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas risr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded risr_inj_image_filter_cartesian_product_def]
  definition "rish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas rish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rish_inj_image_filter_cartesian_product_def]
  definition "risa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas risa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded risa_inj_image_filter_cartesian_product_def]
  definition "risis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product rs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas risis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF rs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded risis_inj_image_filter_cartesian_product_def]
  definition "hlili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas hlili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_inj_image_filter_cartesian_product_def]
  definition "hlil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas hlil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hlil_inj_image_filter_cartesian_product_def]
  definition "hlir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas hlir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlir_inj_image_filter_cartesian_product_def]
  definition "hlih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas hlih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlih_inj_image_filter_cartesian_product_def]
  definition "hlia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas hlia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_inj_image_filter_cartesian_product_def]
  definition "hliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas hliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hliis_inj_image_filter_cartesian_product_def]
  definition "hlli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas hlli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_inj_image_filter_cartesian_product_def]
  definition "hll_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas hll_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hll_inj_image_filter_cartesian_product_def]
  definition "hlr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas hlr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inj_image_filter_cartesian_product_def]
  definition "hlh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas hlh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inj_image_filter_cartesian_product_def]
  definition "hla_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas hla_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_inj_image_filter_cartesian_product_def]
  definition "hlis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas hlis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hlis_inj_image_filter_cartesian_product_def]
  definition "hrli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas hrli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_inj_image_filter_cartesian_product_def]
  definition "hrl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas hrl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inj_image_filter_cartesian_product_def]
  definition "hrr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas hrr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inj_image_filter_cartesian_product_def]
  definition "hrh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas hrh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inj_image_filter_cartesian_product_def]
  definition "hra_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas hra_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_inj_image_filter_cartesian_product_def]
  definition "hris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas hris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hris_inj_image_filter_cartesian_product_def]
  definition "hhli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas hhli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_inj_image_filter_cartesian_product_def]
  definition "hhl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas hhl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inj_image_filter_cartesian_product_def]
  definition "hhr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas hhr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inj_image_filter_cartesian_product_def]
  definition "hhh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas hhh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inj_image_filter_cartesian_product_def]
  definition "hha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas hha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_inj_image_filter_cartesian_product_def]
  definition "hhis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas hhis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hhis_inj_image_filter_cartesian_product_def]
  definition "hali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas hali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_inj_image_filter_cartesian_product_def]
  definition "hal_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas hal_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hal_inj_image_filter_cartesian_product_def]
  definition "har_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas har_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded har_inj_image_filter_cartesian_product_def]
  definition "hah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas hah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hah_inj_image_filter_cartesian_product_def]
  definition "haa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas haa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_inj_image_filter_cartesian_product_def]
  definition "hais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas hais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hais_inj_image_filter_cartesian_product_def]
  definition "hisli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas hisli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hisli_inj_image_filter_cartesian_product_def]
  definition "hisl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas hisl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hisl_inj_image_filter_cartesian_product_def]
  definition "hisr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas hisr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hisr_inj_image_filter_cartesian_product_def]
  definition "hish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas hish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hish_inj_image_filter_cartesian_product_def]
  definition "hisa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas hisa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hisa_inj_image_filter_cartesian_product_def]
  definition "hisis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product hs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas hisis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF hs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hisis_inj_image_filter_cartesian_product_def]
  definition "alili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas alili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_inj_image_filter_cartesian_product_def]
  definition "alil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas alil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded alil_inj_image_filter_cartesian_product_def]
  definition "alir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas alir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alir_inj_image_filter_cartesian_product_def]
  definition "alih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas alih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alih_inj_image_filter_cartesian_product_def]
  definition "alia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas alia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_inj_image_filter_cartesian_product_def]
  definition "aliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas aliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aliis_inj_image_filter_cartesian_product_def]
  definition "alli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas alli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_inj_image_filter_cartesian_product_def]
  definition "all_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas all_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded all_inj_image_filter_cartesian_product_def]
  definition "alr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas alr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alr_inj_image_filter_cartesian_product_def]
  definition "alh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas alh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alh_inj_image_filter_cartesian_product_def]
  definition "ala_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas ala_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_inj_image_filter_cartesian_product_def]
  definition "alis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas alis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded alis_inj_image_filter_cartesian_product_def]
  definition "arli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas arli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_inj_image_filter_cartesian_product_def]
  definition "arl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas arl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded arl_inj_image_filter_cartesian_product_def]
  definition "arr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas arr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded arr_inj_image_filter_cartesian_product_def]
  definition "arh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas arh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded arh_inj_image_filter_cartesian_product_def]
  definition "ara_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas ara_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_inj_image_filter_cartesian_product_def]
  definition "aris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas aris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aris_inj_image_filter_cartesian_product_def]
  definition "ahli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ahli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_inj_image_filter_cartesian_product_def]
  definition "ahl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ahl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ahl_inj_image_filter_cartesian_product_def]
  definition "ahr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ahr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ahr_inj_image_filter_cartesian_product_def]
  definition "ahh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ahh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ahh_inj_image_filter_cartesian_product_def]
  definition "aha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas aha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_inj_image_filter_cartesian_product_def]
  definition "ahis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas ahis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ahis_inj_image_filter_cartesian_product_def]
  definition "aali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas aali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_inj_image_filter_cartesian_product_def]
  definition "aal_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas aal_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aal_inj_image_filter_cartesian_product_def]
  definition "aar_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas aar_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aar_inj_image_filter_cartesian_product_def]
  definition "aah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas aah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aah_inj_image_filter_cartesian_product_def]
  definition "aaa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas aaa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_inj_image_filter_cartesian_product_def]
  definition "aais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas aais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aais_inj_image_filter_cartesian_product_def]
  definition "aisli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas aisli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aisli_inj_image_filter_cartesian_product_def]
  definition "aisl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas aisl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aisl_inj_image_filter_cartesian_product_def]
  definition "aisr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas aisr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aisr_inj_image_filter_cartesian_product_def]
  definition "aish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas aish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aish_inj_image_filter_cartesian_product_def]
  definition "aisa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas aisa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aisa_inj_image_filter_cartesian_product_def]
  definition "aisis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ahs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas aisis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ahs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aisis_inj_image_filter_cartesian_product_def]
  definition "islili_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas islili_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islili_inj_image_filter_cartesian_product_def]
  definition "islil_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas islil_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded islil_inj_image_filter_cartesian_product_def]
  definition "islir_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas islir_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islir_inj_image_filter_cartesian_product_def]
  definition "islih_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas islih_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islih_inj_image_filter_cartesian_product_def]
  definition "islia_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas islia_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded islia_inj_image_filter_cartesian_product_def]
  definition "isliis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas isliis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isliis_inj_image_filter_cartesian_product_def]
  definition "islli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas islli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islli_inj_image_filter_cartesian_product_def]
  definition "isll_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas isll_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isll_inj_image_filter_cartesian_product_def]
  definition "islr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas islr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islr_inj_image_filter_cartesian_product_def]
  definition "islh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas islh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islh_inj_image_filter_cartesian_product_def]
  definition "isla_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas isla_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isla_inj_image_filter_cartesian_product_def]
  definition "islis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas islis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded islis_inj_image_filter_cartesian_product_def]
  definition "isrli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas isrli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isrli_inj_image_filter_cartesian_product_def]
  definition "isrl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas isrl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isrl_inj_image_filter_cartesian_product_def]
  definition "isrr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas isrr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isrr_inj_image_filter_cartesian_product_def]
  definition "isrh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas isrh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isrh_inj_image_filter_cartesian_product_def]
  definition "isra_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas isra_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isra_inj_image_filter_cartesian_product_def]
  definition "isris_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas isris_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isris_inj_image_filter_cartesian_product_def]
  definition "ishli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ishli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ishli_inj_image_filter_cartesian_product_def]
  definition "ishl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ishl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ishl_inj_image_filter_cartesian_product_def]
  definition "ishr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ishr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ishr_inj_image_filter_cartesian_product_def]
  definition "ishh_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ishh_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ishh_inj_image_filter_cartesian_product_def]
  definition "isha_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas isha_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isha_inj_image_filter_cartesian_product_def]
  definition "ishis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas ishis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ishis_inj_image_filter_cartesian_product_def]
  definition "isali_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas isali_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isali_inj_image_filter_cartesian_product_def]
  definition "isal_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas isal_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isal_inj_image_filter_cartesian_product_def]
  definition "isar_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas isar_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isar_inj_image_filter_cartesian_product_def]
  definition "isah_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas isah_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isah_inj_image_filter_cartesian_product_def]
  definition "isaa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas isaa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isaa_inj_image_filter_cartesian_product_def]
  definition "isais_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas isais_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isais_inj_image_filter_cartesian_product_def]
  definition "isisli_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas isisli_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isisli_inj_image_filter_cartesian_product_def]
  definition "isisl_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas isisl_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isisl_inj_image_filter_cartesian_product_def]
  definition "isisr_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas isisr_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isisr_inj_image_filter_cartesian_product_def]
  definition "isish_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas isish_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isish_inj_image_filter_cartesian_product_def]
  definition "isisa_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas isisa_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isisa_inj_image_filter_cartesian_product_def]
  definition "isisis_inj_image_filter_cartesian_product == SetGA.inj_image_filter_cartesian_product ias_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas isisis_inj_image_filter_cartesian_product_correct = SetGA.inj_image_filter_cartesian_product_correct[OF ias_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isisis_inj_image_filter_cartesian_product_def]

  definition "lilili_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas lilili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lilili_image_filter_cp_def]
  definition "lilil_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas lilil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded lilil_image_filter_cp_def]
  definition "lilir_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas lilir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded lilir_image_filter_cp_def]
  definition "lilih_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas lilih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded lilih_image_filter_cp_def]
  definition "lilia_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas lilia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lilia_image_filter_cp_def]
  definition "liliis_image_filter_cp == SetGA.image_filter_cp lsi_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas liliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded liliis_image_filter_cp_def]
  definition "lilli_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas lilli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lilli_image_filter_cp_def]
  definition "lill_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei ls_empty ls_ins"
  lemmas lill_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded lill_image_filter_cp_def]
  definition "lilr_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei rs_empty rs_ins"
  lemmas lilr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded lilr_image_filter_cp_def]
  definition "lilh_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei hs_empty hs_ins"
  lemmas lilh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded lilh_image_filter_cp_def]
  definition "lila_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas lila_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lila_image_filter_cp_def]
  definition "lilis_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ls_iteratei ias_empty ias_ins"
  lemmas lilis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded lilis_image_filter_cp_def]
  definition "lirli_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas lirli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lirli_image_filter_cp_def]
  definition "lirl_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei ls_empty ls_ins"
  lemmas lirl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded lirl_image_filter_cp_def]
  definition "lirr_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei rs_empty rs_ins"
  lemmas lirr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded lirr_image_filter_cp_def]
  definition "lirh_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei hs_empty hs_ins"
  lemmas lirh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded lirh_image_filter_cp_def]
  definition "lira_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas lira_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lira_image_filter_cp_def]
  definition "liris_image_filter_cp == SetGA.image_filter_cp lsi_iteratei rs_iteratei ias_empty ias_ins"
  lemmas liris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded liris_image_filter_cp_def]
  definition "lihli_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas lihli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lihli_image_filter_cp_def]
  definition "lihl_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei ls_empty ls_ins"
  lemmas lihl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded lihl_image_filter_cp_def]
  definition "lihr_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei rs_empty rs_ins"
  lemmas lihr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded lihr_image_filter_cp_def]
  definition "lihh_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei hs_empty hs_ins"
  lemmas lihh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded lihh_image_filter_cp_def]
  definition "liha_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas liha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liha_image_filter_cp_def]
  definition "lihis_image_filter_cp == SetGA.image_filter_cp lsi_iteratei hs_iteratei ias_empty ias_ins"
  lemmas lihis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded lihis_image_filter_cp_def]
  definition "liali_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas liali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded liali_image_filter_cp_def]
  definition "lial_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas lial_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded lial_image_filter_cp_def]
  definition "liar_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas liar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded liar_image_filter_cp_def]
  definition "liah_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas liah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded liah_image_filter_cp_def]
  definition "liaa_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas liaa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liaa_image_filter_cp_def]
  definition "liais_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas liais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded liais_image_filter_cp_def]
  definition "liisli_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas liisli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded liisli_image_filter_cp_def]
  definition "liisl_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei ls_empty ls_ins"
  lemmas liisl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded liisl_image_filter_cp_def]
  definition "liisr_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei rs_empty rs_ins"
  lemmas liisr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded liisr_image_filter_cp_def]
  definition "liish_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei hs_empty hs_ins"
  lemmas liish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded liish_image_filter_cp_def]
  definition "liisa_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas liisa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded liisa_image_filter_cp_def]
  definition "liisis_image_filter_cp == SetGA.image_filter_cp lsi_iteratei ias_iteratei ias_empty ias_ins"
  lemmas liisis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded liisis_image_filter_cp_def]
  definition "llili_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas llili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded llili_image_filter_cp_def]
  definition "llil_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas llil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded llil_image_filter_cp_def]
  definition "llir_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas llir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded llir_image_filter_cp_def]
  definition "llih_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas llih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded llih_image_filter_cp_def]
  definition "llia_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas llia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded llia_image_filter_cp_def]
  definition "lliis_image_filter_cp == SetGA.image_filter_cp ls_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas lliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded lliis_image_filter_cp_def]
  definition "llli_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas llli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded llli_image_filter_cp_def]
  definition "lll_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei ls_empty ls_ins"
  lemmas lll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded lll_image_filter_cp_def]
  definition "llr_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei rs_empty rs_ins"
  lemmas llr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded llr_image_filter_cp_def]
  definition "llh_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei hs_empty hs_ins"
  lemmas llh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded llh_image_filter_cp_def]
  definition "lla_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas lla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lla_image_filter_cp_def]
  definition "llis_image_filter_cp == SetGA.image_filter_cp ls_iteratei ls_iteratei ias_empty ias_ins"
  lemmas llis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded llis_image_filter_cp_def]
  definition "lrli_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas lrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lrli_image_filter_cp_def]
  definition "lrl_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei ls_empty ls_ins"
  lemmas lrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded lrl_image_filter_cp_def]
  definition "lrr_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei rs_empty rs_ins"
  lemmas lrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded lrr_image_filter_cp_def]
  definition "lrh_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei hs_empty hs_ins"
  lemmas lrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded lrh_image_filter_cp_def]
  definition "lra_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas lra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lra_image_filter_cp_def]
  definition "lris_image_filter_cp == SetGA.image_filter_cp ls_iteratei rs_iteratei ias_empty ias_ins"
  lemmas lris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded lris_image_filter_cp_def]
  definition "lhli_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas lhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lhli_image_filter_cp_def]
  definition "lhl_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei ls_empty ls_ins"
  lemmas lhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded lhl_image_filter_cp_def]
  definition "lhr_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei rs_empty rs_ins"
  lemmas lhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded lhr_image_filter_cp_def]
  definition "lhh_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei hs_empty hs_ins"
  lemmas lhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded lhh_image_filter_cp_def]
  definition "lha_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas lha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lha_image_filter_cp_def]
  definition "lhis_image_filter_cp == SetGA.image_filter_cp ls_iteratei hs_iteratei ias_empty ias_ins"
  lemmas lhis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded lhis_image_filter_cp_def]
  definition "lali_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas lali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lali_image_filter_cp_def]
  definition "lal_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas lal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded lal_image_filter_cp_def]
  definition "lar_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas lar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded lar_image_filter_cp_def]
  definition "lah_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas lah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded lah_image_filter_cp_def]
  definition "laa_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas laa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded laa_image_filter_cp_def]
  definition "lais_image_filter_cp == SetGA.image_filter_cp ls_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas lais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded lais_image_filter_cp_def]
  definition "lisli_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas lisli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded lisli_image_filter_cp_def]
  definition "lisl_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei ls_empty ls_ins"
  lemmas lisl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded lisl_image_filter_cp_def]
  definition "lisr_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei rs_empty rs_ins"
  lemmas lisr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded lisr_image_filter_cp_def]
  definition "lish_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei hs_empty hs_ins"
  lemmas lish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded lish_image_filter_cp_def]
  definition "lisa_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas lisa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded lisa_image_filter_cp_def]
  definition "lisis_image_filter_cp == SetGA.image_filter_cp ls_iteratei ias_iteratei ias_empty ias_ins"
  lemmas lisis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded lisis_image_filter_cp_def]
  definition "rlili_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas rlili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rlili_image_filter_cp_def]
  definition "rlil_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas rlil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded rlil_image_filter_cp_def]
  definition "rlir_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas rlir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded rlir_image_filter_cp_def]
  definition "rlih_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas rlih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded rlih_image_filter_cp_def]
  definition "rlia_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas rlia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rlia_image_filter_cp_def]
  definition "rliis_image_filter_cp == SetGA.image_filter_cp rs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas rliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded rliis_image_filter_cp_def]
  definition "rlli_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas rlli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rlli_image_filter_cp_def]
  definition "rll_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas rll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded rll_image_filter_cp_def]
  definition "rlr_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas rlr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded rlr_image_filter_cp_def]
  definition "rlh_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas rlh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded rlh_image_filter_cp_def]
  definition "rla_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas rla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rla_image_filter_cp_def]
  definition "rlis_image_filter_cp == SetGA.image_filter_cp rs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas rlis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded rlis_image_filter_cp_def]
  definition "rrli_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas rrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rrli_image_filter_cp_def]
  definition "rrl_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas rrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded rrl_image_filter_cp_def]
  definition "rrr_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas rrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded rrr_image_filter_cp_def]
  definition "rrh_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas rrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded rrh_image_filter_cp_def]
  definition "rra_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas rra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rra_image_filter_cp_def]
  definition "rris_image_filter_cp == SetGA.image_filter_cp rs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas rris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded rris_image_filter_cp_def]
  definition "rhli_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas rhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rhli_image_filter_cp_def]
  definition "rhl_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas rhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded rhl_image_filter_cp_def]
  definition "rhr_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas rhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded rhr_image_filter_cp_def]
  definition "rhh_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas rhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded rhh_image_filter_cp_def]
  definition "rha_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas rha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded rha_image_filter_cp_def]
  definition "rhis_image_filter_cp == SetGA.image_filter_cp rs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas rhis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded rhis_image_filter_cp_def]
  definition "rali_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas rali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded rali_image_filter_cp_def]
  definition "ral_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas ral_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded ral_image_filter_cp_def]
  definition "rar_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas rar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded rar_image_filter_cp_def]
  definition "rah_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas rah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded rah_image_filter_cp_def]
  definition "raa_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas raa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded raa_image_filter_cp_def]
  definition "rais_image_filter_cp == SetGA.image_filter_cp rs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas rais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded rais_image_filter_cp_def]
  definition "risli_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas risli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded risli_image_filter_cp_def]
  definition "risl_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas risl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded risl_image_filter_cp_def]
  definition "risr_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas risr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded risr_image_filter_cp_def]
  definition "rish_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas rish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded rish_image_filter_cp_def]
  definition "risa_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas risa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded risa_image_filter_cp_def]
  definition "risis_image_filter_cp == SetGA.image_filter_cp rs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas risis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded risis_image_filter_cp_def]
  definition "hlili_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas hlili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hlili_image_filter_cp_def]
  definition "hlil_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas hlil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded hlil_image_filter_cp_def]
  definition "hlir_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas hlir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded hlir_image_filter_cp_def]
  definition "hlih_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas hlih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded hlih_image_filter_cp_def]
  definition "hlia_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas hlia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hlia_image_filter_cp_def]
  definition "hliis_image_filter_cp == SetGA.image_filter_cp hs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas hliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded hliis_image_filter_cp_def]
  definition "hlli_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas hlli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hlli_image_filter_cp_def]
  definition "hll_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas hll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded hll_image_filter_cp_def]
  definition "hlr_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas hlr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded hlr_image_filter_cp_def]
  definition "hlh_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas hlh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded hlh_image_filter_cp_def]
  definition "hla_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas hla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hla_image_filter_cp_def]
  definition "hlis_image_filter_cp == SetGA.image_filter_cp hs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas hlis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded hlis_image_filter_cp_def]
  definition "hrli_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas hrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hrli_image_filter_cp_def]
  definition "hrl_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas hrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded hrl_image_filter_cp_def]
  definition "hrr_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas hrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded hrr_image_filter_cp_def]
  definition "hrh_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas hrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded hrh_image_filter_cp_def]
  definition "hra_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas hra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hra_image_filter_cp_def]
  definition "hris_image_filter_cp == SetGA.image_filter_cp hs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas hris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded hris_image_filter_cp_def]
  definition "hhli_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas hhli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hhli_image_filter_cp_def]
  definition "hhl_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas hhl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded hhl_image_filter_cp_def]
  definition "hhr_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas hhr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded hhr_image_filter_cp_def]
  definition "hhh_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas hhh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded hhh_image_filter_cp_def]
  definition "hha_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas hha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hha_image_filter_cp_def]
  definition "hhis_image_filter_cp == SetGA.image_filter_cp hs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas hhis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded hhis_image_filter_cp_def]
  definition "hali_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas hali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hali_image_filter_cp_def]
  definition "hal_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas hal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded hal_image_filter_cp_def]
  definition "har_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas har_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded har_image_filter_cp_def]
  definition "hah_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas hah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded hah_image_filter_cp_def]
  definition "haa_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas haa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded haa_image_filter_cp_def]
  definition "hais_image_filter_cp == SetGA.image_filter_cp hs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas hais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded hais_image_filter_cp_def]
  definition "hisli_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas hisli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded hisli_image_filter_cp_def]
  definition "hisl_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas hisl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded hisl_image_filter_cp_def]
  definition "hisr_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas hisr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded hisr_image_filter_cp_def]
  definition "hish_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas hish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded hish_image_filter_cp_def]
  definition "hisa_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas hisa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded hisa_image_filter_cp_def]
  definition "hisis_image_filter_cp == SetGA.image_filter_cp hs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas hisis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded hisis_image_filter_cp_def]
  definition "alili_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas alili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded alili_image_filter_cp_def]
  definition "alil_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas alil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded alil_image_filter_cp_def]
  definition "alir_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas alir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded alir_image_filter_cp_def]
  definition "alih_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas alih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded alih_image_filter_cp_def]
  definition "alia_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas alia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded alia_image_filter_cp_def]
  definition "aliis_image_filter_cp == SetGA.image_filter_cp ahs_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas aliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded aliis_image_filter_cp_def]
  definition "alli_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas alli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded alli_image_filter_cp_def]
  definition "all_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei ls_empty ls_ins"
  lemmas all_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded all_image_filter_cp_def]
  definition "alr_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei rs_empty rs_ins"
  lemmas alr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded alr_image_filter_cp_def]
  definition "alh_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei hs_empty hs_ins"
  lemmas alh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded alh_image_filter_cp_def]
  definition "ala_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas ala_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ala_image_filter_cp_def]
  definition "alis_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ls_iteratei ias_empty ias_ins"
  lemmas alis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded alis_image_filter_cp_def]
  definition "arli_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas arli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded arli_image_filter_cp_def]
  definition "arl_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei ls_empty ls_ins"
  lemmas arl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded arl_image_filter_cp_def]
  definition "arr_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei rs_empty rs_ins"
  lemmas arr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded arr_image_filter_cp_def]
  definition "arh_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei hs_empty hs_ins"
  lemmas arh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded arh_image_filter_cp_def]
  definition "ara_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas ara_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded ara_image_filter_cp_def]
  definition "aris_image_filter_cp == SetGA.image_filter_cp ahs_iteratei rs_iteratei ias_empty ias_ins"
  lemmas aris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded aris_image_filter_cp_def]
  definition "ahli_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas ahli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded ahli_image_filter_cp_def]
  definition "ahl_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei ls_empty ls_ins"
  lemmas ahl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded ahl_image_filter_cp_def]
  definition "ahr_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei rs_empty rs_ins"
  lemmas ahr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded ahr_image_filter_cp_def]
  definition "ahh_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei hs_empty hs_ins"
  lemmas ahh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded ahh_image_filter_cp_def]
  definition "aha_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas aha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aha_image_filter_cp_def]
  definition "ahis_image_filter_cp == SetGA.image_filter_cp ahs_iteratei hs_iteratei ias_empty ias_ins"
  lemmas ahis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded ahis_image_filter_cp_def]
  definition "aali_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas aali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded aali_image_filter_cp_def]
  definition "aal_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas aal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded aal_image_filter_cp_def]
  definition "aar_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas aar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded aar_image_filter_cp_def]
  definition "aah_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas aah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded aah_image_filter_cp_def]
  definition "aaa_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas aaa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aaa_image_filter_cp_def]
  definition "aais_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas aais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded aais_image_filter_cp_def]
  definition "aisli_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas aisli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded aisli_image_filter_cp_def]
  definition "aisl_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei ls_empty ls_ins"
  lemmas aisl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded aisl_image_filter_cp_def]
  definition "aisr_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei rs_empty rs_ins"
  lemmas aisr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded aisr_image_filter_cp_def]
  definition "aish_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei hs_empty hs_ins"
  lemmas aish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded aish_image_filter_cp_def]
  definition "aisa_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas aisa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded aisa_image_filter_cp_def]
  definition "aisis_image_filter_cp == SetGA.image_filter_cp ahs_iteratei ias_iteratei ias_empty ias_ins"
  lemmas aisis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded aisis_image_filter_cp_def]
  definition "islili_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei lsi_empty lsi_ins"
  lemmas islili_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_impl, folded islili_image_filter_cp_def]
  definition "islil_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei ls_empty ls_ins"
  lemmas islil_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_impl, folded islil_image_filter_cp_def]
  definition "islir_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei rs_empty rs_ins"
  lemmas islir_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_impl, folded islir_image_filter_cp_def]
  definition "islih_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei hs_empty hs_ins"
  lemmas islih_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_impl, folded islih_image_filter_cp_def]
  definition "islia_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei ahs_empty ahs_ins"
  lemmas islia_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_impl, folded islia_image_filter_cp_def]
  definition "isliis_image_filter_cp == SetGA.image_filter_cp ias_iteratei lsi_iteratei ias_empty ias_ins"
  lemmas isliis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_impl, folded isliis_image_filter_cp_def]
  definition "islli_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei lsi_empty lsi_ins"
  lemmas islli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_impl, folded islli_image_filter_cp_def]
  definition "isll_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei ls_empty ls_ins"
  lemmas isll_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_impl, folded isll_image_filter_cp_def]
  definition "islr_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei rs_empty rs_ins"
  lemmas islr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_impl, folded islr_image_filter_cp_def]
  definition "islh_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei hs_empty hs_ins"
  lemmas islh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_impl, folded islh_image_filter_cp_def]
  definition "isla_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei ahs_empty ahs_ins"
  lemmas isla_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isla_image_filter_cp_def]
  definition "islis_image_filter_cp == SetGA.image_filter_cp ias_iteratei ls_iteratei ias_empty ias_ins"
  lemmas islis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_impl, folded islis_image_filter_cp_def]
  definition "isrli_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei lsi_empty lsi_ins"
  lemmas isrli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isrli_image_filter_cp_def]
  definition "isrl_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei ls_empty ls_ins"
  lemmas isrl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_impl, folded isrl_image_filter_cp_def]
  definition "isrr_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei rs_empty rs_ins"
  lemmas isrr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_impl, folded isrr_image_filter_cp_def]
  definition "isrh_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei hs_empty hs_ins"
  lemmas isrh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_impl, folded isrh_image_filter_cp_def]
  definition "isra_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei ahs_empty ahs_ins"
  lemmas isra_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isra_image_filter_cp_def]
  definition "isris_image_filter_cp == SetGA.image_filter_cp ias_iteratei rs_iteratei ias_empty ias_ins"
  lemmas isris_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_impl, folded isris_image_filter_cp_def]
  definition "ishli_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei lsi_empty lsi_ins"
  lemmas ishli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded ishli_image_filter_cp_def]
  definition "ishl_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei ls_empty ls_ins"
  lemmas ishl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_impl, folded ishl_image_filter_cp_def]
  definition "ishr_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei rs_empty rs_ins"
  lemmas ishr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_impl, folded ishr_image_filter_cp_def]
  definition "ishh_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei hs_empty hs_ins"
  lemmas ishh_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_impl, folded ishh_image_filter_cp_def]
  definition "isha_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei ahs_empty ahs_ins"
  lemmas isha_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isha_image_filter_cp_def]
  definition "ishis_image_filter_cp == SetGA.image_filter_cp ias_iteratei hs_iteratei ias_empty ias_ins"
  lemmas ishis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_impl, folded ishis_image_filter_cp_def]
  definition "isali_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei lsi_empty lsi_ins"
  lemmas isali_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isali_image_filter_cp_def]
  definition "isal_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei ls_empty ls_ins"
  lemmas isal_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_impl, folded isal_image_filter_cp_def]
  definition "isar_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei rs_empty rs_ins"
  lemmas isar_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_impl, folded isar_image_filter_cp_def]
  definition "isah_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei hs_empty hs_ins"
  lemmas isah_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_impl, folded isah_image_filter_cp_def]
  definition "isaa_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei ahs_empty ahs_ins"
  lemmas isaa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isaa_image_filter_cp_def]
  definition "isais_image_filter_cp == SetGA.image_filter_cp ias_iteratei ahs_iteratei ias_empty ias_ins"
  lemmas isais_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_impl, folded isais_image_filter_cp_def]
  definition "isisli_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei lsi_empty lsi_ins"
  lemmas isisli_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_impl, folded isisli_image_filter_cp_def]
  definition "isisl_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei ls_empty ls_ins"
  lemmas isisl_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_impl, folded isisl_image_filter_cp_def]
  definition "isisr_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei rs_empty rs_ins"
  lemmas isisr_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_impl, folded isisr_image_filter_cp_def]
  definition "isish_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei hs_empty hs_ins"
  lemmas isish_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_impl, folded isish_image_filter_cp_def]
  definition "isisa_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei ahs_empty ahs_ins"
  lemmas isisa_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_impl, folded isisa_image_filter_cp_def]
  definition "isisis_image_filter_cp == SetGA.image_filter_cp ias_iteratei ias_iteratei ias_empty ias_ins"
  lemmas isisis_image_filter_cp_correct = SetGA.image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_impl, folded isisis_image_filter_cp_def]

  definition "lilili_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas lilili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_inj_image_filter_cp_def]
  definition "lilil_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas lilil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lilil_inj_image_filter_cp_def]
  definition "lilir_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas lilir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilir_inj_image_filter_cp_def]
  definition "lilih_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas lilih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilih_inj_image_filter_cp_def]
  definition "lilia_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas lilia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_inj_image_filter_cp_def]
  definition "liliis_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas liliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liliis_inj_image_filter_cp_def]
  definition "lilli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas lilli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_inj_image_filter_cp_def]
  definition "lill_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lill_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lill_inj_image_filter_cp_def]
  definition "lilr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas lilr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilr_inj_image_filter_cp_def]
  definition "lilh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas lilh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilh_inj_image_filter_cp_def]
  definition "lila_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lila_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_inj_image_filter_cp_def]
  definition "lilis_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas lilis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lilis_inj_image_filter_cp_def]
  definition "lirli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lirli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_inj_image_filter_cp_def]
  definition "lirl_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lirl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lirl_inj_image_filter_cp_def]
  definition "lirr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lirr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lirr_inj_image_filter_cp_def]
  definition "lirh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lirh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lirh_inj_image_filter_cp_def]
  definition "lira_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lira_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_inj_image_filter_cp_def]
  definition "liris_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas liris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liris_inj_image_filter_cp_def]
  definition "lihli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lihli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_inj_image_filter_cp_def]
  definition "lihl_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lihl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lihl_inj_image_filter_cp_def]
  definition "lihr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lihr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lihr_inj_image_filter_cp_def]
  definition "lihh_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lihh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lihh_inj_image_filter_cp_def]
  definition "liha_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas liha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_inj_image_filter_cp_def]
  definition "lihis_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas lihis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lihis_inj_image_filter_cp_def]
  definition "liali_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas liali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_inj_image_filter_cp_def]
  definition "lial_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lial_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lial_inj_image_filter_cp_def]
  definition "liar_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas liar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liar_inj_image_filter_cp_def]
  definition "liah_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas liah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liah_inj_image_filter_cp_def]
  definition "liaa_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas liaa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_inj_image_filter_cp_def]
  definition "liais_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas liais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liais_inj_image_filter_cp_def]
  definition "liisli_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas liisli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liisli_inj_image_filter_cp_def]
  definition "liisl_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas liisl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded liisl_inj_image_filter_cp_def]
  definition "liisr_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas liisr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liisr_inj_image_filter_cp_def]
  definition "liish_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas liish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liish_inj_image_filter_cp_def]
  definition "liisa_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas liisa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liisa_inj_image_filter_cp_def]
  definition "liisis_inj_image_filter_cp == SetGA.inj_image_filter_cp lsi_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas liisis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF lsi_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded liisis_inj_image_filter_cp_def]
  definition "llili_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas llili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_inj_image_filter_cp_def]
  definition "llil_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas llil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded llil_inj_image_filter_cp_def]
  definition "llir_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas llir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llir_inj_image_filter_cp_def]
  definition "llih_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas llih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llih_inj_image_filter_cp_def]
  definition "llia_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas llia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_inj_image_filter_cp_def]
  definition "lliis_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas lliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lliis_inj_image_filter_cp_def]
  definition "llli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas llli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_inj_image_filter_cp_def]
  definition "lll_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lll_inj_image_filter_cp_def]
  definition "llr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas llr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llr_inj_image_filter_cp_def]
  definition "llh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas llh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llh_inj_image_filter_cp_def]
  definition "lla_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_inj_image_filter_cp_def]
  definition "llis_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas llis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded llis_inj_image_filter_cp_def]
  definition "lrli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_inj_image_filter_cp_def]
  definition "lrl_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inj_image_filter_cp_def]
  definition "lrr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inj_image_filter_cp_def]
  definition "lrh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inj_image_filter_cp_def]
  definition "lra_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_inj_image_filter_cp_def]
  definition "lris_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas lris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lris_inj_image_filter_cp_def]
  definition "lhli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_inj_image_filter_cp_def]
  definition "lhl_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inj_image_filter_cp_def]
  definition "lhr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inj_image_filter_cp_def]
  definition "lhh_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inj_image_filter_cp_def]
  definition "lha_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas lha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_inj_image_filter_cp_def]
  definition "lhis_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas lhis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lhis_inj_image_filter_cp_def]
  definition "lali_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas lali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_inj_image_filter_cp_def]
  definition "lal_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lal_inj_image_filter_cp_def]
  definition "lar_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas lar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lar_inj_image_filter_cp_def]
  definition "lah_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas lah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lah_inj_image_filter_cp_def]
  definition "laa_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas laa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_inj_image_filter_cp_def]
  definition "lais_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas lais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lais_inj_image_filter_cp_def]
  definition "lisli_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas lisli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lisli_inj_image_filter_cp_def]
  definition "lisl_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas lisl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lisl_inj_image_filter_cp_def]
  definition "lisr_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas lisr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lisr_inj_image_filter_cp_def]
  definition "lish_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas lish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lish_inj_image_filter_cp_def]
  definition "lisa_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas lisa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lisa_inj_image_filter_cp_def]
  definition "lisis_inj_image_filter_cp == SetGA.inj_image_filter_cp ls_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas lisis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ls_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded lisis_inj_image_filter_cp_def]
  definition "rlili_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas rlili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_inj_image_filter_cp_def]
  definition "rlil_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas rlil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rlil_inj_image_filter_cp_def]
  definition "rlir_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas rlir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlir_inj_image_filter_cp_def]
  definition "rlih_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas rlih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlih_inj_image_filter_cp_def]
  definition "rlia_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas rlia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_inj_image_filter_cp_def]
  definition "rliis_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas rliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rliis_inj_image_filter_cp_def]
  definition "rlli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas rlli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_inj_image_filter_cp_def]
  definition "rll_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas rll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rll_inj_image_filter_cp_def]
  definition "rlr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas rlr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inj_image_filter_cp_def]
  definition "rlh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas rlh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inj_image_filter_cp_def]
  definition "rla_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas rla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_inj_image_filter_cp_def]
  definition "rlis_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas rlis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rlis_inj_image_filter_cp_def]
  definition "rrli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas rrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_inj_image_filter_cp_def]
  definition "rrl_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas rrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inj_image_filter_cp_def]
  definition "rrr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas rrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inj_image_filter_cp_def]
  definition "rrh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas rrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inj_image_filter_cp_def]
  definition "rra_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas rra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_inj_image_filter_cp_def]
  definition "rris_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas rris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rris_inj_image_filter_cp_def]
  definition "rhli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas rhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_inj_image_filter_cp_def]
  definition "rhl_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas rhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inj_image_filter_cp_def]
  definition "rhr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas rhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inj_image_filter_cp_def]
  definition "rhh_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas rhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inj_image_filter_cp_def]
  definition "rha_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas rha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_inj_image_filter_cp_def]
  definition "rhis_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas rhis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rhis_inj_image_filter_cp_def]
  definition "rali_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas rali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_inj_image_filter_cp_def]
  definition "ral_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas ral_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ral_inj_image_filter_cp_def]
  definition "rar_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas rar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rar_inj_image_filter_cp_def]
  definition "rah_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas rah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rah_inj_image_filter_cp_def]
  definition "raa_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas raa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_inj_image_filter_cp_def]
  definition "rais_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas rais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded rais_inj_image_filter_cp_def]
  definition "risli_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas risli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded risli_inj_image_filter_cp_def]
  definition "risl_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas risl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded risl_inj_image_filter_cp_def]
  definition "risr_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas risr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded risr_inj_image_filter_cp_def]
  definition "rish_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas rish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rish_inj_image_filter_cp_def]
  definition "risa_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas risa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded risa_inj_image_filter_cp_def]
  definition "risis_inj_image_filter_cp == SetGA.inj_image_filter_cp rs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas risis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF rs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded risis_inj_image_filter_cp_def]
  definition "hlili_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas hlili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_inj_image_filter_cp_def]
  definition "hlil_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas hlil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hlil_inj_image_filter_cp_def]
  definition "hlir_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas hlir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlir_inj_image_filter_cp_def]
  definition "hlih_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas hlih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlih_inj_image_filter_cp_def]
  definition "hlia_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas hlia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_inj_image_filter_cp_def]
  definition "hliis_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas hliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hliis_inj_image_filter_cp_def]
  definition "hlli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas hlli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_inj_image_filter_cp_def]
  definition "hll_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas hll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hll_inj_image_filter_cp_def]
  definition "hlr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas hlr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inj_image_filter_cp_def]
  definition "hlh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas hlh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inj_image_filter_cp_def]
  definition "hla_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas hla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_inj_image_filter_cp_def]
  definition "hlis_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas hlis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hlis_inj_image_filter_cp_def]
  definition "hrli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas hrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_inj_image_filter_cp_def]
  definition "hrl_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas hrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inj_image_filter_cp_def]
  definition "hrr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas hrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inj_image_filter_cp_def]
  definition "hrh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas hrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inj_image_filter_cp_def]
  definition "hra_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas hra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_inj_image_filter_cp_def]
  definition "hris_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas hris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hris_inj_image_filter_cp_def]
  definition "hhli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas hhli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_inj_image_filter_cp_def]
  definition "hhl_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas hhl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inj_image_filter_cp_def]
  definition "hhr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas hhr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inj_image_filter_cp_def]
  definition "hhh_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas hhh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inj_image_filter_cp_def]
  definition "hha_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas hha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_inj_image_filter_cp_def]
  definition "hhis_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas hhis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hhis_inj_image_filter_cp_def]
  definition "hali_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas hali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_inj_image_filter_cp_def]
  definition "hal_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas hal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hal_inj_image_filter_cp_def]
  definition "har_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas har_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded har_inj_image_filter_cp_def]
  definition "hah_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas hah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hah_inj_image_filter_cp_def]
  definition "haa_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas haa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_inj_image_filter_cp_def]
  definition "hais_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas hais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hais_inj_image_filter_cp_def]
  definition "hisli_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas hisli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hisli_inj_image_filter_cp_def]
  definition "hisl_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas hisl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hisl_inj_image_filter_cp_def]
  definition "hisr_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas hisr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hisr_inj_image_filter_cp_def]
  definition "hish_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas hish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hish_inj_image_filter_cp_def]
  definition "hisa_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas hisa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hisa_inj_image_filter_cp_def]
  definition "hisis_inj_image_filter_cp == SetGA.inj_image_filter_cp hs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas hisis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF hs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded hisis_inj_image_filter_cp_def]
  definition "alili_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas alili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_inj_image_filter_cp_def]
  definition "alil_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas alil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded alil_inj_image_filter_cp_def]
  definition "alir_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas alir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alir_inj_image_filter_cp_def]
  definition "alih_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas alih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alih_inj_image_filter_cp_def]
  definition "alia_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas alia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_inj_image_filter_cp_def]
  definition "aliis_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas aliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aliis_inj_image_filter_cp_def]
  definition "alli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas alli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_inj_image_filter_cp_def]
  definition "all_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas all_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded all_inj_image_filter_cp_def]
  definition "alr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas alr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alr_inj_image_filter_cp_def]
  definition "alh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas alh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alh_inj_image_filter_cp_def]
  definition "ala_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas ala_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_inj_image_filter_cp_def]
  definition "alis_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas alis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded alis_inj_image_filter_cp_def]
  definition "arli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas arli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_inj_image_filter_cp_def]
  definition "arl_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas arl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded arl_inj_image_filter_cp_def]
  definition "arr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas arr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded arr_inj_image_filter_cp_def]
  definition "arh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas arh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded arh_inj_image_filter_cp_def]
  definition "ara_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas ara_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_inj_image_filter_cp_def]
  definition "aris_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas aris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aris_inj_image_filter_cp_def]
  definition "ahli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ahli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_inj_image_filter_cp_def]
  definition "ahl_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ahl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ahl_inj_image_filter_cp_def]
  definition "ahr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ahr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ahr_inj_image_filter_cp_def]
  definition "ahh_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ahh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ahh_inj_image_filter_cp_def]
  definition "aha_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas aha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_inj_image_filter_cp_def]
  definition "ahis_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas ahis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ahis_inj_image_filter_cp_def]
  definition "aali_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas aali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_inj_image_filter_cp_def]
  definition "aal_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas aal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aal_inj_image_filter_cp_def]
  definition "aar_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas aar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aar_inj_image_filter_cp_def]
  definition "aah_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas aah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aah_inj_image_filter_cp_def]
  definition "aaa_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas aaa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_inj_image_filter_cp_def]
  definition "aais_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas aais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aais_inj_image_filter_cp_def]
  definition "aisli_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas aisli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aisli_inj_image_filter_cp_def]
  definition "aisl_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas aisl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aisl_inj_image_filter_cp_def]
  definition "aisr_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas aisr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aisr_inj_image_filter_cp_def]
  definition "aish_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas aish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aish_inj_image_filter_cp_def]
  definition "aisa_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas aisa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aisa_inj_image_filter_cp_def]
  definition "aisis_inj_image_filter_cp == SetGA.inj_image_filter_cp ahs_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas aisis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ahs_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded aisis_inj_image_filter_cp_def]
  definition "islili_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas islili_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islili_inj_image_filter_cp_def]
  definition "islil_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas islil_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded islil_inj_image_filter_cp_def]
  definition "islir_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas islir_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islir_inj_image_filter_cp_def]
  definition "islih_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas islih_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islih_inj_image_filter_cp_def]
  definition "islia_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas islia_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded islia_inj_image_filter_cp_def]
  definition "isliis_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei lsi_iteratei ias_empty ias_ins_dj"
  lemmas isliis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl lsi_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isliis_inj_image_filter_cp_def]
  definition "islli_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas islli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islli_inj_image_filter_cp_def]
  definition "isll_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas isll_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isll_inj_image_filter_cp_def]
  definition "islr_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas islr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islr_inj_image_filter_cp_def]
  definition "islh_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas islh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islh_inj_image_filter_cp_def]
  definition "isla_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas isla_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isla_inj_image_filter_cp_def]
  definition "islis_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ls_iteratei ias_empty ias_ins_dj"
  lemmas islis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ls_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded islis_inj_image_filter_cp_def]
  definition "isrli_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas isrli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isrli_inj_image_filter_cp_def]
  definition "isrl_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas isrl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isrl_inj_image_filter_cp_def]
  definition "isrr_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas isrr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isrr_inj_image_filter_cp_def]
  definition "isrh_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas isrh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isrh_inj_image_filter_cp_def]
  definition "isra_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas isra_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isra_inj_image_filter_cp_def]
  definition "isris_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei rs_iteratei ias_empty ias_ins_dj"
  lemmas isris_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl rs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isris_inj_image_filter_cp_def]
  definition "ishli_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ishli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ishli_inj_image_filter_cp_def]
  definition "ishl_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ishl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ishl_inj_image_filter_cp_def]
  definition "ishr_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ishr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ishr_inj_image_filter_cp_def]
  definition "ishh_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ishh_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ishh_inj_image_filter_cp_def]
  definition "isha_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas isha_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isha_inj_image_filter_cp_def]
  definition "ishis_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei hs_iteratei ias_empty ias_ins_dj"
  lemmas ishis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl hs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded ishis_inj_image_filter_cp_def]
  definition "isali_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas isali_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isali_inj_image_filter_cp_def]
  definition "isal_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas isal_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isal_inj_image_filter_cp_def]
  definition "isar_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas isar_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isar_inj_image_filter_cp_def]
  definition "isah_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas isah_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isah_inj_image_filter_cp_def]
  definition "isaa_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas isaa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isaa_inj_image_filter_cp_def]
  definition "isais_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ahs_iteratei ias_empty ias_ins_dj"
  lemmas isais_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ahs_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isais_inj_image_filter_cp_def]
  definition "isisli_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas isisli_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isisli_inj_image_filter_cp_def]
  definition "isisl_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas isisl_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isisl_inj_image_filter_cp_def]
  definition "isisr_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas isisr_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isisr_inj_image_filter_cp_def]
  definition "isish_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas isish_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isish_inj_image_filter_cp_def]
  definition "isisa_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas isisa_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isisa_inj_image_filter_cp_def]
  definition "isisis_inj_image_filter_cp == SetGA.inj_image_filter_cp ias_iteratei ias_iteratei ias_empty ias_ins_dj"
  lemmas isisis_inj_image_filter_cp_correct = SetGA.inj_image_filter_cp_correct[OF ias_iteratei_impl ias_iteratei_impl ias_empty_impl ias_ins_dj_impl, folded isisis_inj_image_filter_cp_def]

  definition "lilili_cart == SetGA.cart lsi_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas lilili_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilili_cart_def]
  definition "lilil_cart == SetGA.cart lsi_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas lilil_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lilil_cart_def]
  definition "lilir_cart == SetGA.cart lsi_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas lilir_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilir_cart_def]
  definition "lilih_cart == SetGA.cart lsi_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas lilih_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilih_cart_def]
  definition "lilia_cart == SetGA.cart lsi_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas lilia_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lilia_cart_def]
  definition "lilli_cart == SetGA.cart lsi_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas lilli_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lilli_cart_def]
  definition "lill_cart == SetGA.cart lsi_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lill_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lill_cart_def]
  definition "lilr_cart == SetGA.cart lsi_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas lilr_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lilr_cart_def]
  definition "lilh_cart == SetGA.cart lsi_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas lilh_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lilh_cart_def]
  definition "lila_cart == SetGA.cart lsi_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lila_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lila_cart_def]
  definition "lirli_cart == SetGA.cart lsi_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lirli_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lirli_cart_def]
  definition "lirl_cart == SetGA.cart lsi_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lirl_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lirl_cart_def]
  definition "lirr_cart == SetGA.cart lsi_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lirr_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lirr_cart_def]
  definition "lirh_cart == SetGA.cart lsi_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lirh_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lirh_cart_def]
  definition "lira_cart == SetGA.cart lsi_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lira_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lira_cart_def]
  definition "lihli_cart == SetGA.cart lsi_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lihli_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lihli_cart_def]
  definition "lihl_cart == SetGA.cart lsi_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lihl_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lihl_cart_def]
  definition "lihr_cart == SetGA.cart lsi_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lihr_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lihr_cart_def]
  definition "lihh_cart == SetGA.cart lsi_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lihh_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lihh_cart_def]
  definition "liha_cart == SetGA.cart lsi_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas liha_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liha_cart_def]
  definition "liali_cart == SetGA.cart lsi_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas liali_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liali_cart_def]
  definition "lial_cart == SetGA.cart lsi_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lial_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lial_cart_def]
  definition "liar_cart == SetGA.cart lsi_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas liar_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liar_cart_def]
  definition "liah_cart == SetGA.cart lsi_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas liah_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liah_cart_def]
  definition "liaa_cart == SetGA.cart lsi_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas liaa_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liaa_cart_def]
  definition "liisli_cart == SetGA.cart lsi_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas liisli_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded liisli_cart_def]
  definition "liisl_cart == SetGA.cart lsi_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas liisl_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded liisl_cart_def]
  definition "liisr_cart == SetGA.cart lsi_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas liisr_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded liisr_cart_def]
  definition "liish_cart == SetGA.cart lsi_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas liish_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded liish_cart_def]
  definition "liisa_cart == SetGA.cart lsi_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas liisa_cart_correct = SetGA.cart_correct[OF lsi_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded liisa_cart_def]
  definition "llili_cart == SetGA.cart ls_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas llili_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llili_cart_def]
  definition "llil_cart == SetGA.cart ls_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas llil_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded llil_cart_def]
  definition "llir_cart == SetGA.cart ls_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas llir_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llir_cart_def]
  definition "llih_cart == SetGA.cart ls_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas llih_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llih_cart_def]
  definition "llia_cart == SetGA.cart ls_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas llia_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded llia_cart_def]
  definition "llli_cart == SetGA.cart ls_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas llli_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded llli_cart_def]
  definition "lll_cart == SetGA.cart ls_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas lll_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lll_cart_def]
  definition "llr_cart == SetGA.cart ls_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas llr_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded llr_cart_def]
  definition "llh_cart == SetGA.cart ls_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas llh_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded llh_cart_def]
  definition "lla_cart == SetGA.cart ls_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas lla_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lla_cart_def]
  definition "lrli_cart == SetGA.cart ls_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas lrli_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lrli_cart_def]
  definition "lrl_cart == SetGA.cart ls_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas lrl_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lrl_cart_def]
  definition "lrr_cart == SetGA.cart ls_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas lrr_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lrr_cart_def]
  definition "lrh_cart == SetGA.cart ls_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas lrh_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lrh_cart_def]
  definition "lra_cart == SetGA.cart ls_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas lra_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lra_cart_def]
  definition "lhli_cart == SetGA.cart ls_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas lhli_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lhli_cart_def]
  definition "lhl_cart == SetGA.cart ls_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas lhl_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lhl_cart_def]
  definition "lhr_cart == SetGA.cart ls_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas lhr_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lhr_cart_def]
  definition "lhh_cart == SetGA.cart ls_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas lhh_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lhh_cart_def]
  definition "lha_cart == SetGA.cart ls_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas lha_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lha_cart_def]
  definition "lali_cart == SetGA.cart ls_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas lali_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lali_cart_def]
  definition "lal_cart == SetGA.cart ls_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas lal_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lal_cart_def]
  definition "lar_cart == SetGA.cart ls_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas lar_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lar_cart_def]
  definition "lah_cart == SetGA.cart ls_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas lah_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lah_cart_def]
  definition "laa_cart == SetGA.cart ls_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas laa_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded laa_cart_def]
  definition "lisli_cart == SetGA.cart ls_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas lisli_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded lisli_cart_def]
  definition "lisl_cart == SetGA.cart ls_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas lisl_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded lisl_cart_def]
  definition "lisr_cart == SetGA.cart ls_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas lisr_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded lisr_cart_def]
  definition "lish_cart == SetGA.cart ls_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas lish_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded lish_cart_def]
  definition "lisa_cart == SetGA.cart ls_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas lisa_cart_correct = SetGA.cart_correct[OF ls_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded lisa_cart_def]
  definition "rlili_cart == SetGA.cart rs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas rlili_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlili_cart_def]
  definition "rlil_cart == SetGA.cart rs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas rlil_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rlil_cart_def]
  definition "rlir_cart == SetGA.cart rs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas rlir_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlir_cart_def]
  definition "rlih_cart == SetGA.cart rs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas rlih_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlih_cart_def]
  definition "rlia_cart == SetGA.cart rs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas rlia_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rlia_cart_def]
  definition "rlli_cart == SetGA.cart rs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas rlli_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rlli_cart_def]
  definition "rll_cart == SetGA.cart rs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas rll_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rll_cart_def]
  definition "rlr_cart == SetGA.cart rs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas rlr_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rlr_cart_def]
  definition "rlh_cart == SetGA.cart rs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas rlh_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rlh_cart_def]
  definition "rla_cart == SetGA.cart rs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas rla_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rla_cart_def]
  definition "rrli_cart == SetGA.cart rs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas rrli_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rrli_cart_def]
  definition "rrl_cart == SetGA.cart rs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas rrl_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rrl_cart_def]
  definition "rrr_cart == SetGA.cart rs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas rrr_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rrr_cart_def]
  definition "rrh_cart == SetGA.cart rs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas rrh_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rrh_cart_def]
  definition "rra_cart == SetGA.cart rs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas rra_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rra_cart_def]
  definition "rhli_cart == SetGA.cart rs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas rhli_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rhli_cart_def]
  definition "rhl_cart == SetGA.cart rs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas rhl_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded rhl_cart_def]
  definition "rhr_cart == SetGA.cart rs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas rhr_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rhr_cart_def]
  definition "rhh_cart == SetGA.cart rs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas rhh_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rhh_cart_def]
  definition "rha_cart == SetGA.cart rs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas rha_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded rha_cart_def]
  definition "rali_cart == SetGA.cart rs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas rali_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded rali_cart_def]
  definition "ral_cart == SetGA.cart rs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas ral_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ral_cart_def]
  definition "rar_cart == SetGA.cart rs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas rar_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded rar_cart_def]
  definition "rah_cart == SetGA.cart rs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas rah_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rah_cart_def]
  definition "raa_cart == SetGA.cart rs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas raa_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded raa_cart_def]
  definition "risli_cart == SetGA.cart rs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas risli_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded risli_cart_def]
  definition "risl_cart == SetGA.cart rs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas risl_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded risl_cart_def]
  definition "risr_cart == SetGA.cart rs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas risr_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded risr_cart_def]
  definition "rish_cart == SetGA.cart rs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas rish_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded rish_cart_def]
  definition "risa_cart == SetGA.cart rs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas risa_cart_correct = SetGA.cart_correct[OF rs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded risa_cart_def]
  definition "hlili_cart == SetGA.cart hs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas hlili_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlili_cart_def]
  definition "hlil_cart == SetGA.cart hs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas hlil_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hlil_cart_def]
  definition "hlir_cart == SetGA.cart hs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas hlir_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlir_cart_def]
  definition "hlih_cart == SetGA.cart hs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas hlih_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlih_cart_def]
  definition "hlia_cart == SetGA.cart hs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas hlia_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hlia_cart_def]
  definition "hlli_cart == SetGA.cart hs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas hlli_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hlli_cart_def]
  definition "hll_cart == SetGA.cart hs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas hll_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hll_cart_def]
  definition "hlr_cart == SetGA.cart hs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas hlr_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hlr_cart_def]
  definition "hlh_cart == SetGA.cart hs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas hlh_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hlh_cart_def]
  definition "hla_cart == SetGA.cart hs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas hla_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hla_cart_def]
  definition "hrli_cart == SetGA.cart hs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas hrli_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hrli_cart_def]
  definition "hrl_cart == SetGA.cart hs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas hrl_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hrl_cart_def]
  definition "hrr_cart == SetGA.cart hs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas hrr_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hrr_cart_def]
  definition "hrh_cart == SetGA.cart hs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas hrh_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hrh_cart_def]
  definition "hra_cart == SetGA.cart hs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas hra_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hra_cart_def]
  definition "hhli_cart == SetGA.cart hs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas hhli_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hhli_cart_def]
  definition "hhl_cart == SetGA.cart hs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas hhl_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hhl_cart_def]
  definition "hhr_cart == SetGA.cart hs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas hhr_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hhr_cart_def]
  definition "hhh_cart == SetGA.cart hs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas hhh_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hhh_cart_def]
  definition "hha_cart == SetGA.cart hs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas hha_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hha_cart_def]
  definition "hali_cart == SetGA.cart hs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas hali_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hali_cart_def]
  definition "hal_cart == SetGA.cart hs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas hal_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hal_cart_def]
  definition "har_cart == SetGA.cart hs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas har_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded har_cart_def]
  definition "hah_cart == SetGA.cart hs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas hah_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hah_cart_def]
  definition "haa_cart == SetGA.cart hs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas haa_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded haa_cart_def]
  definition "hisli_cart == SetGA.cart hs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas hisli_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded hisli_cart_def]
  definition "hisl_cart == SetGA.cart hs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas hisl_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded hisl_cart_def]
  definition "hisr_cart == SetGA.cart hs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas hisr_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded hisr_cart_def]
  definition "hish_cart == SetGA.cart hs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas hish_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded hish_cart_def]
  definition "hisa_cart == SetGA.cart hs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas hisa_cart_correct = SetGA.cart_correct[OF hs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded hisa_cart_def]
  definition "alili_cart == SetGA.cart ahs_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas alili_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alili_cart_def]
  definition "alil_cart == SetGA.cart ahs_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas alil_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded alil_cart_def]
  definition "alir_cart == SetGA.cart ahs_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas alir_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alir_cart_def]
  definition "alih_cart == SetGA.cart ahs_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas alih_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alih_cart_def]
  definition "alia_cart == SetGA.cart ahs_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas alia_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded alia_cart_def]
  definition "alli_cart == SetGA.cart ahs_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas alli_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded alli_cart_def]
  definition "all_cart == SetGA.cart ahs_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas all_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded all_cart_def]
  definition "alr_cart == SetGA.cart ahs_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas alr_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded alr_cart_def]
  definition "alh_cart == SetGA.cart ahs_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas alh_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded alh_cart_def]
  definition "ala_cart == SetGA.cart ahs_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas ala_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ala_cart_def]
  definition "arli_cart == SetGA.cart ahs_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas arli_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded arli_cart_def]
  definition "arl_cart == SetGA.cart ahs_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas arl_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded arl_cart_def]
  definition "arr_cart == SetGA.cart ahs_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas arr_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded arr_cart_def]
  definition "arh_cart == SetGA.cart ahs_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas arh_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded arh_cart_def]
  definition "ara_cart == SetGA.cart ahs_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas ara_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded ara_cart_def]
  definition "ahli_cart == SetGA.cart ahs_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ahli_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ahli_cart_def]
  definition "ahl_cart == SetGA.cart ahs_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ahl_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ahl_cart_def]
  definition "ahr_cart == SetGA.cart ahs_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ahr_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ahr_cart_def]
  definition "ahh_cart == SetGA.cart ahs_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ahh_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ahh_cart_def]
  definition "aha_cart == SetGA.cart ahs_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas aha_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aha_cart_def]
  definition "aali_cart == SetGA.cart ahs_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas aali_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aali_cart_def]
  definition "aal_cart == SetGA.cart ahs_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas aal_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aal_cart_def]
  definition "aar_cart == SetGA.cart ahs_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas aar_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aar_cart_def]
  definition "aah_cart == SetGA.cart ahs_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas aah_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aah_cart_def]
  definition "aaa_cart == SetGA.cart ahs_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas aaa_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aaa_cart_def]
  definition "aisli_cart == SetGA.cart ahs_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas aisli_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded aisli_cart_def]
  definition "aisl_cart == SetGA.cart ahs_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas aisl_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded aisl_cart_def]
  definition "aisr_cart == SetGA.cart ahs_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas aisr_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded aisr_cart_def]
  definition "aish_cart == SetGA.cart ahs_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas aish_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded aish_cart_def]
  definition "aisa_cart == SetGA.cart ahs_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas aisa_cart_correct = SetGA.cart_correct[OF ahs_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded aisa_cart_def]
  definition "islili_cart == SetGA.cart ias_iteratei lsi_iteratei lsi_empty lsi_ins_dj"
  lemmas islili_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl lsi_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islili_cart_def]
  definition "islil_cart == SetGA.cart ias_iteratei lsi_iteratei ls_empty ls_ins_dj"
  lemmas islil_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl lsi_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded islil_cart_def]
  definition "islir_cart == SetGA.cart ias_iteratei lsi_iteratei rs_empty rs_ins_dj"
  lemmas islir_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl lsi_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islir_cart_def]
  definition "islih_cart == SetGA.cart ias_iteratei lsi_iteratei hs_empty hs_ins_dj"
  lemmas islih_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl lsi_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islih_cart_def]
  definition "islia_cart == SetGA.cart ias_iteratei lsi_iteratei ahs_empty ahs_ins_dj"
  lemmas islia_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl lsi_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded islia_cart_def]
  definition "islli_cart == SetGA.cart ias_iteratei ls_iteratei lsi_empty lsi_ins_dj"
  lemmas islli_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ls_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded islli_cart_def]
  definition "isll_cart == SetGA.cart ias_iteratei ls_iteratei ls_empty ls_ins_dj"
  lemmas isll_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ls_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isll_cart_def]
  definition "islr_cart == SetGA.cart ias_iteratei ls_iteratei rs_empty rs_ins_dj"
  lemmas islr_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ls_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded islr_cart_def]
  definition "islh_cart == SetGA.cart ias_iteratei ls_iteratei hs_empty hs_ins_dj"
  lemmas islh_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ls_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded islh_cart_def]
  definition "isla_cart == SetGA.cart ias_iteratei ls_iteratei ahs_empty ahs_ins_dj"
  lemmas isla_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ls_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isla_cart_def]
  definition "isrli_cart == SetGA.cart ias_iteratei rs_iteratei lsi_empty lsi_ins_dj"
  lemmas isrli_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl rs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isrli_cart_def]
  definition "isrl_cart == SetGA.cart ias_iteratei rs_iteratei ls_empty ls_ins_dj"
  lemmas isrl_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl rs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isrl_cart_def]
  definition "isrr_cart == SetGA.cart ias_iteratei rs_iteratei rs_empty rs_ins_dj"
  lemmas isrr_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl rs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isrr_cart_def]
  definition "isrh_cart == SetGA.cart ias_iteratei rs_iteratei hs_empty hs_ins_dj"
  lemmas isrh_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl rs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isrh_cart_def]
  definition "isra_cart == SetGA.cart ias_iteratei rs_iteratei ahs_empty ahs_ins_dj"
  lemmas isra_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl rs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isra_cart_def]
  definition "ishli_cart == SetGA.cart ias_iteratei hs_iteratei lsi_empty lsi_ins_dj"
  lemmas ishli_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl hs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded ishli_cart_def]
  definition "ishl_cart == SetGA.cart ias_iteratei hs_iteratei ls_empty ls_ins_dj"
  lemmas ishl_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl hs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded ishl_cart_def]
  definition "ishr_cart == SetGA.cart ias_iteratei hs_iteratei rs_empty rs_ins_dj"
  lemmas ishr_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl hs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded ishr_cart_def]
  definition "ishh_cart == SetGA.cart ias_iteratei hs_iteratei hs_empty hs_ins_dj"
  lemmas ishh_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl hs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded ishh_cart_def]
  definition "isha_cart == SetGA.cart ias_iteratei hs_iteratei ahs_empty ahs_ins_dj"
  lemmas isha_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl hs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isha_cart_def]
  definition "isali_cart == SetGA.cart ias_iteratei ahs_iteratei lsi_empty lsi_ins_dj"
  lemmas isali_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ahs_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isali_cart_def]
  definition "isal_cart == SetGA.cart ias_iteratei ahs_iteratei ls_empty ls_ins_dj"
  lemmas isal_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ahs_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isal_cart_def]
  definition "isar_cart == SetGA.cart ias_iteratei ahs_iteratei rs_empty rs_ins_dj"
  lemmas isar_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ahs_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isar_cart_def]
  definition "isah_cart == SetGA.cart ias_iteratei ahs_iteratei hs_empty hs_ins_dj"
  lemmas isah_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ahs_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isah_cart_def]
  definition "isaa_cart == SetGA.cart ias_iteratei ahs_iteratei ahs_empty ahs_ins_dj"
  lemmas isaa_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ahs_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isaa_cart_def]
  definition "isisli_cart == SetGA.cart ias_iteratei ias_iteratei lsi_empty lsi_ins_dj"
  lemmas isisli_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ias_iteratei_impl lsi_empty_impl lsi_ins_dj_impl, folded isisli_cart_def]
  definition "isisl_cart == SetGA.cart ias_iteratei ias_iteratei ls_empty ls_ins_dj"
  lemmas isisl_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ias_iteratei_impl ls_empty_impl ls_ins_dj_impl, folded isisl_cart_def]
  definition "isisr_cart == SetGA.cart ias_iteratei ias_iteratei rs_empty rs_ins_dj"
  lemmas isisr_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ias_iteratei_impl rs_empty_impl rs_ins_dj_impl, folded isisr_cart_def]
  definition "isish_cart == SetGA.cart ias_iteratei ias_iteratei hs_empty hs_ins_dj"
  lemmas isish_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ias_iteratei_impl hs_empty_impl hs_ins_dj_impl, folded isish_cart_def]
  definition "isisa_cart == SetGA.cart ias_iteratei ias_iteratei ahs_empty ahs_ins_dj"
  lemmas isisa_cart_correct = SetGA.cart_correct[OF ias_iteratei_impl ias_iteratei_impl ahs_empty_impl ahs_ins_dj_impl, folded isisa_cart_def]

  definition "lsi_to_fifo == it_set_to_fifo lsi_iteratei"
  lemmas lsi_to_fifo_correct = it_set_to_fifo_correct[OF lsi_iteratei_impl, folded lsi_to_fifo_def]
  definition "ls_to_fifo == it_set_to_fifo ls_iteratei"
  lemmas ls_to_fifo_correct = it_set_to_fifo_correct[OF ls_iteratei_impl, folded ls_to_fifo_def]
  definition "rs_to_fifo == it_set_to_fifo rs_iteratei"
  lemmas rs_to_fifo_correct = it_set_to_fifo_correct[OF rs_iteratei_impl, folded rs_to_fifo_def]
  definition "hs_to_fifo == it_set_to_fifo hs_iteratei"
  lemmas hs_to_fifo_correct = it_set_to_fifo_correct[OF hs_iteratei_impl, folded hs_to_fifo_def]
  definition "ahs_to_fifo == it_set_to_fifo ahs_iteratei"
  lemmas ahs_to_fifo_correct = it_set_to_fifo_correct[OF ahs_iteratei_impl, folded ahs_to_fifo_def]
  definition "ias_to_fifo == it_set_to_fifo ias_iteratei"
  lemmas ias_to_fifo_correct = it_set_to_fifo_correct[OF ias_iteratei_impl, folded ias_to_fifo_def]

  definition "lili_map_to_nat == map_to_nat lsi_iteratei lmi_empty lmi_update"
  lemmas lili_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl lmi_empty_impl lmi_update_impl, folded lili_map_to_nat_def]
  definition "lil_map_to_nat == map_to_nat lsi_iteratei lm_empty lm_update"
  lemmas lil_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl lm_empty_impl lm_update_impl, folded lil_map_to_nat_def]
  definition "lir_map_to_nat == map_to_nat lsi_iteratei rm_empty rm_update"
  lemmas lir_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl rm_empty_impl rm_update_impl, folded lir_map_to_nat_def]
  definition "lih_map_to_nat == map_to_nat lsi_iteratei hm_empty hm_update"
  lemmas lih_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl hm_empty_impl hm_update_impl, folded lih_map_to_nat_def]
  definition "lia_map_to_nat == map_to_nat lsi_iteratei ahm_empty ahm_update"
  lemmas lia_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl ahm_empty_impl ahm_update_impl, folded lia_map_to_nat_def]
  definition "liim_map_to_nat == map_to_nat lsi_iteratei iam_empty iam_update"
  lemmas liim_map_to_nat_correct = map_to_nat_correct[OF lsi_iteratei_impl iam_empty_impl iam_update_impl, folded liim_map_to_nat_def]
  definition "lli_map_to_nat == map_to_nat ls_iteratei lmi_empty lmi_update"
  lemmas lli_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl lmi_empty_impl lmi_update_impl, folded lli_map_to_nat_def]
  definition "ll_map_to_nat == map_to_nat ls_iteratei lm_empty lm_update"
  lemmas ll_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl lm_empty_impl lm_update_impl, folded ll_map_to_nat_def]
  definition "lr_map_to_nat == map_to_nat ls_iteratei rm_empty rm_update"
  lemmas lr_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl rm_empty_impl rm_update_impl, folded lr_map_to_nat_def]
  definition "lh_map_to_nat == map_to_nat ls_iteratei hm_empty hm_update"
  lemmas lh_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl hm_empty_impl hm_update_impl, folded lh_map_to_nat_def]
  definition "la_map_to_nat == map_to_nat ls_iteratei ahm_empty ahm_update"
  lemmas la_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl ahm_empty_impl ahm_update_impl, folded la_map_to_nat_def]
  definition "lim_map_to_nat == map_to_nat ls_iteratei iam_empty iam_update"
  lemmas lim_map_to_nat_correct = map_to_nat_correct[OF ls_iteratei_impl iam_empty_impl iam_update_impl, folded lim_map_to_nat_def]
  definition "rli_map_to_nat == map_to_nat rs_iteratei lmi_empty lmi_update"
  lemmas rli_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl lmi_empty_impl lmi_update_impl, folded rli_map_to_nat_def]
  definition "rl_map_to_nat == map_to_nat rs_iteratei lm_empty lm_update"
  lemmas rl_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl lm_empty_impl lm_update_impl, folded rl_map_to_nat_def]
  definition "rr_map_to_nat == map_to_nat rs_iteratei rm_empty rm_update"
  lemmas rr_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl rm_empty_impl rm_update_impl, folded rr_map_to_nat_def]
  definition "rh_map_to_nat == map_to_nat rs_iteratei hm_empty hm_update"
  lemmas rh_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl hm_empty_impl hm_update_impl, folded rh_map_to_nat_def]
  definition "ra_map_to_nat == map_to_nat rs_iteratei ahm_empty ahm_update"
  lemmas ra_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl ahm_empty_impl ahm_update_impl, folded ra_map_to_nat_def]
  definition "rim_map_to_nat == map_to_nat rs_iteratei iam_empty iam_update"
  lemmas rim_map_to_nat_correct = map_to_nat_correct[OF rs_iteratei_impl iam_empty_impl iam_update_impl, folded rim_map_to_nat_def]
  definition "hli_map_to_nat == map_to_nat hs_iteratei lmi_empty lmi_update"
  lemmas hli_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl lmi_empty_impl lmi_update_impl, folded hli_map_to_nat_def]
  definition "hl_map_to_nat == map_to_nat hs_iteratei lm_empty lm_update"
  lemmas hl_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl lm_empty_impl lm_update_impl, folded hl_map_to_nat_def]
  definition "hr_map_to_nat == map_to_nat hs_iteratei rm_empty rm_update"
  lemmas hr_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl rm_empty_impl rm_update_impl, folded hr_map_to_nat_def]
  definition "hh_map_to_nat == map_to_nat hs_iteratei hm_empty hm_update"
  lemmas hh_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl hm_empty_impl hm_update_impl, folded hh_map_to_nat_def]
  definition "ha_map_to_nat == map_to_nat hs_iteratei ahm_empty ahm_update"
  lemmas ha_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl ahm_empty_impl ahm_update_impl, folded ha_map_to_nat_def]
  definition "him_map_to_nat == map_to_nat hs_iteratei iam_empty iam_update"
  lemmas him_map_to_nat_correct = map_to_nat_correct[OF hs_iteratei_impl iam_empty_impl iam_update_impl, folded him_map_to_nat_def]
  definition "ali_map_to_nat == map_to_nat ahs_iteratei lmi_empty lmi_update"
  lemmas ali_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl lmi_empty_impl lmi_update_impl, folded ali_map_to_nat_def]
  definition "al_map_to_nat == map_to_nat ahs_iteratei lm_empty lm_update"
  lemmas al_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl lm_empty_impl lm_update_impl, folded al_map_to_nat_def]
  definition "ar_map_to_nat == map_to_nat ahs_iteratei rm_empty rm_update"
  lemmas ar_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl rm_empty_impl rm_update_impl, folded ar_map_to_nat_def]
  definition "ah_map_to_nat == map_to_nat ahs_iteratei hm_empty hm_update"
  lemmas ah_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl hm_empty_impl hm_update_impl, folded ah_map_to_nat_def]
  definition "aa_map_to_nat == map_to_nat ahs_iteratei ahm_empty ahm_update"
  lemmas aa_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl ahm_empty_impl ahm_update_impl, folded aa_map_to_nat_def]
  definition "aim_map_to_nat == map_to_nat ahs_iteratei iam_empty iam_update"
  lemmas aim_map_to_nat_correct = map_to_nat_correct[OF ahs_iteratei_impl iam_empty_impl iam_update_impl, folded aim_map_to_nat_def]
  definition "isli_map_to_nat == map_to_nat ias_iteratei lmi_empty lmi_update"
  lemmas isli_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl lmi_empty_impl lmi_update_impl, folded isli_map_to_nat_def]
  definition "isl_map_to_nat == map_to_nat ias_iteratei lm_empty lm_update"
  lemmas isl_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl lm_empty_impl lm_update_impl, folded isl_map_to_nat_def]
  definition "isr_map_to_nat == map_to_nat ias_iteratei rm_empty rm_update"
  lemmas isr_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl rm_empty_impl rm_update_impl, folded isr_map_to_nat_def]
  definition "ish_map_to_nat == map_to_nat ias_iteratei hm_empty hm_update"
  lemmas ish_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl hm_empty_impl hm_update_impl, folded ish_map_to_nat_def]
  definition "isa_map_to_nat == map_to_nat ias_iteratei ahm_empty ahm_update"
  lemmas isa_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl ahm_empty_impl ahm_update_impl, folded isa_map_to_nat_def]
  definition "isim_map_to_nat == map_to_nat ias_iteratei iam_empty iam_update"
  lemmas isim_map_to_nat_correct = map_to_nat_correct[OF ias_iteratei_impl iam_empty_impl iam_update_impl, folded isim_map_to_nat_def]

  definition "lili_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei lmi_update_dj lmi_empty"
  lemmas lili_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded lili_dom_fun_to_map_def]
  definition "lil_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei lm_update_dj lm_empty"
  lemmas lil_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl lm_update_dj_impl lm_empty_impl, folded lil_dom_fun_to_map_def]
  definition "lir_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei rm_update_dj rm_empty"
  lemmas lir_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl rm_update_dj_impl rm_empty_impl, folded lir_dom_fun_to_map_def]
  definition "lih_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei hm_update_dj hm_empty"
  lemmas lih_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl hm_update_dj_impl hm_empty_impl, folded lih_dom_fun_to_map_def]
  definition "lia_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei ahm_update_dj ahm_empty"
  lemmas lia_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded lia_dom_fun_to_map_def]
  definition "liim_dom_fun_to_map == it_dom_fun_to_map lsi_iteratei iam_update_dj iam_empty"
  lemmas liim_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF lsi_iteratei_impl iam_update_dj_impl iam_empty_impl, folded liim_dom_fun_to_map_def]
  definition "lli_dom_fun_to_map == it_dom_fun_to_map ls_iteratei lmi_update_dj lmi_empty"
  lemmas lli_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded lli_dom_fun_to_map_def]
  definition "ll_dom_fun_to_map == it_dom_fun_to_map ls_iteratei lm_update_dj lm_empty"
  lemmas ll_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl lm_update_dj_impl lm_empty_impl, folded ll_dom_fun_to_map_def]
  definition "lr_dom_fun_to_map == it_dom_fun_to_map ls_iteratei rm_update_dj rm_empty"
  lemmas lr_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl rm_update_dj_impl rm_empty_impl, folded lr_dom_fun_to_map_def]
  definition "lh_dom_fun_to_map == it_dom_fun_to_map ls_iteratei hm_update_dj hm_empty"
  lemmas lh_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl hm_update_dj_impl hm_empty_impl, folded lh_dom_fun_to_map_def]
  definition "la_dom_fun_to_map == it_dom_fun_to_map ls_iteratei ahm_update_dj ahm_empty"
  lemmas la_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded la_dom_fun_to_map_def]
  definition "lim_dom_fun_to_map == it_dom_fun_to_map ls_iteratei iam_update_dj iam_empty"
  lemmas lim_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ls_iteratei_impl iam_update_dj_impl iam_empty_impl, folded lim_dom_fun_to_map_def]
  definition "rli_dom_fun_to_map == it_dom_fun_to_map rs_iteratei lmi_update_dj lmi_empty"
  lemmas rli_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded rli_dom_fun_to_map_def]
  definition "rl_dom_fun_to_map == it_dom_fun_to_map rs_iteratei lm_update_dj lm_empty"
  lemmas rl_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl lm_update_dj_impl lm_empty_impl, folded rl_dom_fun_to_map_def]
  definition "rr_dom_fun_to_map == it_dom_fun_to_map rs_iteratei rm_update_dj rm_empty"
  lemmas rr_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl rm_update_dj_impl rm_empty_impl, folded rr_dom_fun_to_map_def]
  definition "rh_dom_fun_to_map == it_dom_fun_to_map rs_iteratei hm_update_dj hm_empty"
  lemmas rh_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl hm_update_dj_impl hm_empty_impl, folded rh_dom_fun_to_map_def]
  definition "ra_dom_fun_to_map == it_dom_fun_to_map rs_iteratei ahm_update_dj ahm_empty"
  lemmas ra_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded ra_dom_fun_to_map_def]
  definition "rim_dom_fun_to_map == it_dom_fun_to_map rs_iteratei iam_update_dj iam_empty"
  lemmas rim_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF rs_iteratei_impl iam_update_dj_impl iam_empty_impl, folded rim_dom_fun_to_map_def]
  definition "hli_dom_fun_to_map == it_dom_fun_to_map hs_iteratei lmi_update_dj lmi_empty"
  lemmas hli_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded hli_dom_fun_to_map_def]
  definition "hl_dom_fun_to_map == it_dom_fun_to_map hs_iteratei lm_update_dj lm_empty"
  lemmas hl_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl lm_update_dj_impl lm_empty_impl, folded hl_dom_fun_to_map_def]
  definition "hr_dom_fun_to_map == it_dom_fun_to_map hs_iteratei rm_update_dj rm_empty"
  lemmas hr_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl rm_update_dj_impl rm_empty_impl, folded hr_dom_fun_to_map_def]
  definition "hh_dom_fun_to_map == it_dom_fun_to_map hs_iteratei hm_update_dj hm_empty"
  lemmas hh_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl hm_update_dj_impl hm_empty_impl, folded hh_dom_fun_to_map_def]
  definition "ha_dom_fun_to_map == it_dom_fun_to_map hs_iteratei ahm_update_dj ahm_empty"
  lemmas ha_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded ha_dom_fun_to_map_def]
  definition "him_dom_fun_to_map == it_dom_fun_to_map hs_iteratei iam_update_dj iam_empty"
  lemmas him_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF hs_iteratei_impl iam_update_dj_impl iam_empty_impl, folded him_dom_fun_to_map_def]
  definition "ali_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei lmi_update_dj lmi_empty"
  lemmas ali_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded ali_dom_fun_to_map_def]
  definition "al_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei lm_update_dj lm_empty"
  lemmas al_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl lm_update_dj_impl lm_empty_impl, folded al_dom_fun_to_map_def]
  definition "ar_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei rm_update_dj rm_empty"
  lemmas ar_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl rm_update_dj_impl rm_empty_impl, folded ar_dom_fun_to_map_def]
  definition "ah_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei hm_update_dj hm_empty"
  lemmas ah_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl hm_update_dj_impl hm_empty_impl, folded ah_dom_fun_to_map_def]
  definition "aa_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei ahm_update_dj ahm_empty"
  lemmas aa_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded aa_dom_fun_to_map_def]
  definition "aim_dom_fun_to_map == it_dom_fun_to_map ahs_iteratei iam_update_dj iam_empty"
  lemmas aim_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ahs_iteratei_impl iam_update_dj_impl iam_empty_impl, folded aim_dom_fun_to_map_def]
  definition "isli_dom_fun_to_map == it_dom_fun_to_map ias_iteratei lmi_update_dj lmi_empty"
  lemmas isli_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl lmi_update_dj_impl lmi_empty_impl, folded isli_dom_fun_to_map_def]
  definition "isl_dom_fun_to_map == it_dom_fun_to_map ias_iteratei lm_update_dj lm_empty"
  lemmas isl_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl lm_update_dj_impl lm_empty_impl, folded isl_dom_fun_to_map_def]
  definition "isr_dom_fun_to_map == it_dom_fun_to_map ias_iteratei rm_update_dj rm_empty"
  lemmas isr_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl rm_update_dj_impl rm_empty_impl, folded isr_dom_fun_to_map_def]
  definition "ish_dom_fun_to_map == it_dom_fun_to_map ias_iteratei hm_update_dj hm_empty"
  lemmas ish_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl hm_update_dj_impl hm_empty_impl, folded ish_dom_fun_to_map_def]
  definition "isa_dom_fun_to_map == it_dom_fun_to_map ias_iteratei ahm_update_dj ahm_empty"
  lemmas isa_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl ahm_update_dj_impl ahm_empty_impl, folded isa_dom_fun_to_map_def]
  definition "isim_dom_fun_to_map == it_dom_fun_to_map ias_iteratei iam_update_dj iam_empty"
  lemmas isim_dom_fun_to_map_correct = it_dom_fun_to_map_correct[OF ias_iteratei_impl iam_update_dj_impl iam_empty_impl, folded isim_dom_fun_to_map_def]

  definition "lili_restrict == MapGA.it_map_restrict lmi_iteratei lmi_empty lmi_update_dj"
  lemmas lili_restrict_impl = MapGA.it_map_restrict_correct[OF lmi_iteratei_impl lmi_empty_impl lmi_update_dj_impl, folded lili_restrict_def]
  interpretation lili: map_restrict lmi_\<alpha> lmi_invar lmi_\<alpha> lmi_invar lili_restrict using lili_restrict_impl .
  definition "ll_restrict == MapGA.it_map_restrict lm_iteratei lm_empty lm_update_dj"
  lemmas ll_restrict_impl = MapGA.it_map_restrict_correct[OF lm_iteratei_impl lm_empty_impl lm_update_dj_impl, folded ll_restrict_def]
  interpretation ll: map_restrict lm_\<alpha> lm_invar lm_\<alpha> lm_invar ll_restrict using ll_restrict_impl .
  definition "rr_restrict == MapGA.it_map_restrict rm_iteratei rm_empty rm_update_dj"
  lemmas rr_restrict_impl = MapGA.it_map_restrict_correct[OF rm_iteratei_impl rm_empty_impl rm_update_dj_impl, folded rr_restrict_def]
  interpretation rr: map_restrict rm_\<alpha> rm_invar rm_\<alpha> rm_invar rr_restrict using rr_restrict_impl .
  definition "hh_restrict == MapGA.it_map_restrict hm_iteratei hm_empty hm_update_dj"
  lemmas hh_restrict_impl = MapGA.it_map_restrict_correct[OF hm_iteratei_impl hm_empty_impl hm_update_dj_impl, folded hh_restrict_def]
  interpretation hh: map_restrict hm_\<alpha> hm_invar hm_\<alpha> hm_invar hh_restrict using hh_restrict_impl .
  definition "aa_restrict == MapGA.it_map_restrict ahm_iteratei ahm_empty ahm_update_dj"
  lemmas aa_restrict_impl = MapGA.it_map_restrict_correct[OF ahm_iteratei_impl ahm_empty_impl ahm_update_dj_impl, folded aa_restrict_def]
  interpretation aa: map_restrict ahm_\<alpha> ahm_invar ahm_\<alpha> ahm_invar aa_restrict using aa_restrict_impl .
  definition "imim_restrict == MapGA.it_map_restrict iam_iteratei iam_empty iam_update_dj"
  lemmas imim_restrict_impl = MapGA.it_map_restrict_correct[OF iam_iteratei_impl iam_empty_impl iam_update_dj_impl, folded imim_restrict_def]
  interpretation imim: map_restrict iam_\<alpha> iam_invar iam_\<alpha> iam_invar imim_restrict using imim_restrict_impl .

  definition "lili_map_value_image_filter == MapGA.it_map_value_image_filter lmi_iteratei lmi_empty lmi_update_dj"
  lemmas lili_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF lmi_iteratei_impl lmi_empty_impl lmi_update_dj_impl, folded lili_map_value_image_filter_def]
  interpretation lili: map_value_image_filter lmi_\<alpha> lmi_invar lmi_\<alpha> lmi_invar lili_map_value_image_filter using lili_map_value_image_filter_impl .
  definition "ll_map_value_image_filter == MapGA.it_map_value_image_filter lm_iteratei lm_empty lm_update_dj"
  lemmas ll_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF lm_iteratei_impl lm_empty_impl lm_update_dj_impl, folded ll_map_value_image_filter_def]
  interpretation ll: map_value_image_filter lm_\<alpha> lm_invar lm_\<alpha> lm_invar ll_map_value_image_filter using ll_map_value_image_filter_impl .
  definition "rr_map_value_image_filter == MapGA.it_map_value_image_filter rm_iteratei rm_empty rm_update_dj"
  lemmas rr_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF rm_iteratei_impl rm_empty_impl rm_update_dj_impl, folded rr_map_value_image_filter_def]
  interpretation rr: map_value_image_filter rm_\<alpha> rm_invar rm_\<alpha> rm_invar rr_map_value_image_filter using rr_map_value_image_filter_impl .
  definition "hh_map_value_image_filter == MapGA.it_map_value_image_filter hm_iteratei hm_empty hm_update_dj"
  lemmas hh_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF hm_iteratei_impl hm_empty_impl hm_update_dj_impl, folded hh_map_value_image_filter_def]
  interpretation hh: map_value_image_filter hm_\<alpha> hm_invar hm_\<alpha> hm_invar hh_map_value_image_filter using hh_map_value_image_filter_impl .
  definition "aa_map_value_image_filter == MapGA.it_map_value_image_filter ahm_iteratei ahm_empty ahm_update_dj"
  lemmas aa_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF ahm_iteratei_impl ahm_empty_impl ahm_update_dj_impl, folded aa_map_value_image_filter_def]
  interpretation aa: map_value_image_filter ahm_\<alpha> ahm_invar ahm_\<alpha> ahm_invar aa_map_value_image_filter using aa_map_value_image_filter_impl .
  definition "imim_map_value_image_filter == MapGA.it_map_value_image_filter iam_iteratei iam_empty iam_update_dj"
  lemmas imim_map_value_image_filter_impl = MapGA.it_map_value_image_filter_correct[OF iam_iteratei_impl iam_empty_impl iam_update_dj_impl, folded imim_map_value_image_filter_def]
  interpretation imim: map_value_image_filter iam_\<alpha> iam_invar iam_\<alpha> iam_invar imim_map_value_image_filter using imim_map_value_image_filter_impl .

  definition "lili_map_image_filter == MapGA.it_map_image_filter lmi_iteratei lmi_empty lmi_update_dj"
  lemmas lili_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF lmi_iteratei_impl lmi_empty_impl lmi_update_dj_impl, folded lili_map_image_filter_def]
  interpretation lili: map_image_filter lmi_\<alpha> lmi_invar lmi_\<alpha> lmi_invar lili_map_image_filter using lili_map_image_filter_impl .
  definition "ll_map_image_filter == MapGA.it_map_image_filter lm_iteratei lm_empty lm_update_dj"
  lemmas ll_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF lm_iteratei_impl lm_empty_impl lm_update_dj_impl, folded ll_map_image_filter_def]
  interpretation ll: map_image_filter lm_\<alpha> lm_invar lm_\<alpha> lm_invar ll_map_image_filter using ll_map_image_filter_impl .
  definition "rr_map_image_filter == MapGA.it_map_image_filter rm_iteratei rm_empty rm_update_dj"
  lemmas rr_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF rm_iteratei_impl rm_empty_impl rm_update_dj_impl, folded rr_map_image_filter_def]
  interpretation rr: map_image_filter rm_\<alpha> rm_invar rm_\<alpha> rm_invar rr_map_image_filter using rr_map_image_filter_impl .
  definition "hh_map_image_filter == MapGA.it_map_image_filter hm_iteratei hm_empty hm_update_dj"
  lemmas hh_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF hm_iteratei_impl hm_empty_impl hm_update_dj_impl, folded hh_map_image_filter_def]
  interpretation hh: map_image_filter hm_\<alpha> hm_invar hm_\<alpha> hm_invar hh_map_image_filter using hh_map_image_filter_impl .
  definition "aa_map_image_filter == MapGA.it_map_image_filter ahm_iteratei ahm_empty ahm_update_dj"
  lemmas aa_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF ahm_iteratei_impl ahm_empty_impl ahm_update_dj_impl, folded aa_map_image_filter_def]
  interpretation aa: map_image_filter ahm_\<alpha> ahm_invar ahm_\<alpha> ahm_invar aa_map_image_filter using aa_map_image_filter_impl .
  definition "imim_map_image_filter == MapGA.it_map_image_filter iam_iteratei iam_empty iam_update_dj"
  lemmas imim_map_image_filter_impl = MapGA.it_map_image_filter_correct[OF iam_iteratei_impl iam_empty_impl iam_update_dj_impl, folded imim_map_image_filter_def]
  interpretation imim: map_image_filter iam_\<alpha> iam_invar iam_\<alpha> iam_invar imim_map_image_filter using imim_map_image_filter_impl .

  definition "lmi_sng == MapGA.eu_sng lmi_empty lmi_update"
  lemmas lmi_sng_impl = MapGA.eu_sng_correct[OF lmi_empty_impl lmi_update_impl, folded lmi_sng_def]
  interpretation lmi: map_sng lmi_\<alpha> lmi_invar lmi_sng using lmi_sng_impl .
  definition "lm_sng == MapGA.eu_sng lm_empty lm_update"
  lemmas lm_sng_impl = MapGA.eu_sng_correct[OF lm_empty_impl lm_update_impl, folded lm_sng_def]
  interpretation lm: map_sng lm_\<alpha> lm_invar lm_sng using lm_sng_impl .
  definition "rm_sng == MapGA.eu_sng rm_empty rm_update"
  lemmas rm_sng_impl = MapGA.eu_sng_correct[OF rm_empty_impl rm_update_impl, folded rm_sng_def]
  interpretation rm: map_sng rm_\<alpha> rm_invar rm_sng using rm_sng_impl .
  definition "hm_sng == MapGA.eu_sng hm_empty hm_update"
  lemmas hm_sng_impl = MapGA.eu_sng_correct[OF hm_empty_impl hm_update_impl, folded hm_sng_def]
  interpretation hm: map_sng hm_\<alpha> hm_invar hm_sng using hm_sng_impl .
  definition "ahm_sng == MapGA.eu_sng ahm_empty ahm_update"
  lemmas ahm_sng_impl = MapGA.eu_sng_correct[OF ahm_empty_impl ahm_update_impl, folded ahm_sng_def]
  interpretation ahm: map_sng ahm_\<alpha> ahm_invar ahm_sng using ahm_sng_impl .
  definition "iam_sng == MapGA.eu_sng iam_empty iam_update"
  lemmas iam_sng_impl = MapGA.eu_sng_correct[OF iam_empty_impl iam_update_impl, folded iam_sng_def]
  interpretation iam: map_sng iam_\<alpha> iam_invar iam_sng using iam_sng_impl .

  definition "lmi_size == MapGA.it_size lmi_iteratei"
  lemmas lmi_size_impl = MapGA.it_size_correct[OF lmi_iteratei_impl, folded lmi_size_def]
  interpretation lmi: map_size lmi_\<alpha> lmi_invar lmi_size using lmi_size_impl .
  definition "lm_size == MapGA.it_size lm_iteratei"
  lemmas lm_size_impl = MapGA.it_size_correct[OF lm_iteratei_impl, folded lm_size_def]
  interpretation lm: map_size lm_\<alpha> lm_invar lm_size using lm_size_impl .
  definition "rm_size == MapGA.it_size rm_iteratei"
  lemmas rm_size_impl = MapGA.it_size_correct[OF rm_iteratei_impl, folded rm_size_def]
  interpretation rm: map_size rm_\<alpha> rm_invar rm_size using rm_size_impl .
  definition "hm_size == MapGA.it_size hm_iteratei"
  lemmas hm_size_impl = MapGA.it_size_correct[OF hm_iteratei_impl, folded hm_size_def]
  interpretation hm: map_size hm_\<alpha> hm_invar hm_size using hm_size_impl .
  definition "ahm_size == MapGA.it_size ahm_iteratei"
  lemmas ahm_size_impl = MapGA.it_size_correct[OF ahm_iteratei_impl, folded ahm_size_def]
  interpretation ahm: map_size ahm_\<alpha> ahm_invar ahm_size using ahm_size_impl .
  definition "iam_size == MapGA.it_size iam_iteratei"
  lemmas iam_size_impl = MapGA.it_size_correct[OF iam_iteratei_impl, folded iam_size_def]
  interpretation iam: map_size iam_\<alpha> iam_invar iam_size using iam_size_impl .

  definition "lmi_size_abort == MapGA.iti_size_abort lmi_iteratei"
  lemmas lmi_size_abort_impl = MapGA.iti_size_abort_correct[OF lmi_iteratei_impl, folded lmi_size_abort_def]
  interpretation lmi: map_size_abort lmi_\<alpha> lmi_invar lmi_size_abort using lmi_size_abort_impl .
  definition "lm_size_abort == MapGA.iti_size_abort lm_iteratei"
  lemmas lm_size_abort_impl = MapGA.iti_size_abort_correct[OF lm_iteratei_impl, folded lm_size_abort_def]
  interpretation lm: map_size_abort lm_\<alpha> lm_invar lm_size_abort using lm_size_abort_impl .
  definition "rm_size_abort == MapGA.iti_size_abort rm_iteratei"
  lemmas rm_size_abort_impl = MapGA.iti_size_abort_correct[OF rm_iteratei_impl, folded rm_size_abort_def]
  interpretation rm: map_size_abort rm_\<alpha> rm_invar rm_size_abort using rm_size_abort_impl .
  definition "hm_size_abort == MapGA.iti_size_abort hm_iteratei"
  lemmas hm_size_abort_impl = MapGA.iti_size_abort_correct[OF hm_iteratei_impl, folded hm_size_abort_def]
  interpretation hm: map_size_abort hm_\<alpha> hm_invar hm_size_abort using hm_size_abort_impl .
  definition "ahm_size_abort == MapGA.iti_size_abort ahm_iteratei"
  lemmas ahm_size_abort_impl = MapGA.iti_size_abort_correct[OF ahm_iteratei_impl, folded ahm_size_abort_def]
  interpretation ahm: map_size_abort ahm_\<alpha> ahm_invar ahm_size_abort using ahm_size_abort_impl .
  definition "iam_size_abort == MapGA.iti_size_abort iam_iteratei"
  lemmas iam_size_abort_impl = MapGA.iti_size_abort_correct[OF iam_iteratei_impl, folded iam_size_abort_def]
  interpretation iam: map_size_abort iam_\<alpha> iam_invar iam_size_abort using iam_size_abort_impl .

  definition "lmi_isSng == MapGA.sza_isSng lmi_iteratei"
  lemmas lmi_isSng_impl = MapGA.sza_isSng_correct[OF lmi_iteratei_impl, folded lmi_isSng_def]
  interpretation lmi: map_isSng lmi_\<alpha> lmi_invar lmi_isSng using lmi_isSng_impl .
  definition "lm_isSng == MapGA.sza_isSng lm_iteratei"
  lemmas lm_isSng_impl = MapGA.sza_isSng_correct[OF lm_iteratei_impl, folded lm_isSng_def]
  interpretation lm: map_isSng lm_\<alpha> lm_invar lm_isSng using lm_isSng_impl .
  definition "rm_isSng == MapGA.sza_isSng rm_iteratei"
  lemmas rm_isSng_impl = MapGA.sza_isSng_correct[OF rm_iteratei_impl, folded rm_isSng_def]
  interpretation rm: map_isSng rm_\<alpha> rm_invar rm_isSng using rm_isSng_impl .
  definition "hm_isSng == MapGA.sza_isSng hm_iteratei"
  lemmas hm_isSng_impl = MapGA.sza_isSng_correct[OF hm_iteratei_impl, folded hm_isSng_def]
  interpretation hm: map_isSng hm_\<alpha> hm_invar hm_isSng using hm_isSng_impl .
  definition "ahm_isSng == MapGA.sza_isSng ahm_iteratei"
  lemmas ahm_isSng_impl = MapGA.sza_isSng_correct[OF ahm_iteratei_impl, folded ahm_isSng_def]
  interpretation ahm: map_isSng ahm_\<alpha> ahm_invar ahm_isSng using ahm_isSng_impl .
  definition "iam_isSng == MapGA.sza_isSng iam_iteratei"
  lemmas iam_isSng_impl = MapGA.sza_isSng_correct[OF iam_iteratei_impl, folded iam_isSng_def]
  interpretation iam: map_isSng iam_\<alpha> iam_invar iam_isSng using iam_isSng_impl .

  definition "lmi_ball == MapGA.sel_ball lmi_sel"
  lemmas lmi_ball_impl = MapGA.sel_ball_correct[OF lmi_sel_impl, folded lmi_ball_def]
  interpretation lmi: map_ball lmi_\<alpha> lmi_invar lmi_ball using lmi_ball_impl .
  definition "lm_ball == MapGA.sel_ball lm_sel"
  lemmas lm_ball_impl = MapGA.sel_ball_correct[OF lm_sel_impl, folded lm_ball_def]
  interpretation lm: map_ball lm_\<alpha> lm_invar lm_ball using lm_ball_impl .
  definition "rm_ball == MapGA.sel_ball rm_sel"
  lemmas rm_ball_impl = MapGA.sel_ball_correct[OF rm_sel_impl, folded rm_ball_def]
  interpretation rm: map_ball rm_\<alpha> rm_invar rm_ball using rm_ball_impl .
  definition "hm_ball == MapGA.sel_ball hm_sel"
  lemmas hm_ball_impl = MapGA.sel_ball_correct[OF hm_sel_impl, folded hm_ball_def]
  interpretation hm: map_ball hm_\<alpha> hm_invar hm_ball using hm_ball_impl .
  definition "ahm_ball == MapGA.sel_ball ahm_sel"
  lemmas ahm_ball_impl = MapGA.sel_ball_correct[OF ahm_sel_impl, folded ahm_ball_def]
  interpretation ahm: map_ball ahm_\<alpha> ahm_invar ahm_ball using ahm_ball_impl .
  definition "iam_ball == MapGA.sel_ball iam_sel"
  lemmas iam_ball_impl = MapGA.sel_ball_correct[OF iam_sel_impl, folded iam_ball_def]
  interpretation iam: map_ball iam_\<alpha> iam_invar iam_ball using iam_ball_impl .

  definition "lmi_bexists == MapGA.neg_ball_bexists lmi_ball"
  lemmas lmi_bexists_impl = MapGA.neg_ball_bexists_correct[OF lmi_ball_impl, folded lmi_bexists_def]
  interpretation lmi: map_bexists lmi_\<alpha> lmi_invar lmi_bexists using lmi_bexists_impl .
  definition "lm_bexists == MapGA.neg_ball_bexists lm_ball"
  lemmas lm_bexists_impl = MapGA.neg_ball_bexists_correct[OF lm_ball_impl, folded lm_bexists_def]
  interpretation lm: map_bexists lm_\<alpha> lm_invar lm_bexists using lm_bexists_impl .
  definition "rm_bexists == MapGA.neg_ball_bexists rm_ball"
  lemmas rm_bexists_impl = MapGA.neg_ball_bexists_correct[OF rm_ball_impl, folded rm_bexists_def]
  interpretation rm: map_bexists rm_\<alpha> rm_invar rm_bexists using rm_bexists_impl .
  definition "hm_bexists == MapGA.neg_ball_bexists hm_ball"
  lemmas hm_bexists_impl = MapGA.neg_ball_bexists_correct[OF hm_ball_impl, folded hm_bexists_def]
  interpretation hm: map_bexists hm_\<alpha> hm_invar hm_bexists using hm_bexists_impl .
  definition "ahm_bexists == MapGA.neg_ball_bexists ahm_ball"
  lemmas ahm_bexists_impl = MapGA.neg_ball_bexists_correct[OF ahm_ball_impl, folded ahm_bexists_def]
  interpretation ahm: map_bexists ahm_\<alpha> ahm_invar ahm_bexists using ahm_bexists_impl .
  definition "iam_bexists == MapGA.neg_ball_bexists iam_ball"
  lemmas iam_bexists_impl = MapGA.neg_ball_bexists_correct[OF iam_ball_impl, folded iam_bexists_def]
  interpretation iam: map_bexists iam_\<alpha> iam_invar iam_bexists using iam_bexists_impl .
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
definition "liis_idx_invar == idx_invar lmi_\<alpha> lmi_invar ias_\<alpha> ias_invar"
definition "liis_idx_lookup == idx_lookup lmi_lookup ias_empty"
lemmas liis_idx_lookup_correct = idx_lookup_correct[OF lmi_lookup_impl ias_empty_impl, folded liis_idx_invar_def liis_idx_lookup_def]
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
definition "lis_idx_invar == idx_invar lm_\<alpha> lm_invar ias_\<alpha> ias_invar"
definition "lis_idx_lookup == idx_lookup lm_lookup ias_empty"
lemmas lis_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl ias_empty_impl, folded lis_idx_invar_def lis_idx_lookup_def]
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
definition "ris_idx_invar == idx_invar rm_\<alpha> rm_invar ias_\<alpha> ias_invar"
definition "ris_idx_lookup == idx_lookup rm_lookup ias_empty"
lemmas ris_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl ias_empty_impl, folded ris_idx_invar_def ris_idx_lookup_def]
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
definition "his_idx_invar == idx_invar hm_\<alpha> hm_invar ias_\<alpha> ias_invar"
definition "his_idx_lookup == idx_lookup hm_lookup ias_empty"
lemmas his_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl ias_empty_impl, folded his_idx_invar_def his_idx_lookup_def]
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
definition "ais_idx_invar == idx_invar ahm_\<alpha> ahm_invar ias_\<alpha> ias_invar"
definition "ais_idx_lookup == idx_lookup ahm_lookup ias_empty"
lemmas ais_idx_lookup_correct = idx_lookup_correct[OF ahm_lookup_impl ias_empty_impl, folded ais_idx_invar_def ais_idx_lookup_def]
definition "imli_idx_invar == idx_invar iam_\<alpha> iam_invar lsi_\<alpha> lsi_invar"
definition "imli_idx_lookup == idx_lookup iam_lookup lsi_empty"
lemmas imli_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl lsi_empty_impl, folded imli_idx_invar_def imli_idx_lookup_def]
definition "iml_idx_invar == idx_invar iam_\<alpha> iam_invar ls_\<alpha> ls_invar"
definition "iml_idx_lookup == idx_lookup iam_lookup ls_empty"
lemmas iml_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl ls_empty_impl, folded iml_idx_invar_def iml_idx_lookup_def]
definition "imr_idx_invar == idx_invar iam_\<alpha> iam_invar rs_\<alpha> rs_invar"
definition "imr_idx_lookup == idx_lookup iam_lookup rs_empty"
lemmas imr_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl rs_empty_impl, folded imr_idx_invar_def imr_idx_lookup_def]
definition "imh_idx_invar == idx_invar iam_\<alpha> iam_invar hs_\<alpha> hs_invar"
definition "imh_idx_lookup == idx_lookup iam_lookup hs_empty"
lemmas imh_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl hs_empty_impl, folded imh_idx_invar_def imh_idx_lookup_def]
definition "ima_idx_invar == idx_invar iam_\<alpha> iam_invar ahs_\<alpha> ahs_invar"
definition "ima_idx_lookup == idx_lookup iam_lookup ahs_empty"
lemmas ima_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl ahs_empty_impl, folded ima_idx_invar_def ima_idx_lookup_def]
definition "imis_idx_invar == idx_invar iam_\<alpha> iam_invar ias_\<alpha> ias_invar"
definition "imis_idx_lookup == idx_lookup iam_lookup ias_empty"
lemmas imis_idx_lookup_correct = idx_lookup_correct[OF iam_lookup_impl ias_empty_impl, folded imis_idx_invar_def imis_idx_lookup_def]
(*#end_generated*)

(*#begin_generated*)
definition "lilili_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins lsi_iteratei"
lemmas lilili_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded lili_idx_invar_def lilili_idx_build_def]
definition "lilil_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins ls_iteratei"
lemmas lilil_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded lili_idx_invar_def lilil_idx_build_def]
definition "lilir_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins rs_iteratei"
lemmas lilir_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded lili_idx_invar_def lilir_idx_build_def]
definition "lilih_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins hs_iteratei"
lemmas lilih_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded lili_idx_invar_def lilih_idx_build_def]
definition "lilia_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins ahs_iteratei"
lemmas lilia_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded lili_idx_invar_def lilia_idx_build_def]
definition "liliis_idx_build == idx_build lmi_empty lmi_lookup lmi_update lsi_empty lsi_ins ias_iteratei"
lemmas liliis_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded lili_idx_invar_def liliis_idx_build_def]
definition "lilli_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins lsi_iteratei"
lemmas lilli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded lil_idx_invar_def lilli_idx_build_def]
definition "lill_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins ls_iteratei"
lemmas lill_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded lil_idx_invar_def lill_idx_build_def]
definition "lilr_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins rs_iteratei"
lemmas lilr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded lil_idx_invar_def lilr_idx_build_def]
definition "lilh_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins hs_iteratei"
lemmas lilh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded lil_idx_invar_def lilh_idx_build_def]
definition "lila_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins ahs_iteratei"
lemmas lila_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded lil_idx_invar_def lila_idx_build_def]
definition "lilis_idx_build == idx_build lmi_empty lmi_lookup lmi_update ls_empty ls_ins ias_iteratei"
lemmas lilis_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded lil_idx_invar_def lilis_idx_build_def]
definition "lirli_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins lsi_iteratei"
lemmas lirli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded lir_idx_invar_def lirli_idx_build_def]
definition "lirl_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins ls_iteratei"
lemmas lirl_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded lir_idx_invar_def lirl_idx_build_def]
definition "lirr_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins rs_iteratei"
lemmas lirr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded lir_idx_invar_def lirr_idx_build_def]
definition "lirh_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins hs_iteratei"
lemmas lirh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded lir_idx_invar_def lirh_idx_build_def]
definition "lira_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins ahs_iteratei"
lemmas lira_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded lir_idx_invar_def lira_idx_build_def]
definition "liris_idx_build == idx_build lmi_empty lmi_lookup lmi_update rs_empty rs_ins ias_iteratei"
lemmas liris_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded lir_idx_invar_def liris_idx_build_def]
definition "lihli_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins lsi_iteratei"
lemmas lihli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded lih_idx_invar_def lihli_idx_build_def]
definition "lihl_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins ls_iteratei"
lemmas lihl_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded lih_idx_invar_def lihl_idx_build_def]
definition "lihr_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins rs_iteratei"
lemmas lihr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded lih_idx_invar_def lihr_idx_build_def]
definition "lihh_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins hs_iteratei"
lemmas lihh_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded lih_idx_invar_def lihh_idx_build_def]
definition "liha_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins ahs_iteratei"
lemmas liha_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded lih_idx_invar_def liha_idx_build_def]
definition "lihis_idx_build == idx_build lmi_empty lmi_lookup lmi_update hs_empty hs_ins ias_iteratei"
lemmas lihis_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded lih_idx_invar_def lihis_idx_build_def]
definition "liali_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins lsi_iteratei"
lemmas liali_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded lia_idx_invar_def liali_idx_build_def]
definition "lial_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins ls_iteratei"
lemmas lial_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded lia_idx_invar_def lial_idx_build_def]
definition "liar_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins rs_iteratei"
lemmas liar_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded lia_idx_invar_def liar_idx_build_def]
definition "liah_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins hs_iteratei"
lemmas liah_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded lia_idx_invar_def liah_idx_build_def]
definition "liaa_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins ahs_iteratei"
lemmas liaa_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded lia_idx_invar_def liaa_idx_build_def]
definition "liais_idx_build == idx_build lmi_empty lmi_lookup lmi_update ahs_empty ahs_ins ias_iteratei"
lemmas liais_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded lia_idx_invar_def liais_idx_build_def]
definition "liisli_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins lsi_iteratei"
lemmas liisli_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded liis_idx_invar_def liisli_idx_build_def]
definition "liisl_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins ls_iteratei"
lemmas liisl_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded liis_idx_invar_def liisl_idx_build_def]
definition "liisr_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins rs_iteratei"
lemmas liisr_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded liis_idx_invar_def liisr_idx_build_def]
definition "liish_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins hs_iteratei"
lemmas liish_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded liis_idx_invar_def liish_idx_build_def]
definition "liisa_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins ahs_iteratei"
lemmas liisa_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded liis_idx_invar_def liisa_idx_build_def]
definition "liisis_idx_build == idx_build lmi_empty lmi_lookup lmi_update ias_empty ias_ins ias_iteratei"
lemmas liisis_idx_build_correct = idx_build_correct[OF lmi_empty_impl lmi_lookup_impl lmi_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded liis_idx_invar_def liisis_idx_build_def]
definition "llili_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins lsi_iteratei"
lemmas llili_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded lli_idx_invar_def llili_idx_build_def]
definition "llil_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins ls_iteratei"
lemmas llil_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded lli_idx_invar_def llil_idx_build_def]
definition "llir_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins rs_iteratei"
lemmas llir_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded lli_idx_invar_def llir_idx_build_def]
definition "llih_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins hs_iteratei"
lemmas llih_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded lli_idx_invar_def llih_idx_build_def]
definition "llia_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins ahs_iteratei"
lemmas llia_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded lli_idx_invar_def llia_idx_build_def]
definition "lliis_idx_build == idx_build lm_empty lm_lookup lm_update lsi_empty lsi_ins ias_iteratei"
lemmas lliis_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded lli_idx_invar_def lliis_idx_build_def]
definition "llli_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins lsi_iteratei"
lemmas llli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded ll_idx_invar_def llli_idx_build_def]
definition "lll_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins ls_iteratei"
lemmas lll_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded ll_idx_invar_def lll_idx_build_def]
definition "llr_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins rs_iteratei"
lemmas llr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded ll_idx_invar_def llr_idx_build_def]
definition "llh_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins hs_iteratei"
lemmas llh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded ll_idx_invar_def llh_idx_build_def]
definition "lla_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins ahs_iteratei"
lemmas lla_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded ll_idx_invar_def lla_idx_build_def]
definition "llis_idx_build == idx_build lm_empty lm_lookup lm_update ls_empty ls_ins ias_iteratei"
lemmas llis_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded ll_idx_invar_def llis_idx_build_def]
definition "lrli_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins lsi_iteratei"
lemmas lrli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded lr_idx_invar_def lrli_idx_build_def]
definition "lrl_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins ls_iteratei"
lemmas lrl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded lr_idx_invar_def lrl_idx_build_def]
definition "lrr_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins rs_iteratei"
lemmas lrr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded lr_idx_invar_def lrr_idx_build_def]
definition "lrh_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins hs_iteratei"
lemmas lrh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded lr_idx_invar_def lrh_idx_build_def]
definition "lra_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins ahs_iteratei"
lemmas lra_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded lr_idx_invar_def lra_idx_build_def]
definition "lris_idx_build == idx_build lm_empty lm_lookup lm_update rs_empty rs_ins ias_iteratei"
lemmas lris_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded lr_idx_invar_def lris_idx_build_def]
definition "lhli_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins lsi_iteratei"
lemmas lhli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded lh_idx_invar_def lhli_idx_build_def]
definition "lhl_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins ls_iteratei"
lemmas lhl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded lh_idx_invar_def lhl_idx_build_def]
definition "lhr_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins rs_iteratei"
lemmas lhr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded lh_idx_invar_def lhr_idx_build_def]
definition "lhh_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins hs_iteratei"
lemmas lhh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded lh_idx_invar_def lhh_idx_build_def]
definition "lha_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins ahs_iteratei"
lemmas lha_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded lh_idx_invar_def lha_idx_build_def]
definition "lhis_idx_build == idx_build lm_empty lm_lookup lm_update hs_empty hs_ins ias_iteratei"
lemmas lhis_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded lh_idx_invar_def lhis_idx_build_def]
definition "lali_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins lsi_iteratei"
lemmas lali_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded la_idx_invar_def lali_idx_build_def]
definition "lal_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins ls_iteratei"
lemmas lal_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded la_idx_invar_def lal_idx_build_def]
definition "lar_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins rs_iteratei"
lemmas lar_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded la_idx_invar_def lar_idx_build_def]
definition "lah_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins hs_iteratei"
lemmas lah_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded la_idx_invar_def lah_idx_build_def]
definition "laa_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins ahs_iteratei"
lemmas laa_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded la_idx_invar_def laa_idx_build_def]
definition "lais_idx_build == idx_build lm_empty lm_lookup lm_update ahs_empty ahs_ins ias_iteratei"
lemmas lais_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded la_idx_invar_def lais_idx_build_def]
definition "lisli_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins lsi_iteratei"
lemmas lisli_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded lis_idx_invar_def lisli_idx_build_def]
definition "lisl_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins ls_iteratei"
lemmas lisl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded lis_idx_invar_def lisl_idx_build_def]
definition "lisr_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins rs_iteratei"
lemmas lisr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded lis_idx_invar_def lisr_idx_build_def]
definition "lish_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins hs_iteratei"
lemmas lish_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded lis_idx_invar_def lish_idx_build_def]
definition "lisa_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins ahs_iteratei"
lemmas lisa_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded lis_idx_invar_def lisa_idx_build_def]
definition "lisis_idx_build == idx_build lm_empty lm_lookup lm_update ias_empty ias_ins ias_iteratei"
lemmas lisis_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded lis_idx_invar_def lisis_idx_build_def]
definition "rlili_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins lsi_iteratei"
lemmas rlili_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded rli_idx_invar_def rlili_idx_build_def]
definition "rlil_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins ls_iteratei"
lemmas rlil_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded rli_idx_invar_def rlil_idx_build_def]
definition "rlir_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins rs_iteratei"
lemmas rlir_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded rli_idx_invar_def rlir_idx_build_def]
definition "rlih_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins hs_iteratei"
lemmas rlih_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded rli_idx_invar_def rlih_idx_build_def]
definition "rlia_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins ahs_iteratei"
lemmas rlia_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded rli_idx_invar_def rlia_idx_build_def]
definition "rliis_idx_build == idx_build rm_empty rm_lookup rm_update lsi_empty lsi_ins ias_iteratei"
lemmas rliis_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded rli_idx_invar_def rliis_idx_build_def]
definition "rlli_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins lsi_iteratei"
lemmas rlli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded rl_idx_invar_def rlli_idx_build_def]
definition "rll_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins ls_iteratei"
lemmas rll_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded rl_idx_invar_def rll_idx_build_def]
definition "rlr_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins rs_iteratei"
lemmas rlr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded rl_idx_invar_def rlr_idx_build_def]
definition "rlh_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins hs_iteratei"
lemmas rlh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded rl_idx_invar_def rlh_idx_build_def]
definition "rla_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins ahs_iteratei"
lemmas rla_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded rl_idx_invar_def rla_idx_build_def]
definition "rlis_idx_build == idx_build rm_empty rm_lookup rm_update ls_empty ls_ins ias_iteratei"
lemmas rlis_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded rl_idx_invar_def rlis_idx_build_def]
definition "rrli_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins lsi_iteratei"
lemmas rrli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded rr_idx_invar_def rrli_idx_build_def]
definition "rrl_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins ls_iteratei"
lemmas rrl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded rr_idx_invar_def rrl_idx_build_def]
definition "rrr_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins rs_iteratei"
lemmas rrr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded rr_idx_invar_def rrr_idx_build_def]
definition "rrh_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins hs_iteratei"
lemmas rrh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded rr_idx_invar_def rrh_idx_build_def]
definition "rra_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins ahs_iteratei"
lemmas rra_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded rr_idx_invar_def rra_idx_build_def]
definition "rris_idx_build == idx_build rm_empty rm_lookup rm_update rs_empty rs_ins ias_iteratei"
lemmas rris_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded rr_idx_invar_def rris_idx_build_def]
definition "rhli_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins lsi_iteratei"
lemmas rhli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded rh_idx_invar_def rhli_idx_build_def]
definition "rhl_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins ls_iteratei"
lemmas rhl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded rh_idx_invar_def rhl_idx_build_def]
definition "rhr_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins rs_iteratei"
lemmas rhr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded rh_idx_invar_def rhr_idx_build_def]
definition "rhh_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins hs_iteratei"
lemmas rhh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded rh_idx_invar_def rhh_idx_build_def]
definition "rha_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins ahs_iteratei"
lemmas rha_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded rh_idx_invar_def rha_idx_build_def]
definition "rhis_idx_build == idx_build rm_empty rm_lookup rm_update hs_empty hs_ins ias_iteratei"
lemmas rhis_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded rh_idx_invar_def rhis_idx_build_def]
definition "rali_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins lsi_iteratei"
lemmas rali_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded ra_idx_invar_def rali_idx_build_def]
definition "ral_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins ls_iteratei"
lemmas ral_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded ra_idx_invar_def ral_idx_build_def]
definition "rar_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins rs_iteratei"
lemmas rar_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded ra_idx_invar_def rar_idx_build_def]
definition "rah_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins hs_iteratei"
lemmas rah_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded ra_idx_invar_def rah_idx_build_def]
definition "raa_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins ahs_iteratei"
lemmas raa_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded ra_idx_invar_def raa_idx_build_def]
definition "rais_idx_build == idx_build rm_empty rm_lookup rm_update ahs_empty ahs_ins ias_iteratei"
lemmas rais_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded ra_idx_invar_def rais_idx_build_def]
definition "risli_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins lsi_iteratei"
lemmas risli_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded ris_idx_invar_def risli_idx_build_def]
definition "risl_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins ls_iteratei"
lemmas risl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded ris_idx_invar_def risl_idx_build_def]
definition "risr_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins rs_iteratei"
lemmas risr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded ris_idx_invar_def risr_idx_build_def]
definition "rish_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins hs_iteratei"
lemmas rish_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded ris_idx_invar_def rish_idx_build_def]
definition "risa_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins ahs_iteratei"
lemmas risa_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded ris_idx_invar_def risa_idx_build_def]
definition "risis_idx_build == idx_build rm_empty rm_lookup rm_update ias_empty ias_ins ias_iteratei"
lemmas risis_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded ris_idx_invar_def risis_idx_build_def]
definition "hlili_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins lsi_iteratei"
lemmas hlili_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded hli_idx_invar_def hlili_idx_build_def]
definition "hlil_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins ls_iteratei"
lemmas hlil_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded hli_idx_invar_def hlil_idx_build_def]
definition "hlir_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins rs_iteratei"
lemmas hlir_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded hli_idx_invar_def hlir_idx_build_def]
definition "hlih_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins hs_iteratei"
lemmas hlih_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded hli_idx_invar_def hlih_idx_build_def]
definition "hlia_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins ahs_iteratei"
lemmas hlia_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded hli_idx_invar_def hlia_idx_build_def]
definition "hliis_idx_build == idx_build hm_empty hm_lookup hm_update lsi_empty lsi_ins ias_iteratei"
lemmas hliis_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded hli_idx_invar_def hliis_idx_build_def]
definition "hlli_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins lsi_iteratei"
lemmas hlli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded hl_idx_invar_def hlli_idx_build_def]
definition "hll_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins ls_iteratei"
lemmas hll_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded hl_idx_invar_def hll_idx_build_def]
definition "hlr_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins rs_iteratei"
lemmas hlr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded hl_idx_invar_def hlr_idx_build_def]
definition "hlh_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins hs_iteratei"
lemmas hlh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded hl_idx_invar_def hlh_idx_build_def]
definition "hla_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins ahs_iteratei"
lemmas hla_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded hl_idx_invar_def hla_idx_build_def]
definition "hlis_idx_build == idx_build hm_empty hm_lookup hm_update ls_empty ls_ins ias_iteratei"
lemmas hlis_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded hl_idx_invar_def hlis_idx_build_def]
definition "hrli_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins lsi_iteratei"
lemmas hrli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded hr_idx_invar_def hrli_idx_build_def]
definition "hrl_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins ls_iteratei"
lemmas hrl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded hr_idx_invar_def hrl_idx_build_def]
definition "hrr_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins rs_iteratei"
lemmas hrr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded hr_idx_invar_def hrr_idx_build_def]
definition "hrh_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins hs_iteratei"
lemmas hrh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded hr_idx_invar_def hrh_idx_build_def]
definition "hra_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins ahs_iteratei"
lemmas hra_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded hr_idx_invar_def hra_idx_build_def]
definition "hris_idx_build == idx_build hm_empty hm_lookup hm_update rs_empty rs_ins ias_iteratei"
lemmas hris_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded hr_idx_invar_def hris_idx_build_def]
definition "hhli_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins lsi_iteratei"
lemmas hhli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded hh_idx_invar_def hhli_idx_build_def]
definition "hhl_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins ls_iteratei"
lemmas hhl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded hh_idx_invar_def hhl_idx_build_def]
definition "hhr_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins rs_iteratei"
lemmas hhr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded hh_idx_invar_def hhr_idx_build_def]
definition "hhh_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins hs_iteratei"
lemmas hhh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded hh_idx_invar_def hhh_idx_build_def]
definition "hha_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins ahs_iteratei"
lemmas hha_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded hh_idx_invar_def hha_idx_build_def]
definition "hhis_idx_build == idx_build hm_empty hm_lookup hm_update hs_empty hs_ins ias_iteratei"
lemmas hhis_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded hh_idx_invar_def hhis_idx_build_def]
definition "hali_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins lsi_iteratei"
lemmas hali_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded ha_idx_invar_def hali_idx_build_def]
definition "hal_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins ls_iteratei"
lemmas hal_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded ha_idx_invar_def hal_idx_build_def]
definition "har_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins rs_iteratei"
lemmas har_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded ha_idx_invar_def har_idx_build_def]
definition "hah_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins hs_iteratei"
lemmas hah_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded ha_idx_invar_def hah_idx_build_def]
definition "haa_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins ahs_iteratei"
lemmas haa_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded ha_idx_invar_def haa_idx_build_def]
definition "hais_idx_build == idx_build hm_empty hm_lookup hm_update ahs_empty ahs_ins ias_iteratei"
lemmas hais_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded ha_idx_invar_def hais_idx_build_def]
definition "hisli_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins lsi_iteratei"
lemmas hisli_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded his_idx_invar_def hisli_idx_build_def]
definition "hisl_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins ls_iteratei"
lemmas hisl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded his_idx_invar_def hisl_idx_build_def]
definition "hisr_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins rs_iteratei"
lemmas hisr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded his_idx_invar_def hisr_idx_build_def]
definition "hish_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins hs_iteratei"
lemmas hish_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded his_idx_invar_def hish_idx_build_def]
definition "hisa_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins ahs_iteratei"
lemmas hisa_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded his_idx_invar_def hisa_idx_build_def]
definition "hisis_idx_build == idx_build hm_empty hm_lookup hm_update ias_empty ias_ins ias_iteratei"
lemmas hisis_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded his_idx_invar_def hisis_idx_build_def]
definition "alili_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins lsi_iteratei"
lemmas alili_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded ali_idx_invar_def alili_idx_build_def]
definition "alil_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins ls_iteratei"
lemmas alil_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded ali_idx_invar_def alil_idx_build_def]
definition "alir_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins rs_iteratei"
lemmas alir_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded ali_idx_invar_def alir_idx_build_def]
definition "alih_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins hs_iteratei"
lemmas alih_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded ali_idx_invar_def alih_idx_build_def]
definition "alia_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins ahs_iteratei"
lemmas alia_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded ali_idx_invar_def alia_idx_build_def]
definition "aliis_idx_build == idx_build ahm_empty ahm_lookup ahm_update lsi_empty lsi_ins ias_iteratei"
lemmas aliis_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded ali_idx_invar_def aliis_idx_build_def]
definition "alli_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins lsi_iteratei"
lemmas alli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded al_idx_invar_def alli_idx_build_def]
definition "all_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins ls_iteratei"
lemmas all_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded al_idx_invar_def all_idx_build_def]
definition "alr_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins rs_iteratei"
lemmas alr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded al_idx_invar_def alr_idx_build_def]
definition "alh_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins hs_iteratei"
lemmas alh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded al_idx_invar_def alh_idx_build_def]
definition "ala_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins ahs_iteratei"
lemmas ala_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded al_idx_invar_def ala_idx_build_def]
definition "alis_idx_build == idx_build ahm_empty ahm_lookup ahm_update ls_empty ls_ins ias_iteratei"
lemmas alis_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded al_idx_invar_def alis_idx_build_def]
definition "arli_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins lsi_iteratei"
lemmas arli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded ar_idx_invar_def arli_idx_build_def]
definition "arl_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins ls_iteratei"
lemmas arl_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded ar_idx_invar_def arl_idx_build_def]
definition "arr_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins rs_iteratei"
lemmas arr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded ar_idx_invar_def arr_idx_build_def]
definition "arh_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins hs_iteratei"
lemmas arh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded ar_idx_invar_def arh_idx_build_def]
definition "ara_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins ahs_iteratei"
lemmas ara_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded ar_idx_invar_def ara_idx_build_def]
definition "aris_idx_build == idx_build ahm_empty ahm_lookup ahm_update rs_empty rs_ins ias_iteratei"
lemmas aris_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded ar_idx_invar_def aris_idx_build_def]
definition "ahli_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins lsi_iteratei"
lemmas ahli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded ah_idx_invar_def ahli_idx_build_def]
definition "ahl_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins ls_iteratei"
lemmas ahl_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded ah_idx_invar_def ahl_idx_build_def]
definition "ahr_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins rs_iteratei"
lemmas ahr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded ah_idx_invar_def ahr_idx_build_def]
definition "ahh_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins hs_iteratei"
lemmas ahh_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded ah_idx_invar_def ahh_idx_build_def]
definition "aha_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins ahs_iteratei"
lemmas aha_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded ah_idx_invar_def aha_idx_build_def]
definition "ahis_idx_build == idx_build ahm_empty ahm_lookup ahm_update hs_empty hs_ins ias_iteratei"
lemmas ahis_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded ah_idx_invar_def ahis_idx_build_def]
definition "aali_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins lsi_iteratei"
lemmas aali_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded aa_idx_invar_def aali_idx_build_def]
definition "aal_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins ls_iteratei"
lemmas aal_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded aa_idx_invar_def aal_idx_build_def]
definition "aar_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins rs_iteratei"
lemmas aar_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded aa_idx_invar_def aar_idx_build_def]
definition "aah_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins hs_iteratei"
lemmas aah_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded aa_idx_invar_def aah_idx_build_def]
definition "aaa_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins ahs_iteratei"
lemmas aaa_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded aa_idx_invar_def aaa_idx_build_def]
definition "aais_idx_build == idx_build ahm_empty ahm_lookup ahm_update ahs_empty ahs_ins ias_iteratei"
lemmas aais_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded aa_idx_invar_def aais_idx_build_def]
definition "aisli_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins lsi_iteratei"
lemmas aisli_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded ais_idx_invar_def aisli_idx_build_def]
definition "aisl_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins ls_iteratei"
lemmas aisl_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded ais_idx_invar_def aisl_idx_build_def]
definition "aisr_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins rs_iteratei"
lemmas aisr_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded ais_idx_invar_def aisr_idx_build_def]
definition "aish_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins hs_iteratei"
lemmas aish_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded ais_idx_invar_def aish_idx_build_def]
definition "aisa_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins ahs_iteratei"
lemmas aisa_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded ais_idx_invar_def aisa_idx_build_def]
definition "aisis_idx_build == idx_build ahm_empty ahm_lookup ahm_update ias_empty ias_ins ias_iteratei"
lemmas aisis_idx_build_correct = idx_build_correct[OF ahm_empty_impl ahm_lookup_impl ahm_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded ais_idx_invar_def aisis_idx_build_def]
definition "imlili_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins lsi_iteratei"
lemmas imlili_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl lsi_iteratei_impl,
  folded imli_idx_invar_def imlili_idx_build_def]
definition "imlil_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins ls_iteratei"
lemmas imlil_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl ls_iteratei_impl,
  folded imli_idx_invar_def imlil_idx_build_def]
definition "imlir_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins rs_iteratei"
lemmas imlir_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl rs_iteratei_impl,
  folded imli_idx_invar_def imlir_idx_build_def]
definition "imlih_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins hs_iteratei"
lemmas imlih_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl hs_iteratei_impl,
  folded imli_idx_invar_def imlih_idx_build_def]
definition "imlia_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins ahs_iteratei"
lemmas imlia_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl ahs_iteratei_impl,
  folded imli_idx_invar_def imlia_idx_build_def]
definition "imliis_idx_build == idx_build iam_empty iam_lookup iam_update lsi_empty lsi_ins ias_iteratei"
lemmas imliis_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl lsi_empty_impl lsi_ins_impl ias_iteratei_impl,
  folded imli_idx_invar_def imliis_idx_build_def]
definition "imlli_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins lsi_iteratei"
lemmas imlli_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl lsi_iteratei_impl,
  folded iml_idx_invar_def imlli_idx_build_def]
definition "imll_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins ls_iteratei"
lemmas imll_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl ls_iteratei_impl,
  folded iml_idx_invar_def imll_idx_build_def]
definition "imlr_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins rs_iteratei"
lemmas imlr_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl rs_iteratei_impl,
  folded iml_idx_invar_def imlr_idx_build_def]
definition "imlh_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins hs_iteratei"
lemmas imlh_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl hs_iteratei_impl,
  folded iml_idx_invar_def imlh_idx_build_def]
definition "imla_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins ahs_iteratei"
lemmas imla_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl ahs_iteratei_impl,
  folded iml_idx_invar_def imla_idx_build_def]
definition "imlis_idx_build == idx_build iam_empty iam_lookup iam_update ls_empty ls_ins ias_iteratei"
lemmas imlis_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ls_empty_impl ls_ins_impl ias_iteratei_impl,
  folded iml_idx_invar_def imlis_idx_build_def]
definition "imrli_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins lsi_iteratei"
lemmas imrli_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl lsi_iteratei_impl,
  folded imr_idx_invar_def imrli_idx_build_def]
definition "imrl_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins ls_iteratei"
lemmas imrl_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl ls_iteratei_impl,
  folded imr_idx_invar_def imrl_idx_build_def]
definition "imrr_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins rs_iteratei"
lemmas imrr_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl rs_iteratei_impl,
  folded imr_idx_invar_def imrr_idx_build_def]
definition "imrh_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins hs_iteratei"
lemmas imrh_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl hs_iteratei_impl,
  folded imr_idx_invar_def imrh_idx_build_def]
definition "imra_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins ahs_iteratei"
lemmas imra_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl ahs_iteratei_impl,
  folded imr_idx_invar_def imra_idx_build_def]
definition "imris_idx_build == idx_build iam_empty iam_lookup iam_update rs_empty rs_ins ias_iteratei"
lemmas imris_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl rs_empty_impl rs_ins_impl ias_iteratei_impl,
  folded imr_idx_invar_def imris_idx_build_def]
definition "imhli_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins lsi_iteratei"
lemmas imhli_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl lsi_iteratei_impl,
  folded imh_idx_invar_def imhli_idx_build_def]
definition "imhl_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins ls_iteratei"
lemmas imhl_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl ls_iteratei_impl,
  folded imh_idx_invar_def imhl_idx_build_def]
definition "imhr_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins rs_iteratei"
lemmas imhr_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl rs_iteratei_impl,
  folded imh_idx_invar_def imhr_idx_build_def]
definition "imhh_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins hs_iteratei"
lemmas imhh_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl hs_iteratei_impl,
  folded imh_idx_invar_def imhh_idx_build_def]
definition "imha_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins ahs_iteratei"
lemmas imha_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl ahs_iteratei_impl,
  folded imh_idx_invar_def imha_idx_build_def]
definition "imhis_idx_build == idx_build iam_empty iam_lookup iam_update hs_empty hs_ins ias_iteratei"
lemmas imhis_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl hs_empty_impl hs_ins_impl ias_iteratei_impl,
  folded imh_idx_invar_def imhis_idx_build_def]
definition "imali_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins lsi_iteratei"
lemmas imali_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl lsi_iteratei_impl,
  folded ima_idx_invar_def imali_idx_build_def]
definition "imal_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins ls_iteratei"
lemmas imal_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl ls_iteratei_impl,
  folded ima_idx_invar_def imal_idx_build_def]
definition "imar_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins rs_iteratei"
lemmas imar_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl rs_iteratei_impl,
  folded ima_idx_invar_def imar_idx_build_def]
definition "imah_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins hs_iteratei"
lemmas imah_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl hs_iteratei_impl,
  folded ima_idx_invar_def imah_idx_build_def]
definition "imaa_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins ahs_iteratei"
lemmas imaa_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl ahs_iteratei_impl,
  folded ima_idx_invar_def imaa_idx_build_def]
definition "imais_idx_build == idx_build iam_empty iam_lookup iam_update ahs_empty ahs_ins ias_iteratei"
lemmas imais_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ahs_empty_impl ahs_ins_impl ias_iteratei_impl,
  folded ima_idx_invar_def imais_idx_build_def]
definition "imisli_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins lsi_iteratei"
lemmas imisli_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl lsi_iteratei_impl,
  folded imis_idx_invar_def imisli_idx_build_def]
definition "imisl_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins ls_iteratei"
lemmas imisl_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl ls_iteratei_impl,
  folded imis_idx_invar_def imisl_idx_build_def]
definition "imisr_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins rs_iteratei"
lemmas imisr_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl rs_iteratei_impl,
  folded imis_idx_invar_def imisr_idx_build_def]
definition "imish_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins hs_iteratei"
lemmas imish_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl hs_iteratei_impl,
  folded imis_idx_invar_def imish_idx_build_def]
definition "imisa_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins ahs_iteratei"
lemmas imisa_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl ahs_iteratei_impl,
  folded imis_idx_invar_def imisa_idx_build_def]
definition "imisis_idx_build == idx_build iam_empty iam_lookup iam_update ias_empty ias_ins ias_iteratei"
lemmas imisis_idx_build_correct = idx_build_correct[OF iam_empty_impl iam_lookup_impl iam_update_impl ias_empty_impl ias_ins_impl ias_iteratei_impl,
  folded imis_idx_invar_def imisis_idx_build_def]
(*#end_generated*)

end
