(* Generated file *)
(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Standard Instantiations *}
theory StdInst
imports MapStdImpl SetStdImpl HashMap HashSet SetIndex Algos
begin
text_raw {*\label{thy:StdInst}*}
(* We use a small ad-hoc hack to generate the actual instantiations from this file: *)

text {*
  This theory provides standard instantiations of some abstract algorithms
  for rb-trees, lists and hashsets/maps.
*}




(*#begin_generated*)

  definition "lll_union == it_union ls_iterate ls_ins"
  lemmas lll_union_impl = it_union_correct[OF ls_iterate_impl ls_ins_impl, folded lll_union_def]
  interpretation lll: set_union ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union using lll_union_impl .
  definition "lrr_union == it_union ls_iterate rs_ins"
  lemmas lrr_union_impl = it_union_correct[OF ls_iterate_impl rs_ins_impl, folded lrr_union_def]
  interpretation lrr: set_union ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union using lrr_union_impl .
  definition "lhh_union == it_union ls_iterate hs_ins"
  lemmas lhh_union_impl = it_union_correct[OF ls_iterate_impl hs_ins_impl, folded lhh_union_def]
  interpretation lhh: set_union ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union using lhh_union_impl .
  definition "rll_union == it_union rs_iterate ls_ins"
  lemmas rll_union_impl = it_union_correct[OF rs_iterate_impl ls_ins_impl, folded rll_union_def]
  interpretation rll: set_union rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union using rll_union_impl .
  definition "rrr_union == it_union rs_iterate rs_ins"
  lemmas rrr_union_impl = it_union_correct[OF rs_iterate_impl rs_ins_impl, folded rrr_union_def]
  interpretation rrr: set_union rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union using rrr_union_impl .
  definition "rhh_union == it_union rs_iterate hs_ins"
  lemmas rhh_union_impl = it_union_correct[OF rs_iterate_impl hs_ins_impl, folded rhh_union_def]
  interpretation rhh: set_union rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union using rhh_union_impl .
  definition "hll_union == it_union hs_iterate ls_ins"
  lemmas hll_union_impl = it_union_correct[OF hs_iterate_impl ls_ins_impl, folded hll_union_def]
  interpretation hll: set_union hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union using hll_union_impl .
  definition "hrr_union == it_union hs_iterate rs_ins"
  lemmas hrr_union_impl = it_union_correct[OF hs_iterate_impl rs_ins_impl, folded hrr_union_def]
  interpretation hrr: set_union hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union using hrr_union_impl .
  definition "hhh_union == it_union hs_iterate hs_ins"
  lemmas hhh_union_impl = it_union_correct[OF hs_iterate_impl hs_ins_impl, folded hhh_union_def]
  interpretation hhh: set_union hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union using hhh_union_impl .

  definition "lll_union_dj == it_union_dj ls_iterate ls_ins_dj"
  lemmas lll_union_dj_impl = it_union_dj_correct[OF ls_iterate_impl ls_ins_dj_impl, folded lll_union_dj_def]
  interpretation lll: set_union_dj ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_union_dj using lll_union_dj_impl .
  definition "lrr_union_dj == it_union_dj ls_iterate rs_ins_dj"
  lemmas lrr_union_dj_impl = it_union_dj_correct[OF ls_iterate_impl rs_ins_dj_impl, folded lrr_union_dj_def]
  interpretation lrr: set_union_dj ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_union_dj using lrr_union_dj_impl .
  definition "lhh_union_dj == it_union_dj ls_iterate hs_ins_dj"
  lemmas lhh_union_dj_impl = it_union_dj_correct[OF ls_iterate_impl hs_ins_dj_impl, folded lhh_union_dj_def]
  interpretation lhh: set_union_dj ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_union_dj using lhh_union_dj_impl .
  definition "rll_union_dj == it_union_dj rs_iterate ls_ins_dj"
  lemmas rll_union_dj_impl = it_union_dj_correct[OF rs_iterate_impl ls_ins_dj_impl, folded rll_union_dj_def]
  interpretation rll: set_union_dj rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_union_dj using rll_union_dj_impl .
  definition "rrr_union_dj == it_union_dj rs_iterate rs_ins_dj"
  lemmas rrr_union_dj_impl = it_union_dj_correct[OF rs_iterate_impl rs_ins_dj_impl, folded rrr_union_dj_def]
  interpretation rrr: set_union_dj rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_union_dj using rrr_union_dj_impl .
  definition "rhh_union_dj == it_union_dj rs_iterate hs_ins_dj"
  lemmas rhh_union_dj_impl = it_union_dj_correct[OF rs_iterate_impl hs_ins_dj_impl, folded rhh_union_dj_def]
  interpretation rhh: set_union_dj rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_union_dj using rhh_union_dj_impl .
  definition "hll_union_dj == it_union_dj hs_iterate ls_ins_dj"
  lemmas hll_union_dj_impl = it_union_dj_correct[OF hs_iterate_impl ls_ins_dj_impl, folded hll_union_dj_def]
  interpretation hll: set_union_dj hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_union_dj using hll_union_dj_impl .
  definition "hrr_union_dj == it_union_dj hs_iterate rs_ins_dj"
  lemmas hrr_union_dj_impl = it_union_dj_correct[OF hs_iterate_impl rs_ins_dj_impl, folded hrr_union_dj_def]
  interpretation hrr: set_union_dj hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_union_dj using hrr_union_dj_impl .
  definition "hhh_union_dj == it_union_dj hs_iterate hs_ins_dj"
  lemmas hhh_union_dj_impl = it_union_dj_correct[OF hs_iterate_impl hs_ins_dj_impl, folded hhh_union_dj_def]
  interpretation hhh: set_union_dj hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_union_dj using hhh_union_dj_impl .

  definition "lll_inter == it_inter ls_iterate ls_memb ls_empty ls_ins_dj"
  lemmas lll_inter_impl = it_inter_correct[OF ls_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded lll_inter_def]
  interpretation lll: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_inter using lll_inter_impl .
  definition "llr_inter == it_inter ls_iterate ls_memb rs_empty rs_ins_dj"
  lemmas llr_inter_impl = it_inter_correct[OF ls_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded llr_inter_def]
  interpretation llr: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_inter using llr_inter_impl .
  definition "llh_inter == it_inter ls_iterate ls_memb hs_empty hs_ins_dj"
  lemmas llh_inter_impl = it_inter_correct[OF ls_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded llh_inter_def]
  interpretation llh: set_inter ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_inter using llh_inter_impl .
  definition "lrl_inter == it_inter ls_iterate rs_memb ls_empty ls_ins_dj"
  lemmas lrl_inter_impl = it_inter_correct[OF ls_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inter_def]
  interpretation lrl: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_inter using lrl_inter_impl .
  definition "lrr_inter == it_inter ls_iterate rs_memb rs_empty rs_ins_dj"
  lemmas lrr_inter_impl = it_inter_correct[OF ls_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inter_def]
  interpretation lrr: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_inter using lrr_inter_impl .
  definition "lrh_inter == it_inter ls_iterate rs_memb hs_empty hs_ins_dj"
  lemmas lrh_inter_impl = it_inter_correct[OF ls_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inter_def]
  interpretation lrh: set_inter ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_inter using lrh_inter_impl .
  definition "lhl_inter == it_inter ls_iterate hs_memb ls_empty ls_ins_dj"
  lemmas lhl_inter_impl = it_inter_correct[OF ls_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inter_def]
  interpretation lhl: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_inter using lhl_inter_impl .
  definition "lhr_inter == it_inter ls_iterate hs_memb rs_empty rs_ins_dj"
  lemmas lhr_inter_impl = it_inter_correct[OF ls_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inter_def]
  interpretation lhr: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_inter using lhr_inter_impl .
  definition "lhh_inter == it_inter ls_iterate hs_memb hs_empty hs_ins_dj"
  lemmas lhh_inter_impl = it_inter_correct[OF ls_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inter_def]
  interpretation lhh: set_inter ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_inter using lhh_inter_impl .
  definition "rll_inter == it_inter rs_iterate ls_memb ls_empty ls_ins_dj"
  lemmas rll_inter_impl = it_inter_correct[OF rs_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded rll_inter_def]
  interpretation rll: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_inter using rll_inter_impl .
  definition "rlr_inter == it_inter rs_iterate ls_memb rs_empty rs_ins_dj"
  lemmas rlr_inter_impl = it_inter_correct[OF rs_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inter_def]
  interpretation rlr: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_inter using rlr_inter_impl .
  definition "rlh_inter == it_inter rs_iterate ls_memb hs_empty hs_ins_dj"
  lemmas rlh_inter_impl = it_inter_correct[OF rs_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inter_def]
  interpretation rlh: set_inter rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_inter using rlh_inter_impl .
  definition "rrl_inter == it_inter rs_iterate rs_memb ls_empty ls_ins_dj"
  lemmas rrl_inter_impl = it_inter_correct[OF rs_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inter_def]
  interpretation rrl: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_inter using rrl_inter_impl .
  definition "rrr_inter == it_inter rs_iterate rs_memb rs_empty rs_ins_dj"
  lemmas rrr_inter_impl = it_inter_correct[OF rs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inter_def]
  interpretation rrr: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_inter using rrr_inter_impl .
  definition "rrh_inter == it_inter rs_iterate rs_memb hs_empty hs_ins_dj"
  lemmas rrh_inter_impl = it_inter_correct[OF rs_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inter_def]
  interpretation rrh: set_inter rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_inter using rrh_inter_impl .
  definition "rhl_inter == it_inter rs_iterate hs_memb ls_empty ls_ins_dj"
  lemmas rhl_inter_impl = it_inter_correct[OF rs_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inter_def]
  interpretation rhl: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_inter using rhl_inter_impl .
  definition "rhr_inter == it_inter rs_iterate hs_memb rs_empty rs_ins_dj"
  lemmas rhr_inter_impl = it_inter_correct[OF rs_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inter_def]
  interpretation rhr: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_inter using rhr_inter_impl .
  definition "rhh_inter == it_inter rs_iterate hs_memb hs_empty hs_ins_dj"
  lemmas rhh_inter_impl = it_inter_correct[OF rs_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inter_def]
  interpretation rhh: set_inter rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_inter using rhh_inter_impl .
  definition "hll_inter == it_inter hs_iterate ls_memb ls_empty ls_ins_dj"
  lemmas hll_inter_impl = it_inter_correct[OF hs_iterate_impl ls_memb_impl ls_empty_impl ls_ins_dj_impl, folded hll_inter_def]
  interpretation hll: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_inter using hll_inter_impl .
  definition "hlr_inter == it_inter hs_iterate ls_memb rs_empty rs_ins_dj"
  lemmas hlr_inter_impl = it_inter_correct[OF hs_iterate_impl ls_memb_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inter_def]
  interpretation hlr: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_inter using hlr_inter_impl .
  definition "hlh_inter == it_inter hs_iterate ls_memb hs_empty hs_ins_dj"
  lemmas hlh_inter_impl = it_inter_correct[OF hs_iterate_impl ls_memb_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inter_def]
  interpretation hlh: set_inter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_inter using hlh_inter_impl .
  definition "hrl_inter == it_inter hs_iterate rs_memb ls_empty ls_ins_dj"
  lemmas hrl_inter_impl = it_inter_correct[OF hs_iterate_impl rs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inter_def]
  interpretation hrl: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_inter using hrl_inter_impl .
  definition "hrr_inter == it_inter hs_iterate rs_memb rs_empty rs_ins_dj"
  lemmas hrr_inter_impl = it_inter_correct[OF hs_iterate_impl rs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inter_def]
  interpretation hrr: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_inter using hrr_inter_impl .
  definition "hrh_inter == it_inter hs_iterate rs_memb hs_empty hs_ins_dj"
  lemmas hrh_inter_impl = it_inter_correct[OF hs_iterate_impl rs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inter_def]
  interpretation hrh: set_inter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_inter using hrh_inter_impl .
  definition "hhl_inter == it_inter hs_iterate hs_memb ls_empty ls_ins_dj"
  lemmas hhl_inter_impl = it_inter_correct[OF hs_iterate_impl hs_memb_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inter_def]
  interpretation hhl: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_inter using hhl_inter_impl .
  definition "hhr_inter == it_inter hs_iterate hs_memb rs_empty rs_ins_dj"
  lemmas hhr_inter_impl = it_inter_correct[OF hs_iterate_impl hs_memb_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inter_def]
  interpretation hhr: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_inter using hhr_inter_impl .
  definition "hhh_inter == it_inter hs_iterate hs_memb hs_empty hs_ins_dj"
  lemmas hhh_inter_impl = it_inter_correct[OF hs_iterate_impl hs_memb_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inter_def]
  interpretation hhh: set_inter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_inter using hhh_inter_impl .

  definition "ll_subset == ball_subset ls_ball ls_memb"
  lemmas ll_subset_impl = ball_subset_correct[OF ls_ball_impl ls_memb_impl, folded ll_subset_def]
  interpretation ll: set_subset ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_subset using ll_subset_impl .
  definition "lr_subset == ball_subset ls_ball rs_memb"
  lemmas lr_subset_impl = ball_subset_correct[OF ls_ball_impl rs_memb_impl, folded lr_subset_def]
  interpretation lr: set_subset ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_subset using lr_subset_impl .
  definition "lh_subset == ball_subset ls_ball hs_memb"
  lemmas lh_subset_impl = ball_subset_correct[OF ls_ball_impl hs_memb_impl, folded lh_subset_def]
  interpretation lh: set_subset ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_subset using lh_subset_impl .
  definition "rl_subset == ball_subset rs_ball ls_memb"
  lemmas rl_subset_impl = ball_subset_correct[OF rs_ball_impl ls_memb_impl, folded rl_subset_def]
  interpretation rl: set_subset rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_subset using rl_subset_impl .
  definition "rr_subset == ball_subset rs_ball rs_memb"
  lemmas rr_subset_impl = ball_subset_correct[OF rs_ball_impl rs_memb_impl, folded rr_subset_def]
  interpretation rr: set_subset rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_subset using rr_subset_impl .
  definition "rh_subset == ball_subset rs_ball hs_memb"
  lemmas rh_subset_impl = ball_subset_correct[OF rs_ball_impl hs_memb_impl, folded rh_subset_def]
  interpretation rh: set_subset rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_subset using rh_subset_impl .
  definition "hl_subset == ball_subset hs_ball ls_memb"
  lemmas hl_subset_impl = ball_subset_correct[OF hs_ball_impl ls_memb_impl, folded hl_subset_def]
  interpretation hl: set_subset hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_subset using hl_subset_impl .
  definition "hr_subset == ball_subset hs_ball rs_memb"
  lemmas hr_subset_impl = ball_subset_correct[OF hs_ball_impl rs_memb_impl, folded hr_subset_def]
  interpretation hr: set_subset hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_subset using hr_subset_impl .
  definition "hh_subset == ball_subset hs_ball hs_memb"
  lemmas hh_subset_impl = ball_subset_correct[OF hs_ball_impl hs_memb_impl, folded hh_subset_def]
  interpretation hh: set_subset hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_subset using hh_subset_impl .

  definition "ll_equal == subset_equal ll_subset ll_subset"
  lemmas ll_equal_impl = subset_equal_correct[OF ll_subset_impl ll_subset_impl, folded ll_equal_def]
  interpretation ll: set_equal ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_equal using ll_equal_impl .
  definition "lr_equal == subset_equal lr_subset rl_subset"
  lemmas lr_equal_impl = subset_equal_correct[OF lr_subset_impl rl_subset_impl, folded lr_equal_def]
  interpretation lr: set_equal ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_equal using lr_equal_impl .
  definition "lh_equal == subset_equal lh_subset hl_subset"
  lemmas lh_equal_impl = subset_equal_correct[OF lh_subset_impl hl_subset_impl, folded lh_equal_def]
  interpretation lh: set_equal ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_equal using lh_equal_impl .
  definition "rl_equal == subset_equal rl_subset lr_subset"
  lemmas rl_equal_impl = subset_equal_correct[OF rl_subset_impl lr_subset_impl, folded rl_equal_def]
  interpretation rl: set_equal rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_equal using rl_equal_impl .
  definition "rr_equal == subset_equal rr_subset rr_subset"
  lemmas rr_equal_impl = subset_equal_correct[OF rr_subset_impl rr_subset_impl, folded rr_equal_def]
  interpretation rr: set_equal rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_equal using rr_equal_impl .
  definition "rh_equal == subset_equal rh_subset hr_subset"
  lemmas rh_equal_impl = subset_equal_correct[OF rh_subset_impl hr_subset_impl, folded rh_equal_def]
  interpretation rh: set_equal rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_equal using rh_equal_impl .
  definition "hl_equal == subset_equal hl_subset lh_subset"
  lemmas hl_equal_impl = subset_equal_correct[OF hl_subset_impl lh_subset_impl, folded hl_equal_def]
  interpretation hl: set_equal hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_equal using hl_equal_impl .
  definition "hr_equal == subset_equal hr_subset rh_subset"
  lemmas hr_equal_impl = subset_equal_correct[OF hr_subset_impl rh_subset_impl, folded hr_equal_def]
  interpretation hr: set_equal hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_equal using hr_equal_impl .
  definition "hh_equal == subset_equal hh_subset hh_subset"
  lemmas hh_equal_impl = subset_equal_correct[OF hh_subset_impl hh_subset_impl, folded hh_equal_def]
  interpretation hh: set_equal hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_equal using hh_equal_impl .

  definition "ll_image_filter == it_image_filter ls_iterate ls_empty ls_ins"
  lemmas ll_image_filter_impl = it_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_impl, folded ll_image_filter_def]
  interpretation ll: set_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_image_filter using ll_image_filter_impl .
  definition "lr_image_filter == it_image_filter ls_iterate rs_empty rs_ins"
  lemmas lr_image_filter_impl = it_image_filter_correct[OF ls_iterate_impl rs_empty_impl rs_ins_impl, folded lr_image_filter_def]
  interpretation lr: set_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_image_filter using lr_image_filter_impl .
  definition "lh_image_filter == it_image_filter ls_iterate hs_empty hs_ins"
  lemmas lh_image_filter_impl = it_image_filter_correct[OF ls_iterate_impl hs_empty_impl hs_ins_impl, folded lh_image_filter_def]
  interpretation lh: set_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_image_filter using lh_image_filter_impl .
  definition "rl_image_filter == it_image_filter rs_iterate ls_empty ls_ins"
  lemmas rl_image_filter_impl = it_image_filter_correct[OF rs_iterate_impl ls_empty_impl ls_ins_impl, folded rl_image_filter_def]
  interpretation rl: set_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_image_filter using rl_image_filter_impl .
  definition "rr_image_filter == it_image_filter rs_iterate rs_empty rs_ins"
  lemmas rr_image_filter_impl = it_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_impl, folded rr_image_filter_def]
  interpretation rr: set_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_image_filter using rr_image_filter_impl .
  definition "rh_image_filter == it_image_filter rs_iterate hs_empty hs_ins"
  lemmas rh_image_filter_impl = it_image_filter_correct[OF rs_iterate_impl hs_empty_impl hs_ins_impl, folded rh_image_filter_def]
  interpretation rh: set_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_image_filter using rh_image_filter_impl .
  definition "hl_image_filter == it_image_filter hs_iterate ls_empty ls_ins"
  lemmas hl_image_filter_impl = it_image_filter_correct[OF hs_iterate_impl ls_empty_impl ls_ins_impl, folded hl_image_filter_def]
  interpretation hl: set_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_image_filter using hl_image_filter_impl .
  definition "hr_image_filter == it_image_filter hs_iterate rs_empty rs_ins"
  lemmas hr_image_filter_impl = it_image_filter_correct[OF hs_iterate_impl rs_empty_impl rs_ins_impl, folded hr_image_filter_def]
  interpretation hr: set_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_image_filter using hr_image_filter_impl .
  definition "hh_image_filter == it_image_filter hs_iterate hs_empty hs_ins"
  lemmas hh_image_filter_impl = it_image_filter_correct[OF hs_iterate_impl hs_empty_impl hs_ins_impl, folded hh_image_filter_def]
  interpretation hh: set_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_image_filter using hh_image_filter_impl .

  definition "ll_inj_image_filter == it_inj_image_filter ls_iterate ls_empty ls_ins_dj"
  lemmas ll_inj_image_filter_impl = it_inj_image_filter_correct[OF ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded ll_inj_image_filter_def]
  interpretation ll: set_inj_image_filter ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_inj_image_filter using ll_inj_image_filter_impl .
  definition "lr_inj_image_filter == it_inj_image_filter ls_iterate rs_empty rs_ins_dj"
  lemmas lr_inj_image_filter_impl = it_inj_image_filter_correct[OF ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lr_inj_image_filter_def]
  interpretation lr: set_inj_image_filter ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_inj_image_filter using lr_inj_image_filter_impl .
  definition "lh_inj_image_filter == it_inj_image_filter ls_iterate hs_empty hs_ins_dj"
  lemmas lh_inj_image_filter_impl = it_inj_image_filter_correct[OF ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lh_inj_image_filter_def]
  interpretation lh: set_inj_image_filter ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_inj_image_filter using lh_inj_image_filter_impl .
  definition "rl_inj_image_filter == it_inj_image_filter rs_iterate ls_empty ls_ins_dj"
  lemmas rl_inj_image_filter_impl = it_inj_image_filter_correct[OF rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rl_inj_image_filter_def]
  interpretation rl: set_inj_image_filter rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_inj_image_filter using rl_inj_image_filter_impl .
  definition "rr_inj_image_filter == it_inj_image_filter rs_iterate rs_empty rs_ins_dj"
  lemmas rr_inj_image_filter_impl = it_inj_image_filter_correct[OF rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rr_inj_image_filter_def]
  interpretation rr: set_inj_image_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_inj_image_filter using rr_inj_image_filter_impl .
  definition "rh_inj_image_filter == it_inj_image_filter rs_iterate hs_empty hs_ins_dj"
  lemmas rh_inj_image_filter_impl = it_inj_image_filter_correct[OF rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rh_inj_image_filter_def]
  interpretation rh: set_inj_image_filter rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_inj_image_filter using rh_inj_image_filter_impl .
  definition "hl_inj_image_filter == it_inj_image_filter hs_iterate ls_empty ls_ins_dj"
  lemmas hl_inj_image_filter_impl = it_inj_image_filter_correct[OF hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hl_inj_image_filter_def]
  interpretation hl: set_inj_image_filter hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_inj_image_filter using hl_inj_image_filter_impl .
  definition "hr_inj_image_filter == it_inj_image_filter hs_iterate rs_empty rs_ins_dj"
  lemmas hr_inj_image_filter_impl = it_inj_image_filter_correct[OF hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hr_inj_image_filter_def]
  interpretation hr: set_inj_image_filter hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_inj_image_filter using hr_inj_image_filter_impl .
  definition "hh_inj_image_filter == it_inj_image_filter hs_iterate hs_empty hs_ins_dj"
  lemmas hh_inj_image_filter_impl = it_inj_image_filter_correct[OF hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hh_inj_image_filter_def]
  interpretation hh: set_inj_image_filter hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_inj_image_filter using hh_inj_image_filter_impl .

  definition "ll_image == iflt_image ll_image_filter"
  lemmas ll_image_impl = iflt_image_correct[OF ll_image_filter_impl, folded ll_image_def]
  interpretation ll: set_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_image using ll_image_impl .
  definition "lr_image == iflt_image lr_image_filter"
  lemmas lr_image_impl = iflt_image_correct[OF lr_image_filter_impl, folded lr_image_def]
  interpretation lr: set_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_image using lr_image_impl .
  definition "lh_image == iflt_image lh_image_filter"
  lemmas lh_image_impl = iflt_image_correct[OF lh_image_filter_impl, folded lh_image_def]
  interpretation lh: set_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_image using lh_image_impl .
  definition "rl_image == iflt_image rl_image_filter"
  lemmas rl_image_impl = iflt_image_correct[OF rl_image_filter_impl, folded rl_image_def]
  interpretation rl: set_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_image using rl_image_impl .
  definition "rr_image == iflt_image rr_image_filter"
  lemmas rr_image_impl = iflt_image_correct[OF rr_image_filter_impl, folded rr_image_def]
  interpretation rr: set_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_image using rr_image_impl .
  definition "rh_image == iflt_image rh_image_filter"
  lemmas rh_image_impl = iflt_image_correct[OF rh_image_filter_impl, folded rh_image_def]
  interpretation rh: set_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_image using rh_image_impl .
  definition "hl_image == iflt_image hl_image_filter"
  lemmas hl_image_impl = iflt_image_correct[OF hl_image_filter_impl, folded hl_image_def]
  interpretation hl: set_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_image using hl_image_impl .
  definition "hr_image == iflt_image hr_image_filter"
  lemmas hr_image_impl = iflt_image_correct[OF hr_image_filter_impl, folded hr_image_def]
  interpretation hr: set_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_image using hr_image_impl .
  definition "hh_image == iflt_image hh_image_filter"
  lemmas hh_image_impl = iflt_image_correct[OF hh_image_filter_impl, folded hh_image_def]
  interpretation hh: set_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_image using hh_image_impl .

  definition "ll_inj_image == iflt_inj_image ll_inj_image_filter"
  lemmas ll_inj_image_impl = iflt_inj_image_correct[OF ll_inj_image_filter_impl, folded ll_inj_image_def]
  interpretation ll: set_inj_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_inj_image using ll_inj_image_impl .
  definition "lr_inj_image == iflt_inj_image lr_inj_image_filter"
  lemmas lr_inj_image_impl = iflt_inj_image_correct[OF lr_inj_image_filter_impl, folded lr_inj_image_def]
  interpretation lr: set_inj_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_inj_image using lr_inj_image_impl .
  definition "lh_inj_image == iflt_inj_image lh_inj_image_filter"
  lemmas lh_inj_image_impl = iflt_inj_image_correct[OF lh_inj_image_filter_impl, folded lh_inj_image_def]
  interpretation lh: set_inj_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_inj_image using lh_inj_image_impl .
  definition "rl_inj_image == iflt_inj_image rl_inj_image_filter"
  lemmas rl_inj_image_impl = iflt_inj_image_correct[OF rl_inj_image_filter_impl, folded rl_inj_image_def]
  interpretation rl: set_inj_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_inj_image using rl_inj_image_impl .
  definition "rr_inj_image == iflt_inj_image rr_inj_image_filter"
  lemmas rr_inj_image_impl = iflt_inj_image_correct[OF rr_inj_image_filter_impl, folded rr_inj_image_def]
  interpretation rr: set_inj_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_inj_image using rr_inj_image_impl .
  definition "rh_inj_image == iflt_inj_image rh_inj_image_filter"
  lemmas rh_inj_image_impl = iflt_inj_image_correct[OF rh_inj_image_filter_impl, folded rh_inj_image_def]
  interpretation rh: set_inj_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_inj_image using rh_inj_image_impl .
  definition "hl_inj_image == iflt_inj_image hl_inj_image_filter"
  lemmas hl_inj_image_impl = iflt_inj_image_correct[OF hl_inj_image_filter_impl, folded hl_inj_image_def]
  interpretation hl: set_inj_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_inj_image using hl_inj_image_impl .
  definition "hr_inj_image == iflt_inj_image hr_inj_image_filter"
  lemmas hr_inj_image_impl = iflt_inj_image_correct[OF hr_inj_image_filter_impl, folded hr_inj_image_def]
  interpretation hr: set_inj_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_inj_image using hr_inj_image_impl .
  definition "hh_inj_image == iflt_inj_image hh_inj_image_filter"
  lemmas hh_inj_image_impl = iflt_inj_image_correct[OF hh_inj_image_filter_impl, folded hh_inj_image_def]
  interpretation hh: set_inj_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_inj_image using hh_inj_image_impl .

  definition "lll_Union_image == it_Union_image ls_iterate ls_empty lll_union"
  lemmas lll_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl ls_empty_impl lll_union_impl, folded lll_Union_image_def]
  interpretation lll: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar lll_Union_image using lll_Union_image_impl .
  definition "llr_Union_image == it_Union_image ls_iterate rs_empty lrr_union"
  lemmas llr_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl rs_empty_impl lrr_union_impl, folded llr_Union_image_def]
  interpretation llr: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar llr_Union_image using llr_Union_image_impl .
  definition "llh_Union_image == it_Union_image ls_iterate hs_empty lhh_union"
  lemmas llh_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl hs_empty_impl lhh_union_impl, folded llh_Union_image_def]
  interpretation llh: set_Union_image ls_\<alpha> ls_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar llh_Union_image using llh_Union_image_impl .
  definition "lrl_Union_image == it_Union_image ls_iterate ls_empty rll_union"
  lemmas lrl_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl ls_empty_impl rll_union_impl, folded lrl_Union_image_def]
  interpretation lrl: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar lrl_Union_image using lrl_Union_image_impl .
  definition "lrr_Union_image == it_Union_image ls_iterate rs_empty rrr_union"
  lemmas lrr_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl rs_empty_impl rrr_union_impl, folded lrr_Union_image_def]
  interpretation lrr: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar lrr_Union_image using lrr_Union_image_impl .
  definition "lrh_Union_image == it_Union_image ls_iterate hs_empty rhh_union"
  lemmas lrh_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl hs_empty_impl rhh_union_impl, folded lrh_Union_image_def]
  interpretation lrh: set_Union_image ls_\<alpha> ls_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar lrh_Union_image using lrh_Union_image_impl .
  definition "lhl_Union_image == it_Union_image ls_iterate ls_empty hll_union"
  lemmas lhl_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl ls_empty_impl hll_union_impl, folded lhl_Union_image_def]
  interpretation lhl: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar lhl_Union_image using lhl_Union_image_impl .
  definition "lhr_Union_image == it_Union_image ls_iterate rs_empty hrr_union"
  lemmas lhr_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl rs_empty_impl hrr_union_impl, folded lhr_Union_image_def]
  interpretation lhr: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar lhr_Union_image using lhr_Union_image_impl .
  definition "lhh_Union_image == it_Union_image ls_iterate hs_empty hhh_union"
  lemmas lhh_Union_image_impl = it_Union_image_correct[OF ls_iterate_impl hs_empty_impl hhh_union_impl, folded lhh_Union_image_def]
  interpretation lhh: set_Union_image ls_\<alpha> ls_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar lhh_Union_image using lhh_Union_image_impl .
  definition "rll_Union_image == it_Union_image rs_iterate ls_empty lll_union"
  lemmas rll_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl ls_empty_impl lll_union_impl, folded rll_Union_image_def]
  interpretation rll: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar rll_Union_image using rll_Union_image_impl .
  definition "rlr_Union_image == it_Union_image rs_iterate rs_empty lrr_union"
  lemmas rlr_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl rs_empty_impl lrr_union_impl, folded rlr_Union_image_def]
  interpretation rlr: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar rlr_Union_image using rlr_Union_image_impl .
  definition "rlh_Union_image == it_Union_image rs_iterate hs_empty lhh_union"
  lemmas rlh_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl hs_empty_impl lhh_union_impl, folded rlh_Union_image_def]
  interpretation rlh: set_Union_image rs_\<alpha> rs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar rlh_Union_image using rlh_Union_image_impl .
  definition "rrl_Union_image == it_Union_image rs_iterate ls_empty rll_union"
  lemmas rrl_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl ls_empty_impl rll_union_impl, folded rrl_Union_image_def]
  interpretation rrl: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar rrl_Union_image using rrl_Union_image_impl .
  definition "rrr_Union_image == it_Union_image rs_iterate rs_empty rrr_union"
  lemmas rrr_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl rs_empty_impl rrr_union_impl, folded rrr_Union_image_def]
  interpretation rrr: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar rrr_Union_image using rrr_Union_image_impl .
  definition "rrh_Union_image == it_Union_image rs_iterate hs_empty rhh_union"
  lemmas rrh_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl hs_empty_impl rhh_union_impl, folded rrh_Union_image_def]
  interpretation rrh: set_Union_image rs_\<alpha> rs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar rrh_Union_image using rrh_Union_image_impl .
  definition "rhl_Union_image == it_Union_image rs_iterate ls_empty hll_union"
  lemmas rhl_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl ls_empty_impl hll_union_impl, folded rhl_Union_image_def]
  interpretation rhl: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar rhl_Union_image using rhl_Union_image_impl .
  definition "rhr_Union_image == it_Union_image rs_iterate rs_empty hrr_union"
  lemmas rhr_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl rs_empty_impl hrr_union_impl, folded rhr_Union_image_def]
  interpretation rhr: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar rhr_Union_image using rhr_Union_image_impl .
  definition "rhh_Union_image == it_Union_image rs_iterate hs_empty hhh_union"
  lemmas rhh_Union_image_impl = it_Union_image_correct[OF rs_iterate_impl hs_empty_impl hhh_union_impl, folded rhh_Union_image_def]
  interpretation rhh: set_Union_image rs_\<alpha> rs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar rhh_Union_image using rhh_Union_image_impl .
  definition "hll_Union_image == it_Union_image hs_iterate ls_empty lll_union"
  lemmas hll_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl ls_empty_impl lll_union_impl, folded hll_Union_image_def]
  interpretation hll: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar ls_\<alpha> ls_invar hll_Union_image using hll_Union_image_impl .
  definition "hlr_Union_image == it_Union_image hs_iterate rs_empty lrr_union"
  lemmas hlr_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl rs_empty_impl lrr_union_impl, folded hlr_Union_image_def]
  interpretation hlr: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar rs_\<alpha> rs_invar hlr_Union_image using hlr_Union_image_impl .
  definition "hlh_Union_image == it_Union_image hs_iterate hs_empty lhh_union"
  lemmas hlh_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl hs_empty_impl lhh_union_impl, folded hlh_Union_image_def]
  interpretation hlh: set_Union_image hs_\<alpha> hs_invar ls_\<alpha> ls_invar hs_\<alpha> hs_invar hlh_Union_image using hlh_Union_image_impl .
  definition "hrl_Union_image == it_Union_image hs_iterate ls_empty rll_union"
  lemmas hrl_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl ls_empty_impl rll_union_impl, folded hrl_Union_image_def]
  interpretation hrl: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar ls_\<alpha> ls_invar hrl_Union_image using hrl_Union_image_impl .
  definition "hrr_Union_image == it_Union_image hs_iterate rs_empty rrr_union"
  lemmas hrr_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl rs_empty_impl rrr_union_impl, folded hrr_Union_image_def]
  interpretation hrr: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar rs_\<alpha> rs_invar hrr_Union_image using hrr_Union_image_impl .
  definition "hrh_Union_image == it_Union_image hs_iterate hs_empty rhh_union"
  lemmas hrh_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl hs_empty_impl rhh_union_impl, folded hrh_Union_image_def]
  interpretation hrh: set_Union_image hs_\<alpha> hs_invar rs_\<alpha> rs_invar hs_\<alpha> hs_invar hrh_Union_image using hrh_Union_image_impl .
  definition "hhl_Union_image == it_Union_image hs_iterate ls_empty hll_union"
  lemmas hhl_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl ls_empty_impl hll_union_impl, folded hhl_Union_image_def]
  interpretation hhl: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar ls_\<alpha> ls_invar hhl_Union_image using hhl_Union_image_impl .
  definition "hhr_Union_image == it_Union_image hs_iterate rs_empty hrr_union"
  lemmas hhr_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl rs_empty_impl hrr_union_impl, folded hhr_Union_image_def]
  interpretation hhr: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar rs_\<alpha> rs_invar hhr_Union_image using hhr_Union_image_impl .
  definition "hhh_Union_image == it_Union_image hs_iterate hs_empty hhh_union"
  lemmas hhh_Union_image_impl = it_Union_image_correct[OF hs_iterate_impl hs_empty_impl hhh_union_impl, folded hhh_Union_image_def]
  interpretation hhh: set_Union_image hs_\<alpha> hs_invar hs_\<alpha> hs_invar hs_\<alpha> hs_invar hhh_Union_image using hhh_Union_image_impl .

  definition "ll_disjoint_witness == sel_disjoint_witness ls_sel ls_memb"
  lemmas ll_disjoint_witness_impl = sel_disjoint_witness_correct[OF ls_sel_impl ls_memb_impl, folded ll_disjoint_witness_def]
  interpretation ll: set_disjoint_witness ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_disjoint_witness using ll_disjoint_witness_impl .
  definition "lr_disjoint_witness == sel_disjoint_witness ls_sel rs_memb"
  lemmas lr_disjoint_witness_impl = sel_disjoint_witness_correct[OF ls_sel_impl rs_memb_impl, folded lr_disjoint_witness_def]
  interpretation lr: set_disjoint_witness ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_disjoint_witness using lr_disjoint_witness_impl .
  definition "lh_disjoint_witness == sel_disjoint_witness ls_sel hs_memb"
  lemmas lh_disjoint_witness_impl = sel_disjoint_witness_correct[OF ls_sel_impl hs_memb_impl, folded lh_disjoint_witness_def]
  interpretation lh: set_disjoint_witness ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_disjoint_witness using lh_disjoint_witness_impl .
  definition "rl_disjoint_witness == sel_disjoint_witness rs_sel ls_memb"
  lemmas rl_disjoint_witness_impl = sel_disjoint_witness_correct[OF rs_sel_impl ls_memb_impl, folded rl_disjoint_witness_def]
  interpretation rl: set_disjoint_witness rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_disjoint_witness using rl_disjoint_witness_impl .
  definition "rr_disjoint_witness == sel_disjoint_witness rs_sel rs_memb"
  lemmas rr_disjoint_witness_impl = sel_disjoint_witness_correct[OF rs_sel_impl rs_memb_impl, folded rr_disjoint_witness_def]
  interpretation rr: set_disjoint_witness rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_disjoint_witness using rr_disjoint_witness_impl .
  definition "rh_disjoint_witness == sel_disjoint_witness rs_sel hs_memb"
  lemmas rh_disjoint_witness_impl = sel_disjoint_witness_correct[OF rs_sel_impl hs_memb_impl, folded rh_disjoint_witness_def]
  interpretation rh: set_disjoint_witness rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_disjoint_witness using rh_disjoint_witness_impl .
  definition "hl_disjoint_witness == sel_disjoint_witness hs_sel ls_memb"
  lemmas hl_disjoint_witness_impl = sel_disjoint_witness_correct[OF hs_sel_impl ls_memb_impl, folded hl_disjoint_witness_def]
  interpretation hl: set_disjoint_witness hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_disjoint_witness using hl_disjoint_witness_impl .
  definition "hr_disjoint_witness == sel_disjoint_witness hs_sel rs_memb"
  lemmas hr_disjoint_witness_impl = sel_disjoint_witness_correct[OF hs_sel_impl rs_memb_impl, folded hr_disjoint_witness_def]
  interpretation hr: set_disjoint_witness hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_disjoint_witness using hr_disjoint_witness_impl .
  definition "hh_disjoint_witness == sel_disjoint_witness hs_sel hs_memb"
  lemmas hh_disjoint_witness_impl = sel_disjoint_witness_correct[OF hs_sel_impl hs_memb_impl, folded hh_disjoint_witness_def]
  interpretation hh: set_disjoint_witness hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_disjoint_witness using hh_disjoint_witness_impl .

  definition "ll_disjoint == ball_disjoint ls_ball ls_memb"
  lemmas ll_disjoint_impl = ball_disjoint_correct[OF ls_ball_impl ls_memb_impl, folded ll_disjoint_def]
  interpretation ll: set_disjoint ls_\<alpha> ls_invar ls_\<alpha> ls_invar ll_disjoint using ll_disjoint_impl .
  definition "lr_disjoint == ball_disjoint ls_ball rs_memb"
  lemmas lr_disjoint_impl = ball_disjoint_correct[OF ls_ball_impl rs_memb_impl, folded lr_disjoint_def]
  interpretation lr: set_disjoint ls_\<alpha> ls_invar rs_\<alpha> rs_invar lr_disjoint using lr_disjoint_impl .
  definition "lh_disjoint == ball_disjoint ls_ball hs_memb"
  lemmas lh_disjoint_impl = ball_disjoint_correct[OF ls_ball_impl hs_memb_impl, folded lh_disjoint_def]
  interpretation lh: set_disjoint ls_\<alpha> ls_invar hs_\<alpha> hs_invar lh_disjoint using lh_disjoint_impl .
  definition "rl_disjoint == ball_disjoint rs_ball ls_memb"
  lemmas rl_disjoint_impl = ball_disjoint_correct[OF rs_ball_impl ls_memb_impl, folded rl_disjoint_def]
  interpretation rl: set_disjoint rs_\<alpha> rs_invar ls_\<alpha> ls_invar rl_disjoint using rl_disjoint_impl .
  definition "rr_disjoint == ball_disjoint rs_ball rs_memb"
  lemmas rr_disjoint_impl = ball_disjoint_correct[OF rs_ball_impl rs_memb_impl, folded rr_disjoint_def]
  interpretation rr: set_disjoint rs_\<alpha> rs_invar rs_\<alpha> rs_invar rr_disjoint using rr_disjoint_impl .
  definition "rh_disjoint == ball_disjoint rs_ball hs_memb"
  lemmas rh_disjoint_impl = ball_disjoint_correct[OF rs_ball_impl hs_memb_impl, folded rh_disjoint_def]
  interpretation rh: set_disjoint rs_\<alpha> rs_invar hs_\<alpha> hs_invar rh_disjoint using rh_disjoint_impl .
  definition "hl_disjoint == ball_disjoint hs_ball ls_memb"
  lemmas hl_disjoint_impl = ball_disjoint_correct[OF hs_ball_impl ls_memb_impl, folded hl_disjoint_def]
  interpretation hl: set_disjoint hs_\<alpha> hs_invar ls_\<alpha> ls_invar hl_disjoint using hl_disjoint_impl .
  definition "hr_disjoint == ball_disjoint hs_ball rs_memb"
  lemmas hr_disjoint_impl = ball_disjoint_correct[OF hs_ball_impl rs_memb_impl, folded hr_disjoint_def]
  interpretation hr: set_disjoint hs_\<alpha> hs_invar rs_\<alpha> rs_invar hr_disjoint using hr_disjoint_impl .
  definition "hh_disjoint == ball_disjoint hs_ball hs_memb"
  lemmas hh_disjoint_impl = ball_disjoint_correct[OF hs_ball_impl hs_memb_impl, folded hh_disjoint_def]
  interpretation hh: set_disjoint hs_\<alpha> hs_invar hs_\<alpha> hs_invar hh_disjoint using hh_disjoint_impl .

  definition "lll_image_filter_cp == image_filter_cp ls_iterate ls_iterate ls_empty ls_ins"
  lemmas lll_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded lll_image_filter_cp_def]
  definition "llr_image_filter_cp == image_filter_cp ls_iterate ls_iterate rs_empty rs_ins"
  lemmas llr_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded llr_image_filter_cp_def]
  definition "llh_image_filter_cp == image_filter_cp ls_iterate ls_iterate hs_empty hs_ins"
  lemmas llh_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded llh_image_filter_cp_def]
  definition "lrl_image_filter_cp == image_filter_cp ls_iterate rs_iterate ls_empty ls_ins"
  lemmas lrl_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded lrl_image_filter_cp_def]
  definition "lrr_image_filter_cp == image_filter_cp ls_iterate rs_iterate rs_empty rs_ins"
  lemmas lrr_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded lrr_image_filter_cp_def]
  definition "lrh_image_filter_cp == image_filter_cp ls_iterate rs_iterate hs_empty hs_ins"
  lemmas lrh_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded lrh_image_filter_cp_def]
  definition "lhl_image_filter_cp == image_filter_cp ls_iterate hs_iterate ls_empty ls_ins"
  lemmas lhl_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded lhl_image_filter_cp_def]
  definition "lhr_image_filter_cp == image_filter_cp ls_iterate hs_iterate rs_empty rs_ins"
  lemmas lhr_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded lhr_image_filter_cp_def]
  definition "lhh_image_filter_cp == image_filter_cp ls_iterate hs_iterate hs_empty hs_ins"
  lemmas lhh_image_filter_cp_correct = image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded lhh_image_filter_cp_def]
  definition "rll_image_filter_cp == image_filter_cp rs_iterate ls_iterate ls_empty ls_ins"
  lemmas rll_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded rll_image_filter_cp_def]
  definition "rlr_image_filter_cp == image_filter_cp rs_iterate ls_iterate rs_empty rs_ins"
  lemmas rlr_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded rlr_image_filter_cp_def]
  definition "rlh_image_filter_cp == image_filter_cp rs_iterate ls_iterate hs_empty hs_ins"
  lemmas rlh_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded rlh_image_filter_cp_def]
  definition "rrl_image_filter_cp == image_filter_cp rs_iterate rs_iterate ls_empty ls_ins"
  lemmas rrl_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded rrl_image_filter_cp_def]
  definition "rrr_image_filter_cp == image_filter_cp rs_iterate rs_iterate rs_empty rs_ins"
  lemmas rrr_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded rrr_image_filter_cp_def]
  definition "rrh_image_filter_cp == image_filter_cp rs_iterate rs_iterate hs_empty hs_ins"
  lemmas rrh_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded rrh_image_filter_cp_def]
  definition "rhl_image_filter_cp == image_filter_cp rs_iterate hs_iterate ls_empty ls_ins"
  lemmas rhl_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded rhl_image_filter_cp_def]
  definition "rhr_image_filter_cp == image_filter_cp rs_iterate hs_iterate rs_empty rs_ins"
  lemmas rhr_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded rhr_image_filter_cp_def]
  definition "rhh_image_filter_cp == image_filter_cp rs_iterate hs_iterate hs_empty hs_ins"
  lemmas rhh_image_filter_cp_correct = image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded rhh_image_filter_cp_def]
  definition "hll_image_filter_cp == image_filter_cp hs_iterate ls_iterate ls_empty ls_ins"
  lemmas hll_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_impl, folded hll_image_filter_cp_def]
  definition "hlr_image_filter_cp == image_filter_cp hs_iterate ls_iterate rs_empty rs_ins"
  lemmas hlr_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_impl, folded hlr_image_filter_cp_def]
  definition "hlh_image_filter_cp == image_filter_cp hs_iterate ls_iterate hs_empty hs_ins"
  lemmas hlh_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_impl, folded hlh_image_filter_cp_def]
  definition "hrl_image_filter_cp == image_filter_cp hs_iterate rs_iterate ls_empty ls_ins"
  lemmas hrl_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_impl, folded hrl_image_filter_cp_def]
  definition "hrr_image_filter_cp == image_filter_cp hs_iterate rs_iterate rs_empty rs_ins"
  lemmas hrr_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_impl, folded hrr_image_filter_cp_def]
  definition "hrh_image_filter_cp == image_filter_cp hs_iterate rs_iterate hs_empty hs_ins"
  lemmas hrh_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_impl, folded hrh_image_filter_cp_def]
  definition "hhl_image_filter_cp == image_filter_cp hs_iterate hs_iterate ls_empty ls_ins"
  lemmas hhl_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_impl, folded hhl_image_filter_cp_def]
  definition "hhr_image_filter_cp == image_filter_cp hs_iterate hs_iterate rs_empty rs_ins"
  lemmas hhr_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_impl, folded hhr_image_filter_cp_def]
  definition "hhh_image_filter_cp == image_filter_cp hs_iterate hs_iterate hs_empty hs_ins"
  lemmas hhh_image_filter_cp_correct = image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_impl, folded hhh_image_filter_cp_def]

  definition "lll_inj_image_filter_cp == inj_image_filter_cp ls_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lll_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lll_inj_image_filter_cp_def]
  definition "llr_inj_image_filter_cp == inj_image_filter_cp ls_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas llr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llr_inj_image_filter_cp_def]
  definition "llh_inj_image_filter_cp == inj_image_filter_cp ls_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas llh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llh_inj_image_filter_cp_def]
  definition "lrl_inj_image_filter_cp == inj_image_filter_cp ls_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lrl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lrl_inj_image_filter_cp_def]
  definition "lrr_inj_image_filter_cp == inj_image_filter_cp ls_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lrr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lrr_inj_image_filter_cp_def]
  definition "lrh_inj_image_filter_cp == inj_image_filter_cp ls_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lrh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lrh_inj_image_filter_cp_def]
  definition "lhl_inj_image_filter_cp == inj_image_filter_cp ls_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lhl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lhl_inj_image_filter_cp_def]
  definition "lhr_inj_image_filter_cp == inj_image_filter_cp ls_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lhr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lhr_inj_image_filter_cp_def]
  definition "lhh_inj_image_filter_cp == inj_image_filter_cp ls_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lhh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lhh_inj_image_filter_cp_def]
  definition "rll_inj_image_filter_cp == inj_image_filter_cp rs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas rll_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rll_inj_image_filter_cp_def]
  definition "rlr_inj_image_filter_cp == inj_image_filter_cp rs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas rlr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlr_inj_image_filter_cp_def]
  definition "rlh_inj_image_filter_cp == inj_image_filter_cp rs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas rlh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlh_inj_image_filter_cp_def]
  definition "rrl_inj_image_filter_cp == inj_image_filter_cp rs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas rrl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rrl_inj_image_filter_cp_def]
  definition "rrr_inj_image_filter_cp == inj_image_filter_cp rs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas rrr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rrr_inj_image_filter_cp_def]
  definition "rrh_inj_image_filter_cp == inj_image_filter_cp rs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas rrh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rrh_inj_image_filter_cp_def]
  definition "rhl_inj_image_filter_cp == inj_image_filter_cp rs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas rhl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rhl_inj_image_filter_cp_def]
  definition "rhr_inj_image_filter_cp == inj_image_filter_cp rs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas rhr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rhr_inj_image_filter_cp_def]
  definition "rhh_inj_image_filter_cp == inj_image_filter_cp rs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas rhh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rhh_inj_image_filter_cp_def]
  definition "hll_inj_image_filter_cp == inj_image_filter_cp hs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas hll_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hll_inj_image_filter_cp_def]
  definition "hlr_inj_image_filter_cp == inj_image_filter_cp hs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas hlr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlr_inj_image_filter_cp_def]
  definition "hlh_inj_image_filter_cp == inj_image_filter_cp hs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas hlh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlh_inj_image_filter_cp_def]
  definition "hrl_inj_image_filter_cp == inj_image_filter_cp hs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas hrl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hrl_inj_image_filter_cp_def]
  definition "hrr_inj_image_filter_cp == inj_image_filter_cp hs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas hrr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hrr_inj_image_filter_cp_def]
  definition "hrh_inj_image_filter_cp == inj_image_filter_cp hs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas hrh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hrh_inj_image_filter_cp_def]
  definition "hhl_inj_image_filter_cp == inj_image_filter_cp hs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas hhl_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hhl_inj_image_filter_cp_def]
  definition "hhr_inj_image_filter_cp == inj_image_filter_cp hs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas hhr_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hhr_inj_image_filter_cp_def]
  definition "hhh_inj_image_filter_cp == inj_image_filter_cp hs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas hhh_inj_image_filter_cp_correct = inj_image_filter_cp_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hhh_inj_image_filter_cp_def]

  definition "lll_cart == cart ls_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas lll_cart_correct = cart_correct[OF ls_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lll_cart_def]
  definition "llr_cart == cart ls_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas llr_cart_correct = cart_correct[OF ls_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded llr_cart_def]
  definition "llh_cart == cart ls_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas llh_cart_correct = cart_correct[OF ls_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded llh_cart_def]
  definition "lrl_cart == cart ls_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas lrl_cart_correct = cart_correct[OF ls_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lrl_cart_def]
  definition "lrr_cart == cart ls_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas lrr_cart_correct = cart_correct[OF ls_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lrr_cart_def]
  definition "lrh_cart == cart ls_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas lrh_cart_correct = cart_correct[OF ls_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lrh_cart_def]
  definition "lhl_cart == cart ls_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas lhl_cart_correct = cart_correct[OF ls_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded lhl_cart_def]
  definition "lhr_cart == cart ls_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas lhr_cart_correct = cart_correct[OF ls_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded lhr_cart_def]
  definition "lhh_cart == cart ls_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas lhh_cart_correct = cart_correct[OF ls_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded lhh_cart_def]
  definition "rll_cart == cart rs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas rll_cart_correct = cart_correct[OF rs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rll_cart_def]
  definition "rlr_cart == cart rs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas rlr_cart_correct = cart_correct[OF rs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rlr_cart_def]
  definition "rlh_cart == cart rs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas rlh_cart_correct = cart_correct[OF rs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rlh_cart_def]
  definition "rrl_cart == cart rs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas rrl_cart_correct = cart_correct[OF rs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rrl_cart_def]
  definition "rrr_cart == cart rs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas rrr_cart_correct = cart_correct[OF rs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rrr_cart_def]
  definition "rrh_cart == cart rs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas rrh_cart_correct = cart_correct[OF rs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rrh_cart_def]
  definition "rhl_cart == cart rs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas rhl_cart_correct = cart_correct[OF rs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded rhl_cart_def]
  definition "rhr_cart == cart rs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas rhr_cart_correct = cart_correct[OF rs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded rhr_cart_def]
  definition "rhh_cart == cart rs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas rhh_cart_correct = cart_correct[OF rs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded rhh_cart_def]
  definition "hll_cart == cart hs_iterate ls_iterate ls_empty ls_ins_dj"
  lemmas hll_cart_correct = cart_correct[OF hs_iterate_impl ls_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hll_cart_def]
  definition "hlr_cart == cart hs_iterate ls_iterate rs_empty rs_ins_dj"
  lemmas hlr_cart_correct = cart_correct[OF hs_iterate_impl ls_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hlr_cart_def]
  definition "hlh_cart == cart hs_iterate ls_iterate hs_empty hs_ins_dj"
  lemmas hlh_cart_correct = cart_correct[OF hs_iterate_impl ls_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hlh_cart_def]
  definition "hrl_cart == cart hs_iterate rs_iterate ls_empty ls_ins_dj"
  lemmas hrl_cart_correct = cart_correct[OF hs_iterate_impl rs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hrl_cart_def]
  definition "hrr_cart == cart hs_iterate rs_iterate rs_empty rs_ins_dj"
  lemmas hrr_cart_correct = cart_correct[OF hs_iterate_impl rs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hrr_cart_def]
  definition "hrh_cart == cart hs_iterate rs_iterate hs_empty hs_ins_dj"
  lemmas hrh_cart_correct = cart_correct[OF hs_iterate_impl rs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hrh_cart_def]
  definition "hhl_cart == cart hs_iterate hs_iterate ls_empty ls_ins_dj"
  lemmas hhl_cart_correct = cart_correct[OF hs_iterate_impl hs_iterate_impl ls_empty_impl ls_ins_dj_impl, folded hhl_cart_def]
  definition "hhr_cart == cart hs_iterate hs_iterate rs_empty rs_ins_dj"
  lemmas hhr_cart_correct = cart_correct[OF hs_iterate_impl hs_iterate_impl rs_empty_impl rs_ins_dj_impl, folded hhr_cart_def]
  definition "hhh_cart == cart hs_iterate hs_iterate hs_empty hs_ins_dj"
  lemmas hhh_cart_correct = cart_correct[OF hs_iterate_impl hs_iterate_impl hs_empty_impl hs_ins_dj_impl, folded hhh_cart_def]

  definition "ls_to_fifo == it_set_to_fifo ls_iterate"
  lemmas ls_to_fifo_correct = it_set_to_fifo_correct[OF ls_iterate_impl, folded ls_to_fifo_def]
  definition "rs_to_fifo == it_set_to_fifo rs_iterate"
  lemmas rs_to_fifo_correct = it_set_to_fifo_correct[OF rs_iterate_impl, folded rs_to_fifo_def]
  definition "hs_to_fifo == it_set_to_fifo hs_iterate"
  lemmas hs_to_fifo_correct = it_set_to_fifo_correct[OF hs_iterate_impl, folded hs_to_fifo_def]

  definition "ll_map_to_nat == map_to_nat ls_iterate lm_empty lm_update"
  lemmas ll_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl lm_empty_impl lm_update_impl, folded ll_map_to_nat_def]
  definition "lr_map_to_nat == map_to_nat ls_iterate rm_empty rm_update"
  lemmas lr_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl rm_empty_impl rm_update_impl, folded lr_map_to_nat_def]
  definition "lh_map_to_nat == map_to_nat ls_iterate hm_empty hm_update"
  lemmas lh_map_to_nat_correct = map_to_nat_correct[OF ls_iterate_impl hm_empty_impl hm_update_impl, folded lh_map_to_nat_def]
  definition "rl_map_to_nat == map_to_nat rs_iterate lm_empty lm_update"
  lemmas rl_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl lm_empty_impl lm_update_impl, folded rl_map_to_nat_def]
  definition "rr_map_to_nat == map_to_nat rs_iterate rm_empty rm_update"
  lemmas rr_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl rm_empty_impl rm_update_impl, folded rr_map_to_nat_def]
  definition "rh_map_to_nat == map_to_nat rs_iterate hm_empty hm_update"
  lemmas rh_map_to_nat_correct = map_to_nat_correct[OF rs_iterate_impl hm_empty_impl hm_update_impl, folded rh_map_to_nat_def]
  definition "hl_map_to_nat == map_to_nat hs_iterate lm_empty lm_update"
  lemmas hl_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl lm_empty_impl lm_update_impl, folded hl_map_to_nat_def]
  definition "hr_map_to_nat == map_to_nat hs_iterate rm_empty rm_update"
  lemmas hr_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl rm_empty_impl rm_update_impl, folded hr_map_to_nat_def]
  definition "hh_map_to_nat == map_to_nat hs_iterate hm_empty hm_update"
  lemmas hh_map_to_nat_correct = map_to_nat_correct[OF hs_iterate_impl hm_empty_impl hm_update_impl, folded hh_map_to_nat_def]
(*#end_generated*)


(*#begin_generated*)
definition "ll_idx_invar == idx_invar lm_\<alpha> lm_invar ls_\<alpha> ls_invar"
definition "ll_idx_lookup == idx_lookup lm_lookup ls_empty"
lemmas ll_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl ls_empty_impl, folded ll_idx_invar_def ll_idx_lookup_def]
definition "lr_idx_invar == idx_invar lm_\<alpha> lm_invar rs_\<alpha> rs_invar"
definition "lr_idx_lookup == idx_lookup lm_lookup rs_empty"
lemmas lr_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl rs_empty_impl, folded lr_idx_invar_def lr_idx_lookup_def]
definition "lh_idx_invar == idx_invar lm_\<alpha> lm_invar hs_\<alpha> hs_invar"
definition "lh_idx_lookup == idx_lookup lm_lookup hs_empty"
lemmas lh_idx_lookup_correct = idx_lookup_correct[OF lm_lookup_impl hs_empty_impl, folded lh_idx_invar_def lh_idx_lookup_def]
definition "rl_idx_invar == idx_invar rm_\<alpha> rm_invar ls_\<alpha> ls_invar"
definition "rl_idx_lookup == idx_lookup rm_lookup ls_empty"
lemmas rl_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl ls_empty_impl, folded rl_idx_invar_def rl_idx_lookup_def]
definition "rr_idx_invar == idx_invar rm_\<alpha> rm_invar rs_\<alpha> rs_invar"
definition "rr_idx_lookup == idx_lookup rm_lookup rs_empty"
lemmas rr_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl rs_empty_impl, folded rr_idx_invar_def rr_idx_lookup_def]
definition "rh_idx_invar == idx_invar rm_\<alpha> rm_invar hs_\<alpha> hs_invar"
definition "rh_idx_lookup == idx_lookup rm_lookup hs_empty"
lemmas rh_idx_lookup_correct = idx_lookup_correct[OF rm_lookup_impl hs_empty_impl, folded rh_idx_invar_def rh_idx_lookup_def]
definition "hl_idx_invar == idx_invar hm_\<alpha> hm_invar ls_\<alpha> ls_invar"
definition "hl_idx_lookup == idx_lookup hm_lookup ls_empty"
lemmas hl_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl ls_empty_impl, folded hl_idx_invar_def hl_idx_lookup_def]
definition "hr_idx_invar == idx_invar hm_\<alpha> hm_invar rs_\<alpha> rs_invar"
definition "hr_idx_lookup == idx_lookup hm_lookup rs_empty"
lemmas hr_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl rs_empty_impl, folded hr_idx_invar_def hr_idx_lookup_def]
definition "hh_idx_invar == idx_invar hm_\<alpha> hm_invar hs_\<alpha> hs_invar"
definition "hh_idx_lookup == idx_lookup hm_lookup hs_empty"
lemmas hh_idx_lookup_correct = idx_lookup_correct[OF hm_lookup_impl hs_empty_impl, folded hh_idx_invar_def hh_idx_lookup_def]
(*#end_generated*)

(*#begin_generated*)
definition "lll_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    ls_iterate"
lemmas lll_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded ll_idx_invar_def lll_idx_build_def]
definition "llr_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    rs_iterate"
lemmas llr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded ll_idx_invar_def llr_idx_build_def]
definition "llh_idx_build == idx_build lm_empty lm_lookup lm_update   ls_empty ls_ins    hs_iterate"
lemmas llh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded ll_idx_invar_def llh_idx_build_def]
definition "lrl_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    ls_iterate"
lemmas lrl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded lr_idx_invar_def lrl_idx_build_def]
definition "lrr_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    rs_iterate"
lemmas lrr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded lr_idx_invar_def lrr_idx_build_def]
definition "lrh_idx_build == idx_build lm_empty lm_lookup lm_update   rs_empty rs_ins    hs_iterate"
lemmas lrh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded lr_idx_invar_def lrh_idx_build_def]
definition "lhl_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    ls_iterate"
lemmas lhl_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded lh_idx_invar_def lhl_idx_build_def]
definition "lhr_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    rs_iterate"
lemmas lhr_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded lh_idx_invar_def lhr_idx_build_def]
definition "lhh_idx_build == idx_build lm_empty lm_lookup lm_update   hs_empty hs_ins    hs_iterate"
lemmas lhh_idx_build_correct = idx_build_correct[OF lm_empty_impl lm_lookup_impl lm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded lh_idx_invar_def lhh_idx_build_def]
definition "rll_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    ls_iterate"
lemmas rll_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded rl_idx_invar_def rll_idx_build_def]
definition "rlr_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    rs_iterate"
lemmas rlr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded rl_idx_invar_def rlr_idx_build_def]
definition "rlh_idx_build == idx_build rm_empty rm_lookup rm_update   ls_empty ls_ins    hs_iterate"
lemmas rlh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded rl_idx_invar_def rlh_idx_build_def]
definition "rrl_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    ls_iterate"
lemmas rrl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded rr_idx_invar_def rrl_idx_build_def]
definition "rrr_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    rs_iterate"
lemmas rrr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded rr_idx_invar_def rrr_idx_build_def]
definition "rrh_idx_build == idx_build rm_empty rm_lookup rm_update   rs_empty rs_ins    hs_iterate"
lemmas rrh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded rr_idx_invar_def rrh_idx_build_def]
definition "rhl_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    ls_iterate"
lemmas rhl_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded rh_idx_invar_def rhl_idx_build_def]
definition "rhr_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    rs_iterate"
lemmas rhr_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded rh_idx_invar_def rhr_idx_build_def]
definition "rhh_idx_build == idx_build rm_empty rm_lookup rm_update   hs_empty hs_ins    hs_iterate"
lemmas rhh_idx_build_correct = idx_build_correct[OF rm_empty_impl rm_lookup_impl rm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded rh_idx_invar_def rhh_idx_build_def]
definition "hll_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    ls_iterate"
lemmas hll_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   ls_iterate_impl,
  folded hl_idx_invar_def hll_idx_build_def]
definition "hlr_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    rs_iterate"
lemmas hlr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   rs_iterate_impl,
  folded hl_idx_invar_def hlr_idx_build_def]
definition "hlh_idx_build == idx_build hm_empty hm_lookup hm_update   ls_empty ls_ins    hs_iterate"
lemmas hlh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   ls_empty_impl ls_ins_impl   hs_iterate_impl,
  folded hl_idx_invar_def hlh_idx_build_def]
definition "hrl_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    ls_iterate"
lemmas hrl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   ls_iterate_impl,
  folded hr_idx_invar_def hrl_idx_build_def]
definition "hrr_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    rs_iterate"
lemmas hrr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   rs_iterate_impl,
  folded hr_idx_invar_def hrr_idx_build_def]
definition "hrh_idx_build == idx_build hm_empty hm_lookup hm_update   rs_empty rs_ins    hs_iterate"
lemmas hrh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   rs_empty_impl rs_ins_impl   hs_iterate_impl,
  folded hr_idx_invar_def hrh_idx_build_def]
definition "hhl_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    ls_iterate"
lemmas hhl_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   ls_iterate_impl,
  folded hh_idx_invar_def hhl_idx_build_def]
definition "hhr_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    rs_iterate"
lemmas hhr_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   rs_iterate_impl,
  folded hh_idx_invar_def hhr_idx_build_def]
definition "hhh_idx_build == idx_build hm_empty hm_lookup hm_update   hs_empty hs_ins    hs_iterate"
lemmas hhh_idx_build_correct = idx_build_correct[OF hm_empty_impl hm_lookup_impl hm_update_impl   hs_empty_impl hs_ins_impl   hs_iterate_impl,
  folded hh_idx_invar_def hhh_idx_build_def]
(*#end_generated*)

end
