header {* \isaheader{Record-Based Set Interface: Implementation setup} *}
theory RecordSetImpl
imports 
  "../gen_algo/StdInst"
  ListSetImpl_Sorted 
  ListSetImpl_NotDist
begin

(*--------------------------------------------*)
subsection "List Set"

  definition "ls_ops = \<lparr>
    set_op_\<alpha> = ls_\<alpha>,
    set_op_invar = ls_invar,
    set_op_empty = ls_empty,
    set_op_sng = ls_sng,
    set_op_memb = ls_memb,
    set_op_ins = ls_ins,
    set_op_ins_dj = ls_ins_dj,
    set_op_delete = ls_delete,
    set_op_isEmpty = ls_isEmpty,
    set_op_isSng = ls_isSng,
    set_op_ball = ls_ball,
    set_op_bexists = ls_bexists,
    set_op_size = ls_size,
    set_op_size_abort = ls_size_abort,
    set_op_union = ls_union,
    set_op_union_dj = ls_union_dj,
    set_op_diff = ll_diff,
    set_op_filter = ll_filter,
    set_op_inter = ls_inter,
    set_op_subset = ll_subset,
    set_op_equal = ll_equal,
    set_op_disjoint = ll_disjoint,
    set_op_disjoint_witness = ll_disjoint_witness,
    set_op_sel = ls_sel',
    set_op_to_list = ls_to_list,
    set_op_from_list = list_to_ls
    \<rparr>"

  interpretation lsr!: StdSet ls_ops
    apply (rule StdSet.intro)
    apply (simp_all add: ls_ops_def)
    apply unfold_locales
    done

  lemma ls_ops_unfold[code_unfold]:
    "set_op_\<alpha> ls_ops = ls_\<alpha>"
    "set_op_invar ls_ops = ls_invar"
    "set_op_empty ls_ops = ls_empty"
    "set_op_sng ls_ops = ls_sng"
    "set_op_memb ls_ops = ls_memb"
    "set_op_ins ls_ops = ls_ins"
    "set_op_ins_dj ls_ops = ls_ins_dj"
    "set_op_delete ls_ops = ls_delete"
    "set_op_isEmpty ls_ops = ls_isEmpty"
    "set_op_isSng ls_ops = ls_isSng"
    "set_op_ball ls_ops = ls_ball"
    "set_op_bexists ls_ops = ls_bexists"
    "set_op_size ls_ops = ls_size"
    "set_op_size_abort ls_ops = ls_size_abort"
    "set_op_union ls_ops = ls_union"
    "set_op_union_dj ls_ops = ls_union_dj"
    "set_op_diff ls_ops = ll_diff"
    "set_op_filter ls_ops = ll_filter"
    "set_op_inter ls_ops = ls_inter"
    "set_op_subset ls_ops = ll_subset"
    "set_op_equal ls_ops = ll_equal"
    "set_op_disjoint ls_ops = ll_disjoint"
    "set_op_disjoint_witness ls_ops = ll_disjoint_witness"
    "set_op_sel ls_ops = ls_sel'"
    "set_op_to_list ls_ops = ls_to_list"
    "set_op_from_list ls_ops = list_to_ls"
    by (auto simp add: ls_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *} 
  interpretation lsr!: set_iteratei "(set_op_\<alpha> ls_ops)" "(set_op_invar ls_ops)" ls_iteratei using ls_iteratei_impl[folded ls_ops_unfold] .


(*--------------------------------------------*)
subsection "List Set with Invar"

  definition "lsi_ops = \<lparr>
    set_op_\<alpha> = lsi_\<alpha>,
    set_op_invar = lsi_invar,
    set_op_empty = lsi_empty,
    set_op_sng = lsi_sng,
    set_op_memb = lsi_memb,
    set_op_ins = lsi_ins,
    set_op_ins_dj = lsi_ins_dj,
    set_op_delete = lsi_delete,
    set_op_isEmpty = lsi_isEmpty,
    set_op_isSng = lsi_isSng,
    set_op_ball = lsi_ball,
    set_op_bexists = lsi_bexists,
    set_op_size = lsi_size,
    set_op_size_abort = lsi_size_abort,
    set_op_union = lsi_union,
    set_op_union_dj = lsi_union_dj,
    set_op_diff = lili_diff,
    set_op_filter = lili_filter,
    set_op_inter = lsi_inter,
    set_op_subset = lili_subset,
    set_op_equal = lili_equal,
    set_op_disjoint = lili_disjoint,
    set_op_disjoint_witness = lili_disjoint_witness,
    set_op_sel = lsi_sel',
    set_op_to_list = lsi_to_list,
    set_op_from_list = list_to_lsi
    \<rparr>"

  interpretation lsir!: StdSet lsi_ops
    apply (rule StdSet.intro)
    apply (simp_all add: lsi_ops_def)
    apply unfold_locales
    done

  lemma lsi_ops_unfold[code_unfold]:
    "set_op_\<alpha> lsi_ops = lsi_\<alpha>"
    "set_op_invar lsi_ops = lsi_invar"
    "set_op_empty lsi_ops = lsi_empty"
    "set_op_sng lsi_ops = lsi_sng"
    "set_op_memb lsi_ops = lsi_memb"
    "set_op_ins lsi_ops = lsi_ins"
    "set_op_ins_dj lsi_ops = lsi_ins_dj"
    "set_op_delete lsi_ops = lsi_delete"
    "set_op_isEmpty lsi_ops = lsi_isEmpty"
    "set_op_isSng lsi_ops = lsi_isSng"
    "set_op_ball lsi_ops = lsi_ball"
    "set_op_bexists lsi_ops = lsi_bexists"
    "set_op_size lsi_ops = lsi_size"
    "set_op_size_abort lsi_ops = lsi_size_abort"
    "set_op_union lsi_ops = lsi_union"
    "set_op_union_dj lsi_ops = lsi_union_dj"
    "set_op_diff lsi_ops = lili_diff"
    "set_op_filter lsi_ops = lili_filter"
    "set_op_inter lsi_ops = lsi_inter"
    "set_op_subset lsi_ops = lili_subset"
    "set_op_equal lsi_ops = lili_equal"
    "set_op_disjoint lsi_ops = lili_disjoint"
    "set_op_disjoint_witness lsi_ops = lili_disjoint_witness"
    "set_op_sel lsi_ops = lsi_sel'"
    "set_op_to_list lsi_ops = lsi_to_list"
    "set_op_from_list lsi_ops = list_to_lsi"
    by (simp_all add: lsi_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *} 
  interpretation lsir!: set_iteratei "(set_op_\<alpha> lsi_ops)" "(set_op_invar lsi_ops)" lsi_iteratei using lsi_iteratei_impl[folded lsi_ops_unfold] .

(*--------------------------------------------*)
subsection "List Set with Invar and non-distinct lists"

  definition "lsnd_ops = \<lparr>
    set_op_\<alpha> = lsnd_\<alpha>,
    set_op_invar = lsnd_invar,
    set_op_empty = lsnd_empty,
    set_op_sng = lsnd_sng,
    set_op_memb = lsnd_memb,
    set_op_ins = lsnd_ins,
    set_op_ins_dj = lsnd_ins_dj,
    set_op_delete = lsnd_delete,
    set_op_isEmpty = lsnd_isEmpty,
    set_op_isSng = lsnd_isSng,
    set_op_ball = lsnd_ball,
    set_op_bexists = lsnd_bexists,
    set_op_size = lsnd_size,
    set_op_size_abort = lsnd_size_abort,
    set_op_union = lsnd_union,
    set_op_union_dj = lsnd_union_dj,
    set_op_diff = lsnd_diff,
    set_op_filter = lsnd_filter,
    set_op_inter = lsnd_inter,
    set_op_subset = lsnd_subset,
    set_op_equal = lsnd_equal,
    set_op_disjoint = lsnd_disjoint,
    set_op_disjoint_witness = lsnd_disjoint_witness,
    set_op_sel = lsnd_sel',
    set_op_to_list = lsnd_to_list,
    set_op_from_list = list_to_lsnd
    \<rparr>"

  interpretation lsndr!: StdSet lsnd_ops
    apply (rule StdSet.intro)
    apply (simp_all add: lsnd_ops_def)
    apply unfold_locales
    done

  lemma lsnd_ops_unfold[code_unfold]:
    "set_op_\<alpha> lsnd_ops = lsnd_\<alpha>"
    "set_op_invar lsnd_ops = lsnd_invar"
    "set_op_empty lsnd_ops = lsnd_empty"
    "set_op_sng lsnd_ops = lsnd_sng"
    "set_op_memb lsnd_ops = lsnd_memb"
    "set_op_ins lsnd_ops = lsnd_ins"
    "set_op_ins_dj lsnd_ops = lsnd_ins_dj"
    "set_op_delete lsnd_ops = lsnd_delete"
    "set_op_isEmpty lsnd_ops = lsnd_isEmpty"
    "set_op_isSng lsnd_ops = lsnd_isSng"
    "set_op_ball lsnd_ops = lsnd_ball"
    "set_op_bexists lsnd_ops = lsnd_bexists"
    "set_op_size lsnd_ops = lsnd_size"
    "set_op_size_abort lsnd_ops = lsnd_size_abort"
    "set_op_union lsnd_ops = lsnd_union"
    "set_op_union_dj lsnd_ops = lsnd_union_dj"
    "set_op_diff lsnd_ops = lsnd_diff"
    "set_op_filter lsnd_ops = lsnd_filter"
    "set_op_inter lsnd_ops = lsnd_inter"
    "set_op_subset lsnd_ops = lsnd_subset"
    "set_op_equal lsnd_ops = lsnd_equal"
    "set_op_disjoint lsnd_ops = lsnd_disjoint"
    "set_op_disjoint_witness lsnd_ops = lsnd_disjoint_witness"
    "set_op_sel lsnd_ops = lsnd_sel'"
    "set_op_to_list lsnd_ops = lsnd_to_list"
    "set_op_from_list lsnd_ops = list_to_lsnd"
    by (simp_all add: lsnd_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *} 
  interpretation lsndr!: set_iteratei "(set_op_\<alpha> lsnd_ops)" "(set_op_invar lsnd_ops)" lsnd_iteratei using lsnd_iteratei_impl[folded lsnd_ops_unfold] .

(*--------------------------------------------*)
subsection "List Set by sorted lists"
  definition lss_ops :: "('x :: linorder, 'x lss) oset_ops"
  where "lss_ops = \<lparr>
    set_op_\<alpha> = lss_\<alpha>,
    set_op_invar = lss_invar,
    set_op_empty = lss_empty,
    set_op_sng = lss_sng,
    set_op_memb = lss_memb,
    set_op_ins = lss_ins,
    set_op_ins_dj = lss_ins_dj,
    set_op_delete = lss_delete,
    set_op_isEmpty = lss_isEmpty,
    set_op_isSng = lss_isSng,
    set_op_ball = lss_ball,
    set_op_bexists = lss_bexists,
    set_op_size = lss_size,
    set_op_size_abort = lss_size_abort,
    set_op_union = lss_union,
    set_op_union_dj = lss_union_dj,
    set_op_diff = lss_diff,
    set_op_filter = lss_filter,
    set_op_inter = lss_inter,
    set_op_subset = lss_subset,
    set_op_equal = lss_equal,
    set_op_disjoint = lss_disjoint,
    set_op_disjoint_witness = lss_disjoint_witness,
    set_op_sel = lss_sel',
    set_op_to_list = lss_to_list,
    set_op_from_list = list_to_lss,
    set_op_min = lss_min,
    set_op_max = lss_max
    \<rparr>"

  interpretation lssr!: StdSet lss_ops
    apply (rule StdSet.intro)
    apply (simp_all add: lss_ops_def)
    apply unfold_locales
    done

  interpretation lssr!: StdOSet lss_ops
    apply (rule StdOSet.intro)
    apply (rule StdSet.intro)
    apply (simp_all add: lss_ops_def)
    apply unfold_locales
    done

  lemma lss_ops_unfold[code_unfold]:
    "set_op_\<alpha> lss_ops = lss_\<alpha>"
    "set_op_invar lss_ops = lss_invar"
    "set_op_empty lss_ops = lss_empty"
    "set_op_sng lss_ops = lss_sng"
    "set_op_memb lss_ops = lss_memb"
    "set_op_ins lss_ops = lss_ins"
    "set_op_ins_dj lss_ops = lss_ins_dj"
    "set_op_delete lss_ops = lss_delete"
    "set_op_isEmpty lss_ops = lss_isEmpty"
    "set_op_isSng lss_ops = lss_isSng"
    "set_op_ball lss_ops = lss_ball"
    "set_op_size lss_ops = lss_size"
    "set_op_size_abort lss_ops = lss_size_abort"
    "set_op_union lss_ops = lss_union"
    "set_op_union_dj lss_ops = lss_union_dj"
    "set_op_diff lss_ops = lss_diff"
    "set_op_filter lss_ops = lss_filter"
    "set_op_inter lss_ops = lss_inter"
    "set_op_subset lss_ops = lss_subset"
    "set_op_equal lss_ops = lss_equal"
    "set_op_disjoint lss_ops = lss_disjoint"
    "set_op_disjoint_witness lss_ops = lss_disjoint_witness"
    "set_op_sel lss_ops = lss_sel'"
    "set_op_to_list lss_ops = lss_to_list"
    "set_op_from_list lss_ops = list_to_lss"
    "set_op_min lss_ops = lss_min"
    "set_op_max lss_ops = lss_max"
    by (auto simp add: lss_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iteratolss *}
  interpretation lssr!: set_iteratei "(set_op_\<alpha> lss_ops)" "(set_op_invar lss_ops)" lss_iteratei
    unfolding lss_ops_unfold
    using lss_iteratei_impl .
  
  interpretation lssr!: set_iterateoi "(set_op_\<alpha> lss_ops)" "(set_op_invar lss_ops)" lss_iterateoi
    unfolding lss_ops_unfold
    using lss_iterateoi_impl .

  interpretation lssr!: set_reverse_iterateoi "(set_op_\<alpha> lss_ops)" "(set_op_invar lss_ops)" lss_reverse_iterateoi
    unfolding lss_ops_unfold
    using lss_reverse_iterateoi_impl .

(*--------------------------------------------*)
subsection "RBT Set"
  definition rs_ops :: "('x :: linorder, 'x rs) oset_ops"
  where "rs_ops = \<lparr>
    set_op_\<alpha> = rs_\<alpha>,
    set_op_invar = rs_invar,
    set_op_empty = rs_empty,
    set_op_sng = rs_sng,
    set_op_memb = rs_memb,
    set_op_ins = rs_ins,
    set_op_ins_dj = rs_ins_dj,
    set_op_delete = rs_delete,
    set_op_isEmpty = rs_isEmpty,
    set_op_isSng = rs_isSng,
    set_op_ball = rs_ball,
    set_op_bexists = rs_bexists,
    set_op_size = rs_size,
    set_op_size_abort = rs_size_abort,
    set_op_union = rs_union,
    set_op_union_dj = rs_union_dj,
    set_op_diff = rr_diff,
    set_op_filter = rr_filter,
    set_op_inter = rs_inter,
    set_op_subset = rr_subset,
    set_op_equal = rr_equal,
    set_op_disjoint = rr_disjoint,
    set_op_disjoint_witness = rr_disjoint_witness,
    set_op_sel = rs_sel',
    set_op_to_list = rs_to_list,
    set_op_from_list = list_to_rs,
    set_op_min = rs_min,
    set_op_max = rs_max
    \<rparr>"

  interpretation rsr!: StdSet rs_ops
    apply (rule StdSet.intro)
    apply (simp_all add: rs_ops_def)
    apply unfold_locales
    done

  interpretation rsr!: StdOSet rs_ops
    apply (rule StdOSet.intro)
    apply (rule StdSet.intro)
    apply (simp_all add: rs_ops_def)
    apply unfold_locales
    done

  lemma rs_ops_unfold[code_unfold]:
    "set_op_\<alpha> rs_ops = rs_\<alpha>"
    "set_op_invar rs_ops = rs_invar"
    "set_op_empty rs_ops = rs_empty"
    "set_op_sng rs_ops = rs_sng"
    "set_op_memb rs_ops = rs_memb"
    "set_op_ins rs_ops = rs_ins"
    "set_op_ins_dj rs_ops = rs_ins_dj"
    "set_op_delete rs_ops = rs_delete"
    "set_op_isEmpty rs_ops = rs_isEmpty"
    "set_op_isSng rs_ops = rs_isSng"
    "set_op_ball rs_ops = rs_ball"
    "set_op_bexists rs_ops = rs_bexists"
    "set_op_size rs_ops = rs_size"
    "set_op_size_abort rs_ops = rs_size_abort"
    "set_op_union rs_ops = rs_union"
    "set_op_union_dj rs_ops = rs_union_dj"
    "set_op_diff rs_ops = rr_diff"
    "set_op_filter rs_ops = rr_filter"
    "set_op_inter rs_ops = rs_inter"
    "set_op_subset rs_ops = rr_subset"
    "set_op_equal rs_ops = rr_equal"
    "set_op_disjoint rs_ops = rr_disjoint"
    "set_op_disjoint_witness rs_ops = rr_disjoint_witness"
    "set_op_sel rs_ops = rs_sel'"
    "set_op_to_list rs_ops = rs_to_list"
    "set_op_from_list rs_ops = list_to_rs"
    "set_op_min rs_ops = rs_min"
    "set_op_max rs_ops = rs_max"
    by (auto simp add: rs_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}
  interpretation rsr!: set_iteratei "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iteratei
    unfolding rs_ops_unfold
    using rs_iteratei_impl .
  
  interpretation rsr!: set_iterateoi "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iterateoi
    unfolding rs_ops_unfold
    using rs_iterateoi_impl .

  interpretation rsr!: set_reverse_iterateoi "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_reverse_iterateoi
    unfolding rs_ops_unfold
    using rs_reverse_iterateoi_impl .



(*--------------------------------------------*)
subsection "HashSet"
  definition "hs_ops = \<lparr>
    set_op_\<alpha> = hs_\<alpha>,
    set_op_invar = hs_invar,
    set_op_empty = hs_empty,
    set_op_sng = hs_sng,
    set_op_memb = hs_memb,
    set_op_ins = hs_ins,
    set_op_ins_dj = hs_ins_dj,
    set_op_delete = hs_delete,
    set_op_isEmpty = hs_isEmpty,
    set_op_isSng = hs_isSng,
    set_op_ball = hs_ball,
    set_op_bexists = hs_bexists,
    set_op_size = hs_size,
    set_op_size_abort = hs_size_abort,
    set_op_union = hs_union,
    set_op_union_dj = hs_union_dj,
    set_op_diff = hh_diff,
    set_op_filter = hh_filter,
    set_op_inter = hs_inter,
    set_op_subset = hh_subset,
    set_op_equal = hh_equal,
    set_op_disjoint = hh_disjoint,
    set_op_disjoint_witness = hh_disjoint_witness,
    set_op_sel = hs_sel',
    set_op_to_list = hs_to_list,
    set_op_from_list = list_to_hs
    \<rparr>"

  interpretation hsr!: StdSet hs_ops
    apply (rule StdSet.intro)
    apply (simp_all add: hs_ops_def)
    apply unfold_locales
    done

  lemma hs_ops_unfold[code_unfold]:
    "set_op_\<alpha> hs_ops = hs_\<alpha>"
    "set_op_invar hs_ops = hs_invar"
    "set_op_empty hs_ops = hs_empty"
    "set_op_sng hs_ops = hs_sng"
    "set_op_memb hs_ops = hs_memb"
    "set_op_ins hs_ops = hs_ins"
    "set_op_ins_dj hs_ops = hs_ins_dj"
    "set_op_delete hs_ops = hs_delete"
    "set_op_isEmpty hs_ops = hs_isEmpty"
    "set_op_isSng hs_ops = hs_isSng"
    "set_op_ball hs_ops = hs_ball"
    "set_op_bexists hs_ops = hs_bexists"
    "set_op_size hs_ops = hs_size"
    "set_op_size_abort hs_ops = hs_size_abort"
    "set_op_union hs_ops = hs_union"
    "set_op_union_dj hs_ops = hs_union_dj"
    "set_op_diff hs_ops = hh_diff"
    "set_op_filter hs_ops = hh_filter"
    "set_op_inter hs_ops = hs_inter"
    "set_op_subset hs_ops = hh_subset"
    "set_op_equal hs_ops = hh_equal"
    "set_op_disjoint hs_ops = hh_disjoint"
    "set_op_disjoint_witness hs_ops = hh_disjoint_witness"
    "set_op_sel hs_ops = hs_sel'"
    "set_op_to_list hs_ops = hs_to_list"
    "set_op_from_list hs_ops = list_to_hs"
    by (auto simp add: hs_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *}
  interpretation hsr!: set_iteratei "(set_op_\<alpha> hs_ops)" "(set_op_invar hs_ops)" hs_iteratei using hs_iteratei_impl[folded hs_ops_unfold] .


(*--------------------------------------------*)
(* TODO: @Peter Wieder Einfügen, wenn StdInst mit Tries funktioniert 
subsection "Trie Set"
  definition "ts_ops = \<lparr>
    set_op_\<alpha> = ts_\<alpha>,
    set_op_invar = ts_invar,
    set_op_empty = ts_empty,
    set_op_sng = ts_sng,
    set_op_memb = ts_memb,
    set_op_ins = ts_ins,
    set_op_ins_dj = ts_ins_dj,
    set_op_delete = ts_delete,
    set_op_isEmpty = ts_isEmpty,
    set_op_isSng = ts_isSng,
    set_op_ball = ts_ball,
    set_op_bexists = ts_bexists,
    set_op_size = ts_size,
    set_op_size_abort = ts_size_abort,
    set_op_union = ts_union,
    set_op_union_dj = ts_union_dj,
    set_op_diff = ts_diff,
    set_op_filter = ts_filter,
    set_op_inter = ts_inter,
    set_op_subset = tt_subset,
    set_op_equal = tt_equal,
    set_op_disjoint = tt_disjoint,
    set_op_disjoint_witness = tt_disjoint_witness,
    set_op_sel = ts_sel',
    set_op_to_list = ts_to_list,
    set_op_from_list = list_to_ts
    \<rparr>"

  interpretation tsr!: StdSet ts_ops
    apply (rule StdSet.intro)
    apply (simp_all add: ts_ops_def)
    apply unfold_locales
    done

  lemma ts_ops_unfold[code_unfold]:
    "set_op_\<alpha> ts_ops = ts_\<alpha>"
    "set_op_invar ts_ops = ts_invar"
    "set_op_empty ts_ops = ts_empty"
    "set_op_sng ts_ops = ts_sng"
    "set_op_memb ts_ops = ts_memb"
    "set_op_ins ts_ops = ts_ins"
    "set_op_ins_dj ts_ops = ts_ins_dj"
    "set_op_delete ts_ops = ts_delete"
    "set_op_isEmpty ts_ops = ts_isEmpty"
    "set_op_ball ts_ops = ts_ball"
    "set_op_bexists ts_ops = ts_bexists"
    "set_op_size ts_ops = ts_size"
    "set_op_size_abort = ts_size_abort"
    "set_op_union ts_ops = ts_union"
    "set_op_union_dj ts_ops = ts_union_dj"
    "set_op_inter ts_ops = ts_inter"
    "set_op_diff ts_ops = ts_diff"
    "set_op_filter ts_ops = ts_filter"
    "set_op_subset ts_ops = tt_subset"
    "set_op_equal ts_ops = tt_equal"
    "set_op_disjoint ts_ops = tt_disjoint"
    "set_op_disjoint_witness ts_ops = tt_disjoint_witness"
    "set_op_sel ts_ops = ts_sel'"
    "set_op_to_list ts_ops = ts_to_list"
    "set_op_from_list ts_ops = list_to_ts"
    by (auto simp add: ts_ops_def)

  -- "Required to set up unfold_locales in contexts with additional iterators"
  interpretation tsr!: set_iteratei "(set_op_\<alpha> ts_ops)" "(set_op_invar ts_ops)" ts_iteratei using ts_iteratei_impl[folded ts_ops_unfold] .
*)

(*--------------------------------------------*)
subsection "Array Hash Set"
  definition "ahs_ops = \<lparr>
    set_op_\<alpha> = ahs_\<alpha>,
    set_op_invar = ahs_invar,
    set_op_empty = ahs_empty,
    set_op_sng = ahs_sng,
    set_op_memb = ahs_memb,
    set_op_ins = ahs_ins,
    set_op_ins_dj = ahs_ins_dj,
    set_op_delete = ahs_delete,
    set_op_isEmpty = ahs_isEmpty,
    set_op_isSng = ahs_isSng,
    set_op_ball = ahs_ball,
    set_op_bexists = ahs_bexists,
    set_op_size = ahs_size,
    set_op_size_abort = ahs_size_abort,
    set_op_union = ahs_union,
    set_op_union_dj = ahs_union_dj,
    set_op_diff = aa_diff,
    set_op_filter = aa_filter,
    set_op_inter = ahs_inter,
    set_op_subset = aa_subset,
    set_op_equal = aa_equal,
    set_op_disjoint = aa_disjoint,
    set_op_disjoint_witness = aa_disjoint_witness,
    set_op_sel = ahs_sel',
    set_op_to_list = ahs_to_list,
    set_op_from_list = list_to_ahs
    \<rparr>"

  interpretation ahsr!: StdSet ahs_ops
    apply (rule StdSet.intro)
    apply (simp_all add: ahs_ops_def)
    apply unfold_locales
    done

  lemma ahs_ops_unfold[code_unfold]:
    "set_op_\<alpha> ahs_ops = ahs_\<alpha>"
    "set_op_invar ahs_ops = ahs_invar"
    "set_op_empty ahs_ops = ahs_empty"
    "set_op_sng ahs_ops = ahs_sng"
    "set_op_memb ahs_ops = ahs_memb"
    "set_op_ins ahs_ops = ahs_ins"
    "set_op_ins_dj ahs_ops = ahs_ins_dj"
    "set_op_delete ahs_ops = ahs_delete"
    "set_op_isEmpty ahs_ops = ahs_isEmpty"
    "set_op_isSng ahs_ops = ahs_isSng"
    "set_op_ball ahs_ops = ahs_ball"
    "set_op_bexists ahs_ops = ahs_bexists"
    "set_op_size ahs_ops = ahs_size"
    "set_op_size_abort ahs_ops = ahs_size_abort"
    "set_op_union ahs_ops = ahs_union"
    "set_op_union_dj ahs_ops = ahs_union_dj"
    "set_op_diff ahs_ops = aa_diff"
    "set_op_filter ahs_ops = aa_filter"
    "set_op_inter ahs_ops = ahs_inter"
    "set_op_subset ahs_ops = aa_subset"
    "set_op_equal ahs_ops = aa_equal"
    "set_op_disjoint ahs_ops = aa_disjoint"
    "set_op_disjoint_witness ahs_ops = aa_disjoint_witness"
    "set_op_sel ahs_ops = ahs_sel'"
    "set_op_to_list ahs_ops = ahs_to_list"
    "set_op_from_list ahs_ops = list_to_ahs"
    by (auto simp add: ahs_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *} 
  interpretation ahsr!: set_iteratei "(set_op_\<alpha> ahs_ops)" "(set_op_invar ahs_ops)" ahs_iteratei using ahs_iteratei_impl[folded ahs_ops_unfold] .



(*--------------------------------------------*)
subsection "Array Set"
  definition "ias_ops = \<lparr>
    set_op_\<alpha> = ias_\<alpha>,
    set_op_invar = ias_invar,
    set_op_empty = ias_empty,
    set_op_sng = ias_sng,
    set_op_memb = ias_memb,
    set_op_ins = ias_ins,
    set_op_ins_dj = ias_ins_dj,
    set_op_delete = ias_delete,
    set_op_isEmpty = ias_isEmpty,
    set_op_isSng = ias_isSng,
    set_op_ball = ias_ball,
    set_op_bexists = ias_bexists,
    set_op_size = ias_size,
    set_op_size_abort = ias_size_abort,
    set_op_union = ias_union,
    set_op_union_dj = ias_union_dj,
    set_op_diff = isis_diff,
    set_op_filter = isis_filter,
    set_op_inter = ias_inter,
    set_op_subset = isis_subset,
    set_op_equal = isis_equal,
    set_op_disjoint = isis_disjoint,
    set_op_disjoint_witness = isis_disjoint_witness,
    set_op_sel = ias_sel',
    set_op_to_list = ias_to_list,
    set_op_from_list = list_to_ias
    \<rparr>"

  interpretation iasr!: StdSet ias_ops
    apply (rule StdSet.intro)
    apply (simp_all add: ias_ops_def)
    apply unfold_locales
    done

  lemma ias_ops_unfold[code_unfold]:
    "set_op_\<alpha> ias_ops = ias_\<alpha>"
    "set_op_invar ias_ops = ias_invar"
    "set_op_empty ias_ops = ias_empty"
    "set_op_sng ias_ops = ias_sng"
    "set_op_memb ias_ops = ias_memb"
    "set_op_ins ias_ops = ias_ins"
    "set_op_ins_dj ias_ops = ias_ins_dj"
    "set_op_delete ias_ops = ias_delete"
    "set_op_isEmpty ias_ops = ias_isEmpty"
    "set_op_isSng ias_ops = ias_isSng"
    "set_op_ball ias_ops = ias_ball"
    "set_op_bexists ias_ops = ias_bexists"
    "set_op_size ias_ops = ias_size"
    "set_op_size_abort ias_ops = ias_size_abort"
    "set_op_union ias_ops = ias_union"
    "set_op_union_dj ias_ops = ias_union_dj"
    "set_op_diff ias_ops = isis_diff"
    "set_op_filter ias_ops = isis_filter"
    "set_op_inter ias_ops = ias_inter"
    "set_op_subset ias_ops = isis_subset"
    "set_op_equal ias_ops = isis_equal"
    "set_op_disjoint ias_ops = isis_disjoint"
    "set_op_disjoint_witness ias_ops = isis_disjoint_witness"
    "set_op_sel ias_ops = ias_sel'"
    "set_op_to_list ias_ops = ias_to_list"
    "set_op_from_list ias_ops = list_to_ias"
    by (auto simp add: ias_ops_def)

  -- {* Required to set up unfold\_locales in contexts with additional iterators *} 
  interpretation iasr!: set_iteratei "(set_op_\<alpha> ias_ops)" "(set_op_invar ias_ops)" ias_iteratei using ias_iteratei_impl[folded ias_ops_unfold] .

end
