header {* \isaheader{Record-Based Set Interface: Implementation setup} *}
theory RecordSetImpl
imports 
  StdInst
begin

(*--------------------------------------------*)
subsection "List Set"

  definition "ls_ops = \<lparr>
    set_op_\<alpha> = ls_\<alpha>,
    set_op_invar = ls_invar,
    set_op_empty = ls_empty,
    set_op_memb = ls_memb,
    set_op_ins = ls_ins,
    set_op_ins_dj = ls_ins_dj,
    set_op_delete = ls_delete,
    set_op_isEmpty = ls_isEmpty,
    set_op_ball = ls_ball,
    set_op_size = ls_size,
    set_op_union = ls_union,
    set_op_union_dj = ls_union_dj,
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
    "set_op_memb ls_ops = ls_memb"
    "set_op_ins ls_ops = ls_ins"
    "set_op_ins_dj ls_ops = ls_ins_dj"
    "set_op_delete ls_ops = ls_delete"
    "set_op_isEmpty ls_ops = ls_isEmpty"
    "set_op_ball ls_ops = ls_ball"
    "set_op_size ls_ops = ls_size"
    "set_op_union ls_ops = ls_union"
    "set_op_union_dj ls_ops = ls_union_dj"
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
  interpretation lsr!: set_iterate "(set_op_\<alpha> ls_ops)" "(set_op_invar ls_ops)" ls_iterate using ls_iterate_impl[folded ls_ops_unfold] .
  
  interpretation lsr!: set_iteratei "(set_op_\<alpha> ls_ops)" "(set_op_invar ls_ops)" ls_iteratei using ls_iteratei_impl[folded ls_ops_unfold] .



(*--------------------------------------------*)
subsection "RBT Set"
  definition rs_ops :: "('x :: linorder, 'x rs) oset_ops"
  where "rs_ops = \<lparr>
    set_op_\<alpha> = rs_\<alpha>,
    set_op_invar = rs_invar,
    set_op_empty = rs_empty,
    set_op_memb = rs_memb,
    set_op_ins = rs_ins,
    set_op_ins_dj = rs_ins_dj,
    set_op_delete = rs_delete,
    set_op_isEmpty = rs_isEmpty,
    set_op_ball = rs_ball,
    set_op_size = rs_size,
    set_op_union = rs_union,
    set_op_union_dj = rs_union_dj,
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
    "set_op_memb rs_ops = rs_memb"
    "set_op_ins rs_ops = rs_ins"
    "set_op_ins_dj rs_ops = rs_ins_dj"
    "set_op_delete rs_ops = rs_delete"
    "set_op_isEmpty rs_ops = rs_isEmpty"
    "set_op_ball rs_ops = rs_ball"
    "set_op_size rs_ops = rs_size"
    "set_op_union rs_ops = rs_union"
    "set_op_union_dj rs_ops = rs_union_dj"
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
  interpretation rsr!: set_iterate "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iterate
    unfolding rs_ops_unfold
    using rs_iterate_impl .

  interpretation rsr!: set_iteratei "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iteratei
    unfolding rs_ops_unfold
    using rs_iteratei_impl .
  
  interpretation rsr!: set_iterateo "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iterateo
    unfolding rs_ops_unfold
    using rs_iterateo_impl .

  interpretation rsr!: set_iterateoi "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_iterateoi
    unfolding rs_ops_unfold
    using rs_iterateoi_impl .

  interpretation rsr!: set_reverse_iterateo "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_reverse_iterateo
    unfolding rs_ops_unfold
    using rs_reverse_iterateo_impl .

  interpretation rsr!: set_reverse_iterateoi "(set_op_\<alpha> rs_ops)" "(set_op_invar rs_ops)" rs_reverse_iterateoi
    unfolding rs_ops_unfold
    using rs_reverse_iterateoi_impl .



(*--------------------------------------------*)
subsection "HashSet"
  definition "hs_ops = \<lparr>
    set_op_\<alpha> = hs_\<alpha>,
    set_op_invar = hs_invar,
    set_op_empty = hs_empty,
    set_op_memb = hs_memb,
    set_op_ins = hs_ins,
    set_op_ins_dj = hs_ins_dj,
    set_op_delete = hs_delete,
    set_op_isEmpty = hs_isEmpty,
    set_op_ball = hs_ball,
    set_op_size = hs_size,
    set_op_union = hs_union,
    set_op_union_dj = hs_union_dj,
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
    "set_op_memb hs_ops = hs_memb"
    "set_op_ins hs_ops = hs_ins"
    "set_op_ins_dj hs_ops = hs_ins_dj"
    "set_op_delete hs_ops = hs_delete"
    "set_op_isEmpty hs_ops = hs_isEmpty"
    "set_op_ball hs_ops = hs_ball"
    "set_op_size hs_ops = hs_size"
    "set_op_union hs_ops = hs_union"
    "set_op_union_dj hs_ops = hs_union_dj"
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
  interpretation hsr!: set_iterate "(set_op_\<alpha> hs_ops)" "(set_op_invar hs_ops)" hs_iterate using hs_iterate_impl[folded hs_ops_unfold] .
  
  interpretation hsr!: set_iteratei "(set_op_\<alpha> hs_ops)" "(set_op_invar hs_ops)" hs_iteratei using hs_iteratei_impl[folded hs_ops_unfold] .


(*--------------------------------------------*)
(* TODO: @Peter Wieder Einfügen, wenn StdInst mit Tries funktioniert 
subsection "Trie Set"
  definition "ts_ops = \<lparr>
    set_op_\<alpha> = ts_\<alpha>,
    set_op_invar = ts_invar,
    set_op_empty = ts_empty,
    set_op_memb = ts_memb,
    set_op_ins = ts_ins,
    set_op_ins_dj = ts_ins_dj,
    set_op_delete = ts_delete,
    set_op_isEmpty = ts_isEmpty,
    set_op_ball = ts_ball,
    set_op_size = ts_size,
    set_op_union = ts_union,
    set_op_union_dj = ts_union_dj,
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
    "set_op_memb ts_ops = ts_memb"
    "set_op_ins ts_ops = ts_ins"
    "set_op_ins_dj ts_ops = ts_ins_dj"
    "set_op_delete ts_ops = ts_delete"
    "set_op_isEmpty ts_ops = ts_isEmpty"
    "set_op_ball ts_ops = ts_ball"
    "set_op_size ts_ops = ts_size"
    "set_op_union ts_ops = ts_union"
    "set_op_union_dj ts_ops = ts_union_dj"
    "set_op_inter ts_ops = ts_inter"
    "set_op_subset ts_ops = tt_subset"
    "set_op_equal ts_ops = tt_equal"
    "set_op_disjoint ts_ops = tt_disjoint"
    "set_op_disjoint_witness ts_ops = tt_disjoint_witness"
    "set_op_sel ts_ops = ts_sel'"
    "set_op_to_list ts_ops = ts_to_list"
    "set_op_from_list ts_ops = list_to_ts"
    by (auto simp add: ts_ops_def)

  -- "Required to set up unfold_locales in contexts with additional iterators"
  interpretation tsr!: set_iterate "(set_op_\<alpha> ts_ops)" "(set_op_invar ts_ops)" ts_iterate using ts_iterate_impl[folded ts_ops_unfold] .
  
  interpretation tsr!: set_iteratei "(set_op_\<alpha> ts_ops)" "(set_op_invar ts_ops)" ts_iteratei using ts_iteratei_impl[folded ts_ops_unfold] .
*)

(*--------------------------------------------*)
subsection "Array Hash Set"
  definition "ahs_ops = \<lparr>
    set_op_\<alpha> = ahs_\<alpha>,
    set_op_invar = ahs_invar,
    set_op_empty = ahs_empty,
    set_op_memb = ahs_memb,
    set_op_ins = ahs_ins,
    set_op_ins_dj = ahs_ins_dj,
    set_op_delete = ahs_delete,
    set_op_isEmpty = ahs_isEmpty,
    set_op_ball = ahs_ball,
    set_op_size = ahs_size,
    set_op_union = ahs_union,
    set_op_union_dj = ahs_union_dj,
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
    "set_op_memb ahs_ops = ahs_memb"
    "set_op_ins ahs_ops = ahs_ins"
    "set_op_ins_dj ahs_ops = ahs_ins_dj"
    "set_op_delete ahs_ops = ahs_delete"
    "set_op_isEmpty ahs_ops = ahs_isEmpty"
    "set_op_ball ahs_ops = ahs_ball"
    "set_op_size ahs_ops = ahs_size"
    "set_op_union ahs_ops = ahs_union"
    "set_op_union_dj ahs_ops = ahs_union_dj"
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
  interpretation ahsr!: set_iterate "(set_op_\<alpha> ahs_ops)" "(set_op_invar ahs_ops)" ahs_iterate using ahs_iterate_impl[folded ahs_ops_unfold] .
  
  interpretation ahsr!: set_iteratei "(set_op_\<alpha> ahs_ops)" "(set_op_invar ahs_ops)" ahs_iteratei using ahs_iteratei_impl[folded ahs_ops_unfold] .

end
