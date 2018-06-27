theory Reduced_GB_Examples
  imports Buchberger Reduced_GB Polynomials.MPoly_Type_Class_FMap
begin

context gd_term
begin

definition rgb :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb bs = comp_red_monic_basis (map fst (gb (map (\<lambda>b. (b, ())) bs) ()))"

definition rgb_punit :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb_punit bs = punit.comp_red_monic_basis (map fst (gb_punit (map (\<lambda>b. (b, ())) bs) ()))"

end

text \<open>We only consider scalar polynomials here, but vector-polynomials could be handled, too.\<close>

global_interpretation drlex: gd_powerprod drlex_pm drlex_pm_strict
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"

  defines min_term_scalar_drlex = drlex.punit.min_term
  and lt_scalar_drlex = drlex.punit.lt
  and max_scalar_drlex = drlex.ordered_powerprod_lin.max
  and list_max_scalar_drlex = drlex.punit.list_max
  and higher_scalar_drlex = drlex.punit.higher
  and lower_scalar_drlex = drlex.punit.lower
  and lc_scalar_drlex = drlex.punit.lc
  and tail_scalar_drlex = drlex.punit.tail
  and ord_p_scalar_drlex = drlex.punit.ord_p
  and ord_strict_p_scalar_drlex = drlex.punit.ord_strict_p
  and find_adds_scalar_drlex = drlex.punit.find_adds
  and trd_aux_scalar_drlex = drlex.punit.trd_aux
  and trd_scalar_drlex = drlex.punit.trd
  and spoly_scalar_drlex = drlex.punit.spoly
  and count_const_lt_components_scalar_drlex = drlex.punit.count_const_lt_components
  and count_rem_components_scalar_drlex = drlex.punit.count_rem_components
  and const_lt_component_scalar_drlex = drlex.punit.const_lt_component
  and full_gb_scalar_drlex = drlex.punit.full_gb
  and add_pairs_single_sorted_scalar_drlex = drlex.punit.add_pairs_single_sorted
  and add_pairs_scalar_drlex = drlex.punit.add_pairs
  and canon_pair_order_aux_scalar_drlex = drlex.punit.canon_pair_order_aux
  and canon_basis_order_scalar_drlex = drlex.punit.canon_basis_order
  and new_pairs_sorted_scalar_drlex = drlex.punit.new_pairs_sorted
  and product_crit_scalar_drlex = drlex.punit.product_crit
  and chain_ncrit_scalar_drlex = drlex.punit.chain_ncrit
  and chain_ocrit_scalar_drlex = drlex.punit.chain_ocrit
  and apply_icrit_scalar_drlex = drlex.punit.apply_icrit
  and apply_ncrit_scalar_drlex = drlex.punit.apply_ncrit
  and apply_ocrit_scalar_drlex = drlex.punit.apply_ocrit
  and trdsp_scalar_drlex = drlex.punit.trdsp
  and gb_sel_scalar_drlex = drlex.punit.gb_sel
  and gb_red_aux_scalar_drlex = drlex.punit.gb_red_aux
  and gb_red_scalar_drlex = drlex.punit.gb_red
  and gb_aux_scalar_drlex = drlex.punit.gb_aux_punit
  and gb_scalar_drlex = drlex.punit.gb_punit
  and comp_min_basis_pre_scalar_drlex = drlex.punit.comp_min_basis_pre
  and comp_min_basis_aux_scalar_drlex = drlex.punit.comp_min_basis_aux
  and comp_min_basis_scalar_drlex = drlex.punit.comp_min_basis
  and comp_red_basis_aux_scalar_drlex = drlex.punit.comp_red_basis_aux
  and comp_red_basis_scalar_drlex = drlex.punit.comp_red_basis
  and monic_scalar_drlex = drlex.punit.monic
  and comp_red_monic_basis_scalar_drlex = drlex.punit.comp_red_monic_basis
  and rgb_scalar_drlex = drlex.punit.rgb_punit
proof -
  show "gd_powerprod drlex_pm drlex_pm_strict"
    apply standard
    subgoal by (simp add: drlex_pm_strict_def)
    subgoal by (rule drlex_pm_refl)
    subgoal by (erule drlex_pm_trans, simp)
    subgoal by (erule drlex_pm_antisym, simp)
    subgoal by (rule drlex_pm_lin)
    subgoal by (rule drlex_pm_zero_min)
    subgoal by (erule drlex_pm_plus_monotone)
    done
  show "punit.adds_term = (adds)" by (fact punit_adds_term)
  show "punit.pp_of_term = (\<lambda>x. x)" by (fact punit_pp_of_term)
  show "punit.component_of_term = (\<lambda>_. ())" by (fact punit_component_of_term)
  show "punit.monom_mult = monom_mult_punit" by (simp only: monom_mult_punit_def)
  show "punit.mult_scalar = mult_scalar_punit" by (simp only: mult_scalar_punit_def)
qed

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "rgb_scalar_drlex
    [
     X ^ 3 - X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1
    ] =
    [
     X ^ 3 * Y - X * Z,
     - (X ^ 3) + X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1,
     - (X * Z ^ 3) + X ^ 5
    ]"
  by eval

lemma
  "rgb_scalar_drlex
    [
     X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1,
     X * Y - Z - 1,
     Y\<^sup>2 + X,
     Z\<^sup>2 + X
    ] =
    [
     1
    ]"
  by eval

text \<open>Note: The above computations have been cross-checked with Mathematica 11.1.\<close>

end

end (* theory *)
