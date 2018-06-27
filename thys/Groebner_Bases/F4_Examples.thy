(* Author: Alexander Maletzky *)

section \<open>Sample Computations with the F4 Algorithm\<close>

theory F4_Examples
  imports F4 Algorithm_Schema_Impl Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
begin

text \<open>We only consider scalar polynomials here, but vector-polynomials could be handled, too.\<close>

lemma (in ordered_term) compute_keys_to_list [code]:
  "keys_to_list (Pm_fmap (fmap_of_list xs)) = rev (ord_term_lin.sort (keys_list xs))"
  by (simp add: keys_to_list_def compute_keys_alt pps_to_list_def distinct_keys_list
        distinct_remdups_id ord_term_lin.sorted_list_of_set_sort_remdups)

lemma (in term_powerprod) compute_list_to_poly [code]: "list_to_poly ts cs = sparse\<^sub>0 (zip ts cs)"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly sparse\<^sub>0_def list_to_fun_def
      fmlookup_default_def fmlookup_of_list)

lemma (in ordered_term) compute_Macaulay_list [code]:
  "Macaulay_list ps =
     (let ts = Keys_to_list ps in
      filter (\<lambda>p. p \<noteq> 0) (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))
     )"
  by (simp add: Macaulay_list_def Macaulay_mat_def Let_def)

declare conversep_iff [code]

derive (eq) ceq poly_mapping
derive (no) ccompare poly_mapping
derive (dlist) set_impl poly_mapping
derive (no) cenum poly_mapping

derive (eq) ceq rat
derive (no) ccompare rat
derive (dlist) set_impl rat
derive (no) cenum rat

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

global_interpretation drlex: gd_powerprod drlex_pm drlex_pm_strict
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"

  defines min_term_scalar_drlex = drlex.punit.min_term
  and lt_scalar_drlex = drlex.punit.lt
  and max_scalar_drlex = drlex.ordered_powerprod_lin.max
  and max_list_scalar_drlex = drlex.ordered_powerprod_lin.max_list
  and list_max_scalar_drlex = drlex.punit.list_max
  and higher_scalar_drlex = drlex.punit.higher
  and lower_scalar_drlex = drlex.punit.lower
  and lc_scalar_drlex = drlex.punit.lc
  and tail_scalar_drlex = drlex.punit.tail
  and ord_p_scalar_drlex = drlex.punit.ord_p
  and ord_strict_p_scalar_drlex = drlex.punit.ord_strict_p
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
  and part_key_scalar_drlex = drlex.ordered_powerprod_lin.part
  and sort_key_scalar_drlex = drlex.ordered_powerprod_lin.sort_key
  and pps_to_list_scalar_drlex = drlex.punit.pps_to_list
  and keys_to_list_scalar_drlex = drlex.punit.keys_to_list
  and Keys_to_list_scalar_drlex = drlex.punit.Keys_to_list
  and sym_preproc_addnew_scalar_drlex = drlex.punit.sym_preproc_addnew
  and sym_preproc_aux_scalar_drlex = drlex.punit.sym_preproc_aux
  and sym_preproc_scalar_drlex = drlex.punit.sym_preproc
  and Macaulay_mat_scalar_drlex = drlex.punit.Macaulay_mat
  and Macaulay_list_scalar_drlex = drlex.punit.Macaulay_list
  and pdata_pairs_to_list_scalar_drlex = drlex.punit.pdata_pairs_to_list
  and Macaulay_red_scalar_drlex = drlex.punit.Macaulay_red
  and f4_sel_aux_scalar_drlex = drlex.punit.f4_sel_aux
  and f4_sel_scalar_drlex = drlex.punit.f4_sel
  and f4_red_aux_scalar_drlex = drlex.punit.f4_red_aux
  and f4_red_scalar_drlex = drlex.punit.f4_red
  and f4_aux_scalar_drlex = drlex.punit.f4_aux_punit
  and f4_scalar_drlex = drlex.punit.f4_punit
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

subsubsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "lt_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "higher_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) (sparse\<^sub>0 [(0, 2)]) = X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_p_scalar_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "f4_scalar_drlex
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2 + 4 * Y ^ 3 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (X\<^sup>2 * Y ^ 4 * Z + 4 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "f4_scalar_drlex
    [
     (X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1, ()),
     (X * Y - Z - 1, ()),
     (Y\<^sup>2 + X, ()),
     (Z\<^sup>2 + X, ())
    ] () =
    [
     (1, ())
    ]"
  by eval

end

value [code] "length (f4_scalar_drlex (map (\<lambda>p. (p, ())) ((cyclic 4)::(_ \<Rightarrow>\<^sub>0 rat) list)) ())"

value [code] "length (f4_scalar_drlex (map (\<lambda>p. (p, ())) (Katsura 2)) ())"

end (* theory *)
