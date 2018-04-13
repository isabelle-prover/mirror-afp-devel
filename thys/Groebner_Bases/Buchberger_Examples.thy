(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports Buchberger Algorithm_Schema_Impl
begin

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

global_interpretation opp_drlex: gd_powerprod drlex_pm drlex_pm_strict
  defines lp_drlex = opp_drlex.lp
  and max_drlex = opp_drlex.ordered_powerprod_lin.max
  and list_max_drlex = opp_drlex.list_max
  and higher_drlex = opp_drlex.higher
  and lower_drlex = opp_drlex.lower
  and lc_drlex = opp_drlex.lc
  and tail_drlex = opp_drlex.tail
  and ord_drlex = opp_drlex.ord_p
  and ord_strict_drlex = opp_drlex.ord_strict_p
  and rd_mult_drlex = opp_drlex.rd_mult
  and rd_drlex = opp_drlex.rd
  and rd_list_drlex = opp_drlex.rd_list
  and trd_drlex = opp_drlex.trd
  and spoly_drlex = opp_drlex.spoly
  and canon_pair_order_drlex = opp_drlex.canon_pair_order
  and canon_basis_order_drlex = opp_drlex.canon_basis_order
  and product_crit_drlex = opp_drlex.product_crit
  and chain_crit_drlex = opp_drlex.chain_crit
  and comb_crit_drlex = opp_drlex.comb_crit
  and pc_crit_drlex = opp_drlex.pc_crit
  and discard_crit_pairs_aux_drlex = opp_drlex.discard_crit_pairs_aux
  and discard_crit_pairs_drlex = opp_drlex.discard_crit_pairs
  and discard_red_cp_drlex = opp_drlex.discard_red_cp
  and trdsp_drlex = opp_drlex.trdsp
  and gb_sel_drlex = opp_drlex.gb_sel
  and gb_red_aux_drlex = opp_drlex.gb_red_aux
  and gb_red_drlex = opp_drlex.gb_red
  and gb_aux_drlex = opp_drlex.gb_aux
  and gb_drlex = opp_drlex.gb
  apply standard
  subgoal by (simp add: drlex_pm_strict_def)
  subgoal by (rule drlex_pm_refl)
  subgoal by (erule drlex_pm_trans, simp)
  subgoal by (erule drlex_pm_antisym, simp)
  subgoal by (rule drlex_pm_lin)
  subgoal by (rule drlex_pm_zero_min)
  subgoal by (erule drlex_pm_plus_monotone)
  done

subsubsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "lp_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "higher_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) (sparse\<^sub>0 [(0, 2)]) = X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "rd_mult_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    Some (1 / 2, sparse\<^sub>0 [(0, 2), (2, 1)])"
  by eval

lemma
  "rd_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    (-2 * Y ^ 3 * Z\<^sup>2 - Const\<^sub>0 (1 / 2) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, True)"
  by eval

lemma
  "rd_list_drlex [Y\<^sup>2 * Z + 2 * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) =
    (-2 * Y ^ 3 * Z\<^sup>2 - Const\<^sub>0 (1 / 2) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, True)"
  by eval

lemma
  "trd_drlex [Y\<^sup>2 * Z + 2 * Y * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) =
    (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "spoly_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    -2 * Y ^ 3 * Z\<^sup>2 - (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2"
  by eval

lemma
  "gb_drlex
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (-2 * Y ^ 3 * Z\<^sup>2 - (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (- (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y ^ 4 * Z - 2 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "gb_drlex
    [
     (X\<^sup>2 * Z\<^sup>2 - Y, ()),
     (Y\<^sup>2 * Z - 1, ())
    ] () =
    [
     (- (Y ^ 3) + X\<^sup>2 * Z, ()),
     (X\<^sup>2 * Z\<^sup>2 - Y, ()),
     (Y\<^sup>2 * Z - 1, ())
    ]"
  by eval

lemma
  "gb_drlex
    [
     (X ^ 3 - X * Y * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z - 1, ())
    ] () =
    [
     (- (X ^ 3 * Y) + X * Z, ()),
     (X ^ 3 - X * Y * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z - 1, ()),
     (- (X * Z ^ 3) + X ^ 5, ())
    ]"
  by eval

lemma
  "gb_drlex
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

value [code] "gb_drlex (map (\<lambda>p. (p, ())) (cyclic 4)) ()"

value [code] "gb_drlex (map (\<lambda>p. (p, ())) (Katsura 2)) ()"

end (* theory *)
