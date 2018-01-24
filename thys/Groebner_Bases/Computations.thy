(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Computing Gr\"obner Bases\<close>

theory Computations
  imports
    Buchberger_Algorithm
    Polynomials.MPoly_Type_Class_FMap
begin

text \<open>We now compute concrete Gr\"obner bases w.r.t. both the purely lexicographic and the
  degree-lexicographic term order, making use of the implementation of multivariate polynomials in
  @{theory "MPoly_Type_Class_FMap"}.\<close>

subsection \<open>Lexicographic Order\<close>

global_interpretation opp_lex: gd_powerprod lex_pm lex_pm_strict
  defines lp_lex = opp_lex.lp
  and max_lex = opp_lex.ordered_powerprod_lin.max
  and list_max_lex = opp_lex.list_max
  and higher_lex = opp_lex.higher
  and lower_lex = opp_lex.lower
  and lc_lex = opp_lex.lc
  and tail_lex = opp_lex.tail
  and ord_lex = opp_lex.ord_p
  and ord_strict_lex = opp_lex.ord_strict_p
  and rd_mult_lex = opp_lex.rd_mult
  and rd_lex = opp_lex.rd
  and rd_list_lex = opp_lex.rd_list
  and trd_lex = opp_lex.trd
  and spoly_lex = opp_lex.spoly
  and trdsp_lex = opp_lex.trdsp
  and add_pairs_naive_lex = opp_lex.add_pairs_naive
  and add_pairs_sorted_lex = opp_lex.add_pairs_sorted
  and pairs_lex = opp_lex.pairs
  and product_crit_lex = opp_lex.product_crit
  and chain_crit_lex = opp_lex.chain_crit
  and comb_crit_lex = opp_lex.comb_crit
  and pc_crit_lex = opp_lex.pc_crit
  and gb_aux_lex = opp_lex.gb_aux
  and gb_lex = opp_lex.gb
  apply standard
  subgoal by (simp add: lex_pm_strict_def)
  subgoal by (rule lex_pm_refl)
  subgoal by (erule lex_pm_trans, simp)
  subgoal by (erule lex_pm_antisym, simp)
  subgoal by (rule lex_pm_lin)
  subgoal by (rule lex_pm_zero_min)
  subgoal by (erule lex_pm_plus_monotone)
  done

subsubsection \<open>Computations\<close>

context begin interpretation trivariate\<^sub>0_rat .

lemma
  "lp_lex (X\<^sup>2 * Z^3 + 3*X\<^sup>2*Y) = sparse\<^sub>0 [(0, 2), (1, 1)]"
  by eval

lemma
  "lc_lex (X\<^sup>2 * Z^3 + 3*X\<^sup>2*Y) = 3"
  by eval

lemma
  "tail_lex (X\<^sup>2 * Z^3 + 3*X\<^sup>2*Y) = X\<^sup>2 * Z^3"
  by eval

lemma
  "higher_lex (X\<^sup>2 * Z^3 + 3*X\<^sup>2*Y) (sparse\<^sub>0 [(0, 2)]) = X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
  by eval

lemma "ord_strict_lex (X\<^sup>2*Z^4 - 2*Y^3*Z\<^sup>2) (X\<^sup>2*Z^7 + 2 * Y^3*Z\<^sup>2)"
  by eval

lemma
  "rd_mult_lex (X\<^sup>2*Z^4 - 2*Y^3*Z\<^sup>2) (Y\<^sup>2*Z + 2*Z^3) = (- 2, sparse\<^sub>0 [(1, 1), (2, 1)])"
  by eval

lemma
  "rd_lex (X\<^sup>2*Z^4 - 2*Y^3*Z\<^sup>2) (Y\<^sup>2*Z + 2*Z^3) = X\<^sup>2*Z^4 + 4*Y*Z^4"
  by eval

lemma
  "rd_list_lex [Y\<^sup>2*Z + 2*Z^3] (X\<^sup>2*Z^4 - 2*Y^3*Z\<^sup>2) = X\<^sup>2*Z^4 + 4 * Y * Z^4"
  by eval

lemma
  "trd_lex
      [Y\<^sup>2 * Z + 2 * Y * Z ^ 3]
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X\<^sup>2 * Z ^ 4 + - 8 * Y * Z ^ 6"
  by eval

lemma
  "spoly_lex
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    - 2 * Z\<^sup>2 * Y ^ 5 + - 2 * X\<^sup>2 * Z ^ 6"
  by eval

lemma
  "trdsp_lex
      [X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2,
        Y\<^sup>2 * Z + 2 * Z ^ 3]
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    0"
  by eval


lemma
  "add_pairs_sorted_lex [] [X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2]
    (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    [(Y\<^sup>2 * Z + 2 * Z ^ 3,
     X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)]"
  by eval

lemma
  "gb_lex
    [
     X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2,
     Y\<^sup>2 * Z + 2 * Z ^ 3
    ] =
    [
      X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2,
      Y\<^sup>2 * Z + 2 * Z ^ 3
    ]"
  by eval

lemma
  "gb_lex
    [X\<^sup>2 * Z\<^sup>2 - Y,
     Y\<^sup>2 * Z - 1
    ] =
    [ - (Y^5) + X\<^sup>2,
      - (Y^3) + X\<^sup>2 * Z,
      X\<^sup>2 * Z\<^sup>2 - Y,
      Y\<^sup>2 * Z - 1
    ]"
  by eval

lemma
  "gb_lex
    [
     X ^ 3 -  X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1
    ] =
    [
     X ^ 3 -  X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1
    ]"
  by eval

end


subsection \<open>Degree-Lexicographic Order\<close>

global_interpretation opp_dlex: gd_powerprod dlex_pm dlex_pm_strict
  defines lp_dlex = opp_dlex.lp
  and max_dlex = opp_dlex.ordered_powerprod_lin.max
  and list_max_dlex = opp_dlex.list_max
  and higher_dlex = opp_dlex.higher
  and lower_dlex = opp_dlex.lower
  and lc_dlex = opp_dlex.lc
  and tail_dlex = opp_dlex.tail
  and ord_dlex = opp_dlex.ord_p
  and ord_strict_dlex = opp_dlex.ord_strict_p
  and rd_mult_dlex = opp_dlex.rd_mult
  and rd_dlex = opp_dlex.rd
  and rd_list_dlex = opp_dlex.rd_list
  and trd_dlex = opp_dlex.trd
  and spoly_dlex = opp_dlex.spoly
  and trdsp_dlex = opp_dlex.trdsp
  and add_pairs_naive_dlex = opp_dlex.add_pairs_naive
  and add_pairs_sorted_dlex = opp_dlex.add_pairs_sorted
  and pairs_dlex = opp_dlex.pairs
  and product_crit_dlex = opp_dlex.product_crit
  and chain_crit_dlex = opp_dlex.chain_crit
  and comb_crit_dlex = opp_dlex.comb_crit
  and pc_crit_dlex = opp_dlex.pc_crit
  and gb_aux_dlex = opp_dlex.gb_aux
  and gb_dlex = opp_dlex.gb
  apply standard
  subgoal by (simp add: dlex_pm_strict_def)
  subgoal by (rule dlex_pm_refl)
  subgoal by (erule dlex_pm_trans, simp)
  subgoal by (erule dlex_pm_antisym, simp)
  subgoal by (rule dlex_pm_lin)
  subgoal by (rule dlex_pm_zero_min)
  subgoal by (erule dlex_pm_plus_monotone)
  done

subsubsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "lp_lex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, Suc (Suc 0)), (1, Suc 0)]"
  by eval

lemma
  "lc_lex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3"
by eval

lemma
  "tail_lex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(sparse\<^sub>0 [(0, 2), (2, 3)], 1)]"
by eval

lemma
  "higher_lex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) (sparse\<^sub>0 [(0, 2)]) =
    X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
by eval

lemma
  "ord_strict_lex
    (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
    (X\<^sup>2 *Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
by eval

lemma
  "rd_mult_lex
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    (- 2, sparse\<^sub>0 [(1, 1), (2, 1)])"
by eval

lemma
  "rd_lex
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    X\<^sup>2*Z^4 + 4*Y*Z^4"
by eval

lemma
  "rd_list_lex
      [Y\<^sup>2 * Z + 2 * Z ^ 3]
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X\<^sup>2*Z^4 + 4*Y*Z^4"
by eval

lemma
  "trd_lex
      [Y\<^sup>2*Z + 2*Y*Z^3]
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X\<^sup>2 * Z ^ 4 + - 8 * Y * Z ^ 6"
by eval

lemma
  "spoly_lex
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    - 2 * Z\<^sup>2 * Y ^ 5 + - 2 * X\<^sup>2 * Z ^ 6"
by eval

lemma
  "trdsp_lex
      [(X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2), (Y\<^sup>2 * Z + 2 * Z ^ 3)]
      (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2)
      (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    0"
  by eval

lemma
  "gb_dlex
    [
     (X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2),
     (Y\<^sup>2 * Z + 2 * Z ^ 3)
    ] =
    [
     X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2,
     Y\<^sup>2 * Z + 2 * Z ^ 3
    ]"
  by eval

lemma
  "gb_dlex
    [
     (X\<^sup>2 * Z\<^sup>2 + - 1 * X),
     (Y\<^sup>2 * Z + - 1)
    ] =
    [
     -X*Y^4 + X\<^sup>2,
     - 1 * X * Y\<^sup>2 + X\<^sup>2 * Z,
     X\<^sup>2 * Z\<^sup>2 + - 1 * X,
     Y\<^sup>2 * Z + - 1
    ]"
  by eval

text \<open>The following Gr\"obner basis differs from the one obtained w.r.t. the purely lexicographic
  term-order.\<close>

lemma
  "gb_dlex
    [
     (X ^ 3 + - 1 * X * Y * Z\<^sup>2),
     (Y\<^sup>2 * Z + - 1)
    ] =
    [- 1 * X * Z ^ 3 + X ^ 5,
     - 1 * X ^ 3 * Y + X * Z,
    X ^ 3 + - 1 * X * Y * Z\<^sup>2,
    Y\<^sup>2 * Z + - 1]"
  by eval

lemma
  "gb_dlex
    [
     (X ^ 3 + - 1 * X * Y * Z\<^sup>2),
     (Y\<^sup>2 * Z + - 1)
    ]
   \<noteq>
   gb_lex
    [
     (X ^ 3 + - 1 * X * Y * Z\<^sup>2),
     (Y\<^sup>2 * Z + - 1)
    ]"
  by eval

end

end (* theory *)
