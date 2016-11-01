(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Computing Gr\"obner Bases\<close>

theory Computations
imports Groebner_Bases "../Polynomials/Poly_Lists" "~~/src/HOL/Library/AList"
begin

text \<open>We now compute concrete Gr\"obner bases w.r.t. both the purely lexicographic and the
  degree-lexicographic term order, making use of the implementation of multivariate polynomials in
  @{theory "Poly_Lists"}.\<close>

subsection \<open>Lexicographic Order\<close>

global_interpretation opp_lex: od_powerprod lex
  defines lex_strict = opp_lex.ord_strict
  and lp_lex = opp_lex.lp
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
  and gbaux_lex = opp_lex.gbaux
  and gb_lex = opp_lex.gb
apply standard
subgoal by (rule lex_refl)
subgoal by (erule lex_antisym, simp)
subgoal by (erule lex_trans, simp)
subgoal by (rule lex_lin)
subgoal by (rule lex_one_min)
subgoal by (erule lex_times_monotone)
done

subsubsection \<open>Computations\<close>

lemma
  "lp_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = PP [(X, 2), (Y, 1)]"
by eval

lemma
  "lc_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = 3"
by eval

lemma
  "tail_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) =
    MP [(PP [(X, 2), (Z, 3)], 1::rat)]"
by eval

lemma
  "higher_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) (PP [(X, 2)]) =
    MP [(PP [(X, 2), (Z, 3)], 1), (PP [(X,2), (Y,1)], 3)]"
by eval

lemma
  "ord_strict_lex
    (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
    (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)])"
by eval

lemma
  "rd_mult_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    (- 2, PP [(Y, 1), (Z, 1)])"
by eval

lemma
  "rd_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "rd_list_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "trd_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Y, 1), (Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 6)], - 8)]"
by eval

lemma
  "spoly_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Z, 2), (Y, 5)], - 2), (PP [(X, 2), (Z, 6)], - 2)]"
by eval

lemma
  "trdsp_lex
      [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]), (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    0"
by eval

lemma
  "up [] [MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]] (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)], MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)])]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]
    ] =
    [
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)],
    MP [(PP [(Y,2), (Z, 1)], 1), (PP [(Z, 3)], 2)]
   ]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], -1)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (1, -1)]
    ] =
    [
     MP [(PP [(X, 2)], - 1), (PP [(Y, 5)], 1)],
     MP [(PP [(Y, 3)], - 1), (PP [(X, 2), (Z, 1)], 1)],
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

lemma
  "gb_lex
    [
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)],
     MP [(PP [(Y, 2), (Z, 1)], 1::rat), (1, -1)]
    ] =
    [
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], - 1)],
     MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

subsection \<open>Degree-Lexicographic Order\<close>

global_interpretation opp_dlex: od_powerprod dlex
  defines dlex_strict = opp_dlex.ord_strict
  and lp_dlex = opp_dlex.lp
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
  and gbaux_dlex = opp_dlex.gbaux
  and gb_dlex = opp_dlex.gb
apply standard
subgoal by (rule dlex_refl)
subgoal by (erule dlex_antisym, simp)
subgoal by (erule dlex_trans, simp)
subgoal by (rule dlex_lin)
subgoal by (rule dlex_one_min)
subgoal by (erule dlex_times_monotone)
done

subsubsection \<open>Computations\<close>

lemma
  "lp_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = PP [(X, Suc (Suc 0)), (Y, Suc 0)]"
by eval

lemma
  "lc_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = 3"
by eval

lemma
  "tail_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = MP [(PP [(X, 2), (Z, 3)], 1)]"
by eval

lemma
  "higher_lex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) (PP [(X, 2)]) =
    MP [(PP [(X, 2), (Z, 3)], 1), (PP [(X, 2), (Y, 1)], 3)]"
by eval

lemma
  "ord_strict_lex
    (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
    (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)])"
by eval

lemma
  "rd_mult_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    (- 2, PP [(Y, 1), (Z, 1)])"
by eval

lemma
  "rd_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "rd_list_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 4)], 4)]"
by eval

lemma
  "trd_lex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Y, 1), (Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 1), (Z, 6)], - 8)]"
by eval

lemma
  "spoly_lex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Z, 2), (Y, 5)], - 2), (PP [(X, 2), (Z, 6)], - 2)]"
by eval

lemma
  "trdsp_lex
      [(MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]), (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    0"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)])
    ] =
    [
     MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)],
     MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)]
    ]"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 2), (Z, 2)], 1), (PP [(X, 1)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ] =
    [
     MP [(PP [(X, 2)], - 1), (PP [(Y, 4), (X, 1)], 1)],
     MP [(PP [(X, 1), (Y, 2)], - 1), (PP [(X, 2), (Z, 1)], 1)],
     MP [(PP [(X, 2), (Z, 2)], 1), (PP [(X, 1)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

text \<open>The following Gr\"obner basis differs from the one obtained w.r.t. the purely lexicographic
  term-order.\<close>

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ] =
    [
     MP [(PP [(X, 5)], - 1), (PP [(X, 1), (Z, 3)], 1)],
     MP [(PP [(X, 3), (Y, 1)], - 1), (PP [(X, 1), (Z, 1)], 1)],
     MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], - 1)], MP [(PP [(Y, 2), (Z, 1)], 1), (1, - 1)]
    ]"
by eval

lemma
  "gb_dlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ]
   \<noteq>
   gb_lex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ]"
by eval

end (* theory *)