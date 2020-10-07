(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "More Lemmas on Division"

theory More_Divides
imports Main
begin

lemma div_mult_le:
  \<open>a div b * b \<le> a\<close> for a b :: nat
  by (fact div_times_less_eq_dividend)

lemma diff_mod_le:
  \<open>a - a mod b \<le> d - b\<close> if \<open>a < d\<close> \<open>b dvd d\<close> for a b d :: nat
  using that
  apply(subst minus_mod_eq_mult_div)
  apply(clarsimp simp: dvd_def)
  apply(cases \<open>b = 0\<close>)
   apply simp
  apply(subgoal_tac "a div b \<le> k - 1")
   prefer 2
   apply(subgoal_tac "a div b < k")
    apply(simp add: less_Suc_eq_le [symmetric])
   apply(subgoal_tac "b * (a div b) < b * ((b * k) div b)")
    apply clarsimp
   apply(subst div_mult_self1_is_m)
    apply arith
   apply(rule le_less_trans)
    apply simp
    apply(subst mult.commute)
    apply(rule div_mult_le)
   apply assumption
  apply clarsimp
  apply(subgoal_tac "b * (a div b) \<le> b * (k - 1)")
   apply(erule le_trans)
   apply(simp add: diff_mult_distrib2)
  apply simp
  done

lemma int_div_same_is_1 [simp]:
  \<open>a div b = a \<longleftrightarrow> b = 1\<close> if \<open>0 < a\<close> for a b :: int
  using that by (metis div_by_1 abs_ge_zero abs_of_pos int_div_less_self neq_iff
            nonneg1_imp_zdiv_pos_iff zabs_less_one_iff)

lemma int_div_minus_is_minus1 [simp]:
  \<open>a div b = - a \<longleftrightarrow> b = - 1\<close> if \<open>0 > a\<close> for a b :: int
  using that by (metis div_minus_right equation_minus_iff int_div_same_is_1 neg_0_less_iff_less)

declare div_eq_dividend_iff [simp]

end
