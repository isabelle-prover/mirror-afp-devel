section\<open>Results on lower bounds on additive energy\<close>

(*
  Session: Balog_Szemeredi_Gowers
  Title:   Additive_Energy_Lower_Bounds.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds 
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Additive_Energy_Lower_Bounds
  imports 
    Additive_Combinatorics_Preliminaries
    Miscellaneous_Lemmas
begin

context additive_abelian_group

begin

text\<open>The following corresponds to Proposition 2.11 in Gowers's notes \cite{Gowersnotes}.\<close>

proposition additive_energy_lower_bound_sumset: fixes C::real
  assumes "finite A" and "A \<subseteq> G" and "(card (sumset A A)) \<le> C * card A" and "card A \<noteq> 0"
  shows "additive_energy A \<ge> 1/C"

proof-
  have "(card A)^2 =  (\<Sum> x \<in> sumset A A. real (f_sum x A))"
   using assms f_sum_card by (metis of_nat_sum)
  also have "... \<le> (card((sumset A A)) powr(1/2)) * (\<Sum> x \<in> sumset A A . (f_sum x A)^2) powr(1/2)"
    using Cauchy_Schwarz_ineq_sum2[of "\<lambda> d. 1" "\<lambda> d. f_sum d A"] by auto
  also have "...\<le> ((C * (card A)) powr(1/2)) * ((\<Sum> x \<in> sumset A A . (f_sum x A)^2)) powr(1/2) "
    by (metis mult.commute mult_left_mono assms(3) of_nat_0_le_iff powr_ge_pzero powr_mono2 
        zero_le_divide_1_iff zero_le_numeral)
  finally have "((card A)^2)^2 \<le> (((C * (card A)) powr(1/2)) * ((\<Sum> x \<in> sumset A A . (f_sum x A)^2)) powr(1/2))^2"
    by (metis of_nat_0_le_iff of_nat_power_eq_of_nat_cancel_iff power_mono)
  then have "(card A)^4 \<le> (((C * (card A)) * ((\<Sum> x \<in> sumset A A. (f_sum x A)^2))) powr (1/2))^2"
    by (smt (verit) assms of_nat_0_le_iff powr_mult
      mult.left_commute power2_eq_square power3_eq_cube power4_eq_xxxx power_commutes)
  then have "(card A)^4 \<le> (( C * (card A)) * ((\<Sum> x \<in> sumset A A. (f_sum x A)^2)))"
    using assms powr_half_sqrt of_nat_0 of_nat_le_0_iff power_mult_distrib 
      real_sqrt_pow2 by (smt (verit, best) powr_mult)
  moreover have "additive_energy A =  (\<Sum> x \<in> sumset A A. (f_sum x A)^2)/ (card A)^3" 
    using additive_energy_def f_sum_card_quadruple_set assms by simp
  moreover then have "additive_energy A * (card A)^3 = (\<Sum> x \<in> sumset A A. (f_sum x A)^2)"
    using assms by simp
  ultimately have "(additive_energy A) \<ge> ((card A)^4)/ ( C * (card A)^4 )"
    using additive_energy_upper_bound 
      additive_abelian_group_axioms assms divide_le_eq divide_le_eq_1_pos mult.left_commute 
      mult_left_mono of_nat_0_eq_iff of_nat_0_le_iff power_eq_0_iff power3_eq_cube power4_eq_xxxx 
      linorder_not_less mult.assoc mult_zero_left of_nat_0_less_iff of_nat_mult 
      order_trans_rules(23) times_divide_eq_right by (smt (verit) card_sumset_0_iff 
      div_by_1 mult_cancel_left1 nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_right 
      nonzero_mult_divide_mult_cancel_right2 of_nat_1 of_nat_le_0_iff times_divide_eq_left)
   then show ?thesis by (simp add: assms)
qed


text\<open>An analogous version of Proposition 2.11 where the assumption is on a difference set is given 
below. The proof is identical to the proof of @{term additive_energy_lower_bound_sumset}
above (with the obvious modifications). \<close>

proposition additive_energy_lower_bound_differenceset: fixes C::real
  assumes "finite A" and "A \<subseteq> G" and "(card (differenceset A A)) \<le> C * card A" and "card A \<noteq> 0"
  shows "additive_energy A \<ge> 1/C"

proof-
  have "(card A)^2 =  (\<Sum> x \<in> differenceset A A. real (f_diff x A))"
   using assms f_diff_card by (metis of_nat_sum)
  also have "... \<le> (card((differenceset A A)) powr (1/2)) * (\<Sum> x \<in> differenceset A A . (f_diff x A)^2) powr(1/2)"
    using Cauchy_Schwarz_ineq_sum2[of "\<lambda> d. 1" "\<lambda> d. f_diff d A"] by auto
  also have "...\<le> ((C * (card A))powr (1/2)) * ((\<Sum> x \<in> differenceset A A . (f_diff x A)^2)) powr(1/2)"
    by (metis mult.commute mult_left_mono assms(3) of_nat_0_le_iff powr_ge_pzero powr_mono2 
        zero_le_divide_1_iff zero_le_numeral)
  finally have "((card A)^2)^2 \<le> (((C * (card A))powr (1/2)) * ((\<Sum> x \<in> differenceset A A . (f_diff x A)^2)) powr(1/2))^2"
    by (metis of_nat_0_le_iff of_nat_power_eq_of_nat_cancel_iff power_mono)
  then have "(card A)^4 \<le> (((C * (card A)) * ((\<Sum> x \<in> differenceset A A. (f_diff x A)^2))) powr (1/2))^2"
    by (smt (verit) assms of_nat_0_le_iff powr_mult
      mult.left_commute power2_eq_square power3_eq_cube power4_eq_xxxx power_commutes)
  then have "(card A)^4 \<le> ((C * (card A)) * ((\<Sum> x \<in> differenceset A A . (f_diff x A)^2)))"
    using assms powr_half_sqrt of_nat_0 of_nat_le_0_iff power_mult_distrib 
      real_sqrt_pow2 by (smt (verit, best) powr_mult)
  moreover have "additive_energy A =  (\<Sum> x \<in> differenceset A A. (f_diff x A)^2)/ (card A)^3" 
    using additive_energy_def f_diff_card_quadruple_set assms by simp
  moreover then have "additive_energy A * (card A)^3 = (\<Sum> x \<in> differenceset A A. (f_diff x A)^2)"
    using assms by simp
  ultimately have "(additive_energy A) \<ge> ((card A)^4)/ (C * (card A)^4 )"
    using additive_energy_upper_bound 
      additive_abelian_group_axioms assms divide_le_eq divide_le_eq_1_pos mult.left_commute 
      mult_left_mono of_nat_0_eq_iff of_nat_0_le_iff power_eq_0_iff power3_eq_cube power4_eq_xxxx 
      linorder_not_less mult.assoc mult_zero_left of_nat_0_less_iff of_nat_mult 
      order_trans_rules(23) times_divide_eq_right by (smt (verit) card_sumset_0_iff 
      div_by_1 mult_cancel_left1 nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_right 
      nonzero_mult_divide_mult_cancel_right2 of_nat_1 of_nat_le_0_iff times_divide_eq_left)
   then show ?thesis by (simp add: assms)
qed

end
end