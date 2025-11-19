(*
 Title:Differential_Privacy_Randomized_Response.thy
 Last Updated: January 9, 2024
 Author: Tetsuya Sato
*)

theory Differential_Privacy_Randomized_Response
  imports"Differential_Privacy_Divergence"
begin

section \<open>Randomized Response Mechanism\<close>

definition RR_mechanism :: "real \<Rightarrow> bool \<Rightarrow> bool pmf"
  where "RR_mechanism \<epsilon> x =
 (if x then (bernoulli_pmf ((exp \<epsilon>) / (1 + exp \<epsilon>)))
 else (bernoulli_pmf (1 / (1 + exp \<epsilon>))))"

lemma meausrable_RR_mechanism[measurable]:
  shows "measure_pmf o (RR_mechanism \<epsilon>) \<in> measurable (count_space UNIV) (prob_algebra (count_space UNIV))"
proof(rule measurable_prob_algebraI)
  fix x :: bool
  show "prob_space ((measure_pmf \<circ> RR_mechanism \<epsilon>) x)"
    unfolding RR_mechanism_def using prob_space_measure_pmf if_split_mem1 by auto
  thus "measure_pmf \<circ> RR_mechanism \<epsilon> \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra (count_space UNIV)"
    unfolding RR_mechanism_def space_measure_pmf
    by (auto simp: measure_pmf_in_subprob_space)
qed

lemma RR_probability_flip1:
  fixes \<epsilon> :: real
  assumes "\<epsilon> \<ge> 0"
  shows "1 - 1 / (1 + exp \<epsilon>) = exp \<epsilon> / (1 + exp \<epsilon>)"
  using add_diff_cancel_left' add_divide_distrib div_self not_exp_less_zero square_bound_lemma vector_space_over_itself.scale_zero_left
  by metis

lemma RR_probability_flip2:
  fixes \<epsilon> :: real
  assumes "\<epsilon> \<ge> 0"
  shows "1- exp \<epsilon> / (1 + exp \<epsilon>) = 1 / (1 + exp \<epsilon>)"
  using RR_probability_flip1 assms
  by fastforce

lemma RR_mechanism_flip:
  assumes "\<epsilon> \<ge> 0"
  shows "bind_pmf (RR_mechanism \<epsilon> x) (\<lambda> b :: bool. return_pmf (\<not> b)) = (RR_mechanism \<epsilon> (\<not> x))"
  unfolding RR_mechanism_def
proof-
  have eq1: "bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>)) \<bind> (\<lambda>b. return_pmf (\<not> b)) = bernoulli_pmf (1 / (1 + exp \<epsilon>))"
  proof(rule pmf_eqI)
    fix i :: bool
    have "pmf (bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) \<bind> (\<lambda>b :: bool. return_pmf (\<not> b))) i = (\<integral>\<^sup>+x. (pmf ((\<lambda>b :: bool. return_pmf (\<not> b)) x) i) \<partial>(measure_pmf (bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)))))"
      using ennreal_pmf_bind by metis
    also have "... = ennreal (pmf (return_pmf (\<not> True)) i) * ennreal (exp \<epsilon> / (1 + exp \<epsilon>)) + ennreal (pmf (return_pmf (\<not> False)) i) * ennreal (1 - exp \<epsilon> / (1 + exp \<epsilon>))"
      by(rule nn_integral_bernoulli_pmf ; simp_all add: add_pos_nonneg)
    also have "... = ennreal (pmf (return_pmf True) i) * ennreal (1 - exp \<epsilon> / (1 + exp \<epsilon>)) + ennreal (pmf (return_pmf False) i) * ennreal (1- (1 - exp \<epsilon> / (1 + exp \<epsilon>)))"
      by auto
    also have "... = (\<integral>\<^sup>+x. (pmf (return_pmf x) i) \<partial>bernoulli_pmf (1 - exp \<epsilon> / (1 + exp \<epsilon>)))"
      by(rule nn_integral_bernoulli_pmf[where p ="(1 - exp \<epsilon> / (1 + exp \<epsilon>))",THEN sym] ; simp_all add: add_pos_nonneg)
    also have "... = pmf (bind_pmf (bernoulli_pmf (1 - exp \<epsilon> / (1 + exp \<epsilon>))) return_pmf) i"
      using ennreal_pmf_bind by metis
    also have "... = (pmf (bernoulli_pmf (1 - exp \<epsilon> / (1 + exp \<epsilon>))) i)"
      by (auto simp: bind_return_pmf')
    also have "... = (pmf (bernoulli_pmf (1 / (1 + exp \<epsilon>))) i)"
      by (metis add.commute add_diff_cancel_left' add_divide_distrib div_self not_exp_less_zero square_bound_lemma vector_space_over_itself.scale_zero_left)
    finally show "pmf (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>)) \<bind> (\<lambda>b. return_pmf (\<not> b))) i = pmf (bernoulli_pmf (1 / (1 + exp \<epsilon>))) i"by auto
  qed
  have eq2: "bernoulli_pmf (1 / (1 + exp \<epsilon>)) \<bind> (\<lambda>b. return_pmf (\<not> b)) = bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))"
  proof(rule pmf_eqI)
    fix i :: bool
    have "pmf (bernoulli_pmf (1/ ((1 :: real) + exp \<epsilon>)) \<bind> (\<lambda>b :: bool. return_pmf (\<not> b))) i = (\<integral>\<^sup>+x. (pmf ((\<lambda>b :: bool. return_pmf (\<not> b)) x) i) \<partial>(measure_pmf (bernoulli_pmf (1 / ((1 :: real) + exp \<epsilon>)))))"
      using ennreal_pmf_bind by metis
    also have "... = ennreal (pmf (return_pmf (\<not> True)) i) * ennreal (1 / (1 + exp \<epsilon>)) + ennreal (pmf (return_pmf (\<not> False)) i) * ennreal (1 - 1/ (1 + exp \<epsilon>))"
      by(rule nn_integral_bernoulli_pmf ; simp_all add: add_pos_nonneg)
    also have "... = ennreal (pmf (return_pmf True) i) * ennreal (exp \<epsilon> / (1 + exp \<epsilon>)) + ennreal (pmf (return_pmf False) i) * ennreal (1 - exp \<epsilon> / (1 + exp \<epsilon>))"
      by(auto simp:RR_probability_flip1 RR_probability_flip2 assms)
    also have "... = (\<integral>\<^sup>+x. (pmf (return_pmf x) i) \<partial>bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>)))"
      by(rule nn_integral_bernoulli_pmf[where p ="(exp \<epsilon> / (1 + exp \<epsilon>))",THEN sym] ; simp_all add: add_pos_nonneg)
    also have "... = pmf (bind_pmf (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) return_pmf) i"
      using ennreal_pmf_bind by metis
    also have "... = (pmf (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) i)"
      by (auto simp: bind_return_pmf')
    finally show "pmf (bernoulli_pmf (1/ ((1 :: real) + exp \<epsilon>)) \<bind> (\<lambda>b :: bool. return_pmf (\<not> b))) i = pmf (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) i"by auto
  qed
  show "(if x then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>))) \<bind> (\<lambda>b :: bool. return_pmf (\<not> b)) =
 (if \<not> x then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>)))"
    using eq1 eq2 by auto
qed

proposition DP_RR_mechanism:
  fixes \<epsilon> :: real and x y :: bool
  assumes "\<epsilon> > 0"
  shows "DP_divergence (RR_mechanism \<epsilon> x) (RR_mechanism \<epsilon> y) \<epsilon> \<le> (0 :: real)"
proof(subst DP_divergence_forall[THEN sym],unfold RR_mechanism_def)
  {
    fix A :: "bool set" assume "A \<in> measure_pmf.events (if x then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>)))"
    have ineq1: "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A"
      by (auto simp: assms leI mult_le_cancel_right1 order_less_imp_not_less)
    have ineq2: "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A"
      by (meson assms linorder_not_less measure_nonneg' mult_le_cancel_right1 nle_le one_le_exp_iff)
    consider"A = {}"|"A = {True}"|"A = {False}"|"A = {True,False}"
      by (metis (full_types) Set.set_insert all_not_in_conv insertI2)
    note split_A = this
    hence ineq3: "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A"
    proof(cases)
      case 1
      thus ?thesis by auto
    next
      case 2
      hence "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A = (exp \<epsilon> / (1 + exp \<epsilon>))"
        using pmf_bernoulli_True
        by (auto simp: pmf.rep_eq pos_add_strict)
      also have "... = exp \<epsilon> * (1 / (1 + exp \<epsilon>))"
        by auto
      also have "... = exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A"
        using pmf_bernoulli_True 2
        by (auto simp: pmf.rep_eq pos_add_strict)
      finally show ?thesis by auto
    next
      case 3
      hence "measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A = 1 - (exp \<epsilon> / (1 + exp \<epsilon>))"
        using pmf_bernoulli_False
        by (auto simp: pmf.rep_eq pos_add_strict)
      also have "... = (1 / (1 + exp \<epsilon>))"
        using RR_probability_flip2 assms by auto
      also have "... \<le> exp \<epsilon> * (exp \<epsilon> / (1 + exp \<epsilon>))"
        by (metis (no_types, opaque_lifting) add_le_same_cancel1 assms divide_right_mono dual_order.trans less_add_one linorder_not_less mult_exp_exp nle_le one_le_exp_iff times_divide_eq_right)
      also have "... = exp \<epsilon> * (measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A)"
      proof-
        have "(measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A) = 1 - (1 / (1 + exp \<epsilon>))"
          using pmf_bernoulli_False 3
          by (auto simp: pmf.rep_eq pos_add_strict)
        also have "... = exp \<epsilon> / (1 + exp \<epsilon>)"
          using RR_probability_flip1 assms by auto
        finally show ?thesis by auto
      qed
      thus ?thesis
        using calculation by auto
    next
      case 4
      hence "A = UNIV"
        by auto
      thus ?thesis
        using assms by fastforce
    qed
    from split_A
    have ineq4: "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A \<le> exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A"
    proof(cases)
      case 1
      thus ?thesis
        by auto
    next
      case 2
      hence "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A = (1 / (1 + exp \<epsilon>))"
        using pmf_bernoulli_True
        by (auto simp: pmf.rep_eq pos_add_strict)
      also have "... \<le> exp \<epsilon> * (exp \<epsilon> / (1 + exp \<epsilon>))"
        by (metis (no_types, opaque_lifting) add_le_same_cancel1 assms divide_right_mono dual_order.trans less_add_one linorder_not_less mult_exp_exp nle_le one_le_exp_iff times_divide_eq_right)
      also have "... = exp \<epsilon> * measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A"
        using pmf_bernoulli_True 2
        by (auto simp: pmf.rep_eq pos_add_strict)
      finally show ?thesis
        by auto
    next
      case 3
      hence "measure_pmf.prob (bernoulli_pmf (1 / (1 + exp \<epsilon>))) A = 1 - (1 / (1 + exp \<epsilon>))"
        using pmf_bernoulli_False
        by (auto simp: pmf.rep_eq pos_add_strict)
      also have "... = (exp \<epsilon> / (1 + exp \<epsilon>))"
        using RR_probability_flip1 assms by auto
      also have "... = exp \<epsilon> * (1 / (1 + exp \<epsilon>))"
        by auto
      also have "... = exp \<epsilon> * (measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A)"
      proof-
        have "(measure_pmf.prob (bernoulli_pmf (exp \<epsilon> / (1 + exp \<epsilon>))) A) = 1 - (exp \<epsilon> / (1 + exp \<epsilon>))"
          using pmf_bernoulli_False 3
          by (auto simp: pmf.rep_eq pos_add_strict)
        also have "... = 1 / (1 + exp \<epsilon>)"
          using RR_probability_flip2 assms by auto
        finally show ?thesis by auto
      qed
      thus ?thesis
        using calculation by auto
    next
      case 4
      hence "A = UNIV"
        by auto
      thus ?thesis
        using assms by fastforce
    qed
    note ineq1 ineq2 ineq3 ineq4
  }
  thus"\<forall>A :: bool set\<in>measure_pmf.events (if x then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>))). measure_pmf.prob (if x then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>))) A - exp \<epsilon> * measure_pmf.prob (if y then bernoulli_pmf (exp \<epsilon> / ((1 :: real) + exp \<epsilon>)) else bernoulli_pmf ((1 :: real) / ((1 :: real) + exp \<epsilon>))) A \<le> (0 :: real)"
    by auto
qed

end

