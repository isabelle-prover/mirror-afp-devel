section \<open>Auxiliary Facts\<close>

theory Auxilary_Facts
  imports
    "Sigmoid_Universal_Approximation.Limits_Higher_Order_Derivatives"   
begin

subsection \<open>Differentiation Lemmas\<close>

lemma has_derivative_imp:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x)"
  shows "f differentiable (at x) \<and> deriv f x = f' 1"
proof safe
  show "f differentiable at x"
    by (meson assms differentiableI)
  then show "deriv f x = f' 1"
    by (metis DERIV_deriv_iff_real_differentiable assms has_derivative_unique 
        has_field_derivative_imp_has_derivative mult.comm_neutral)
qed

lemma DERIV_inverse_func:
  assumes "x \<noteq> 0"
  shows "DERIV (\<lambda>w. 1 / w) x :> -1 / x^2"
proof -
  have "inverse = (/) (1::'a)"
    using inverse_eq_divide by auto
  then show ?thesis
    by (metis (no_types) DERIV_inverse assms divide_minus_left numeral_2_eq_2 power_one_over)
qed

lemma power_rule:
  fixes z :: real  and  n :: nat
  shows "deriv (\<lambda>x. x ^ n) z = (if n = 0 then 0 else real n * z ^ (n - 1))"
  by(subst deriv_pow, simp_all)


subsubsection \<open>Transfer Lemmas\<close>

\<comment> \<open>The following pair of results are similar to @{thm has_field_derivative_transform_within_open}  
    and @{thm has_derivative_at_within}, but more applicable to the Euclidean setting.\<close>

lemma has_derivative_transfer_on_ball:
  fixes f g :: "real \<Rightarrow> real"
  assumes eps_gt0: "0 < \<epsilon>"
  assumes eq_on_ball: "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
  assumes f_has_deriv: "(f has_derivative D) (at x)"
  shows "(g has_derivative D) (at x)"
  using centre_in_ball eps_gt0 eq_on_ball f_has_deriv
    has_derivative_transform_within_open by blast

corollary field_differentiable_transfer_on_ball:
  fixes f g :: "real \<Rightarrow> real"
  assumes "0 < \<epsilon>"
  assumes eq_on_ball: "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
  assumes f_diff: "f field_differentiable at x"
  shows "g field_differentiable at x"
  by (metis UNIV_I assms dist_commute_lessI
      field_differentiable_transform_within mem_ball)

subsection \<open>Trigonometric Contraction\<close>

lemma cos_contractive:
  fixes x y :: real
  shows "\<bar>cos x - cos y\<bar> \<le> \<bar>x - y\<bar>"
proof -
  have "\<bar>cos x - cos y\<bar> = \<bar>-2 * sin ((x + y) / 2) * sin ((x - y) / 2)\<bar>"
    by (smt (verit) cos_diff_cos mult_minus_left)
  also have "... \<le> \<bar>sin ((x + y) / 2)\<bar> * (2* \<bar>sin ((x - y) / 2)\<bar>)"
    by (subst abs_mult, force)
  also have "... \<le> 2 * \<bar>sin ((x - y) / 2)\<bar>"
  proof - 
    have "\<bar>sin ((x + y) / 2)\<bar> \<le> 1"
      using abs_sin_le_one by blast
    then have "\<bar>sin ((x + y) / 2)\<bar> * (2* \<bar>sin ((x - y) / 2)\<bar>) \<le> 1 * (2* \<bar>sin ((x - y) / 2)\<bar>)"
      by(rule mult_right_mono, simp)
    then show ?thesis
      by linarith
  qed
  also have "... \<le> 2 * \<bar>(x - y) / 2\<bar>"
    using abs_sin_le_one by (smt (verit, del_insts) abs_sin_x_le_abs_x)
  also have "... = \<bar>x - y\<bar>"
    by simp
  finally show ?thesis.
qed

lemma sin_contractive:
  fixes x y :: real
  shows "\<bar>sin x - sin y\<bar> \<le> \<bar>x - y\<bar>"
proof -
  have "\<bar>sin x - sin y\<bar> = \<bar>2 * cos ((x + y) / 2) * sin ((x - y) / 2)\<bar>"
    by (metis (no_types) mult.assoc mult.commute sin_diff_sin)    
  also have "... \<le> \<bar>cos ((x + y) / 2)\<bar> * (2 * \<bar>sin ((x - y) / 2)\<bar>)"
    by (subst abs_mult, force)
  also have "... \<le> 2 * \<bar>sin ((x - y) / 2)\<bar>"
  proof -
    have "\<bar>cos ((x + y) / 2)\<bar> \<le> 1"
      using abs_cos_le_one by blast
    then have "\<bar>cos ((x + y) / 2)\<bar> * (2 * \<bar>sin ((x - y) / 2)\<bar>) \<le> 1 * (2 * \<bar>sin ((x - y) / 2)\<bar>)"
      by (rule mult_right_mono, simp)
    then show ?thesis
      by linarith
  qed
  also have "... \<le> 2 * \<bar>(x - y) / 2\<bar>"
    using abs_sin_le_one by (smt (verit, del_insts) abs_sin_x_le_abs_x)
  also have "... = \<bar>x - y\<bar>"
    by simp
  finally show ?thesis.
qed

subsection \<open>Algebraic Factorizations\<close>

lemma biquadrate_diff_biquadrate_factored:    
  fixes x y::real
  shows "y^4 - x^4 = (y - x) * (y^3 + y^2 * x + y * x^2 + x^3)"
proof -
    have "y^4 - x^4 = (y^2 - x^2) * (y^2 + x^2)"
      by (metis mult.commute numeral_Bit0 power_add square_diff_square_factored) 
    also have "... = (y - x) * (y + x) * (y^2 + x^2)"
      by (simp add: power2_eq_square square_diff_square_factored)
    also have "... = (y - x) * (y^3 + y^2 * x + y * x^2 + x^3)"
      by (simp add: distrib_left mult.commute power2_eq_square power3_eq_cube)  
    finally show ?thesis.
qed

subsection \<open>Specific Trigonometric Values\<close>

lemma sin_5pi_div_4: "sin (5 * pi / 4) = - (sqrt 2 / 2)" 
proof -
  have "5 * pi / 4 = pi + pi / 4"
    by simp
  moreover have "sin (pi + x) = - sin x" for x
    by (simp add: sin_add)
  ultimately show ?thesis
    using sin_45 by presburger
qed

lemma cos_5pi_div_4: "cos (5 * pi / 4) = - (sqrt 2 / 2)"
proof -
  have "5 * pi / 4 = pi + pi / 4"
    by simp
  moreover have "cos (pi + x) = - cos x" for x
    by (simp add: cos_add)
  moreover have "cos (pi / 4) = sqrt 2 / 2"
    by (simp add: real_div_sqrt cos_45)
  ultimately show ?thesis
    by presburger
qed

subsection \<open>Local Sign Preservation of Continuous Functions\<close>

subsubsection \<open>Local Positivity\<close>

lemma cont_at_pos_imp_loc_pos:
  fixes g :: "real \<Rightarrow> real" and x :: real
  assumes "continuous (at x) g" and "g x > 0"
  shows "\<exists>\<delta> > 0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y > 0"
proof -
  from assms obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> \<bar>g y - g x\<bar> < (g x)/2"
    using continuous_at_eps_delta half_gt_zero by blast
  then have "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y > 0"
    by (smt (verit, best) field_sum_of_halves)
  then show ?thesis
    using \<delta>_pos by blast
qed

lemma cont_at_pos_imp_loc_pos':
  fixes g :: "real \<Rightarrow> real" and x :: real
  assumes "continuous (at x) g" and "g x > 0"
  shows "\<exists>\<Delta> > 0. \<forall>\<delta>. 0 < \<delta> \<and> \<delta> \<le> \<Delta> \<longrightarrow> (\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y > 0)"
proof -
  from assms obtain \<delta> where \<delta>_pos: "\<delta> > 0" and H: "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y > 0"
    using cont_at_pos_imp_loc_pos by blast
  have "\<forall>\<delta>' \<le> \<delta>. \<forall>y. \<bar>y - x\<bar> < \<delta>' \<longrightarrow> g y > 0"
  proof clarify
    fix \<delta>' y :: real
    assume "\<delta>' \<le> \<delta>" and "\<bar>y - x\<bar> < \<delta>'"
    thus "g y > 0" by (auto simp: H)
  qed
  then show ?thesis
    using \<delta>_pos by blast
qed

subsubsection \<open>Local Negativity\<close>

lemma cont_at_neg_imp_loc_neg:
  fixes g :: "real \<Rightarrow> real" and x :: real
  assumes "continuous (at x) g" and "g x < 0"
  shows "\<exists>\<delta> > 0. \<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y < 0"
proof -
  from assms obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> \<bar>g y - g x\<bar> < -(g x)/2"
    by (metis continuous_at_eps_delta half_gt_zero neg_0_less_iff_less)
  then have "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> - g y > 0"
    by (smt (verit, best) field_sum_of_halves)
  then show ?thesis
    using \<delta>_pos neg_0_less_iff_less by blast
qed

lemma cont_at_neg_imp_loc_neg':
  fixes g :: "real \<Rightarrow> real" and x :: real
  assumes "continuous (at x) g" and "g x < 0"
  shows "\<exists>\<Delta> > 0. \<forall>\<delta>. 0 < \<delta> \<and> \<delta> \<le> \<Delta> \<longrightarrow> (\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> g y < 0)"
proof -
  from assms obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and H: "\<forall>y. \<bar>y - x\<bar> < \<delta> \<longrightarrow> -(g y) > 0"
    by (smt (verit) cont_at_neg_imp_loc_neg)
  have "\<forall>\<delta>' \<le> \<delta>. \<forall>y. \<bar>y - x\<bar> < \<delta>' \<longrightarrow> -(g y) > 0"
  proof clarify
    fix \<delta>' y :: real
    assume "\<delta>' \<le> \<delta>" and "\<bar>y - x\<bar> < \<delta>'"
    then show "-(g y) > 0"
      using H by auto 
  qed
  then show ?thesis
    using \<delta>_pos neg_0_less_iff_less by blast
qed

end