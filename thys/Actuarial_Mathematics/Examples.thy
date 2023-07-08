theory Examples
  imports Life_Table
begin

section \<open>Examples\<close>

text \<open>
  The following lemma is a verification of the solution to the multiple choice question No.\ 3
  of Exam LTAM Spring 2022 by Society of Actuaries.
\<close>

context smooth_survival_function
begin

lemma SoA_LTAM_2022_Spring_MCQ_No3:
  assumes "\<And>x::real. 0 \<le> x \<Longrightarrow> x \<le> 100 \<Longrightarrow> ccdf (distr \<MM> borel X) x = (1 - 0.01*x).^0.5"
  shows "\<bar>1000*$\<mu>_25 - 6.7\<bar> < 0.05"
proof -
  let ?svl = "ccdf (distr \<MM> borel X)"
  have [simp]: "ereal 25 < $\<psi>"
    apply (rewrite not_le[THEN sym])
    using assms by (rewrite ccdfX_0_equiv[THEN sym]) simp
  have \<star>: "((\<lambda>x. ln (1 - x/100)) has_real_derivative (-1/75)) (at 25)"
  proof -
    have "((\<lambda>x. (1 - x/100)) has_real_derivative (0 - 1/100)) (at 25)"
      apply (intro derivative_intros)
      by (rule DERIV_cdivide) simp
    hence "((\<lambda>x. ln (1 - x/100)) has_real_derivative (1 / (1 - 25/100) * (-1/100))) (at 25)"
      by (intro derivative_intros) auto
    thus ?thesis by simp
  qed
  have "exp \<circ> (\<lambda>x::real. 0.5 * ln (1 - 0.01*x)) field_differentiable at 25"
    apply (rule field_differentiable_compose, simp_all)
     apply (rule derivative_intros, simp_all)
    using \<star> field_differentiable_def apply blast
    using field_differentiable_within_exp by blast
  hence "?svl differentiable at 25"
    apply (rewrite differentiable_eq_field_differentiable_real)
    by (rule field_differentiable_transform_within[where d=1])
      (simp_all add: powr_def dist_real_def assms)
  hence "$\<mu>_25 = - deriv (\<lambda>x. ln (?svl x)) 25" by (rule mu_deriv_ln; simp)
  also have "\<dots> = 0.005 / (1 - 0.01*25)"
  proof -
    have "\<forall>\<^sub>F x in nhds 25. ln (?svl x) * 2 = ln (1 - x/100)"
    proof -
      { fix x::real assume "dist x 25 < 1"
        hence asm: "0 < x" "x < 100" using dist_real_def by auto
        hence "ln (?svl x) * 2 = ln ((1 - 0.01*x).^0.5) * 2" using assms by (smt (verit))
        also have "\<dots> = (0.5 * ln (1 - 0.01*x)) * 2" using asm by (rewrite ln_powr) auto
        finally have "ln (?svl x) * 2 = ln (1 - x/100)" by simp }
      thus ?thesis by (rewrite eventually_nhds_metric) (smt (verit, del_insts))
    qed
    hence "((\<lambda>x. ln (?svl x)) has_real_derivative (-0.005 / (1 - 0.01*25))) (at 25)"
      using \<star> apply (rewrite DERIV_cong_ev[where g="\<lambda>x. 0.5 * ln (1 - 0.01*x)"], simp_all)
      by (rule derivative_eq_intros) auto
    thus ?thesis using DERIV_imp_deriv by force
  qed
  finally show ?thesis by simp
qed

end

text \<open>
  The following lemma is a verification of the solution to the problem No.\ 2.\ (1)-1
  of Life Insurance Mathematics 2016 by the Institute of Actuaries of Japan,
  slightly modified; see the remark below.
\<close>

context smooth_life_table
begin

lemma IAJ_Life_Insurance_Math_2016_2_1_1:
  fixes a b :: real
  assumes "-1 < a" "a < 0" "0 < b" "-b/a \<le> $\<psi>" and
    "\<And>x. 0 < x \<Longrightarrow> x < -b/a \<Longrightarrow> l differentiable at x" and
    "\<And>x. 0 \<le> x \<Longrightarrow> x < -b/a \<Longrightarrow> l integrable_on {x..} \<and> $e`\<circ>_x = a*x + b"
  shows "\<And>x. 0 \<le> x \<Longrightarrow> x < -b/a \<Longrightarrow> $l_x = $l_0 * (b / (a*x + b)).^((a+1)/a)"
proof -
  fix x assume asm_x: "0 \<le> x" "x < -b/a"
  hence x_lt_psi[simp]: "ereal x < $\<psi>" using assms ereal_le_less by presburger
  from asm_x have axb_pos[simp]: "a*x + b > 0"
    using assms by (smt (verit, ccfv_threshold) mult.commute neg_less_divide_eq)
  have mu: "\<And>t. t\<in>{0<..<-b/a} \<Longrightarrow> $\<mu>_t = (a + 1) / (a*t + b)"
  proof -
    fix t assume asm_t: "t\<in>{0<..<-b/a}"
    with assms have "((\<lambda>u. $e`\<circ>_u) has_real_derivative ($\<mu>_t * $e`\<circ>_t - 1)) (at t)"
      using asm_t assms by (intro e_has_derivative_mu_e_l'[where a=0]; simp)
    moreover have "((\<lambda>u. $e`\<circ>_u) has_real_derivative a) (at t)"
    proof -
      let ?d = "min t (-b/a - t)"
      have "?d > 0" using assms asm_t by simp
      moreover have "\<And>u. dist u t < ?d \<Longrightarrow> $e`\<circ>_u = a*u + b" using assms dist_real_def by auto
      ultimately have "\<forall>\<^sub>F u in nhds t. $e`\<circ>_u = a*u + b" by (rewrite eventually_nhds_metric) blast
      thus ?thesis 
        using assms apply (rewrite DERIV_cong_ev[where g="\<lambda>t. a*t + b"], simp_all)
        by (intro derivative_eq_intros) auto
    qed
    ultimately have "$\<mu>_t * $e`\<circ>_t - 1 = a" using DERIV_unique by blast
    moreover have "$e`\<circ>_t = a*t + b" using assms asm_t by simp
    ultimately show "$\<mu>_t = (a + 1) / (a*t + b)"
      using assms by (smt (verit) mult_eq_0_iff nonzero_mult_div_cancel_right)
  qed
  hence "$p_{x&0} = (b / (a*x + b)).^((a+1)/a)"
  proof -
    have integ_mu: "integral {0..x} (\<lambda>t. $\<mu>_t) = (a + 1) / a * ln ((a*x + b) / b)"
    proof -
      have "integral {0..x} (\<lambda>t. $\<mu>_t) = integral {0<..x} (\<lambda>t. $\<mu>_t)"
        apply (rule integral_spike_set)
         apply (rule negligible_subset[where s="{0}"]; force)
        by (rule negligible_subset[where s="{}"]; simp)
      also have "\<dots> = integral {0<..x} (\<lambda>t. ((a + 1) / a) * (a / (a*t + b)))"
        using asm_x assms by (intro integral_cong) (rewrite mu; simp)
      also have "\<dots> = (a + 1) / a * integral {0<..x} (\<lambda>t. a / (a*t + b))"
        by (metis integral_mult_right)
      also have "\<dots> = (a + 1) / a * ln ((a*x + b) / b)"
      proof -
        have "integral {0<..x} (\<lambda>t. a / (a*t + b)) = integral {0..x} (\<lambda>t. a / (a*t + b))"
          apply (rule integral_spike_set)
           apply (rule negligible_subset[where s="{}"]; simp)
          by (rule negligible_subset[where s="{0}"]; force)
        also have "\<dots> = ln (a*x + b) - ln (a*0 + b)"
          apply (rule integral_unique)
          using assms asm_x apply (intro inverse_fun_has_integral_ln, simp_all)
          using axb_pos assms apply (smt (verit) mult_less_cancel_left)
           apply (intro continuous_intros)
          by (intro derivative_eq_intros) auto
        also have "\<dots> = ln ((a*x + b) / b)" using assms by (rewrite ln_div; simp)
        finally have "integral {0<..x} (\<lambda>t. a / (a*t + b)) = ln ((a*x + b) / b)" .
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    thus ?thesis
      apply (rewrite p_exp_integral_mu, simp_all add: asm_x)
      unfolding powr_def using assms
      by simp (smt (verit) axb_pos ln_div
          nonzero_minus_divide_divide nonzero_minus_divide_right right_diff_distrib')
  qed
  thus "$l_x = $l_0 * (b / (a*x + b)).^((a+1)/a)"
    using assms asm_x apply (rewrite in asm p_l, simp_all)
    by (metis divide_mult_cancel l_0_neq_0 mult.commute)
qed

text \<open>REMARK.
  The original problem lacks the following hypotheses:
    (i) @{text "0 < b"},
    (ii) @{text "-b/a \<le> $\<psi>"},
    (iii) @{text "\<forall>x. 0 < x < -b/a \<longrightarrow> l differentiable at x"},
    (iv) @{text "\<forall>x. 0 \<le> x < -b/a \<longrightarrow> l integrable_on {x..}"}.
  Moreover, the hypothesis @{text "\<forall>x. 0 \<le> x < -b/a"} is originally @{text "\<forall>x. 0 \<le> x \<le> -b/a"}.
\<close>

end

end

