section \<open>Example application: boundary cases of binomial theorem\<close>

theory Binomial_Sqrt_Series_Boundary
  imports 
    "Abel_Limit_Theorem"
    "Catalan_Numbers.Catalan_Numbers"
    "HOL-Real_Asymp.Real_Asymp"
begin

text \<open>
  Newton's generalized binomial theorem is applicable to @{text "\<bar>x\<bar> < 1"} as seen from this 
  @{thm "sqrt_series"}. However, it doesn't apply to the boundary cases where @{text "\<bar>x\<bar> = 1"} or 
  @{text "\<bar>x\<bar> = -1"}.

  Here, Abel's limit theorem is applied to establish the binomial theorem for the boundary cases.
\<close>

subsection \<open>Binomial series\<close>

lemma binomial_sqrt_series:
  fixes x :: real
  assumes "\<bar>x\<bar> < 1"
  shows "suminf (\<lambda>n. ((1/2) gchoose n) * x ^ n) = sqrt (1 + x)"
  apply (subst sums_unique[where s = "sqrt (1 + x)" and f = "(\<lambda>n. ((1/2) gchoose n) * x ^ n)"])
   apply (rule sqrt_series[where z = "x"])
   using assms apply blast
  by simp

text \<open>
  The generalized binomial coefficient \<^term>\<open>a gchoose n\<close> where $a = \frac{1}{2}$ can also be
  rewritten as an expression including a Catalan numbers. This is used to prove its summability 
  using the property of Catalan numbers.
\<close>
lemma gbinomial_1_2_catalan: "((1/2) gchoose (Suc n)) = ((-1)^(n)/(2^(2*n+1))) * real (catalan n)"
  by (subst catalan_closed_form_gbinomial) (simp add: power_mult power_minus')

lemma gbinomial_1_2_catalan': "((1/2) gchoose (Suc n)) = ((-1)^n/2) * (1/4^n) * real (catalan n)"
  by (subst gbinomial_1_2_catalan) (simp_all add: power_mult)

text \<open>
  Rewrite the generalized binomial coefficient \<^term>\<open>a gchoose n\<close> where $a = \frac{1}{2}$ as a
  binomial coefficient.
\<close>
lemma gbinomial_1_2_simp: 
  "((1/2) gchoose (Suc n)) = ((-1)^n / real (2^(2*n+1) * (Suc n))) * ((2*n) choose n)"
  by (subst gbinomial_1_2_catalan, subst of_nat_catalan_closed_form)
     (auto simp: algebra_simps)


lemma summable_real_powr_iff': "summable (\<lambda>n. 1 / of_nat n powr s :: real) \<longleftrightarrow> s > 1"
  apply (subgoal_tac "\<forall> n. 1 / of_nat n powr s = of_nat n powr (-s) ")
   apply (simp)
   using summable_real_powr_iff apply auto[1]
  by (simp add: powr_minus_divide)

lemma summable_1_2_gchoose: "summable (\<lambda>n. ((1::real)/2) gchoose n)"
proof -
  have f0: "(\<lambda>n. ((1/2) gchoose (Suc n))) \<sim>[at_top] (\<lambda>n. (((-1)^n/2) * (1/4^n)) * (4^n / ((sqrt pi * n powr (3/2)))))"
    apply (simp only: gbinomial_1_2_catalan')
    apply (subst asymp_equiv_mult)
      using asymp_equiv_refl apply blast
     using catalan_asymptotics apply blast
    by simp
  have f1: "... = (\<lambda>n. (-1)^n / (2 * (sqrt pi * n powr (3/2))))"
    by auto
  have f2: "... = (\<lambda>n. 1 / (2 * (sqrt pi)) * ((-1)^n / (n powr (3/2))))" (is "_ = ?g")
    by auto

  have summable_g: "summable ?g"
  proof (rule summable_mult)
    have f1: "\<forall>n. (- (1::real)) ^ n / real n powr ((3::real) / (2::real)) = 
      (- (1::real)) ^ n * real n powr (- ((3::real) / (2::real)))"
      using divide_powr_uminus by presburger

    have f2: "summable (\<lambda>n::nat. - ((- (1::real)) ^ n * real (n + 1) powr (- ((3::real) / (2::real)))))"
      apply (rule summable_minus)
      apply (rule summable_Leibniz')
        apply (subst tendsto_neg_powr)
      subgoal by simp
         using filterlim_real_sequentially
         apply (metis filterlim_add_const_nat_at_top filterlim_sequentially_iff_filterlim_real)
         subgoal by simp
       subgoal by simp
      by (simp add: powr_mono2')

    have f3: "summable (\<lambda>n::nat. ((- (1::real)) ^ (n + 1) * real (n + 1) powr (- ((3::real) / (2::real)))))"
      using f2 by simp

    show "summable (\<lambda>n::nat. (- (1::real)) ^ n / real n powr ((3::real) / (2::real)))"
      apply (simp only: f1)
      apply (subst summable_Suc_iff[symmetric])
      using f3 Suc_eq_plus1 by presburger
  qed

  have summable_norm_g: "summable (\<lambda>n. norm(?g n))"
  proof -
    have f0: "\<forall>n. norm(?g n) = ((1::real) / ((2::real) * sqrt pi) * (1 / real n powr ((3::real) / (2::real))))"
      by auto
    show ?thesis
      apply (simp only: f0)
      apply (rule summable_mult)
      apply (subst summable_real_powr_iff')
      by simp
  qed

  show ?thesis
    apply (subst summable_Suc_iff[symmetric])
    apply (subst summable_comparison_test_bigo[where g = ?g])
      apply (simp only: summable_norm_g)
     apply (rule asymp_equiv_imp_bigo)
     using f0 f1 f2 apply metis
    by simp
qed

lemma gbinomial_1_2_gchoose_sum_sqrt_2:
  shows "(\<Sum>n. (((1::real) / (2::real) gchoose n))) = sqrt 2" (is "(\<Sum>n. ?f_1 n) = _")
proof -
  let ?f = "\<lambda>x. (\<Sum>n. ((((1::real) / (2::real) gchoose n)) * x ^ n))"

  \<comment> \<open> Inside the disk: expansion gives sqrt(1+x) \<close>
  have eq_inside: "\<And>x. abs x < 1 \<Longrightarrow> ?f (x) = sqrt (1+x)"
    using sqrt_series sums_unique by force

  have "(?f \<longlongrightarrow> sqrt (2)) (at_left (1))"
  proof -
    have "((\<lambda>x. sqrt (1+x)) \<longlongrightarrow> sqrt 2) (at_left (1))"
    proof (intro tendsto_intros)
      have "((+) (1::real) \<longlongrightarrow> 1 + 1) (at_left 1)"
        using tendsto_add_const_iff by fastforce
      then show "((+) (1::real) \<longlongrightarrow> 2) (at_left 1)"
        by simp
    qed
    moreover have "eventually (\<lambda>x. ?f (x) = sqrt(1+x)) (at_left (1))"
      apply(subst eventually_at)
      apply (rule exI[of _ "0.1"])
      apply (auto simp: dist_real_def)[1]
      using eq_inside by force
    ultimately show ?thesis
      by (simp add: filterlim_cong)
  qed
  hence lim: "(?f \<longlongrightarrow> sqrt 2) (at_left (1))" by simp

  have lim_by_abel_from_left: "(?f \<longlongrightarrow> (\<Sum>n. ?f_1 n)) (at_left (1))"
    apply (subst Abel_limit_theorem)
      using summable_1_2_gchoose apply simp
     apply (subst conv_radius_gchoose)
     apply (smt (verit, best) Nats_cases field_sum_of_halves nat_less_real_le of_nat_0 of_nat_0_less_iff)
    by auto

  from lim lim_by_abel_from_left show "?thesis"
    apply (subst tendsto_unique[where f = "?f" and a = "(\<Sum>n. ?f_1 n)" 
          and F = "(at_left (1))" and b = "sqrt 2"])
       using trivial_limit_at_left_real apply blast
      apply blast
     apply blast
    by simp
qed


subsection \<open>Alternating series\<close>

lemma gbinomial_ratio_limit':
  fixes a :: "'a :: real_normed_field"
  assumes "a \<notin> \<nat>"
  shows "(\<lambda>n. ((a gchoose n) * (-1) ^ n) / ((a gchoose Suc n) * (-1) ^ (Suc n))) \<longlonglongrightarrow> 1"
proof -
  have "(\<lambda>n. ((a gchoose n) * (-1) ^ n) / ((a gchoose Suc n) * (-1) ^ (Suc n)))
      = (\<lambda>n. - ((a gchoose n) / (a gchoose Suc n)))"
    by auto
  then show ?thesis
    using gbinomial_ratio_limit assms tendsto_minus_cancel_left by fastforce
qed

lemma conv_radius_gchoose_alternating:
  fixes a :: "'a :: {real_normed_field,banach}"
  assumes "a \<notin> \<nat>"
  shows "conv_radius (\<lambda>n::nat. (a gchoose n) * (-1) ^ n) = (1::ereal)"
proof -
  from tendsto_norm[OF gbinomial_ratio_limit']
  have "conv_radius (\<lambda>n::nat. (a gchoose n) * (-1) ^ n) = 1"
      apply (intro conv_radius_ratio_limit_nonzero[of _ 1])
    subgoal by (simp add: norm_divide)
       subgoal by (simp add: norm_divide)
      apply (simp add: norm_divide[symmetric])
      using assms by blast
  then show ?thesis by blast
qed

lemma summable_1_2_gchoose_alternating: 
  "summable (\<lambda>n::nat. (1 / 2 gchoose n) * (-1) ^ n :: real)" (is "summable ?f")
proof -
  have f0: "(\<lambda>n. ((1/2) gchoose (Suc n))) \<sim>[at_top] 
              (\<lambda>n. (((-1)^n/2) * (1/4^n)) * (4^n / ((sqrt pi * n powr (3/2)))))"
    apply (simp only: gbinomial_1_2_catalan')
    apply (subst asymp_equiv_mult)
      using asymp_equiv_refl apply blast
     using catalan_asymptotics apply blast
    by simp
  have f1: "... = (\<lambda>n. (-1)^n / (2 * (sqrt pi * n powr (3/2))))"
    by auto
  have f2: "... = (\<lambda>n. 1 / (2 * (sqrt pi)) * ((-1)^n / (n powr (3/2))))" (is "_ = ?g")
    by auto
  have f3: "(\<lambda>n. ?g (n) * (- (1::real)) ^ (Suc n)) = 
      (\<lambda>n. (-1 / (2 * (sqrt pi))) * (1 / (n powr (3/2))))" (is "_ = ?g1")
    by auto
  have f4: "(\<lambda>n. ?f (Suc n)) \<sim>[at_top] (\<lambda>n. ?g (n) * (- (1::real)) ^ (Suc n))" (is "_ \<sim>[at_top] ?g1")
    apply (subst asymp_equiv_mult)
      using f0 f1 f2 subgoal by auto
     using asymp_equiv_refl apply blast
    by simp

  have summable_g: "summable ?g"
  proof (rule summable_mult)
    have f1: "\<forall>n. (- (1::real)) ^ n / real n powr ((3::real) / (2::real)) = 
      (- (1::real)) ^ n * real n powr (- ((3::real) / (2::real)))"
      using divide_powr_uminus by presburger

    have f2: "summable (\<lambda>n::nat. - ((- (1::real)) ^ n * real (n + 1) powr (- ((3::real) / (2::real)))))"
      apply (rule summable_minus)
      apply (rule summable_Leibniz')
        apply (subst tendsto_neg_powr)
          subgoal by simp
         using filterlim_real_sequentially
         apply (metis filterlim_add_const_nat_at_top filterlim_sequentially_iff_filterlim_real)
        subgoal by simp
       subgoal by simp
      by (simp add: powr_mono2')

    have f3: "summable (\<lambda>n::nat. ((- (1::real)) ^ (n + 1) * real (n + 1) powr (- ((3::real) / (2::real)))))"
      using f2 by simp

    show "summable (\<lambda>n::nat. (- (1::real)) ^ n / real n powr ((3::real) / (2::real)))"
      apply (simp only: f1)
      apply (subst summable_Suc_iff[symmetric])
      using f3 Suc_eq_plus1 by presburger
  qed

  have summable_g1: "summable ?g1"
    apply (simp only: f3)
    apply (rule summable_mult)
    apply (subgoal_tac "(\<lambda>n::nat. (1::real) / real n powr ((3::real) / (2::real))) = 
        (\<lambda>n::nat. real n powr (- (3::real) / (2::real)))")
    subgoal by (simp add: summable_real_powr_iff)
    by (simp add: inverse_eq_divide powr_minus)

  have summable_norm_g1: "summable (\<lambda>n. norm (?g1 n))"
    apply (simp add: f3)
    apply (subgoal_tac "(\<lambda>n::nat. (1::real) / ((2::real) * sqrt pi * real n powr (3 / 2))) = 
      (\<lambda>n::nat. (1::real) / ((2::real) * sqrt pi) * real n powr (-3 / 2))")
    subgoal by (simp add: summable_real_powr_iff)
    by (simp add: inverse_eq_divide powr_minus)

  show ?thesis
    apply (subst summable_Suc_iff[symmetric])
    apply (subst summable_comparison_test_bigo[where g = ?g1])
      using summable_norm_g1 apply blast
     apply (rule asymp_equiv_imp_bigo)
     using f4 apply blast
    by simp
qed

lemma gbinomial_1_2_gchoose_alternating_sum_0:
  shows "(\<Sum>n. ((1/2 gchoose n) * (- (1::real)) ^ n)) = 0" (is "(\<Sum>n. ?f_1 n) = 0")
proof -
  let ?f = "\<lambda>x. (\<Sum>n. ((((1::real) / (2::real) gchoose n) * (-1) ^ n) * x ^ n))"

  have f0: "\<forall>x. ?f x = (\<Sum>n. ((((1::real) / (2::real) gchoose n) * (-x) ^ n)))"
    by (metis (no_types, lifting) more_arith_simps(11) power_minus suminf_cong)
  
  \<comment> \<open> Inside the disk: expansion gives sqrt(1+x) \<close>
  have eq_inside: "\<And>x. abs x < 1 \<Longrightarrow> ?f (-x) = sqrt (1-(-x))"
    apply (simp only: f0)
    using sqrt_series sums_unique by force

  have "((\<lambda>x. ?f (-x)) \<longlongrightarrow> sqrt (1 + (-1))) (at_right (-1))"
  proof -
    have "((\<lambda>x. sqrt (1+x)) \<longlongrightarrow> sqrt 0) (at_right (-1))"
      apply (intro tendsto_intros)
      using filterlim_at_right_to_0 by fastforce
    moreover have "eventually (\<lambda>x. ?f (-x) = sqrt(1+x)) (at_right (-1))"
      apply (subst eventually_at)
      apply (rule exI[of _ "0.1"])
      apply (auto simp: dist_real_def)[1]
      using eq_inside by force
    ultimately show ?thesis
      by (simp add: filterlim_cong)
  qed
  hence lim: "((\<lambda>x. ?f (-x)) \<longlongrightarrow> 0) (at_right (-1))" by simp

  have lim_by_abel_from_right: "((\<lambda>x. ?f (-x)) \<longlongrightarrow> (\<Sum>n. ?f_1 n)) (at_right (-1))"
    apply (subst Abel_limit_theorem')
      subgoal using summable_1_2_gchoose_alternating by simp
     apply (subst conv_radius_gchoose_alternating[where a = "1/2::real"])
      apply (smt (verit, ccfv_threshold) Multiseries_Expansion.intyness_simps(1) Nats_cases One_nat_def 
        Rings.ring_distribs(2) divide_inverse inverse_eq_divide nat_less_real_le 
        nonzero_mult_div_cancel_left of_nat_0_less_iff one_power2 plus_1_eq_Suc times_divide_eq_right)
    by auto

  from lim lim_by_abel_from_right show "?thesis"
    apply (subst tendsto_unique[where f = "(\<lambda>x. ?f (-x))" and a = "(\<Sum>n. ?f_1 n)" 
          and F = "(at_right (-1))" and b = "0"])
    using trivial_limit_at_right_real apply blast
    apply blast
    apply blast
    by simp
qed


subsection \<open>Binomial sqrt series with the boundary cases \<close>

text \<open>
  This lemma incorporates the boundary values where $x = 1$ and $x = -1$.
\<close>
theorem binomial_sqrt_series':
  assumes "\<bar>x\<bar> \<le> (1 :: real)"
  shows "suminf (\<lambda>n. ((1/2) gchoose n) * x ^ n) = sqrt (1 + x)"
proof (cases "\<bar>x\<bar> < 1")
  case True
  then show ?thesis using binomial_sqrt_series by presburger
next
  case abs_x_1: False
  then show ?thesis 
  proof (cases "x = 1")
    case True
    then show ?thesis 
      by (simp add: gbinomial_1_2_gchoose_sum_sqrt_2)
  next
    case False
    then have "x = -1"
      using abs_x_1 assms by linarith
    then show ?thesis by (simp add: gbinomial_1_2_gchoose_alternating_sum_0)
  qed
qed

end