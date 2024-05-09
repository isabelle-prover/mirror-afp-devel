theory Relation_of_PNTs
imports
  "PNT_Remainder_Library"
begin
unbundle pnt_notation
unbundle prime_counting_notation

section \<open>Implication relation of many forms of prime number theorem\<close>

definition rem_est :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> _" where
"rem_est c m n \<equiv> O(\<lambda> x. x * exp (-c * ln x powr m * ln (ln x) powr n))"

definition Li :: "real \<Rightarrow> real" where "Li x \<equiv> integral {2..x} (\<lambda>x. 1 / ln x)"
definition PNT_1 where "PNT_1 c m n \<equiv> ((\<lambda>x. \<pi> x - Li x) \<in> rem_est c m n)"
definition PNT_2 where "PNT_2 c m n \<equiv> ((\<lambda>x. \<theta> x - x) \<in> rem_est c m n)"
definition PNT_3 where "PNT_3 c m n \<equiv> ((\<lambda>x. \<psi> x - x) \<in> rem_est c m n)"

lemma rem_est_compare_powr:
  fixes c m n :: real
  assumes h: "0 < m" "m < 1"
  shows "(\<lambda>x. x powr (2 / 3)) \<in> rem_est c m n"
  unfolding rem_est_def using assms
  by (cases c "0 :: real" rule: linorder_cases; real_asymp)

lemma PNT_3_imp_PNT_2:
  fixes c m n :: real
  assumes h: "0 < m" "m < 1" and "PNT_3 c m n"
  shows "PNT_2 c m n"
proof -
  have 1: "(\<lambda> x. \<psi> x - x) \<in> rem_est c m n"
    using assms(3) unfolding PNT_3_def by auto
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)" by (rule \<psi>_minus_\<theta>_bigo)
  moreover have "(\<lambda>x. ln x * sqrt x) \<in> O(\<lambda>x. x powr (2 / 3))" by real_asymp
  ultimately have 2: "(\<lambda>x. \<psi> x - \<theta> x) \<in> rem_est c m n"
    using rem_est_compare_powr [OF h, of c n] unfolding rem_est_def
    by (blast intro: landau_o.big.trans)
  have "(\<lambda>x. \<psi> x - x - (\<psi> x - \<theta> x)) \<in> rem_est c m n"
    using 1 2 unfolding rem_est_def by (rule sum_in_bigo)
  thus ?thesis unfolding PNT_2_def by simp
qed

definition r\<^sub>1 where "r\<^sub>1 x \<equiv> \<pi> x - Li x" for x
definition r\<^sub>2 where "r\<^sub>2 x \<equiv> \<theta> x - x" for x

lemma pi_represent_by_theta:
  fixes x :: real
  assumes "2 \<le> x"
  shows "\<pi> x = \<theta> x / (ln x) + integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))"
proof -
  note integral_unique [OF \<pi>_conv_\<theta>_integral]
  with assms show ?thesis by auto
qed

lemma Li_integrate_by_part:
  fixes x :: real
  assumes "2 \<le> x"
  shows
  "(\<lambda>x. 1 / (ln x)\<^sup>2) integrable_on {2..x}"
  "Li x = x / (ln x) - 2 / (ln 2) + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
proof -
  have "(\<lambda>x. x * (- 1 / (x * (ln x)\<^sup>2))) integrable_on {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
  hence "(\<lambda>x. - (if x = 0 then 0 else 1 / (ln x)\<^sup>2)) integrable_on {2..x}"
    by simp
  moreover have "((\<lambda>t. 1 / ln t) has_vector_derivative -1 / (t * (ln t)\<^sup>2)) (at t)"
    when Ht: "2 \<le> t" for t
  proof -
    define a where "a \<equiv> (0 * ln t - 1 * (1 / t))/(ln t * ln t)"
    have "DERIV (\<lambda>t. 1 / (ln t)) t :> a"
    unfolding a_def
    proof (rule derivative_intros DERIV_ln_divide)+
      from Ht show "0 < t" by linarith
      note ln_gt_zero and Ht thus "ln t \<noteq> 0" by auto
    qed
    also have "a = -1 / (t * (ln t)\<^sup>2)"
      unfolding a_def by (simp add: power2_eq_square)
    finally have "DERIV (\<lambda>t. 1 / (ln t)) t :> -1 / (t * (ln t)\<^sup>2)" by auto
    thus ?thesis
      by (subst has_real_derivative_iff_has_vector_derivative [symmetric])
  qed
  ultimately have "((\<lambda>x. 1 * (1 / ln x)) has_integral
    x * (1 / ln x) - 2 * (1 / ln 2) - integral {2..x} (\<lambda>x. x * (-1 / (x * (ln x)\<^sup>2))))
    {2..x}"
    using \<open>2 \<le> x\<close> by (intro integration_by_part') auto
  note 3 = this [simplified]
  have "((\<lambda>x. 1 / ln x) has_integral (x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2))) {2..x}"
  proof -
    define a where "a t \<equiv> if t = 0 then 0 else 1 / (ln t)\<^sup>2" for t :: real
    have "\<And>t :: real. t \<in> {2..x} \<Longrightarrow> a t = 1 / (ln t)\<^sup>2"
      unfolding a_def by auto
    hence 4: "integral {2..x} a = integral {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2)" by (rule integral_cong)
    from 3 show ?thesis
      by (subst (asm) 4 [unfolded a_def])
  qed
  thus "Li x = x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)" unfolding Li_def by auto
  show "(\<lambda>x. 1 / (ln x)\<^sup>2) integrable_on {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
qed

lemma \<theta>_integrable:
  fixes x :: "real"
  assumes "2 \<le> x"
  shows "(\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) integrable_on {2..x}"
by (rule \<pi>_conv_\<theta>_integral [THEN has_integral_integrable], rule assms)

lemma r\<^sub>1_represent_by_r\<^sub>2:
  fixes x :: real
  assumes Hx: "2 \<le> x"
  shows "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) integrable_on {2..x}" (is ?P)
    "r\<^sub>1 x = r\<^sub>2 x / (ln x) + 2 / ln 2 + integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))" (is ?Q)
proof -
  have 0: "\<And>t. t \<in> {2..x} \<Longrightarrow> (\<theta> t - t) / (t * (ln t)\<^sup>2) = \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2"
    by (subst diff_divide_distrib, auto)
  note integrables = \<theta>_integrable Li_integrate_by_part(1)
  let ?D = "integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) -
    integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
  have "((\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2) has_integral
    ?D) {2..x}"
  unfolding r\<^sub>2_def by
    (rule has_integral_diff)
    (rule integrables [THEN integrable_integral], rule Hx)+
  hence 0: "((\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) has_integral
    ?D) {2..x}"
  unfolding r\<^sub>2_def by (subst has_integral_cong [OF 0])
  thus ?P by (rule has_integral_integrable)
  note 1 = 0 [THEN integral_unique]
  have 2: "r\<^sub>2 x / ln x = \<theta> x / ln x - x / ln x"
    unfolding r\<^sub>2_def by (rule diff_divide_distrib)
  from pi_represent_by_theta and Li_integrate_by_part(2) and assms
  have "\<pi> x - Li x = \<theta> x / ln x
    + integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))
    - (x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2))"
    by auto
  also have "\<dots> = r\<^sub>2 x / ln x + 2 / ln 2
    + integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
    by (subst 2, subst 1) auto
  finally show ?Q unfolding r\<^sub>1_def by auto
qed

lemma exp_integral_asymp:
  fixes f f' :: "real \<Rightarrow> real"
  assumes cf: "continuous_on {a..} f"
      and der: "\<And>x. a < x \<Longrightarrow> DERIV f x :> f' x"
      and td: "((\<lambda>x. x * f' x) \<longlongrightarrow> 0) at_top"
      and f_ln: "f \<in> o(ln)"
  shows "(\<lambda>x. integral {a..x} (\<lambda>t. exp (-f t))) \<sim>[at_top] (\<lambda>x. x * exp(-f x))"
proof (rule asymp_equivI', rule lhospital_at_top_at_top)
  have cont_exp: "continuous_on {a..} (\<lambda>t. exp (- f t))"
    using cf by (intro continuous_intros)
  show "\<forall>\<^sub>F x in at_top. ((\<lambda>x. integral {a..x} (\<lambda>t. exp (- f t)))
    has_real_derivative exp (- f x)) (at x)" (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "a \<le> x" by linarith
    have 3: "(at x within {a..x+1}) = (at x)"
      by (rule at_within_interior) (auto intro: 1)
    show "?P x"
      by (subst 3 [symmetric], rule integral_has_real_derivative)
         (rule continuous_on_subset [OF cont_exp], auto intro: 2)
  qed
  have "\<forall>\<^sub>F x in at_top. ((\<lambda>x. x * exp (- f x))
    has_real_derivative 1 * exp (- f x) + exp (- f x) * (- f' x) * x) (at x)"
    (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "(at x within {a<..}) = (at x)" by (auto intro: at_within_open)
    show "?P x"
      by (subst 2 [symmetric], intro derivative_intros)
         (subst 2, rule der, rule 1)
  qed
  moreover have
    "1 * exp (- f x) + exp (- f x) * (- f' x) * x
    = exp (- f x) * (1 - x * f' x)" for x :: real
    by (simp add: field_simps)
  ultimately show "\<forall>\<^sub>F x in at_top.
       ((\<lambda>x. x * exp (- f x))
    has_real_derivative exp (- f x) * (1 - x * f' x)) (at x)" by auto
  show "LIM x at_top. x * exp (- f x) :> at_top"
    using f_ln by (rule smallo_ln_diverge_1)
  have "((\<lambda>x. 1 / (1 - x * f' x)) \<longlongrightarrow> 1 / (1 - 0)) at_top"
    by ((rule tendsto_intros)+, rule td, linarith)
  thus "((\<lambda>x. exp (- f x) / (exp (- f x) * (1 - x * f' x))) \<longlongrightarrow> 1) at_top" by auto
  have "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1 - 0) at_top"
    by ((rule tendsto_intros)+, rule td)
  hence 0: "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1) at_top" by simp
  hence "\<forall>\<^sub>F x in at_top. 0 < 1 - x * f' x"
    by (rule order_tendstoD) linarith
  moreover have "\<forall>\<^sub>F x in at_top. 0 < 1 - x * f' x \<longrightarrow> exp (- f x) * (1 - x * f' x) \<noteq> 0" by auto
  ultimately show "\<forall>\<^sub>F x in at_top. exp (- f x) * (1 - x * f' x) \<noteq> 0"
    by (rule eventually_rev_mp)
qed

lemma x_mul_exp_larger_than_const:
  fixes c :: real and g :: "real \<Rightarrow> real"
  assumes g_ln: "g \<in> o(ln)"
  shows "(\<lambda>x. c) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "LIM x at_top. x * exp (- g x) :> at_top"
    using g_ln by (rule smallo_ln_diverge_1)
  hence "\<forall>\<^sub>F x in at_top. 1 \<le> x * exp (- g x)"
    using filterlim_at_top by fast
  hence "\<forall>\<^sub>F x in at_top. \<parallel>c\<parallel> * 1 \<le> \<parallel>c\<parallel> * \<parallel>x * exp (- g x)\<parallel>"
    by (rule eventually_rev_mp)
       (auto simp del: mult_1_right
             intro!: eventuallyI mult_left_mono)
  thus "(\<lambda>x. c :: real) \<in> O(\<lambda>x. x * exp (- g x))" by auto
qed

lemma integral_bigo_exp':
  fixes a :: real and f g g' :: "real \<Rightarrow> real"
  assumes f_bound: "f \<in> O(\<lambda>x. exp(-g x))"
    and Hf:   "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf':  "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {a..x}"
    and Hg:   "continuous_on {a..} g"
    and der:  "\<And>x. a < x \<Longrightarrow> DERIV g x :> g' x"
    and td:   "((\<lambda>x. x * g' x) \<longlongrightarrow> 0) at_top"
    and g_ln: "g \<in> o(ln)"
  shows "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "\<And>y. continuous_on {a..y} g"
    by (rule continuous_on_subset, rule Hg) auto
  hence "\<And>y. (\<lambda>x. exp(-g x)) integrable_on {a..y}"
    by (intro integrable_continuous_interval)
       (rule continuous_intros)+
  hence "\<And>y. (\<lambda>x. \<bar>exp(-g x)\<bar>) integrable_on {a..y}" by simp
  hence "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. \<bar>exp(-g x)\<bar>))"
    using assms by (intro integral_bigo)
  hence "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. exp(-g x)))" by simp
  also have "(\<lambda>x. 1 + integral{a..x} (\<lambda>x. exp(-g x))) \<in> O(\<lambda>x. x * exp(-g x))"
  proof (rule sum_in_bigo)
    show "(\<lambda>x. 1 :: real) \<in> O(\<lambda>x. x * exp (- g x))"
      by (intro x_mul_exp_larger_than_const g_ln)
    show "(\<lambda>x. integral {a..x} (\<lambda>x. exp (- g x))) \<in> O(\<lambda>x. x * exp (- g x))"
      by (rule asymp_equiv_imp_bigo, rule exp_integral_asymp, auto intro: assms)
  qed
  finally show ?thesis .
qed

lemma integral_bigo_exp:
  fixes a b :: real and f g g' :: "real \<Rightarrow> real"
  assumes le: "a \<le> b"
    and f_bound: "f \<in> O(\<lambda>x. exp(-g x))"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf': "\<And>x. b \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {b..x}"
    and Hg:  "continuous_on {b..} g"
    and der: "\<And>x. b < x \<Longrightarrow> DERIV g x :> g' x"
    and td:  "((\<lambda>x. x * g' x) \<longlongrightarrow> 0) at_top"
    and g_ln:"g \<in> o(ln)"
  shows "(\<lambda>x. integral {a..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "(\<lambda>x. integral {a..b} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (intro x_mul_exp_larger_than_const g_ln)
  moreover have "(\<lambda>x. integral {b..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (intro integral_bigo_exp' [where ?g' = g']
              f_bound Hf Hf' Hg der td g_ln)
       (use le Hf integrable_cut' in auto)
  ultimately have "(\<lambda>x. integral {a..b} f + integral {b..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (rule sum_in_bigo)
  moreover have "integral {a..x} f = integral {a..b} f + integral {b..x} f" when "b \<le> x" for x
    by (subst eq_commute, rule Henstock_Kurzweil_Integration.integral_combine)
       (insert le that, auto intro: Hf)
  hence "\<forall>\<^sub>F x in at_top. integral {a..x} f = integral {a..b} f + integral {b..x} f"
    by (rule eventually_at_top_linorderI)
  ultimately show ?thesis
    by (simp add: landau_o.big.in_cong)
qed

lemma integrate_r\<^sub>2_estimate:
  fixes c m n :: real
  assumes hm: "0 < m" "m < 1"
    and h: "r\<^sub>2 \<in> rem_est c m n"
  shows "(\<lambda>x. integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))) \<in> rem_est c m n"
unfolding rem_est_def
proof (subst mult.assoc,
       subst minus_mult_left [symmetric],
       rule integral_bigo_exp)
  show "(2 :: real) \<le> 3" by auto
  show "(\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) \<in> o(ln)"
    using hm by real_asymp
  have "ln x \<noteq> 1" when "3 \<le> x" for x :: real
    using ln_when_ge_3 [of x] that by auto
  thus "continuous_on {3..} (\<lambda>x. c * (ln x powr m * ln (ln x) powr n))"
    by (intro continuous_intros) auto
  show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) integrable_on {2..x}"
    if "2 \<le> x" for x using that by (rule r\<^sub>1_represent_by_r\<^sub>2(1))
  define g where "g x \<equiv>
    c * (m * ln x powr (m - 1) * (1 / x * 1) * ln (ln x) powr n
       + n * ln (ln x) powr (n - 1) * (1 / ln x * (1 / x)) * ln x powr m)"
    for x
  show "((\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) has_real_derivative g x) (at x)"
    if "3 < x" for x
  proof -
    have *: "at x within {3<..} = at x"
      by (rule at_within_open) (auto intro: that)
    moreover have
      "((\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) has_real_derivative g x)
       (at x within {3<..})"
    unfolding g_def using that
    by (intro derivative_intros DERIV_mult DERIV_cmult)
       (auto intro: ln_when_ge_3 DERIV_ln_divide simp add: *)
    ultimately show ?thesis by auto
  qed
  show "((\<lambda>x. x * g x) \<longlongrightarrow> 0) at_top"
    unfolding g_def using hm by real_asymp
  have nz: "\<forall>\<^sub>F t :: real in at_top. t * (ln t)\<^sup>2 \<noteq> 0"
  proof (rule eventually_at_top_linorderI')
    fix x :: real assume "1 < x"
    thus "x * (ln x)\<^sup>2 \<noteq> 0" by auto
  qed
  define h where "h x \<equiv> exp (- c * ln x powr m * ln (ln x) powr n)" for x
  have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) \<in> O(\<lambda>x. (x * h x) / (x * (ln x)\<^sup>2))"
    by (rule landau_o.big.divide_right, rule nz)
       (unfold h_def, fold rem_est_def, rule h)
  also have "(\<lambda>x. (x * h x) / (x * (ln x)\<^sup>2)) \<in> O(\<lambda>x. h x)"
  proof -
    have "(\<lambda>x :: real. 1 / (ln x)\<^sup>2) \<in> O(\<lambda>x. 1)" by real_asymp
    hence "(\<lambda>x. h x * (1 / (ln x)\<^sup>2)) \<in> O(\<lambda>x. h x * 1)"
      by (rule landau_o.big.mult_left)
    thus ?thesis
      by (auto simp add: field_simps
               intro!: landau_o.big.ev_eq_trans2)
         (auto intro: eventually_at_top_linorderI [of 1])
  qed
  finally show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))
    \<in> O(\<lambda>x. exp (- (c * (ln x powr m * ln (ln x) powr n))))"
    unfolding h_def by (simp add: algebra_simps)
  have "(\<lambda>x. r\<^sub>2 x / (x * (ln x)\<^sup>2)) absolutely_integrable_on {2..x}"
    if *:"2 \<le> x" for x
  proof (rule set_integrableI_bounded)
    show "{2..x} \<in> sets lebesgue" by auto
    show "emeasure lebesgue {2..x} < \<infinity>" using * by auto
    have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2) * indicator {2..x} t) \<in> borel_measurable lebesgue"
      using * by (intro integrable_integral
        [THEN has_integral_implies_lebesgue_measurable_real])
        (rule r\<^sub>1_represent_by_r\<^sub>2(1))
    thus "(\<lambda>t. indicat_real {2..x} t *\<^sub>R (r\<^sub>2 t / (t * (ln t)\<^sup>2))) \<in> borel_measurable lebesgue"
      by (simp add: mult_ac)
    let ?C = "(ln 4 + 1) / (ln 2)\<^sup>2 :: real"
    show "AE t\<in>{2..x} in lebesgue. \<parallel>r\<^sub>2 t / (t * (ln t)\<^sup>2)\<parallel> \<le> ?C"
    proof (rule AE_I2, safe)
      fix t assume "t \<in> {2..x}"
      hence h: "1 \<le> t" "2 \<le> t" by auto
      hence "0 \<le> \<theta> t \<and> \<theta> t < ln 4 * t" by (auto intro: \<theta>_upper_bound)
      hence *:"\<bar>\<theta> t\<bar> \<le> ln 4 * t" by auto
      have "1 \<le> ln t / ln 2" using h by auto
      hence "1 \<le> (ln t / ln 2)\<^sup>2" by auto
      also have "\<dots> = (ln t)\<^sup>2 / (ln 2)\<^sup>2" unfolding power2_eq_square by auto
      finally have "1 \<le> (ln t)\<^sup>2 / (ln 2)\<^sup>2" .
      hence "\<bar>r\<^sub>2 t\<bar> \<le> \<bar>\<theta> t\<bar> + \<bar>t\<bar>" unfolding r\<^sub>2_def by auto
      also have "\<dots> \<le> ln 4 * t + 1 * t" using h * by auto
      also have "\<dots> = (ln 4 + 1) * t" by (simp add: algebra_simps)
      also have "\<dots> \<le> (ln 4 + 1) * t * ((ln t)\<^sup>2 / (ln 2)\<^sup>2)"
        by (auto simp add: field_simps)
           (rule add_mono; rule rev_mp[OF h(2)], auto)
      finally have *:"\<bar>r\<^sub>2 t\<bar> \<le> ?C * (t * (ln t)\<^sup>2)" by auto
      thus "\<parallel>r\<^sub>2 t / (t * (ln t)\<^sup>2)\<parallel> \<le> ?C"
        using h * by (auto simp add: field_simps)
    qed
  qed
  hence "\<And>x. 2 \<le> x \<Longrightarrow> (\<lambda>x. \<bar>r\<^sub>2 x / (x * (ln x)\<^sup>2)\<bar>) integrable_on {2..x}"
    by (fold real_norm_def)
       (rule absolutely_integrable_on_def [THEN iffD1, THEN conjunct2])
  thus "\<And>x. 3 \<le> x \<Longrightarrow> (\<lambda>x. \<bar>r\<^sub>2 x / (x * (ln x)\<^sup>2)\<bar>) integrable_on {3..x}"
    using \<open>2 \<le> 3\<close> integrable_cut' by blast
qed

lemma r\<^sub>2_div_ln_estimate:
  fixes c m n :: real
  assumes hm: "0 < m" "m < 1"
    and h: "r\<^sub>2 \<in> rem_est c m n"
  shows "(\<lambda>x. r\<^sub>2 x / (ln x) + 2 / ln 2) \<in> rem_est c m n"
proof -
  have "(\<lambda>x. r\<^sub>2 x / ln x) \<in> O(r\<^sub>2)"
  proof (intro bigoI eventually_at_top_linorderI)
    fix x :: real assume 1:"exp 1 \<le> x"
    have 2:"(0 :: real) < exp 1" by simp
    hence 3:"0 < x" using 1 by linarith
    have 4: "0 \<le> \<bar>r\<^sub>2 x\<bar>" by auto
    have "(1 :: real) = ln (exp 1)" by simp
    also have "\<dots> \<le> ln x" using 1 2 3 by (subst ln_le_cancel_iff)
    finally have "1 \<le> ln x" .
    thus "\<parallel>r\<^sub>2 x / ln x\<parallel> \<le> 1 * \<parallel>r\<^sub>2 x\<parallel>"
      by (auto simp add: field_simps, subst mult_le_cancel_right1, auto)
  qed
  with h have 1: "(\<lambda>x. r\<^sub>2 x / ln x) \<in> rem_est c m n"
    unfolding rem_est_def using landau_o.big_trans by blast
  moreover have "(\<lambda>x :: real. 2 / ln 2) \<in> O(\<lambda>x. x powr (2 / 3))"
    by real_asymp
  hence "(\<lambda>x :: real. 2 / ln 2) \<in> rem_est c m n"
    using rem_est_compare_powr [OF hm, of c n]
    unfolding rem_est_def by (rule landau_o.big.trans)
  ultimately show ?thesis
    unfolding rem_est_def by (rule sum_in_bigo)
qed

lemma PNT_2_imp_PNT_1:
  fixes l :: real
  assumes h: "0 < m" "m < 1" and "PNT_2 c m n"
  shows "PNT_1 c m n"
proof -
  from assms(3) have h': "r\<^sub>2 \<in> rem_est c m n"
    unfolding PNT_2_def r\<^sub>2_def by auto
  let ?a = "\<lambda>x. r\<^sub>2 x / ln x + 2 / ln 2"
  let ?b = "\<lambda>x. integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
  have 1: "\<forall>\<^sub>F x in at_top. \<pi> x - Li x = ?a x + ?b x"
    by (rule eventually_at_top_linorderI, fold r\<^sub>1_def)
       (rule r\<^sub>1_represent_by_r\<^sub>2(2), blast)
  have 2: "(\<lambda>x. ?a x + ?b x) \<in> rem_est c m n"
    by (unfold rem_est_def, (rule sum_in_bigo; fold rem_est_def))
       (intro r\<^sub>2_div_ln_estimate integrate_r\<^sub>2_estimate h h')+
  from landau_o.big.in_cong [OF 1] and 2 show ?thesis
    unfolding PNT_1_def rem_est_def by blast
qed

theorem PNT_3_imp_PNT_1:
  fixes l :: real
  assumes h : "0 < m" "m < 1" and "PNT_3 c m n"
  shows "PNT_1 c m n"
  by (intro PNT_2_imp_PNT_1 PNT_3_imp_PNT_2 assms)

hide_const (open) r\<^sub>1 r\<^sub>2
unbundle no_prime_counting_notation
unbundle no_pnt_notation
end