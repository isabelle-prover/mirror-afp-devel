section \<open>The Dottie Number\<close>

theory Dottie
  imports "HOL-Analysis.Analysis"
          "HOL-Decision_Procs.Approximation"
          "Hermite_Lindemann.Hermite_Lindemann"

begin

text \<open>
  The Dottie number, approximately 0.739085133215,
  is the unique fixed point of the cosine function.

  This theory establishes the Dottie number's basic theory. 
  We first show that the fixed point
  \emph{exists} (by the intermediate value theorem) and is \emph{unique} (because
  $\cos x - x$ has a strictly negative derivative), justifying the definition of
  @{term dottie}, and we pin it down to twelve decimal places. We then prove three
  further results: that the Dottie number is a \emph{universal attractor}, in the
  sense that iterating cosine from any real starting point converges to it; the
  trigonometric identity $\sin(\mathit{dottie}) = \sqrt{1 - \mathit{dottie}^2}$; and,
  using the Hermite--Lindemann--Weierstra\ss\ theorem, that the Dottie number is
  \emph{transcendental}.
\<close>

definition dottie :: real where
  "dottie \<equiv> THE x. cos x = x"

lemma cos_1_lt_1: "cos (1::real) < 1"
  using cos_monotone_0_pi pi_gt3 by force

text \<open>We shall reason about the function $g(x) = \cos x - x$.
The locale provides a scope for $g$ and its
properties, which are used by several of the lemmas below.\<close>

locale Dottie =
  fixes g :: "real \<Rightarrow> real"
  defines "g \<equiv> \<lambda>x::real. cos x - x"

begin

lemma g_has_negative_deriv:
  assumes "\<bar>t\<bar> \<le> 1" 
  shows "\<exists>d. (g has_real_derivative d) (at t) \<and> d < 0"
proof (intro exI conjI)
  show "(g has_real_derivative (- sin t - 1)) (at t)"
    unfolding g_def by (auto intro!: derivative_eq_intros)
  show "- sin t - 1 < 0"
    using assms pi_gt3 le_arcsin_iff [of _ t] by fastforce
qed

subsection \<open>Existence\<close>

text \<open>We have $g(0) = 1 > 0$ and $g(1) = \cos 1 - 1 < 0$.
  Since $g$ is continuous, the intermediate value theorem gives
  a point $x \in (0, 1)$ where $g(x) = 0$, i.e.\ $\cos x = x$.\<close>

lemma dottie_exists: "\<exists>x::real. 0 < x \<and> x < 1 \<and> cos x = x"
proof -
  \<comment> \<open>Apply the IVT to @{term g} on the unit interval at 0.\<close>
  have g_cont: "continuous_on {0..1} g"
    unfolding g_def by (intro continuous_intros)
  obtain "g 0 = 1" "g 1 < 0" using cos_1_lt_1 by (simp add: g_def)
  with IVT2'[of g 1 0 0] g_cont
  obtain x where hx: "0 \<le> x" "x \<le> 1" "g x = 0"
    by (metis less_eq_real_def zero_le_one)
  hence cos_eq: "cos x = x" by (simp add: g_def)
  with hx show ?thesis
    by (metis cos_1_lt_1 cos_zero order_less_le)
qed

subsection \<open>Uniqueness\<close>

text \<open>The function $g(x) = \cos x - x$ has derivative
  $g'(x) = -\sin x - 1$, which is strictly negative for $x \in [-1,1]$
  (since $\sin x \ge 0$ there).  A function with strictly negative derivative
  is strictly decreasing, so $g$ can have at most one zero. 
  We can extend uniqueness to the entire real line.\<close>

lemma dottie_unique:
  fixes x y :: real
  assumes "cos x = x" "cos y = y"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have gx: "g x = 0" and gy: "g y = 0" using assms by (auto simp: g_def)
  \<comment> \<open>The derivative of @{term g} is @{term "\<lambda>x. - sin x - 1"}, which is negative on @{term "{-1..1}"}.\<close>
  show False
  proof (cases "\<bar>x\<bar> > 1 \<or> \<bar>y\<bar> > 1")
    case True
    then show ?thesis
      by (metis assms abs_cos_le_one not_less)
  next
    case False
    then have "\<bar>x\<bar> \<le> 1 \<and> \<bar>y\<bar> \<le> 1"
      by simp
    moreover have "x < y \<or> y < x" using \<open>x \<noteq> y\<close> by linarith
    ultimately show ?thesis
      using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] gx gy
      by force
  qed
qed

lemma facts: "0 < dottie" "dottie < 1" "cos dottie = dottie" 
proof -
  obtain x :: real where hx: "0 < x" "x < 1" "cos x = x"
    using dottie_exists by blast
  have unique: "y = x" if "cos y = y" for y :: real
    by (simp add: dottie_unique \<open>cos x = x\<close> that)
  have the_eq: "dottie = x"
    unfolding dottie_def using \<open>cos x = x\<close> unique by blast
  then show "0 < dottie" "dottie < 1" "cos dottie = dottie" 
    using hx by (auto simp: g_def)
qed

subsection \<open>Approximation\<close>

text \<open>We pin down the Dottie number to 12 decimal
  places. Note that $g$ is decreasing. We check that
  $\cos(lb) > lb$ (so the fixed point is above $lb$) and
  $\cos(ub) < u$ (so it is below $ub$).\<close>

definition lb::real where "lb \<equiv> 0.739085133215"

definition ub::real where "ub \<equiv> 0.739085133216"

lemma lb_gt: "cos lb > lb"
  unfolding lb_def
  by (approximation 50)

lemma ub_lt: "cos ub < ub"
  unfolding ub_def
  by (approximation 50)

lemma lb: "lb < dottie"
proof (rule ccontr)
  assume neg: "\<not> lb < dottie"
  have gd: "g lb > 0" 
    using facts lb_gt by (auto simp: g_def)
  show False
    using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] facts neg
    by (smt (verit, ccfv_SIG) cos_le_one cos_monotone_0_pi lb_gt pi_gt3)
qed

lemma ub: "ub > dottie"
proof (rule ccontr)
  assume neg: "\<not> ub > dottie"
  have gd: "g ub < 0" 
    using facts ub_lt by (auto simp: g_def)
  show False
    using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] facts neg
    by (smt (verit) cos_ge_minus_one ub_lt gd g_def)
qed

subsection \<open>The Dottie number is a universal attractor\<close>

text \<open>Iterating cosine from \emph{any} real starting point converges to the
  Dottie number. The key fact is that $\cos$ is a contraction on $[-1,1]$ with
  Lipschitz constant $\sin 1 < 1$ (since $|\cos' x| = |\sin x| \le \sin 1$ there),
  and that $\cos$ maps all of $\mathbb{R}$ into $[-1,1]$.\<close>

lemma sin1_bounds: "0 < sin (1::real)" "sin (1::real) < 1"
proof -
  have lt: "(1::real) < pi" using pi_gt3 by simp
  have "0 < (1::real)" by simp
  from sin_gt_zero[OF this lt] show "0 < sin (1::real)" .
next
  have "sin 1 < sin (pi/2)"
    using sin_monotone_2pi[of 1 "pi/2"] pi_gt3 by simp
  then show "sin (1::real) < 1" by simp
qed

lemma abs_sin_le_sin1:
  assumes "\<bar>t\<bar> \<le> 1" shows "\<bar>sin t\<bar> \<le> sin (1::real)"
proof -
  have "1 < pi/2" using pi_gt3 by simp
  then show ?thesis
    by (smt (verit, best) assms sin_minus sin_monotone_2pi_le)
qed

text \<open>The mean value theorem turns the derivative bound into a Lipschitz bound.\<close>

lemma cos_contraction_lt:
  fixes x y :: real
  assumes "x < y" "\<bar>x\<bar> \<le> 1" "\<bar>y\<bar> \<le> 1"
  shows "\<bar>cos x - cos y\<bar> \<le> sin 1 * \<bar>x - y\<bar>"
proof -
  have cont: "continuous_on {x..y} cos" by (intro continuous_intros)
  have deriv: "((cos::real\<Rightarrow>real) has_derivative (*) (- sin u)) (at u)" for u :: real
    using DERIV_cos[of u] unfolding has_field_derivative_def by simp
  have "\<exists>\<xi>\<in>{x<..<y}. norm (cos y - cos x) \<le> norm ((*) (- sin \<xi>) (y - x))"
    by (rule mvt_general[OF \<open>x < y\<close> cont]) (use deriv in blast)
  then obtain \<xi> where \<xi>: "\<xi> \<in> {x<..<y}" "norm (cos y - cos x) \<le> norm (- sin \<xi> * (y - x))"
    by auto
  have "\<bar>\<xi>\<bar> \<le> 1" using \<xi> assms by auto
  then have absxi: "\<bar>sin \<xi>\<bar> \<le> sin 1" by (rule abs_sin_le_sin1)
  have "\<bar>cos y - cos x\<bar> \<le> \<bar>sin \<xi>\<bar> * \<bar>y - x\<bar>"
    using \<xi>(2) by (simp add: abs_mult)
  also have "\<dots> \<le> sin 1 * \<bar>y - x\<bar>"
    using absxi by (simp add: mult_right_mono)
  finally show ?thesis
    by (simp add: abs_minus_commute)
qed

lemma cos_contraction:
  fixes x y :: real
  assumes "\<bar>x\<bar> \<le> 1" "\<bar>y\<bar> \<le> 1"
  shows "\<bar>cos x - cos y\<bar> \<le> sin 1 * \<bar>x - y\<bar>"
  using cos_contraction_lt[of x y] cos_contraction_lt[of y x] assms
  by (cases x y rule: linorder_cases) (auto simp: abs_minus_commute)

lemma dottie_in_pm1: "\<bar>dottie\<bar> \<le> 1"
  using facts by simp

lemma cos_step_to_dottie:
  assumes "\<bar>w\<bar> \<le> 1"
  shows "\<bar>cos w - dottie\<bar> \<le> sin 1 * \<bar>w - dottie\<bar>"
  using facts by (metis assms cos_contraction dottie_in_pm1)

text \<open>After one step the iteration lands in $[-1,1]$ and stays there.\<close>

lemma cos_funpow_in_pm1:
  fixes x0 :: real
  assumes "n \<ge> 1"
  shows "\<bar>(cos ^^ n) x0\<bar> \<le> 1"
proof -
  obtain m where "n = Suc m" using assms not0_implies_Suc by force
  then have "(cos ^^ n) x0 = cos ((cos ^^ m) x0)"
    by (simp add: funpow_swap1)
  then show ?thesis by (simp add: abs_cos_le_one)
qed

text \<open>From a start in $[-1,1]$, the distance to the fixed point decays geometrically.\<close>

lemma cos_funpow_bound:
  fixes y0 :: real
  assumes "\<bar>y0\<bar> \<le> 1"
  shows "\<bar>(cos ^^ n) y0 - dottie\<bar> \<le> (sin 1)^n * \<bar>y0 - dottie\<bar>"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have inpm1: "\<bar>(cos ^^ n) y0\<bar> \<le> 1"
    using cos_funpow_in_pm1[of n y0] assms
    by (metis funpow_0 less_one not_le)
  have "\<bar>(cos ^^ Suc n) y0 - dottie\<bar> = \<bar>cos ((cos ^^ n) y0) - dottie\<bar>"
    by (simp add: funpow_swap1)
  also have "\<dots> \<le> sin 1 * \<bar>(cos ^^ n) y0 - dottie\<bar>"
    using cos_step_to_dottie[OF inpm1] .
  also have "\<dots> \<le> sin 1 * ((sin 1)^n * \<bar>y0 - dottie\<bar>)"
    using Suc.IH sin1_bounds(1) by (simp add: mult_left_mono)
  also have "\<dots> = (sin 1)^(Suc n) * \<bar>y0 - dottie\<bar>"
    by (simp add: mult.assoc)
  finally show ?case .
qed

lemma cos_iter_tendsto_unit:
  fixes y0 :: real
  assumes "\<bar>y0\<bar> \<le> 1"
  shows "(\<lambda>n. (cos ^^ n) y0) \<longlonglongrightarrow> dottie"
proof -
  have pow0: "(\<lambda>n. (sin 1)^n) \<longlonglongrightarrow> (0::real)"
    using sin1_bounds by (intro LIMSEQ_realpow_zero) auto
  have null: "(\<lambda>n. (sin 1)^n * \<bar>y0 - dottie\<bar>) \<longlonglongrightarrow> 0"
    using tendsto_mult[OF pow0 tendsto_const, of "\<bar>y0 - dottie\<bar>"] by simp
  have "(\<lambda>n. \<bar>(cos ^^ n) y0 - dottie\<bar>) \<longlonglongrightarrow> 0"
    using tendsto_sandwich[OF _ _ tendsto_const null] cos_funpow_bound[OF assms] by auto
  then have "(\<lambda>n. (cos ^^ n) y0 - dottie) \<longlonglongrightarrow> 0"
    by (rule tendsto_rabs_zero_cancel)
  then show ?thesis
    using Lim_null by blast
qed

theorem cos_iter_tendsto_dottie:
  fixes x0 :: real
  shows "(\<lambda>n. (cos ^^ n) x0) \<longlonglongrightarrow> dottie"
proof -
  have "\<bar>cos x0\<bar> \<le> 1" by (simp add: abs_cos_le_one)
  from cos_iter_tendsto_unit[OF this]
  have "(\<lambda>n. (cos ^^ n) (cos x0)) \<longlonglongrightarrow> dottie" .
  moreover have "\<And>n. (cos ^^ n) (cos x0) = (cos ^^ Suc n) x0"
    by (simp add: funpow_swap1)
  ultimately have "(\<lambda>n. (cos ^^ Suc n) x0) \<longlonglongrightarrow> dottie" by simp
  then show ?thesis
    using filterlim_sequentially_Suc by blast
qed

subsection \<open>A trigonometric identity\<close>

text \<open>Since $\cos(\mathit{dottie}) = \mathit{dottie}$ and $\mathit{dottie} \in (0,1)$, the
  Pythagorean identity gives $\sin(\mathit{dottie}) = \sqrt{1 - \mathit{dottie}^2}$.\<close>

lemma sin_dottie: "sin dottie = sqrt (1 - dottie\<^sup>2)"
proof -
  have "0 < dottie" "dottie < pi" using facts pi_gt3 by auto
  then have pos: "0 < sin dottie" by (rule sin_gt_zero)
  have "(sin dottie)\<^sup>2 = 1 - (cos dottie)\<^sup>2"
    using sin_cos_squared_add[of dottie] by (simp add: algebra_simps)
  also have "\<dots> = 1 - dottie\<^sup>2"
    using facts(3) by simp
  finally have "(sin dottie)\<^sup>2 = 1 - dottie\<^sup>2" .
  then show ?thesis
    using pos by (simp add: real_sqrt_unique)
qed

subsection \<open>Transcendence\<close>

text \<open>By the Hermite--Lindemann--Weierstra\ss\ theorem, $\cos z$ is transcendental
  for every nonzero algebraic @{term z}. If the Dottie number were algebraic, then
  $\cos(\mathit{dottie}) = \mathit{dottie}$ would be both algebraic and transcendental.\<close>

theorem dottie_transcendental: "\<not> algebraic dottie"
proof
  assume alg: "algebraic dottie"
  then have "\<not> algebraic (cos (complex_of_real dottie))"
    using facts transcendental_cos by auto 
  moreover have "cos (complex_of_real dottie) = complex_of_real dottie"
    using facts by (simp add: cos_of_real)
  ultimately show False using alg by simp
qed

end

text \<open> We make key facts available outside the locale \<close>
lemmas dottie_fp = Dottie.facts(3)
lemmas dottie_bounds = Dottie.lb Dottie.ub
lemmas dottie_attractor = Dottie.cos_iter_tendsto_dottie
lemmas dottie_sin = Dottie.sin_dottie
lemmas dottie_transcendental = Dottie.dottie_transcendental

end



