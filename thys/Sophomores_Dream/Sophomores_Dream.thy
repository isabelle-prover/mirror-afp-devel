(*
  File:    Sophomores_Dream.thy
  Author:  Manuel Eberl, University of Innsbruck
*)
section \<open>The Sophomore's Dream\<close>
theory Sophomores_Dream
  imports "HOL-Analysis.Analysis" "HOL-Real_Asymp.Real_Asymp"
begin

text \<open>
  This formalisation mostly follows the very clear proof sketch from Wikipedia~\<^cite>\<open>"wikipedia"\<close>.
  That article also provides an interesting historical perspective. A more detailed 
  exploration of Bernoulli's historical proof can be found in the book by Dunham~\<^cite>\<open>"dunham"\<close>.

  The name `Sophomore's Dream' apparently comes from a book by Borwein et al., in analogy to
  the `Freshman's Dream' equation $(x+y)^n = x^n + y^n$ (which is generally \<^emph>\<open>not\<close> true except
  in rings of characteristic $n$).
\<close>

subsection \<open>Continuity and bounds for $x \log x$\<close>

lemma x_log_x_continuous: "continuous_on {0..1} (\<lambda>x::real. x * ln x)"
proof -
  have "continuous (at x within {0..1}) (\<lambda>x::real. x * ln x)" if "x \<in> {0..1}" for x
  proof (cases "x = 0")
    case True
    have "((\<lambda>x::real. x * ln x) \<longlongrightarrow> 0) (at_right 0)"
      by real_asymp
    thus ?thesis using True
      by (simp add: continuous_def Lim_ident_at at_within_Icc_at_right)
  qed (auto intro!: continuous_intros)
  thus ?thesis
    using continuous_on_eq_continuous_within by blast
qed

lemma x_log_x_within_01_le:
  assumes "x \<in> {0..(1::real)}"
  shows   "x * ln x \<in> {-exp (-1)..0}"
proof -
  have "x * ln x \<le> 0"
    using assms by (cases "x = 0") (auto simp: mult_nonneg_nonpos)
  let ?f = "\<lambda>x::real. x * ln x"
  have diff: "(?f has_field_derivative (ln x + 1)) (at x)" if "x > 0" for x
    using that by (auto intro!: derivative_eq_intros)
  have diff': "?f differentiable at x" if "x > 0" for x
    using diff[OF that] real_differentiable_def by blast

  consider "x = 0" | "x = 1" | "x = exp (-1)" | "0 < x" "x < exp (-1)" | "exp (-1) < x" "x < 1"
    using assms unfolding atLeastAtMost_iff by linarith
  hence "x * ln x \<ge> -exp (-1)"
  proof cases
    assume x: "0 < x" "x < exp (-1)"
    have "\<exists>l z. x < z \<and> z < exp (-1) \<and> (?f has_real_derivative l) (at z) \<and>
             ?f (exp (-1)) - ?f x = (exp (-1) - x) * l"
      using x by (intro MVT continuous_on_subset [OF x_log_x_continuous] diff') auto
    then obtain l z where lz:
      "x < z" "z < exp (-1)" "(?f has_real_derivative l) (at z)"
      "?f x = -exp (-1) - (exp (-1) - x) * l"
      by (auto simp: algebra_simps)
    have [simp]: "l = ln z + 1"
      using DERIV_unique[OF diff[of z] lz(3)] lz(1) x by auto
    have "ln z \<le> ln (exp (-1))"
      using lz x by (subst ln_le_cancel_iff) auto
    hence "(exp (- 1) - x) * l \<le> 0"
      using x lz by (intro mult_nonneg_nonpos) auto
    with lz show ?thesis
      by linarith
  next
    assume x: "exp (-1) < x" "x < 1"
    have "\<exists>l z. exp (-1) < z \<and> z < x \<and> (?f has_real_derivative l) (at z) \<and>
             ?f x - ?f (exp (-1)) = (x - exp (-1)) * l"
    proof (intro MVT continuous_on_subset [OF x_log_x_continuous] diff')
      fix t :: real assume t: "exp (-1) < t"
      show "t > 0"
        by (rule less_trans [OF _ t]) auto
    qed (use x in auto)
    then obtain l z where lz:
      "exp (-1) < z" "z < x" "(?f has_real_derivative l) (at z)"
      "?f x = -exp (-1) - (exp (-1) - x) * l"
      by (auto simp: algebra_simps)
    have "z > 0"
      by (rule less_trans [OF _ lz(1)]) auto
    have [simp]: "l = ln z + 1"
      using DERIV_unique[OF diff[of z] lz(3)] \<open>z > 0\<close> by auto
    have "ln z \<ge> ln (exp (-1))"
      using lz \<open>z > 0\<close> by (subst ln_le_cancel_iff) auto
    hence "(exp (- 1) - x) * l \<le> 0"
      using x lz by (intro mult_nonpos_nonneg) auto
    with lz show ?thesis
      by linarith
  qed auto

  with \<open>x * ln x \<le> 0\<close> show ?thesis
    by auto
qed


subsection \<open>Convergence, Summability, Integrability\<close>

text \<open>
  As a first result we can show that the two sums that occur in the two different versions
  of the Sophomore's Dream are absolutely summable. This is achieved by a simple comparison 
  test with the series $\sum_{k=1}^\infty k^{-2}$, as $k^{-k} \in O(k^{-2})$.
\<close>
theorem abs_summable_sophomores_dream: "summable (\<lambda>k. 1 / real (k ^ k))"
proof (rule summable_comparison_test_bigo)
  show "(\<lambda>k. 1 / real (k ^ k)) \<in> O(\<lambda>k. 1 / real k ^ 2)"
    by real_asymp
  show "summable (\<lambda>n. norm (1 / real n ^ 2))"
    using inverse_power_summable[of 2, where ?'a = real] by (simp add: field_simps)
qed

text \<open>
  The existence of the integral is also fairly easy to show since the integrand is continuous
  and the integration domain is compact. There is, however, one hiccup: The integrand is not
  actually continuous.

  We have $\lim_{x\to 0} x^x = 1$, but in Isabelle $0^0$ is defined as \<open>0\<close> (for real numbers).
  Thus, there is a discontinuity at \<open>x = 0\<close>

  However, this is a removable discontinuity since for any $x>0$ we have $x^x = e^{x\log x}$, and
  as we have just shown, $e^{x \log x}$ \<^emph>\<open>is\<close> continuous on $[0, 1]$. Since the two integrands
  differ only for \<open>x = 0\<close> (which is negligible), the integral still exists.
\<close>
theorem integrable_sophomores_dream: "(\<lambda>x::real. x powr x) integrable_on {0..1}"
proof -
  have "(\<lambda>x::real. exp (x * ln x)) integrable_on {0..1}"
    by (intro integrable_continuous_real continuous_on_exp x_log_x_continuous)
  also have "?this \<longleftrightarrow> (\<lambda>x::real. exp (x * ln x)) integrable_on {0<..<1}"
    by (simp add: integrable_on_Icc_iff_Ioo)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x::real. x powr x) integrable_on {0<..<1}"
    by (intro integrable_cong) (auto simp: powr_def)
  also have "\<dots> \<longleftrightarrow> ?thesis"
    by (simp add: integrable_on_Icc_iff_Ioo)
  finally show ?thesis .
qed

text \<open>
  Next, we have to show the absolute convergence of the two auxiliary sums that will occur in
  our proofs so that we can exchange the order of integration and summation. This is done
  with a straightforward application of the Weierstra\ss\ \<open>M\<close> test.
\<close>
lemma uniform_limit_sophomores_dream1:
  "uniform_limit {0..(1::real)}
      (\<lambda>n x. \<Sum>k<n. (x * ln x) ^ k / fact k)
      (\<lambda>x. \<Sum>k. (x * ln x) ^ k / fact k)
      sequentially"
proof (rule Weierstrass_m_test)
  show "summable (\<lambda>k. exp (-1) ^ k / fact k :: real)"
    using summable_exp[of "exp (-1)"] by (simp add: field_simps)
next
  fix k :: nat and x :: real
  assume x: "x \<in> {0..1}"
  have "norm ((x * ln x) ^ k / fact k) = norm (x * ln x) ^ k / fact k"
    by (simp add: power_abs)
  also have "\<dots> \<le> exp (-1) ^ k / fact k"
    by (intro divide_right_mono power_mono) (use x_log_x_within_01_le [of x] x in auto)
  finally show "norm ((x * ln x) ^ k / fact k) \<le> exp (- 1) ^ k / fact k" .
qed

lemma uniform_limit_sophomores_dream2:
  "uniform_limit {0..(1::real)}
      (\<lambda>n x. \<Sum>k<n. (-(x * ln x)) ^ k / fact k)
      (\<lambda>x. \<Sum>k. (-(x * ln x)) ^ k / fact k)
      sequentially"
proof (rule Weierstrass_m_test)
  show "summable (\<lambda>k. exp (-1) ^ k / fact k :: real)"
    using summable_exp[of "exp (-1)"] by (simp add: field_simps)
next
  fix k :: nat and x :: real
  assume x: "x \<in> {0..1}"
  have "norm ((-x * ln x) ^ k / fact k) = norm (x * ln x) ^ k / fact k"
    by (simp add: power_abs)
  also have "\<dots> \<le> exp (-1) ^ k / fact k"
    by (intro divide_right_mono power_mono) (use x_log_x_within_01_le [of x] x in auto)
  finally show "norm ((-(x * ln x)) ^ k / fact k) \<le> exp (- 1) ^ k / fact k" by simp
qed


subsection \<open>An auxiliary integral\<close>

text \<open>
  Next we compute the integral
    \[\int_0^1 (x\log x)^n\,\text{d}x = \frac{(-1)^n\, n!}{(n+1)^{n+1}}\ ,\]
  which is a key ingredient in our proof.
\<close>
lemma sophomores_dream_aux_integral:
  "((\<lambda>x. (x * ln x) ^ n) has_integral (- 1) ^ n * fact n / real ((n + 1) ^ (n + 1))) {0<..<1}"
proof -
  have "((\<lambda>t. t powr real n / exp t) has_integral fact n) {0..}"
    using Gamma_integral_real[of "n + 1"] by (auto simp: Gamma_fact powr_realpow)
  also have "?this \<longleftrightarrow> ((\<lambda>t. t powr real n / exp t) has_integral fact n) {0<..}"
  proof (rule has_integral_spike_set_eq)
    have eq: "{x \<in> {0<..} - {0..}. x powr real n / exp x \<noteq> 0} = {}"
      by auto
    thus "negligible {x \<in> {0<..} - {0..}. x powr real n / exp x \<noteq> 0}"
      by (subst eq) auto
    have "{x \<in> {0..} - {0<..}. x powr real n / exp x \<noteq> 0} \<subseteq> {0}"
      by auto
    moreover have "negligible {0::real}"
      by simp
    ultimately show "negligible {x \<in> {0..} - {0<..}. x powr real n / exp x \<noteq> 0}"
      by (meson negligible_subset)
  qed
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t::real. t ^ n / exp t) has_integral fact n) {0<..}"
    by (intro has_integral_spike_eq) (auto simp: powr_realpow)
  finally have 1: "((\<lambda>t::real. t ^ n / exp t) has_integral fact n) {0<..}" .

  have "(\<lambda>x::real. \<bar>x\<bar> ^ n / exp x) integrable_on {0<..} \<longleftrightarrow>
        (\<lambda>x::real. x ^ n / exp x) integrable_on {0<..}"
    by (intro integrable_cong) auto
  hence 2: "(\<lambda>t::real. t ^ n / exp t) absolutely_integrable_on {0<..}"
    using 1 by (simp add: absolutely_integrable_on_def power_abs has_integral_iff)

  define g :: "real \<Rightarrow> real" where "g = (\<lambda>x. -ln x * (n + 1))"
  define g' :: "real \<Rightarrow> real" where "g' = (\<lambda>x. -(n + 1) / x)"
  define h :: "real \<Rightarrow> real" where "h = (\<lambda>u. exp (-u / (n + 1)))"
  have bij: "bij_betw g {0<..<1} {0<..}"
    by (rule bij_betwI[of _ _ _ h]) (auto simp: g_def h_def mult_neg_pos)
  have deriv: "(g has_real_derivative g' x) (at x within {0<..<1})"
    if "x \<in> {0<..<1}" for x
    unfolding g_def g'_def using that by (auto intro!: derivative_eq_intros simp: field_simps)

  have "(\<lambda>t::real. t ^ n / exp t) absolutely_integrable_on g ` {0<..<1} \<and>
        integral (g ` {0<..<1}) (\<lambda>t::real. t ^ n / exp t) = fact n"
    using 1 2 bij by (simp add: bij_betw_def has_integral_iff)
  also have "?this \<longleftrightarrow> ((\<lambda>x. \<bar>g' x\<bar> *\<^sub>R (g x ^ n / exp (g x))) absolutely_integrable_on {0<..<1} \<and>
                       integral {0<..<1} (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R (g x ^ n / exp (g x))) = fact n)"
    by (intro has_absolute_integral_change_of_variables_1' [symmetric] deriv)
       (auto simp: inj_on_def g_def)
  finally have "((\<lambda>x. \<bar>g' x\<bar> *\<^sub>R (g x ^ n / exp (g x))) has_integral fact n) {0<..<1}"
    using eq_integralD set_lebesgue_integral_eq_integral(1) by blast
  also have "?this \<longleftrightarrow>
     ((\<lambda>x::real. ((-1)^n*(n+1)^(n+1)) *\<^sub>R (ln x ^ n * x ^ n)) has_integral fact n) {0<..<1}"
  proof (rule has_integral_cong)
    fix x :: real assume x: "x \<in> {0<..<1}"
    have "\<bar>g' x\<bar> *\<^sub>R (g x ^ n / exp (g x)) =
            (-1) ^ n * (real n + 1) ^ (n + 1) * ln x ^ n * (exp (ln x * (n + 1)) / x)"
      using x by (simp add: g_def g'_def exp_minus power_minus' divide_simps add_ac)
    also have "exp (ln x * (n + 1)) = x powr real (n + 1)"
      using x by (simp add: powr_def)
    also have "\<dots> / x = x ^ n"
      using x by (subst powr_realpow) auto
    finally show "\<bar>g' x\<bar> *\<^sub>R (g x ^ n / exp (g x)) =
                    ((-1)^n*(n+1)^(n+1)) *\<^sub>R (ln x ^ n * x ^ n)"
      by (simp add: algebra_simps)
  qed
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x::real. ln x ^ n * x ^ n) has_integral
                      fact n /\<^sub>R real_of_int ((- 1) ^ n * int ((n + 1) ^ (n + 1)))) {0<..<1}"
    by (intro has_integral_cmul_iff') (auto simp del: power_Suc)
  also have "fact n /\<^sub>R real_of_int ((- 1) ^ n * int ((n + 1) ^ (n + 1))) =
             (-1) ^ n * fact n / (n+1) ^ (n+1)"
    by (auto simp: divide_simps)
  finally show ?thesis
    by (simp add: power_mult_distrib mult_ac)
qed

subsection \<open>Main proofs\<close>


text \<open>
  We can now show the first formula: $\int_0^1 x^{-x}\,\text{d}x = \sum_{n=1}^\infty n^{-n}$
\<close>
lemma sophomores_dream_aux1:
  "summable (\<lambda>k. 1 / real ((k+1)^(k+1)))"
  "integral {0..1} (\<lambda>x. x powr (-x)) = (\<Sum>n. 1 / (n+1)^(n+1))"
proof -
  define S where "S = (\<lambda>x::real. \<Sum>k. (-(x * ln x)) ^ k / fact k)"
  have S_eq: "S x = x powr (-x)" if "x > 0" for x
  proof -
    have "S x = exp (-x * ln x)"
      by (simp add: S_def exp_def field_simps)
    also have "\<dots> = x powr (-x)"
      using \<open>x > 0\<close> by (simp add: powr_def)
    finally show ?thesis .
  qed

  have cont: "continuous_on {0..1} (\<lambda>x::real. \<Sum>k<n. (-(x * ln x)) ^ k / fact k)" for n
    by (intro continuous_on_sum continuous_on_divide x_log_x_continuous continuous_on_power
              continuous_on_const continuous_on_minus) auto

  obtain I J where IJ: "\<And>n. ((\<lambda>x. \<Sum>k<n. (-(x * ln x)) ^ k / fact k) has_integral I n) {0..1}"
                       "(S has_integral J) {0..1}" "I \<longlonglongrightarrow> J"
    using uniform_limit_integral [OF uniform_limit_sophomores_dream2 cont] by (auto simp: S_def)

  note \<open>(S has_integral J) {0..1}\<close>
  also have "(S has_integral J) {0..1} \<longleftrightarrow> (S has_integral J) {0<..<1}"
    by (simp add: has_integral_Icc_iff_Ioo)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. x powr (-x)) has_integral J) {0<..<1}"
    by (intro has_integral_cong) (use S_eq in auto)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. x powr (-x)) has_integral J) {0..1}"
    by (simp add: has_integral_Icc_iff_Ioo)
  finally have integral: "((\<lambda>x. x powr (-x)) has_integral J) {0..1}" .

  have I_eq: "I = (\<lambda>n. \<Sum>k<n. 1 / real ((k+1)^(k+1)))"
  proof
    fix n :: nat
    have "((\<lambda>x::real. \<Sum>k<n. (-1)^k * ((x * ln x) ^ k / fact k)) has_integral
            (\<Sum>k<n. (-1)^k * ((-1)^k * fact k / real ((k + 1) ^ (k + 1)) / fact k))) {0<..<1}"
      by (intro has_integral_sum[OF _ has_integral_mult_right] has_integral_divide
                sophomores_dream_aux_integral) auto
    also have "(\<lambda>x::real. \<Sum>k<n. (-1)^k * ((x * ln x) ^ k / fact k)) =
               (\<lambda>x::real. \<Sum>k<n. (-(x * ln x)) ^ k / fact k)"
      by (simp add: power_minus')
    also have "(\<Sum>k<n. (-1)^k * ((-1) ^ k * fact k / real ((k + 1) ^ (k + 1)) / fact k)) =
               (\<Sum>k<n. 1 / real ((k + 1) ^ (k + 1)))"
      by simp
    also note has_integral_Icc_iff_Ioo [symmetric]
    finally show "I n = (\<Sum>k<n. 1 / real ((k+1)^(k+1)))"
      by (rule has_integral_unique [OF IJ(1)[of n]])
  qed
  hence sums: "(\<lambda>k. 1 / real ((k + 1) ^ (k + 1))) sums J"
    using IJ(3) I_eq by (simp add: sums_def)
  
  from sums show "summable (\<lambda>k. 1 / real ((k+1)^(k+1)))"
    by (simp add: sums_iff)
  from integral sums show "integral {0..1} (\<lambda>x. x powr (-x)) = (\<Sum>n. 1 / (n+1)^(n+1))"
    by (simp add: sums_iff has_integral_iff)
qed

theorem sophomores_dream1:
  "(\<lambda>k::nat. norm (k powi (-k))) summable_on {1..}"
  "integral {0..1} (\<lambda>x. x powr (-x)) = (\<Sum>\<^sub>\<infinity> k\<in>{(1::nat)..}. k powi (-k))"
proof -
  let ?I = "integral {0..1} (\<lambda>x. x powr (-x))"
  have "(\<lambda>k::nat. norm (k powi (-k))) summable_on UNIV"
    using abs_summable_sophomores_dream
    by (intro norm_summable_imp_summable_on) (auto simp: power_int_minus field_simps)
  thus "(\<lambda>k::nat. norm (k powi (-k))) summable_on {1..}"
    by (rule summable_on_subset_banach) auto

  have "(\<lambda>n. 1 / (n+1)^(n+1)) sums ?I"
    using sophomores_dream_aux1 by (simp add: sums_iff)
  moreover have "summable (\<lambda>n. norm (1 / real (Suc n ^ Suc n)))"
    by (subst summable_Suc_iff) (use abs_summable_sophomores_dream in \<open>auto simp: field_simps\<close>)
  ultimately have "((\<lambda>n::nat. 1 / (n+1)^(n+1)) has_sum ?I) UNIV"
    by (intro norm_summable_imp_has_sum) auto
  also have "?this \<longleftrightarrow> (((\<lambda>n::nat. 1 / n^n) \<circ> Suc) has_sum ?I) UNIV"
    by (simp add: o_def field_simps)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n::nat. 1 / n^n) has_sum ?I) (Suc ` UNIV)"
    by (intro has_sum_reindex [symmetric]) auto
  also have "Suc ` UNIV = {1..}"
    using greaterThan_0 by auto
  also have "((\<lambda>n::nat. (1 / real (n ^ n))) has_sum ?I) {1..} \<longleftrightarrow>
             ((\<lambda>n::nat. n powi (-n)) has_sum ?I) {1..}"
    by (intro has_sum_cong) (auto simp: power_int_minus field_simps power_minus')
  finally show "integral {0..1} (\<lambda>x. x powr (-x)) = (\<Sum>\<^sub>\<infinity>k\<in>{(1::nat)..}. k powi (-k))"
    by (auto dest!: infsumI simp: algebra_simps)
qed


text \<open>
  Next, we show the second formula: $\int_0^1 x^x\,\text{d}x = -\sum_{n=1}^\infty (-n)^{-n}$
\<close>
lemma sophomores_dream_aux2:
  "summable (\<lambda>k. (-1) ^ k / real ((k+1)^(k+1)))"
  "integral {0..1} (\<lambda>x. x powr x) = (\<Sum>n. (-1)^n / (n+1)^(n+1))"
proof -
  define S where "S = (\<lambda>x::real. \<Sum>k. (x * ln x) ^ k / fact k)"
  have S_eq: "S x = x powr x" if "x > 0" for x
  proof -
    have "S x = exp (x * ln x)"
      by (simp add: S_def exp_def field_simps)
    also have "\<dots> = x powr x"
      using \<open>x > 0\<close> by (simp add: powr_def)
    finally show ?thesis .
  qed

  have cont: "continuous_on {0..1} (\<lambda>x::real. \<Sum>k<n. (x * ln x) ^ k / fact k)" for n
    by (intro continuous_on_sum continuous_on_divide x_log_x_continuous continuous_on_power
              continuous_on_const) auto

  obtain I J where IJ: "\<And>n. ((\<lambda>x. \<Sum>k<n. (x * ln x) ^ k / fact k) has_integral I n) {0..1}"
                       "(S has_integral J) {0..1}" "I \<longlonglongrightarrow> J"
    using uniform_limit_integral [OF uniform_limit_sophomores_dream1 cont] by (auto simp: S_def)

  note \<open>(S has_integral J) {0..1}\<close>
  also have "(S has_integral J) {0..1} \<longleftrightarrow> (S has_integral J) {0<..<1}"
    by (simp add: has_integral_Icc_iff_Ioo)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. x powr x) has_integral J) {0<..<1}"
    by (intro has_integral_cong) (use S_eq in auto)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. x powr x) has_integral J) {0..1}"
    by (simp add: has_integral_Icc_iff_Ioo)
  finally have integral: "((\<lambda>x. x powr x) has_integral J) {0..1}" .

  have I_eq: "I = (\<lambda>n. \<Sum>k<n. (-1) ^ k / real ((k+1)^(k+1)))"
  proof
    fix n :: nat
    have "((\<lambda>x::real. \<Sum>k<n. (x * ln x) ^ k / fact k) has_integral
            (\<Sum>k<n. (-1) ^ k * fact k / real ((k + 1) ^ (k + 1)) / fact k)) {0<..<1}"
      by (intro has_integral_sum has_integral_divide sophomores_dream_aux_integral) auto
    also have "(\<Sum>k<n. (- 1) ^ k * fact k / real ((k + 1) ^ (k + 1)) / fact k) =
               (\<Sum>k<n. (- 1) ^ k / real ((k + 1) ^ (k + 1)))"
      by simp
    also note has_integral_Icc_iff_Ioo [symmetric]
    finally show "I n = (\<Sum>k<n. (-1) ^ k / real ((k+1)^(k+1)))"
      by (rule has_integral_unique [OF IJ(1)[of n]])
  qed
  hence sums: "(\<lambda>k. (-1) ^ k / real ((k + 1) ^ (k + 1))) sums J"
    using IJ(3) I_eq by (simp add: sums_def)
  
  from sums show "summable (\<lambda>k. (-1) ^ k / real ((k+1)^(k+1)))"
    by (simp add: sums_iff)
  from integral sums show "integral {0..1} (\<lambda>x. x powr x) = (\<Sum>n. (-1)^n / (n+1)^(n+1))"
    by (simp add: sums_iff has_integral_iff)
qed

theorem sophomores_dream2:
  "(\<lambda>k::nat. norm ((-k) powi (-k))) summable_on {1..}"
  "integral {0..1} (\<lambda>x. x powr x) = -(\<Sum>\<^sub>\<infinity> k\<in>{(1::nat)..}. (-k) powi (-k))"
proof -
  let ?I = "integral {0..1} (\<lambda>x. x powr x)"
  have "(\<lambda>k::nat. norm ((-k) powi (-k))) summable_on UNIV"
    using abs_summable_sophomores_dream
    by (intro norm_summable_imp_summable_on) (auto simp: power_int_minus field_simps)
  thus "(\<lambda>k::nat. norm ((-k) powi (-k))) summable_on {1..}"
    by (rule summable_on_subset_banach) auto

  have "(\<lambda>n. (-1)^n / (n+1)^(n+1)) sums ?I"
    using sophomores_dream_aux2 by (simp add: sums_iff)
  moreover have "summable (\<lambda>n. 1 / real (Suc n ^ Suc n))"
    by (subst summable_Suc_iff) (use abs_summable_sophomores_dream in \<open>auto simp: field_simps\<close>)
  hence "summable (\<lambda>n. norm ((- 1) ^ n / real (Suc n ^ Suc n)))"
    by simp
  ultimately have "((\<lambda>n::nat. (-1)^n / (n+1)^(n+1)) has_sum ?I) UNIV"
    by (intro norm_summable_imp_has_sum) auto
  also have "?this \<longleftrightarrow> (((\<lambda>n::nat. -((-1)^n / n^n)) \<circ> Suc) has_sum ?I) UNIV"
    by (simp add: o_def field_simps)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n::nat. -((-1)^n / n ^ n)) has_sum ?I) (Suc ` UNIV)"
    by (intro has_sum_reindex [symmetric]) auto
  also have "Suc ` UNIV = {1..}"
    using greaterThan_0 by auto
  also have "((\<lambda>n::nat. -((- 1) ^ n / real (n ^ n))) has_sum ?I) {1..} \<longleftrightarrow>
             ((\<lambda>n::nat. -((-n) powi (-n))) has_sum ?I) {1..}"
    by (intro has_sum_cong) (auto simp: power_int_minus field_simps power_minus')
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n::nat. (-n) powi (-n)) has_sum (-?I)) {1..}"
    by (simp add: has_sum_uminus)
  finally show "integral {0..1} (\<lambda>x. x powr x) = -(\<Sum>\<^sub>\<infinity>k\<in>{(1::nat)..}. (-k) powi (-k))"
    by (auto dest!: infsumI simp: algebra_simps)
qed

end