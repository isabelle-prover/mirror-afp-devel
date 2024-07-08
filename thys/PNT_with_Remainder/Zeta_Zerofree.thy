theory Zeta_Zerofree
imports
  "PNT_Complex_Analysis_Lemmas"
begin
unbundle pnt_notation

section \<open>Zero-free region of zeta function\<close>

lemma cos_inequality_1:
  fixes x :: real
  shows "3 + 4 * cos x + cos (2 * x) \<ge> 0"
proof -
  have "cos (2 * x) = (cos x)\<^sup>2 - (sin x)\<^sup>2"
    by (rule cos_double)
  also have "\<dots> = (cos x)\<^sup>2 - (1 - (cos x)\<^sup>2)"
    unfolding sin_squared_eq ..
  also have "\<dots> = 2 * (cos x)\<^sup>2 - 1" by auto
  finally have 1: "cos (2 * x) = 2 * (cos x)\<^sup>2 - 1" .
  have "0 \<le> 2 * (1 + cos x)\<^sup>2" by auto
  also have "\<dots> = 3 + 4 * cos x + (2 * (cos x)\<^sup>2 - 1)"
    by (simp add: field_simps power2_eq_square)
  finally show ?thesis unfolding 1.
qed

lemma multiplicative_fds_zeta:
  "completely_multiplicative_function (fds_nth fds_zeta_complex)"
  by standard auto

lemma fds_mangoldt_eq:
  "fds mangoldt_complex = -(fds_deriv fds_zeta / fds_zeta)"
proof -
  have "fds_nth fds_zeta_complex 1 \<noteq> 0" by auto
  hence "fds_nth (fds_deriv fds_zeta_complex / fds_zeta) n = -fds_nth fds_zeta n * mangoldt n" for n
    using multiplicative_fds_zeta
    by (intro fds_nth_logderiv_completely_multiplicative)
  thus ?thesis by (intro fds_eqI, auto)
qed

lemma abs_conv_abscissa_log_deriv:
  "abs_conv_abscissa (fds_deriv fds_zeta_complex / fds_zeta) \<le> 1"
  by (rule abs_conv_abscissa_completely_multiplicative_log_deriv
      [OF multiplicative_fds_zeta, unfolded abs_conv_abscissa_zeta], auto)

lemma abs_conv_abscissa_mangoldt:
  "abs_conv_abscissa (fds mangoldt_complex) \<le> 1"
  using abs_conv_abscissa_log_deriv
  by (subst fds_mangoldt_eq, subst abs_conv_abscissa_minus)

lemma
  assumes s: "Re s > 1"
  shows eval_fds_mangoldt: "eval_fds (fds mangoldt) s = - deriv zeta s / zeta s"
    and abs_conv_mangoldt: "fds_abs_converges (fds mangoldt) s"
proof -
  from abs_conv_abscissa_log_deriv
  have 1: "abs_conv_abscissa (fds_deriv fds_zeta_complex / fds_zeta) < ereal (s \<bullet> 1)"
    using s by (intro le_ereal_less, auto simp: one_ereal_def)
  have 2: "abs_conv_abscissa fds_zeta_complex < ereal (s \<bullet> 1)"
    using s by (subst abs_conv_abscissa_zeta, auto)
  hence 3: "fds_abs_converges (fds_deriv fds_zeta_complex / fds_zeta) s"
    by (intro fds_abs_converges) (rule 1)
  have "eval_fds (fds mangoldt) s = eval_fds (-(fds_deriv fds_zeta_complex / fds_zeta)) s"
    using fds_mangoldt_eq by auto
  also have "\<dots> = -eval_fds (fds_deriv fds_zeta_complex / fds_zeta) s"
    by (intro eval_fds_uminus fds_abs_converges_imp_converges 3)
  also have "\<dots> = -(eval_fds (fds_deriv fds_zeta_complex) s / eval_fds fds_zeta s)"
    using s by (subst eval_fds_log_deriv; ((intro 1 2)?, (auto intro!: eval_fds_zeta_nonzero)?))
  also have "\<dots> = - deriv zeta s / zeta s"
    using s by (subst eval_fds_zeta, blast, subst eval_fds_deriv_zeta, auto)
  finally show "eval_fds (fds mangoldt) s = - deriv zeta s / zeta s" .
  show "fds_abs_converges (fds mangoldt) s"
    by (subst fds_mangoldt_eq) (intro fds_abs_converges_uminus 3)
qed

lemma sums_mangoldt:
  fixes s :: complex
  assumes s: "Re s > 1"
  shows "((\<lambda>n. mangoldt n / n nat_powr s) has_sum - deriv zeta s / zeta s) {1..}"
proof -
  let ?f = "(\<lambda>n. mangoldt n / n nat_powr s)"
  have 1: "fds_abs_converges (fds mangoldt) s"
    by (intro abs_conv_mangoldt s)
  hence 2: "fds_converges (fds mangoldt) s"
    by (rule fds_abs_converges_imp_converges)
  hence "summable (\<lambda>n. \<parallel>fds_nth (fds mangoldt) n / nat_power n s\<parallel>)"
    by (fold fds_abs_converges_def, intro 1)
  moreover have "(\<lambda>n. fds_nth (fds mangoldt) n / nat_power n s) sums (- deriv zeta s / zeta s)"
    by (subst eval_fds_mangoldt(1) [symmetric], intro s, fold fds_converges_iff, intro 2)
  ultimately have "((\<lambda>n. fds_nth (fds mangoldt) n / n nat_powr s) has_sum - deriv zeta s / zeta s) UNIV"
    by (fold nat_power_complex_def, rule norm_summable_imp_has_sum)
  moreover have [simp]: "(if n = 0 then 0 else mangoldt n) = mangoldt n" for n by auto
  ultimately have "(?f has_sum - deriv zeta s / zeta s) UNIV" by (auto simp add: fds_nth_fds)
  hence 3: "(?f has_sum - deriv zeta s / zeta s) UNIV" by auto
  have "sum ?f {0} = 0" by auto
  moreover have "(?f has_sum sum ?f {0}) {0}"
    by (rule has_sum_finite, auto)
  ultimately have "(?f has_sum 0) {0}" by auto
  hence "(?f has_sum - deriv zeta s / zeta s - 0) (UNIV - {0})"
    by (intro has_sum_Diff 3, auto)
  moreover have "UNIV - {0 :: nat} = {1..}" by auto
  ultimately show "(?f has_sum - deriv zeta s / zeta s) {1..}" by auto
qed

lemma sums_Re_logderiv_zeta:
  fixes \<sigma> t :: real
  assumes s: "\<sigma> > 1"
  shows "((\<lambda>n. mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n))
    has_sum Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))) {1..}"
proof -
  have "((\<lambda>x. Re (mangoldt_complex x / x nat_powr Complex \<sigma> t))
    has_sum Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))) {1..}"
    using s by (intro has_sum_Re sums_mangoldt) auto
  moreover have "Re (mangoldt n / n nat_powr (Complex \<sigma> t))
    = mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n)" if *: "1 \<le> n" for n
  proof -
    let ?n = "n :: complex"
    have "1 / n nat_powr (Complex \<sigma> t) = n nat_powr (Complex (-\<sigma>) (-t))"
      by (fold powr_minus_divide, auto simp add: legacy_Complex_simps)
    also have "\<dots> = exp (Complex (-\<sigma> * ln n) (-t * ln n))"
      unfolding powr_def by (auto simp add: field_simps legacy_Complex_simps, use * in linarith)
    finally have "Re (1 / n nat_powr (Complex \<sigma> t)) = Re \<dots>" by auto
    also have "\<dots> = n nat_powr (-\<sigma>) * cos (t * ln n)"
      by (unfold powr_def, subst Re_exp, use * in auto)
    finally have 1: "mangoldt_real n * Re (1 / n nat_powr (Complex \<sigma> t))
      = mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n)" by auto
    have rule_1: "Re (w * z) = Re w * Re z" if *: "Im w = 0" for z w :: complex using * by auto
    have "Re (mangoldt n * (1 / n nat_powr (Complex \<sigma> t)))
      = mangoldt_real n * Re (1 / n nat_powr (Complex \<sigma> t))"
      by (subst rule_1, auto)
    with 1 show ?thesis by auto
  qed
  ultimately show "((\<lambda>n. mangoldt_real n * n nat_powr (- \<sigma>) * cos (t * ln (real n)))
    has_sum Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))) {1..}"
    by (subst has_sum_cong) auto
qed

lemma logderiv_zeta_ineq:
  fixes \<sigma> t :: real
  assumes s: "\<sigma> > 1"
  shows "3 * Re (logderiv zeta (Complex \<sigma> 0)) + 4 * Re (logderiv zeta (Complex \<sigma> t))
    + Re (logderiv zeta (Complex \<sigma> (2*t))) \<le> 0" (is "?x \<le> 0")
proof -
  have [simp]: "Re (-z) = - Re z" for z by auto
  have "((\<lambda>n.
      3 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (0 * ln n))
    + 4 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n))
    + 1 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (2*t * ln n))
    ) has_sum
      3 * Re (- deriv zeta (Complex \<sigma> 0) / zeta (Complex \<sigma> 0))
    + 4 * Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))
    + 1 * Re (- deriv zeta (Complex \<sigma> (2*t)) / zeta (Complex \<sigma> (2*t)))
    ) {1..}"
  by (intro has_sum_add has_sum_cmult_right sums_Re_logderiv_zeta s)
  hence *: "((\<lambda>n. mangoldt_real n * n nat_powr (-\<sigma>)
    * (3 + 4 * cos (t * ln n) + cos (2 * (t * ln n)))
    ) has_sum -?x) {1..}"
  unfolding logderiv_def by (auto simp add: field_simps)
  have "-?x \<ge> 0"
  by (rule has_sum_nonneg, rule *,
     intro mult_nonneg_nonneg,
     auto intro: mangoldt_nonneg cos_inequality_1)
  thus "?x \<le> 0" by linarith
qed

lemma sums_zeta_real:
  fixes r :: real
  assumes "1 < r"
  shows "(\<Sum>n. (n\<^sub>+) powr -r) = Re (zeta r)"
proof -
  have "(\<Sum>n. (n\<^sub>+) powr -r) = (\<Sum>n. Re (n\<^sub>+ powr (-r :: complex)))"
    by (subst of_real_nat_power) auto
  also have "\<dots> = (\<Sum>n. Re (n\<^sub>+ powr - (r :: complex)))" by auto
  also have "\<dots> = Re (\<Sum>n. n\<^sub>+ powr - (r :: complex))"
    by (intro Re_suminf [symmetric] summable_zeta)
       (use assms in auto)
  also have "\<dots> = Re (zeta r)"
    using Re_complex_of_real zeta_conv_suminf assms by presburger
  finally show ?thesis .
qed

lemma inverse_zeta_bound':
  assumes "1 < Re s"
  shows "\<parallel>inverse (zeta s)\<parallel> \<le> Re (zeta (Re s))"
proof -
  write moebius_mu (\<open>\<mu>\<close>)
  let ?f = "\<lambda>n :: nat. \<mu> (n\<^sub>+) / (n\<^sub>+) powr s"
  let ?g = "\<lambda>n :: nat. (n\<^sub>+) powr - Re s"
  have "\<parallel>\<mu> n :: complex\<parallel> \<le> 1" for n by (auto simp add: power_neg_one_If moebius_mu_def)
  hence 1: "\<parallel>?f n\<parallel> \<le> ?g n" for n
    by (auto simp add: powr_minus norm_divide norm_powr_real_powr field_simps)
  have "inverse (zeta s) = (\<Sum>n. ?f n)"
    by (intro sums_unique inverse_zeta_sums assms)
  hence "\<parallel>inverse (zeta s)\<parallel> = \<parallel>\<Sum>n. ?f n\<parallel>" by auto
  also have "\<dots> \<le> (\<Sum>n. ?g n)" by (intro suminf_norm_bound summable_zeta_real assms 1)
  finally show ?thesis using sums_zeta_real assms by auto
qed

lemma zeta_bound':
  assumes "1 < Re s"
  shows "\<parallel>zeta s\<parallel> \<le> Re (zeta (Re s))"
proof -
  let ?f = "\<lambda>n :: nat. (n\<^sub>+) powr - s"
  let ?g = "\<lambda>n :: nat. (n\<^sub>+) powr - Re s"
  have "zeta s = (\<Sum>n. ?f n)" by (intro sums_unique sums_zeta assms)
  hence "\<parallel>zeta s\<parallel> = \<parallel>\<Sum>n. ?f n\<parallel>" by auto
  also have "\<dots> \<le> (\<Sum>n. ?g n)"
    by (intro suminf_norm_bound summable_zeta_real assms)
       (subst norm_nat_power, auto)
  also have "\<dots> = Re (zeta (Re s))" by (subst sums_zeta_real) (use assms in auto)
  finally show ?thesis .
qed

lemma zeta_bound_trivial':
  assumes "1 / 2 \<le> Re s \<and> Re s \<le> 2"
    and "\<bar>Im s\<bar> \<ge> 1 / 11"
  shows "\<parallel>zeta s\<parallel> \<le> 12 + 2 * \<bar>Im s\<bar>"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s"
    by (rule pre_zeta_1_bound) (use assms in auto)
  also have "\<dots> \<le> (\<bar>Re s\<bar> + \<bar>Im s\<bar>) / Re s"
  proof -
    have "\<parallel>s\<parallel> \<le> \<bar>Re s\<bar> + \<bar>Im s\<bar>" using cmod_le by auto
    thus ?thesis using assms by (auto intro: divide_right_mono)
  qed
  also have "\<dots> = 1 + \<bar>Im s\<bar> / Re s"
    using assms by (simp add: field_simps)
  also have "\<dots> \<le> 1 + \<bar>Im s\<bar> / (1 / 2)"
    using assms by (intro add_left_mono divide_left_mono) auto
  finally have 1: "\<parallel>pre_zeta 1 s\<parallel> \<le> 1 + 2 * \<bar>Im s\<bar>" by auto
  have "\<parallel>1 / (s - 1)\<parallel> = 1 / \<parallel>s - 1\<parallel>" by (subst norm_divide) auto
  also have "\<dots> \<le> 11" proof -
    have "1 / 11 \<le> \<bar>Im s\<bar>" by (rule assms(2))
    also have "\<dots> = \<bar>Im (s - 1)\<bar>" by auto
    also have "\<dots> \<le> \<parallel>s - 1\<parallel>" by (rule abs_Im_le_cmod)
    finally show ?thesis by (intro mult_imp_div_pos_le) auto
  qed
  finally have 2: "\<parallel>1 / (s - 1)\<parallel> \<le> 11" by auto
  have "zeta s = pre_zeta 1 s + 1 / (s - 1)" by (intro zeta_pole_eq) (use assms in auto)
  moreover have "\<parallel>\<dots>\<parallel> \<le> \<parallel>pre_zeta 1 s\<parallel> + \<parallel>1 / (s - 1)\<parallel>" by (rule norm_triangle_ineq)
  ultimately have "\<parallel>zeta s\<parallel> \<le> \<dots>" by auto
  also have "\<dots> \<le> 12 + 2 * \<bar>Im s\<bar>" using 1 2 by auto
  finally show ?thesis .
qed

lemma zeta_bound_gt_1:
  assumes "1 < Re s"
  shows "\<parallel>zeta s\<parallel> \<le> Re s / (Re s - 1)"
proof -
  have "\<parallel>zeta s\<parallel> \<le> Re (zeta (Re s))" by (intro zeta_bound' assms)
  also have "\<dots> \<le> \<parallel>zeta (Re s)\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> = \<parallel>pre_zeta 1 (Re s) + 1 / (Re s - 1)\<parallel>"
    by (subst zeta_pole_eq) (use assms in auto)
  also have "\<dots> \<le> \<parallel>pre_zeta 1 (Re s)\<parallel> + \<parallel>1 / (Re s - 1) :: complex\<parallel>"
    by (rule norm_triangle_ineq)
  also have "\<dots> \<le> 1 + 1 / (Re s - 1)"
  proof -
    have "\<parallel>pre_zeta 1 (Re s)\<parallel> \<le> \<parallel>Re s :: complex\<parallel> / Re (Re s)"
      by (rule pre_zeta_1_bound) (use assms in auto)
    also have "\<dots> = 1" using assms by auto
    moreover have "\<parallel>1 / (Re s - 1) :: complex\<parallel> = 1 / (Re s - 1)"
      by (subst norm_of_real) (use assms in auto)
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = Re s / (Re s - 1)"
    using assms by (auto simp add: field_simps)
  finally show ?thesis .
qed

lemma zeta_bound_trivial:
  assumes "1 / 2 \<le> Re s" and "\<bar>Im s\<bar> \<ge> 1 / 11"
  shows "\<parallel>zeta s\<parallel> \<le> 12 + 2 * \<bar>Im s\<bar>"
proof (cases "Re s \<le> 2")
  assume "Re s \<le> 2"
  thus ?thesis by (intro zeta_bound_trivial') (use assms in auto)
next
  assume "\<not> Re s \<le> 2"
  hence *: "Re s > 1" "Re s > 2" by auto
  hence "\<parallel>zeta s\<parallel> \<le> Re s / (Re s - 1)" by (intro zeta_bound_gt_1)
  also have "\<dots> \<le> 2" using * by (auto simp add: field_simps)
  also have "\<dots> \<le> 12 + 2 * \<bar>Im s\<bar>" by auto
  finally show ?thesis .
qed

lemma zeta_nonzero_small_imag':
  assumes "\<bar>Im s\<bar> \<le> 13 / 22" and "Re s \<ge> 1 / 2" and "Re s < 1"
  shows "zeta s \<noteq> 0"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> (1 + \<parallel>s\<parallel> / Re s) / 2 * 1 powr - Re s"
    by (rule pre_zeta_bound) (use assms(2) in auto)
  also have "\<dots> \<le> 129 / 100" proof -
    have "\<parallel>s\<parallel> / Re s \<le> 79 / 50"
    proof (rule ccontr)
      assume "\<not> \<parallel>s\<parallel> / Re s \<le> 79 / 50"
      hence "sqrt (6241 / 2500) < \<parallel>s\<parallel> / Re s" by (simp add: real_sqrt_divide)
      also have "\<dots> = \<parallel>s\<parallel> / sqrt ((Re s)\<^sup>2)" using assms(2) by simp
      also have "\<dots> = sqrt (1 + (Im s / Re s)\<^sup>2)"
        unfolding cmod_def using assms(2)
        by (auto simp add: real_sqrt_divide [symmetric] field_simps
                 simp del: real_sqrt_abs)
      finally have 1: "6241 / 2500 < 1 + (Im s / Re s)\<^sup>2" by auto
      have "\<bar>Im s / Re s\<bar> \<le> \<bar>6 / 5\<bar>" using assms by (auto simp add: field_simps abs_le_square_iff)
      hence "(Im s / Re s)\<^sup>2 \<le> (6 / 5)\<^sup>2" by (subst (asm) abs_le_square_iff)
      hence 2: "1 + (Im s / Re s)\<^sup>2 \<le> 61 / 25" unfolding power2_eq_square by auto
      from 1 2 show False by auto
    qed
    hence "(1 + \<parallel>s\<parallel> / Re s) / 2 \<le> (129 / 50) / 2" by (subst divide_right_mono) auto
    also have "\<dots> = 129 / 100" by auto
    finally show ?thesis by auto
  qed
  finally have 1: "\<parallel>pre_zeta 1 s\<parallel> \<le> 129 / 100" .
  have "\<parallel>s - 1\<parallel> < 100 / 129" proof -
    from assms have "(Re (s - 1))\<^sup>2 \<le> (1 / 2)\<^sup>2" by (simp add: abs_le_square_iff [symmetric])
    moreover have "(Im (s - 1))\<^sup>2 \<le> (13 / 22)\<^sup>2" using assms(1) by (simp add: abs_le_square_iff [symmetric])
    ultimately have "(Re (s - 1))\<^sup>2 + (Im (s - 1))\<^sup>2 \<le> 145 / 242" by (auto simp add: power2_eq_square)
    hence "sqrt ((Re (s - 1))\<^sup>2 + (Im (s - 1))\<^sup>2) \<le> sqrt (145 / 242)" by (rule real_sqrt_le_mono)
    also have "\<dots> < sqrt ((100 / 129)\<^sup>2)" by (subst real_sqrt_less_iff) (simp add: power2_eq_square)
    finally show ?thesis unfolding cmod_def by auto
  qed
  moreover have "\<parallel>s - 1\<parallel> \<noteq> 0" using assms(3) by auto
  ultimately have 2: "\<parallel>1 / (s - 1)\<parallel> > 129 / 100" by (auto simp add: field_simps norm_divide)
  from 1 2 have "0 < \<parallel>1 / (s - 1)\<parallel> - \<parallel>pre_zeta 1 s\<parallel>" by auto
  also have "\<dots> \<le> \<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel>" by (subst add.commute) (rule norm_diff_ineq)
  also from assms(3) have "s \<noteq> 1" by auto
  hence "\<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel> = \<parallel>zeta s\<parallel>" using zeta_pole_eq by auto
  finally show ?thesis by auto
qed

lemma zeta_nonzero_small_imag:
  assumes "\<bar>Im s\<bar> \<le> 13 / 22" and "Re s > 0" and "s \<noteq> 1"
  shows "zeta s \<noteq> 0"
proof -
  consider "Re s \<le> 1 / 2" | "1 / 2 \<le> Re s \<and> Re s < 1" | "Re s \<ge> 1" by fastforce
  thus ?thesis proof cases
    case 1 hence "zeta (1 - s) \<noteq> 0" using assms by (intro zeta_nonzero_small_imag') auto
    moreover case 1
    ultimately show ?thesis using assms(2) zeta_zero_reflect_iff by auto
  next
    case 2 thus ?thesis using assms(1) by (intro zeta_nonzero_small_imag') auto
  next
    case 3 thus ?thesis using zeta_Re_ge_1_nonzero assms(3) by auto
  qed
qed

lemma inverse_zeta_bound:
  assumes "1 < Re s"
  shows "\<parallel>inverse (zeta s)\<parallel> \<le> Re s / (Re s - 1)"
proof -
  have "\<parallel>inverse (zeta s)\<parallel> \<le> Re (zeta (Re s))" by (intro inverse_zeta_bound' assms)
  also have "\<dots> \<le> \<parallel>zeta (Re s)\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> Re (Re s) / (Re (Re s) - 1)"
    by (intro zeta_bound_gt_1) (use assms in auto)
  also have "\<dots> = Re s / (Re s - 1)" by auto
  finally show ?thesis .
qed

lemma deriv_zeta_bound:
  fixes s :: complex
  assumes Hr: "0 < r" and Hs: "s \<noteq> 1"
    and hB: "\<And>w. \<parallel>s - w\<parallel> = r \<Longrightarrow> \<parallel>pre_zeta 1 w\<parallel> \<le> B"
  shows "\<parallel>deriv zeta s\<parallel> \<le> B / r + 1 / \<parallel>s - 1\<parallel>\<^sup>2"
proof -
  have "\<parallel>deriv zeta s\<parallel> = \<parallel>deriv (pre_zeta 1) s - 1 / (s - 1)\<^sup>2\<parallel>"
  proof -
    let ?A = "UNIV - {1 :: complex}"
    let ?f = "\<lambda>s. pre_zeta 1 s + 1 / (s - 1)"
    let ?v = "deriv (pre_zeta 1) s + (0 * (s - 1) - 1 * (1 - 0)) / (s - 1)\<^sup>2"
    let ?v' = "deriv (pre_zeta 1) s - 1 / (s - 1 :: complex)\<^sup>2"
    have "\<forall>z\<in>?A. zeta z = pre_zeta 1 z + 1 / (z - 1)"
      by (auto intro: zeta_pole_eq)
    hence "\<forall>\<^sub>F z in nhds s. zeta z = pre_zeta 1 z + 1 / (z - 1)"
      using Hs by (subst eventually_nhds, intro exI [where x = ?A]) auto
    hence "DERIV zeta s :> ?v' = DERIV ?f s :> ?v'"
      by (intro DERIV_cong_ev) auto
    moreover have "DERIV ?f s :> ?v"
      unfolding power2_eq_square
      by (intro derivative_intros field_differentiable_derivI holomorphic_pre_zeta
          holomorphic_on_imp_differentiable_at [where s = ?A])
         (use Hs in auto)
    moreover have "?v = ?v'" by (auto simp add: field_simps)
    ultimately have "DERIV zeta s :> ?v'" by auto
    moreover have "DERIV zeta s :> deriv zeta s"
      by (intro field_differentiable_derivI field_differentiable_at_zeta)
         (use Hs in auto)
    ultimately have "?v' = deriv zeta s" by (rule DERIV_unique)
    thus ?thesis by auto
  qed
  also have "\<dots> \<le> \<parallel>deriv (pre_zeta 1) s\<parallel> + \<parallel>1 / (s - 1)\<^sup>2\<parallel>" by (rule norm_triangle_ineq4)
  also have "\<dots> \<le> B / r + 1 / \<parallel>s - 1\<parallel>\<^sup>2"
  proof -
    have "\<parallel>(deriv ^^ 1) (pre_zeta 1) s\<parallel> \<le> fact 1 * B / r ^ 1"
      by (intro Cauchy_inequality holomorphic_pre_zeta continuous_on_pre_zeta assms) auto
    thus ?thesis by (auto simp add: norm_divide norm_power)
  qed
  finally show ?thesis .
qed

lemma zeta_lower_bound:
  assumes "0 < Re s" "s \<noteq> 1"
  shows "1 / \<parallel>s - 1\<parallel> - \<parallel>s\<parallel> / Re s \<le> \<parallel>zeta s\<parallel>"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s" by (intro pre_zeta_1_bound assms)
  hence "1 / \<parallel>s - 1\<parallel> - \<parallel>s\<parallel> / Re s \<le> \<parallel>1 / (s - 1)\<parallel> - \<parallel>pre_zeta 1 s\<parallel>"
    using assms by (auto simp add: norm_divide)
  also have "\<dots> \<le> \<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel>"
    by (subst add.commute) (rule norm_diff_ineq)
  also have "\<dots> = \<parallel>zeta s\<parallel>" using assms by (subst zeta_pole_eq) auto
  finally show ?thesis .
qed

lemma logderiv_zeta_bound:
  fixes \<sigma> :: real
  assumes "1 < \<sigma>" "\<sigma> \<le> 23 / 20"
  shows "\<parallel>logderiv zeta \<sigma>\<parallel> \<le> 5 / 4 * (1 / (\<sigma> - 1))"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> sqrt 2" if *: "\<parallel>\<sigma> - s\<parallel> = 1 / sqrt 2" for s :: complex
  proof -
    have 1: "0 < Re s" proof -
      have "1 - Re s \<le> Re (\<sigma> - s)" using assms(1) by auto
      also have "Re (\<sigma> - s) \<le> \<parallel>\<sigma> - s\<parallel>" by (rule complex_Re_le_cmod)
      also have "\<dots> = 1 / sqrt 2" by (rule *)
      finally have "1 - 1 / sqrt 2 \<le> Re s" by auto
      moreover have "0 < 1 - 1 / sqrt 2" by auto
      ultimately show ?thesis by linarith
    qed
    hence "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s" by (rule pre_zeta_1_bound)
    also have "\<dots> \<le> sqrt 2" proof -
      define x y where "x \<equiv> Re s" and "y \<equiv> Im s"
      have "sqrt ((\<sigma> - x)\<^sup>2 + y\<^sup>2) = 1 / sqrt 2"
        using * unfolding cmod_def x_def y_def by auto
      also have "\<dots> = sqrt (1 / 2)" by (auto simp add: field_simps real_sqrt_mult [symmetric])
      finally have 2: "x\<^sup>2 + y\<^sup>2 - 2*\<sigma>*x + \<sigma>\<^sup>2 = 1 / 2" by (auto simp add: field_simps power2_eq_square)
      have "y\<^sup>2 \<le> x\<^sup>2" proof (rule ccontr)
        assume "\<not> y\<^sup>2 \<le> x\<^sup>2"
        hence "x\<^sup>2 < y\<^sup>2" by auto
        with 2 have "2*x\<^sup>2 - 2*\<sigma>*x + \<sigma>\<^sup>2 < 1 / 2" by auto
        hence "2 * (x - \<sigma> / 2)\<^sup>2 < (1 - \<sigma>\<^sup>2) / 2" by (auto simp add: field_simps power2_eq_square)
        also have "\<dots> < 0" using \<open>1 < \<sigma>\<close> by auto
        finally show False by auto
      qed
      moreover have "x \<noteq> 0" unfolding x_def using 1 by auto
      ultimately have "sqrt ((x\<^sup>2 + y\<^sup>2) / x\<^sup>2) \<le> sqrt 2" by (auto simp add: field_simps)
      with 1 show ?thesis unfolding cmod_def x_def y_def by (auto simp add: real_sqrt_divide)
    qed
    finally show ?thesis .
  qed
  hence "\<parallel>deriv zeta \<sigma>\<parallel> \<le> sqrt 2 / (1 / sqrt 2) + 1 / \<parallel>(\<sigma> :: complex) - 1\<parallel>\<^sup>2"
    by (intro deriv_zeta_bound) (use assms(1) in auto)
  also have "\<dots> \<le> 2 + 1 / (\<sigma> - 1)\<^sup>2"
    by (subst in_Reals_norm) (use assms(1) in auto)
  also have "\<dots> = (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2"
  proof -
    have "\<sigma> * \<sigma> - 2 * \<sigma> + 1 = (\<sigma> - 1) * (\<sigma> - 1)" by (auto simp add: field_simps)
    also have "\<dots> \<noteq> 0" using assms(1) by auto
    finally show ?thesis by (auto simp add: power2_eq_square field_simps)
  qed
  finally have 1: "\<parallel>deriv zeta \<sigma>\<parallel> \<le> (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2" .
  have "(2 - \<sigma>) / (\<sigma> - 1) = 1 / \<parallel>(\<sigma> :: complex) - 1\<parallel> - \<parallel>\<sigma> :: complex\<parallel> / Re \<sigma>"
    using assms(1) by (auto simp add: field_simps in_Reals_norm)
  also have "\<dots> \<le> \<parallel>zeta \<sigma>\<parallel>" by (rule zeta_lower_bound) (use assms(1) in auto)
  finally have 2: "(2 - \<sigma>) / (\<sigma> - 1) \<le> \<parallel>zeta \<sigma>\<parallel>" .
  have "4 * (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) - 5 * (2 - \<sigma>) = 8 * (\<sigma> - 11 / 16)\<^sup>2 - 57 / 32"
    by (auto simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 0" proof -
    have "0 \<le> \<sigma> - 11 / 16" using assms(1) by auto
    moreover have "\<sigma> - 11 / 16 \<le> 37 / 80" using assms(2) by auto
    ultimately have "(\<sigma> - 11 / 16)\<^sup>2 \<le> (37 / 80)\<^sup>2" by auto
    thus ?thesis by (auto simp add: power2_eq_square)
  qed
  finally have "4 * (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) - 5 * (2 - \<sigma>) \<le> 0" .
  moreover have "0 < 2 - \<sigma>" using assms(2) by auto
  ultimately have 3: "(2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (2 - \<sigma>) \<le> 5 / 4" by (subst pos_divide_le_eq) auto
  moreover have "0 \<le> 2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3" proof -
    have "0 \<le> 2 * (\<sigma> - 1)\<^sup>2 + 1" by auto
    also have "\<dots> = 2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3" by (auto simp add: field_simps power2_eq_square)
    finally show ?thesis .
  qed
  moreover have "0 < (2 - \<sigma>) / (\<sigma> - 1)" using assms by auto
  ultimately have "\<parallel>logderiv zeta \<sigma>\<parallel> \<le> ((2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2) / ((2 - \<sigma>) / (\<sigma> - 1))"
    unfolding logderiv_def using 1 2 by (subst norm_divide) (rule frac_le, auto)
  also have "\<dots> = (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (2 - \<sigma>) * (1 / (\<sigma> - 1))"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> 5 / 4 * (1 / (\<sigma> - 1))"
    using 3 by (rule mult_right_mono) (use assms(1) in auto)
  finally show ?thesis .
qed

lemma Re_logderiv_zeta_bound:
  fixes \<sigma> :: real
  assumes "1 < \<sigma>" "\<sigma> \<le> 23 / 20"
  shows "Re (logderiv zeta \<sigma>) \<ge> - 5 / 4 * (1 / (\<sigma> - 1))"
proof -
  have "- Re (logderiv zeta \<sigma>) = Re (- logderiv zeta \<sigma>)" by auto
  also have "Re (- logderiv zeta \<sigma>) \<le> \<parallel>- logderiv zeta \<sigma>\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> = \<parallel>logderiv zeta \<sigma>\<parallel>" by auto
  also have "\<dots> \<le> 5 / 4 * (1 / (\<sigma> - 1))" by (intro logderiv_zeta_bound assms)
  finally show ?thesis by auto
qed

locale zeta_bound_param =
  fixes \<theta> \<phi> :: "real \<Rightarrow> real"
  assumes zeta_bn': "\<And>z. 1 - \<theta> (Im z) \<le> Re z \<Longrightarrow> Im z \<ge> 1 / 11 \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    and \<theta>_pos: "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
    and \<phi>_pos: "\<And>t. 1 \<le> \<phi> t"
    and inv_\<theta>: "\<And>t. \<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)"
    and mo\<theta>: "antimono \<theta>" and mo\<phi>: "mono \<phi>"
begin
  definition "region \<equiv> {z. 1 - \<theta> (Im z) \<le> Re z \<and> Im z \<ge> 1 / 11}"
  lemma zeta_bn: "\<And>z. z \<in> region \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    using zeta_bn' unfolding region_def by auto
  lemma \<theta>_pos': "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1"
    using \<theta>_pos by (smt (verit) exp_ge_add_one_self exp_half_le2)
  lemma \<phi>_pos': "\<And>t. 0 < \<phi> t" using \<phi>_pos by (smt (verit, ccfv_SIG))
end

locale zeta_bound_param_1 = zeta_bound_param +
  fixes \<gamma> :: real
  assumes \<gamma>_cnd: "\<gamma> \<ge> 13 / 22"
begin
  definition r where "r \<equiv> \<theta> (2 * \<gamma> + 1)"
end

locale zeta_bound_param_2 = zeta_bound_param_1 +
  fixes \<sigma> \<delta> :: real
  assumes \<sigma>_cnd: "\<sigma> \<ge> 1 + exp (- \<phi>(2 * \<gamma> + 1))"
      and \<delta>_cnd: "\<delta> = \<gamma> \<or> \<delta> = 2 * \<gamma>"
begin
  definition s where "s \<equiv> Complex \<sigma> \<delta>"
end

context zeta_bound_param_2 begin
declare dist_complex_def [simp] norm_minus_commute [simp]
declare legacy_Complex_simps [simp]

lemma cball_lm:
  assumes "z \<in> cball s r"
  shows "r \<le> 1" "\<bar>Re z - \<sigma>\<bar> \<le> r" "\<bar>Im z - \<delta>\<bar> \<le> r"
        "1 / 11 \<le> Im z" "Im z \<le> 2 * \<gamma> + r"
proof -
  have "\<bar>Re (z - s)\<bar> \<le> \<parallel>z - s\<parallel>" "\<bar>Im (z - s)\<bar> \<le> \<parallel>z - s\<parallel>"
    by (rule abs_Re_le_cmod) (rule abs_Im_le_cmod)
  moreover have "\<parallel>z - s\<parallel> \<le> r" using assms by auto
  ultimately show 1: "\<bar>Re z - \<sigma>\<bar> \<le> r" "\<bar>Im z - \<delta>\<bar> \<le> r" unfolding s_def by auto
  moreover have 3: "r \<le> 1 / 2" unfolding r_def using \<theta>_pos by auto
  ultimately have 2: "\<bar>Re z - \<sigma>\<bar> \<le> 1 / 2" "\<bar>Im z - \<delta>\<bar> \<le> 1 / 2" by auto
  moreover have "\<delta> \<le> 2 * \<gamma>" using \<delta>_cnd \<gamma>_cnd by auto
  ultimately show "Im z \<le> 2 * \<gamma> + r" using 1 by auto
  have "1 / 11 \<le> \<delta> - 1 / 2" using \<delta>_cnd \<gamma>_cnd by auto
  also have "\<dots> \<le> Im z" using 2 by (auto simp del: Num.le_divide_eq_numeral1)
  finally show "1 / 11 \<le> Im z" .
  from 3 show "r \<le> 1" by auto
qed

lemma cball_in_region:
  shows "cball s r \<subseteq> region"
proof
  fix z :: complex
  assume hz: "z \<in> cball s r"
  note lm = cball_lm [OF hz]
  hence "1 - \<theta> (Im z) \<le> 1 - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1))"
    unfolding r_def using mo\<theta> lm by (auto intro: antimonoD)
  also have "\<dots> \<le> 1 + exp (-\<phi> (2 * \<gamma> + 1)) - \<theta> (2 * \<gamma> + 1)"
  proof -
    have "2 * \<gamma> + \<theta> (2 * \<gamma> + 1) \<le> 2 * \<gamma> + 1"
      unfolding r_def using \<theta>_pos' by auto
    hence "\<theta> (2 * \<gamma> + 1) - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1)) \<le> 0"
      using mo\<theta> by (auto intro: antimonoD)
    also have "0 \<le> exp (-\<phi> (2 * \<gamma> + 1))" by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> \<le> \<sigma> - r" using \<sigma>_cnd unfolding r_def s_def by auto
  also have "\<dots> \<le> Re z" using lm by auto
  finally have "1 - \<theta> (Im z) \<le> Re z" .
  thus "z \<in> region" unfolding region_def using lm by auto
qed

lemma Re_s_gt_1:
  shows "1 < Re s"
proof -
  have *: "exp (- \<phi> (2 * \<gamma> + 1)) > 0" by auto
  show ?thesis using \<sigma>_cnd s_def by auto (use * in linarith)
qed

lemma zeta_analytic_on_region:
  shows "zeta analytic_on region"
  by (rule analytic_zeta) (unfold region_def, auto)

lemma zeta_div_bound:
  assumes "z \<in> cball s r"
  shows "\<parallel>zeta z / zeta s\<parallel> \<le> exp (3 * \<phi> (2 * \<gamma> + 1))"
proof -
  let ?\<phi> = "\<phi> (2 * \<gamma> + 1)"
  have "\<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))" using cball_in_region zeta_bn assms by auto
  also have "\<dots> \<le> exp (?\<phi>)"
  proof -
    have "Im z \<le> 2 * \<gamma> + 1" using cball_lm [OF assms] by auto
    thus ?thesis by auto (rule monoD [OF mo\<phi>])
  qed
  also have "\<parallel>inverse (zeta s)\<parallel> \<le> exp (2 * ?\<phi>)"
  proof -
    have "\<parallel>inverse (zeta s)\<parallel> \<le> Re s / (Re s - 1)"
      by (intro inverse_zeta_bound Re_s_gt_1)
    also have "\<dots> = 1 + 1 / (Re s - 1)"
      using Re_s_gt_1 by (auto simp add: field_simps)
    also have "\<dots> \<le> 1 + exp (?\<phi>)"
    proof -
      have "Re s - 1 \<ge> exp (-?\<phi>)" using s_def \<sigma>_cnd by auto
      hence "1 / (Re s - 1) \<le> 1 / exp (-?\<phi>)"
        using Re_s_gt_1 by (auto intro: divide_left_mono)
      thus ?thesis by (auto simp add: exp_minus field_simps)
    qed
    also have "\<dots> \<le> exp (2 * ?\<phi>)" by (intro exp_lemma_1 less_imp_le \<phi>_pos)
    finally show ?thesis .
  qed
  ultimately have "\<parallel>zeta z * inverse (zeta s)\<parallel> \<le> exp (?\<phi>) * exp (2 * ?\<phi>)"
    by (subst norm_mult, intro mult_mono') auto
  also have "\<dots> = exp (3 * ?\<phi>)" by (subst exp_add [symmetric]) auto
  finally show ?thesis by (auto simp add: divide_inverse)
qed

lemma logderiv_zeta_bound:
  shows "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r"
    and "\<And>\<beta>. \<sigma> - r / 2 \<le> \<beta> \<Longrightarrow> zeta (Complex \<beta> \<delta>) = 0 \<Longrightarrow>
        Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
proof -
  have 1: "0 < r" unfolding r_def using \<theta>_pos' by auto
  have 2: "0 \<le> 3 * \<phi> (2 * \<gamma> + 1)" using \<phi>_pos' by (auto simp add: less_imp_le)
  have 3: "zeta s \<noteq> 0" "\<And>z. Re s < Re z \<Longrightarrow> zeta z \<noteq> 0"
    using Re_s_gt_1 by (auto intro!: zeta_Re_gt_1_nonzero)
  have 4: "zeta analytic_on cball s r" 
    by (rule analytic_on_subset;
        rule cball_in_region zeta_analytic_on_region)
  have 5: "z \<in> cball s r \<Longrightarrow> \<parallel>zeta z / zeta s\<parallel> \<le> exp (3 * \<phi> (2 * \<gamma> + 1))"
    for z by (rule zeta_div_bound)
  have 6: "{} \<subseteq> {z \<in> cball s (r / 2). zeta z = 0 \<and> Re z \<le> Re s}" by auto
  have 7: "{Complex \<beta> \<delta>} \<subseteq> {z \<in> cball s (r / 2). zeta z = 0 \<and> Re z \<le> Re s}"
    if "\<sigma> - r / 2 \<le> \<beta>" "zeta (Complex \<beta> \<delta>) = 0" for \<beta>
  proof -
    have "\<beta> \<le> \<sigma>"
      using zeta_Re_gt_1_nonzero [of "Complex \<beta> \<delta>"] Re_s_gt_1 that(2)
      unfolding s_def by fastforce
    thus ?thesis using that unfolding s_def by auto
  qed
  have "- Re (logderiv zeta s) \<le> 8 * (3 * \<phi> (2 * \<gamma> + 1)) / r + Re (\<Sum>z\<in>{}. 1 / (z - s))"
    by (intro lemma_3_9_beta3 1 2 3 4 5 6)
  thus "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r" by auto
  show "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
    if *: "\<sigma> - r / 2 \<le> \<beta>" "zeta (Complex \<beta> \<delta>) = 0" for \<beta>
  proof -
    have bs: "\<beta> \<noteq> \<sigma>" using *(2) 3(1) unfolding s_def by auto
    hence bs': "1 / (\<beta> - \<sigma>) = - 1 / (\<sigma> - \<beta>)" by (auto simp add: field_simps)
    have inv_r: "1 / (Complex r 0) = Complex (1 / r) 0" if "r \<noteq> 0" for r
      using that by (auto simp add: field_simps)
    have "- Re (logderiv zeta s) \<le> 8 * (3 * \<phi> (2 * \<gamma> + 1)) / r + Re (\<Sum>z\<in>{Complex \<beta> \<delta>}. 1 / (z - s))"
      by (intro lemma_3_9_beta3 1 2 3 4 5 7 *)
    thus ?thesis unfolding s_def
      by (auto simp add: field_simps)
         (subst (asm) inv_r, use bs bs' in auto)
  qed
qed
end

context zeta_bound_param_1 begin
lemma zeta_nonzero_region':
  assumes "1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1)) - r / 2 \<le> \<beta>"
    and "zeta (Complex \<beta> \<gamma>) = 0"
  shows "1 - \<beta> \<ge> 1 / 29760 * (r / \<phi> (2 * \<gamma> + 1))"
proof -
  let ?\<phi> = "\<phi> (2 * \<gamma> + 1)" and ?\<theta> = "\<theta> (2 * \<gamma> + 1)"
  define \<sigma> where "\<sigma> \<equiv> 1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1))"
  define a where "a \<equiv> - 5 / 4 * (1 / (\<sigma> - 1))"
  define b where "b \<equiv> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
  define c where "c \<equiv> - 24 * \<phi> (2 * \<gamma> + 1) / r"
  have "1 + exp (- ?\<phi>) \<le> \<sigma>"
  proof -
    have "960 * exp (- ?\<phi>) = 1 / (1 / 960 * exp ?\<phi>)"
      by (auto simp add: exp_add [symmetric] field_simps)
    also have "\<dots> \<le> 1 / (?\<phi> / ?\<theta>)" proof -
      have "?\<phi> / ?\<theta> \<le> 1 / 960 * exp ?\<phi>" by (rule inv_\<theta>)
      thus ?thesis by (intro divide_left_mono) (use \<theta>_pos \<phi>_pos' in auto)
    qed
    also have "\<dots> = r / ?\<phi>" unfolding r_def by auto
    finally show ?thesis unfolding \<sigma>_def by auto
  qed
  note * = this \<gamma>_cnd
  interpret z: zeta_bound_param_2 \<theta> \<phi> \<gamma> \<sigma> \<gamma> by (standard, use * in auto)
  interpret z': zeta_bound_param_2 \<theta> \<phi> \<gamma> \<sigma> "2 * \<gamma>" by (standard, use * in auto)
  have "r \<le> 1" unfolding r_def using \<theta>_pos' [of "2 * \<gamma> + 1"] by auto
  moreover have "1 \<le> \<phi> (2 * \<gamma> + 1)" using \<phi>_pos by auto
  ultimately have "r / \<phi> (2 * \<gamma> + 1) \<le> 1" by auto
  moreover have "0 < r" "0 < \<phi> (2 * \<gamma> + 1)" unfolding r_def using \<theta>_pos' \<phi>_pos' by auto
  hence "0 < r / \<phi> (2 * \<gamma> + 1)" by auto
  ultimately have 1: "1 < \<sigma>" "\<sigma> \<le> 23 / 20" unfolding \<sigma>_def by auto
  hence "Re (logderiv zeta \<sigma>) \<ge> a" unfolding a_def by (intro Re_logderiv_zeta_bound)
  hence "Re (logderiv zeta (Complex \<sigma> 0)) \<ge> a" by auto
  moreover have "Re (logderiv zeta z.s) \<ge> b" unfolding b_def
    by (rule z.logderiv_zeta_bound) (use assms r_def \<sigma>_def in auto)
  hence "Re (logderiv zeta (Complex \<sigma> \<gamma>)) \<ge> b" unfolding z.s_def by auto
  moreover have "Re (logderiv zeta z'.s) \<ge> c" unfolding c_def by (rule z'.logderiv_zeta_bound)
  hence "Re (logderiv zeta (Complex \<sigma> (2 * \<gamma>))) \<ge> c" unfolding z'.s_def by auto
  ultimately have "3 * a + 4 * b + c
    \<le> 3 * Re (logderiv zeta (Complex \<sigma> 0)) + 4 * Re (logderiv zeta (Complex \<sigma> \<gamma>))
    + Re (logderiv zeta (Complex \<sigma> (2 * \<gamma>)))" by auto
  also have "\<dots> \<le> 0" by (rule logderiv_zeta_ineq, rule 1)
  finally have "3 * a + 4 * b + c \<le> 0" .
  hence "4 / (\<sigma> - \<beta>) \<le> 15 / 4 * (1 / (\<sigma> - 1)) + 120 * \<phi> (2 * \<gamma> + 1) / r"
    unfolding a_def b_def c_def by auto
  also have "\<dots> = 3720 * \<phi> (2 * \<gamma> + 1) / r" unfolding \<sigma>_def by auto
  finally have 2: "inverse (\<sigma> - \<beta>) \<le> 930 * \<phi> (2 * \<gamma> + 1) / r" by (auto simp add: inverse_eq_divide)
  have 3: "\<sigma> - \<beta> \<ge> 1 / 930 * (r / \<phi> (2 * \<gamma> + 1))"
  proof -
    have "1 / 930 * (r / \<phi> (2 * \<gamma> + 1)) = 1 / (930 * (\<phi> (2 * \<gamma> + 1) / r))"
      by (auto simp add: field_simps)
    also have "\<dots> \<le> \<sigma> - \<beta>" proof -
      have "\<beta> \<le> 1" using assms(2) zeta_Re_gt_1_nonzero [of "Complex \<beta> \<gamma>"] by fastforce
      also have "1 < \<sigma>" by (rule 1)
      finally have "\<beta> < \<sigma>" .
      thus ?thesis using 2 by (auto intro: inverse_le_imp_le)
    qed
    finally show ?thesis .
  qed
  show ?thesis proof -
    let ?x = "r / \<phi> (2 * \<gamma> + 1)"
    have "1 / 29760 * ?x = 1 / 930 * ?x - 1 / 960 * ?x" by auto
    also have "\<dots> \<le> (\<sigma> - \<beta>) - (\<sigma> - 1)" using 3 by (subst (2) \<sigma>_def) auto
    also have "\<dots> = 1 - \<beta>" by auto
    finally show ?thesis .
  qed
qed

lemma zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0"
  shows "1 - \<beta> \<ge> 1 / 29760 * (r / \<phi> (2 * \<gamma> + 1))"
proof (cases "1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1)) - r / 2 \<le> \<beta>")
  case True
  thus ?thesis using assms by (rule zeta_nonzero_region')
next
  case False
  let ?x = "r / \<phi> (2 * \<gamma> + 1)"
  assume 1: "\<not> 1 + 1 / 960 * ?x - r / 2 \<le> \<beta>"
  have "0 < r" using \<theta>_pos' unfolding r_def by auto
  hence "1 / 930 * ?x \<le> r / 2"
    using \<phi>_pos [of "2 * \<gamma> + 1"] by (auto intro!: mult_imp_div_pos_le)
  hence "1 / 29760 * ?x \<le> r / 2 - 1 / 960 * ?x" by auto
  also have "\<dots> \<le> 1 - \<beta>" using 1 by auto
  finally show ?thesis .
qed
end

context zeta_bound_param begin
theorem zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0" and "Complex \<beta> \<gamma> \<noteq> 1"
  shows "1 - \<beta> \<ge> 1 / 29760 * (\<theta> (2 * \<bar>\<gamma>\<bar> + 1) / \<phi> (2 * \<bar>\<gamma>\<bar> + 1))"
proof (cases "\<bar>\<gamma>\<bar> \<ge> 13 / 22")
  case True
  assume 1: "13 / 22 \<le> \<bar>\<gamma>\<bar>"
  have 2: "zeta (Complex \<beta> \<bar>\<gamma>\<bar>) = 0"
  proof (cases "\<gamma> \<ge> 0")
    case True thus ?thesis using assms by auto
  next
    case False thus ?thesis by (auto simp add: complex_cnj [symmetric] intro: assms)
  qed
  interpret z: zeta_bound_param_1 \<theta> \<phi> \<open>\<bar>\<gamma>\<bar>\<close> by standard (use 1 in auto)
  show ?thesis by (intro z.zeta_nonzero_region [unfolded z.r_def] 2)
next
  case False
  hence 1: "\<bar>\<gamma>\<bar> \<le> 13 / 22" by auto
  show ?thesis
  proof (cases "0 < \<beta>", rule ccontr)
    case True thus False using zeta_nonzero_small_imag [of "Complex \<beta> \<gamma>"] assms 1 by auto
  next
    have "0 < \<theta> (2 * \<bar>\<gamma>\<bar> + 1)" "\<theta> (2 * \<bar>\<gamma>\<bar> + 1) \<le> 1" "1 \<le> \<phi> (2 * \<bar>\<gamma>\<bar> + 1)"
      using \<theta>_pos' \<phi>_pos by auto
    hence "1 / 29760 * (\<theta> (2 * \<bar>\<gamma>\<bar> + 1) / \<phi> (2 * \<bar>\<gamma>\<bar> + 1)) \<le> 1" by auto
    also case False hence "1 \<le> 1 - \<beta>" by auto
    finally show ?thesis .
  qed
qed
end

lemma zeta_bound_param_nonneg:
  fixes \<theta> \<phi> :: "real \<Rightarrow> real"
  assumes zeta_bn': "\<And>z. 1 - \<theta> (Im z) \<le> Re z \<Longrightarrow> Im z \<ge> 1 / 11 \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    and \<theta>_pos: "\<And>t. 0 \<le> t \<Longrightarrow> 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
    and \<phi>_pos: "\<And>t. 0 \<le> t \<Longrightarrow> 1 \<le> \<phi> t"
    and inv_\<theta>: "\<And>t. 0 \<le> t \<Longrightarrow> \<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)"
    and mo\<theta>: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<theta> y \<le> \<theta> x"
    and mo\<phi>: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "zeta_bound_param (\<lambda>t. \<theta> (max 0 t)) (\<lambda>t. \<phi> (max 0 t))"
  by standard (insert assms, auto simp add: antimono_def mono_def)

interpretation classical_zeta_bound:
  zeta_bound_param "\<lambda>t. 1 / 2" "\<lambda>t. 4 * ln (12 + 2 * max 0 t)"
proof -
  define \<theta> :: "real \<Rightarrow> real" where "\<theta> \<equiv> \<lambda>t. 1 / 2"
  define \<phi> :: "real \<Rightarrow> real" where "\<phi> \<equiv> \<lambda>t. 4 * ln (12 + 2 * t)"
  have "zeta_bound_param (\<lambda>t. \<theta> (max 0 t)) (\<lambda>t. \<phi> (max 0 t))"
  proof (rule zeta_bound_param_nonneg)
    fix z assume *: "1 - \<theta> (Im z) \<le> Re z" "Im z \<ge> 1 / 11"
    have "\<parallel>zeta z\<parallel> \<le> 12 + 2 * \<bar>Im z\<bar>"
      using * unfolding \<theta>_def by (intro zeta_bound_trivial) auto
    also have "\<dots> = exp (ln (12 + 2 * Im z))" using *(2) by auto
    also have "\<dots> \<le> exp (\<phi> (Im z))" proof -
      have "0 \<le> ln (12 + 2 * Im z)" using *(2) by auto
      thus ?thesis unfolding \<phi>_def by auto
    qed
    finally show "\<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))" .
  next
    fix t :: real assume *: "0 \<le> t"
    have "\<phi> t / \<theta> t = 8 * ln (12 + 2 * t)" unfolding \<phi>_def \<theta>_def by auto
    also have "\<dots> \<le> 8 * (5 / 2 + t)"
    proof -
      have "ln (12 + 2 * t) = ln (12 * (1 + t / 6))" by auto
      also have "\<dots> = ln 12 + ln (1 + t / 6)"
        unfolding ln_mult using * by simp
      also have "\<dots> \<le> 5 / 2 + t / 6"
      proof (rule add_mono)
        have "(144 :: real) < (271 / 100) ^ 5"
          by (simp add: power_numeral_reduce)
        also have "271 / 100 < exp (1 :: real)"
          using e_approx_32 by (simp add: abs_if split: if_split_asm)
        hence "(271 / 100) ^ 5 < exp (1 :: real) ^ 5"
          by (rule power_strict_mono) auto
        also have "\<dots> = exp ((5 :: nat) * (1 :: real))"
          by (rule exp_of_nat_mult [symmetric])
        also have "\<dots> = exp (5 :: real)"
          by auto
        finally have "exp (ln (12 :: real) * (2 :: nat)) \<le> exp 5"
          by (subst exp_of_nat2_mult) auto
        thus "ln (12 :: real) \<le> 5 / 2"
          by auto
        show "ln (1 + t / 6) \<le> t / 6"
          by (intro ln_add_one_self_le_self) (use * in auto)
      qed
      finally show ?thesis using * by auto
    qed
    also have "\<dots> \<le> 1 / 960 * exp (\<phi> t)"
    proof -
      have "8 * (5 / 2 + t) - 1 / 960 * (12 + 2 * t) ^ 4
          = -(1 / 60 * t ^ 4 + 2 / 5 * t ^ 3 + 18 / 5 * t ^ 2 + 32 / 5 * t + 8 / 5)"
        by (simp add: power_numeral_reduce field_simps)
      also have "\<dots> \<le> 0" using *
        by (subst neg_le_0_iff_le) (auto intro: add_nonneg_nonneg)
      moreover have "exp (\<phi> t) = (12 + 2 * t) ^ 4"
      proof -
        have "exp (\<phi> t) = (12 + 2 * t) powr (real 4)" unfolding \<phi>_def powr_def using * by auto
        also have "\<dots> = (12 + 2 * t) ^ 4" by (rule powr_realpow) (use * in auto)
        finally show ?thesis .
      qed
      ultimately show ?thesis by auto
    qed
    finally show "\<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)" .
  next
    fix t :: real assume *: "0 \<le> t"
    have "(1 :: real) \<le> 4 * 1" by auto
    also have "\<dots> \<le> 4 * ln 12"
    proof -
      have "exp (1 :: real) \<le> 3" by (rule exp_le)
      also have "\<dots> \<le> exp (ln 12)" by auto
      finally have "(1 :: real) \<le> ln 12" using exp_le_cancel_iff by blast
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> 4 * ln (12 + 2 * t)" using * by auto
    finally show "1 \<le> \<phi> t" unfolding \<phi>_def .
  next
    show "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
         "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<theta> y \<le> \<theta> x"
         "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
      unfolding \<theta>_def \<phi>_def by auto
  qed
  thus "zeta_bound_param (\<lambda>t. 1 / 2) (\<lambda>t. 4 * ln (12 + 2 * max 0 t))"
    unfolding \<theta>_def \<phi>_def by auto
qed

theorem zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0" and "Complex \<beta> \<gamma> \<noteq> 1"
  shows "1 - \<beta> \<ge> C\<^sub>1 / ln (\<bar>\<gamma>\<bar> + 2)"
proof -
  have "1 / 952320 * (1 / ln (\<bar>\<gamma>\<bar> + 2))
      \<le> 1 / 29760 * (1 / 2 / (4 * ln (12 + 2 * max 0 (2 * \<bar>\<gamma>\<bar> + 1))))" (is "?x \<le> ?y")
  proof -
    have "ln (14 + 4 * \<bar>\<gamma>\<bar>) \<le> 4 * ln (\<bar>\<gamma>\<bar> + 2)" by (rule ln_bound_1) auto
    hence "1 / 238080 / (4 * ln (\<bar>\<gamma>\<bar> + 2)) \<le> 1 / 238080 / (ln (14 + 4 * \<bar>\<gamma>\<bar>))"
      by (intro divide_left_mono) auto
    also have "\<dots> = ?y" by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> \<le> 1 - \<beta>" by (intro classical_zeta_bound.zeta_nonzero_region assms)
  finally show ?thesis unfolding PNT_const_C\<^sub>1_def by auto
qed

unbundle no_pnt_notation
end