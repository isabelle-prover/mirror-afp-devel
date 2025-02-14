(*
 Title:Laplacian_Distribution.thy
 Author: Tetsuya Sato
*)

theory Laplace_Distribution
  imports "HOL-Probability.Probability"
    "Additional_Lemmas_for_Integrals"
    "Additional_Lemmas_for_Calculation"
begin

section \<open>Laplace Distribution\<close>

subsection \<open> Desity Function and Cumulative Distribution Function \<close>

text \<open> We refer {\tt  HOL/Probability/Distributions.thy} in the standard library. \<close>

definition laplace_density :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "laplace_density l m x = (if l > 0 then exp(-\<bar>x - m\<bar> / l) / (2 * l) else 0)"

definition laplace_CDF :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "laplace_CDF l m x =
 (if l > 0 then
 if x < m then exp((x - m) / l) / 2 else 1 - exp(-(x - m) / l) / 2 else 0)"

lemma laplace_density_nonneg[simp]:
  shows "0 \<le> laplace_density l m x"
  unfolding laplace_density_def by auto

lemma laplace_CDF_nonneg[simp]:
  shows "0 \<le> laplace_CDF l m x"
  unfolding laplace_CDF_def
proof-
  consider"0 \<ge> l"|"0 < l \<and> x < m" | "0 < l \<and> x \<ge> m"
    by linarith
  thus "0 \<le> (if 0 < l then if x < m then exp ((x - m) / l) / 2 else 1 - exp (- (x - m) / l) / 2 else 0)"
  proof(cases)
    assume "l \<le> 0"
    thus ?thesis by auto
  next assume "0 < l \<and> x < m"
    thus ?thesis by auto
  next assume "0 < l \<and> x \<ge> m"
    hence "exp (- (x - m) / l) \<le> 1"
      by (auto simp: divide_nonpos_pos)
    hence "exp (- (x - m) / l)/2 \<le> 1"
      by linarith
    thus ?thesis by auto
  qed
qed

lemma borel_measurable_laplace_density[measurable]:
  shows "laplace_density l m \<in> borel \<rightarrow>\<^sub>M borel"
  unfolding laplace_density_def by auto

lemma borel_measurable_laplace_density2[measurable]:
  shows "(\<lambda> m :: real. (laplace_density l m x)) \<in> borel \<rightarrow>\<^sub>M borel"
  unfolding laplace_density_def by auto

lemma laplace_density_mirror:
  shows "laplace_density l m (2 * m - x) = laplace_density l m x"
  unfolding laplace_density_def by auto

lemma laplace_density_shift:
  shows "laplace_density l (m + c) (x + c) = laplace_density l m x"
  unfolding laplace_density_def by auto

lemma borel_measurable_laplace_CDF[measurable]:
  shows "laplace_CDF l m \<in> borel \<rightarrow>\<^sub>M borel"
  unfolding laplace_CDF_def by auto

lemma borel_measurable_laplace_CDF2[measurable]:
  shows "(\<lambda> m :: real. laplace_CDF l m x)\<in> borel \<rightarrow>\<^sub>M borel"
  unfolding laplace_CDF_def by auto

lemma laplace_CDF_mirror:
  assumes "l > 0"
  shows "laplace_CDF l m (2 * m - x) = 1 - laplace_CDF l m x"
  unfolding laplace_CDF_def
  using assms by auto

lemma laplace_CDF_shift:
  shows "laplace_CDF l (m + c) (x + c) = laplace_CDF l m x"
  unfolding laplace_CDF_def by auto

lemma nn_integral_laplace_density_pos:
  assumes pos[arith]: "0 < l" and 1: "a \<ge> m"
  shows "(\<integral>\<^sup>+ x \<in> {a..}. ennreal (laplace_density l m x) \<partial>lborel) = 1 - laplace_CDF l m a"
proof-
  from 1 have "(\<integral>\<^sup>+ x \<in> {a..}. ennreal (laplace_density l m x) \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {a..}. (exp ((m - x) / l)/ (2 * l)) \<partial>lborel)"
    by(intro nn_integral_cong,unfold laplace_density_def)(auto simp add: field_simps split: split_indicator)
  also have "... = 0 - (- exp ((m - a) / l) / 2)"
  proof(rule nn_integral_FTC_atLeast)
    show "((\<lambda>a. - exp ((m - a) / l) / 2) \<longlongrightarrow> 0) at_top"
    proof(rule tendstoI,subst eventually_at_top_linorder)
      fix e :: real assume A0: "0 < e"
      show "\<exists>N. \<forall>n\<ge>N. dist (- exp ((m - n) / l) / 2) 0 < e"
      proof(intro exI allI impI)
        fix n assume A1: "m - ln (e * 2) * l + 1 \<le> n"
        have "(m - n) / l \<le> (m - (m - ln (e * 2) * l + 1)) / l"
          using A1 pos by (auto simp: divide_le_cancel)
        also have "... =(m - m + ln (e * 2) * l - 1) / l"
          by auto
        also have "... =(ln (e * 2) * l - 1) / l"
          by auto
        also have "... <(ln (e * 2) * l) / l"
          by (auto simp: mult_imp_div_pos_less)
        also have "... \<le>ln (e * 2)"
          using pos by auto
        finally have "(m - n) / l < ln (e * 2)".
        hence "exp ((m - n) / l) < exp (ln (e * 2))"
          by auto
        also have "... = e * 2"
          using A0 by auto
        finally show "dist (- exp ((m - n) / l) / 2) 0 < e"by auto
      qed
    qed
    fix x :: real assume "a \<le> x"
    have "DERIV (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (m-x))) x :> exp ((m-x) * (1 / l)) * (1 / l) * (-1)"
    proof(intro DERIV_chain)
      show "(exp has_real_derivative exp ((m - x) * (1 / l))) (at ((m - x) * (1 / l)))"
        by auto
      show "((\<lambda>x. x * (1 / l)) has_real_derivative 1 / l) (at (m - x))"
        by (metis DERIV_cmult_Id mult_commute_abs)
      have P21: "((-) m) = (\<lambda> x. m - x)"
        by auto
      have "((\<lambda> x. m - x) has_real_derivative 0 - 1) (at x)"
        by (rule DERIV_diff,auto intro!:DERIV_const DERIV_ident)
      thus"((-) m has_real_derivative - 1) (at x)"
        using P21 by auto
    qed
    hence P1: "DERIV (\<lambda> y. (-1/2) * (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (m-x))) y) x :> (-1/2) * (exp ((m-x) * (1 / l)) * (1 / l) * (-1))"
      by(rule DERIV_cmult)
    have P2: "(\<lambda> y. (-1/2) * (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (m-x))) y) = ((\<lambda>a. - (exp ((m - a) / l) / 2)))"
      by auto
    have P3: "(-1/2) * (exp ((m-x) * (1 / l)) * (1 / l) * (-1)) = exp ((m - x) / l) / (2 * l)"
      by auto
    from P1 P2 P3 show "((\<lambda>a. - exp ((m - a) / l) / 2) has_real_derivative exp ((m - x) / l) / (2 * l)) (at x)"
      by auto
  qed(auto)
  also have "... = ennreal (exp ((m - a) / l) / 2)"
    by auto
  also have "... = ennreal (1 - laplace_CDF l m a)"
    using laplace_CDF_def pos 1 by auto
  finally show "(\<integral>\<^sup>+x\<in>{a..}. ennreal (laplace_density l m x)\<partial>lborel) = ennreal (1 - laplace_CDF l m a)" by auto
qed

lemma nn_integral_laplace_density_pos_center:
  assumes pos[arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x \<in> {m..}. ennreal (laplace_density l m x) \<partial>lborel) = 1/2"
proof-
  have "(\<integral>\<^sup>+ x \<in> {m..}. ennreal (laplace_density l m x) \<partial>lborel) = ennreal (1 - laplace_CDF l m m)"
    using nn_integral_laplace_density_pos by auto
  also have "... = 1/2"
    by (auto simp: laplace_CDF_def assms divide_ennreal_def)
  finally show ?thesis.
qed

lemma nn_integral_laplace_density_neg:
  assumes pos[arith]: "0 < l" and 1: "a \<le> m"
  shows "(\<integral>\<^sup>+ x \<in> {..a}. ennreal (laplace_density l m x) \<partial>lborel) = laplace_CDF l m a"
proof-
  from 1 have "(\<integral>\<^sup>+ x \<in> {..a}. ennreal (laplace_density l m x) \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..a}. (exp ((x - m) / l)/ (2 * l)) \<partial>lborel)"
    by(intro nn_integral_cong,unfold laplace_density_def)(auto simp add: field_simps split: split_indicator)
  also have "... = (exp ((a - m) / l) / 2) - 0"
  proof(rule nn_integral_FTC_atGreatest)
    show "((\<lambda>a. exp ((a - m) / l) / 2) \<longlongrightarrow> 0) at_bot"
    proof(rule tendstoI,subst eventually_at_bot_linorder)
      fix e :: real assume A0: "0 < e"
      show "\<exists>N. \<forall>n\<le>N. dist (exp ((n - m) / l) / 2) 0 < e"
      proof(intro exI allI impI)
        fix n assume "n \<le> m + ln (e * 2) * l - 1"
        hence "(n - m) \<le>((m + ln (e * 2) * l - 1) - m)"
          by auto
        hence "(n - m)/l \<le>(ln (e * 2) * l - 1) /l"
          by (auto simp: pos divide_le_cancel)
        also have "... = ln (e * 2) - 1/l"
          by (auto simp: diff_divide_distrib)
        also have "... < ln (e * 2) "
          by auto
        finally have "(n - m)/l <ln (e * 2)".
        hence "exp ((n - m) / l) < exp(ln (e * 2))"
          by auto
        also have "... = e * 2"
          by (auto simp: A0)
        finally show "dist (exp ((n - m) / l) / 2) 0 < e"by auto
      qed
    qed
    fix x :: real assume A1: "x \<le> a"
    have "DERIV (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (x - m))) x :> exp ((x-m) * (1 / l)) * (1 / l) * 1"
    proof(rule DERIV_chain)
      show "((\<lambda>x. x - m) has_real_derivative 1) (at x)"
        using DERIV_const DERIV_ident Deriv.field_differentiable_diff
      proof -
        have "\<exists>r ra. r - ra = 1 \<and> ((\<lambda>r. m) has_real_derivative ra) (at x) \<and> ((\<lambda>r. r) has_real_derivative r) (at x)"
          using DERIV_const DERIV_ident diff_zero by blast
        then show ?thesis
          using Deriv.field_differentiable_diff by force
      qed
      show "(exp \<circ> (\<lambda>x. x * (1 / l)) has_real_derivative exp ((x - m) * (1 / l)) * (1 / l)) (at (x - m))"
      proof(rule DERIV_chain)
        show "((\<lambda>x. x * (1 / l)) has_real_derivative 1 / l) (at (x - m))"
          by (metis DERIV_cmult_Id mult_commute_abs)
        show "(exp has_real_derivative exp ((x - m) * (1 / l))) (at ((x - m) * (1 / l)))"
          by auto
      qed
    qed
    hence P1: "DERIV (\<lambda> y. (1/2) * (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (x - m))) y) x :> (1/2) *(exp ((x-m) * (1 / l)) * (1 / l) * 1)"
      by(rule DERIV_cmult)
    have P2: "(\<lambda> y. (1/2) * (exp \<circ> (\<lambda>x. x * (1 / l)) \<circ> (\<lambda> x. (x - m))) y) = ((\<lambda>a. exp ((a - m) / l) / 2))"
      by auto
    have P3: "(1/2) *(exp ((x-m) * (1 / l)) * (1 / l) * 1) = exp ((x - m) / l) / (2 * l)"
      by auto
    from P1 P2 P3
    show "((\<lambda>a. exp ((a - m) / l) / 2) has_real_derivative exp ((x - m) / l) / (2 * l)) (at x)"
      by auto
  qed(auto)
  also have "... = ennreal (exp ((a - m) / l) / 2)"
    by auto
  also have "... = ennreal (laplace_CDF l m a)"
    using laplace_CDF_def pos 1 by auto
  finally show ?thesis.
qed

lemma nn_integral_laplace_density_neg_center:
  assumes pos[arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x \<in> {..m}. ennreal (laplace_density l m x) \<partial>lborel) = 1/2"
proof-
  have "(\<integral>\<^sup>+ x \<in> {..m}. ennreal (laplace_density l m x) \<partial>lborel) = ennreal (laplace_CDF l m m)"
    using nn_integral_laplace_density_neg by auto
  also have "... = 1/2"
    by (auto simp: laplace_CDF_def assms divide_ennreal_def)
  finally show ?thesis.
qed

proposition nn_integral_laplace_density_mass_1:
  assumes pos[arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x. ennreal (laplace_density l m x) \<partial>lborel) = 1"
proof-
  have "(\<integral>\<^sup>+ x. ennreal (laplace_density l m x) \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {..m}. ennreal (laplace_density l m x) \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {m..}. ennreal (laplace_density l m x) \<partial>lborel)"
    by(rule nn_integral_lborel_split,auto)
  also have "... = 1/2 + 1/2"
    by(auto simp:nn_integral_laplace_density_neg_center[of l m,OF pos] nn_integral_laplace_density_pos_center[of l m,OF pos])
  also have "... = 2/2"
    by (auto simp: add_divide_distrib_ennreal[THEN sym])
  also have "... = 1"
    by auto
  finally show ?thesis.
qed

lemma emeasure_laplace_density_mass_1:
  "0 < l \<Longrightarrow> emeasure (density lborel (laplace_density l m)) UNIV = 1"
  by(auto simp: emeasure_density nn_integral_laplace_density_mass_1)

proposition nn_integral_laplace_density:
  assumes pos[arith]: "0 < l"
  shows "(\<integral>\<^sup>+ x \<in> {..a}. ennreal (laplace_density l m x) \<partial>lborel) = laplace_CDF l m a"
proof(cases"a \<le> m")
  case True
  thus ?thesis using nn_integral_laplace_density_neg pos by auto
next
  case False
  have eq0: "1 - laplace_CDF l m a = (\<integral>\<^sup>+ x \<in> {a..}. ennreal (laplace_density l m x) \<partial>lborel)"
    using nn_integral_laplace_density_pos pos False by auto
  also have "... = (\<integral>\<^sup>+ x \<in> {a<..}. ennreal (laplace_density l m x) \<partial>lborel)"
    by(auto simp: nn_integral_interval_greaterThan_atLeast)
  finally have eqA: "1 - laplace_CDF l m a = (\<integral>\<^sup>+ x \<in> {a<..}. ennreal (laplace_density l m x) \<partial>lborel)".

  hence eqA2: "1 = (\<integral>\<^sup>+ x \<in> {a<..}. ennreal (laplace_density l m x) \<partial>lborel) + laplace_CDF l m a"
  proof(intro ennreal_diff_add_transpose)
    show "ennreal (laplace_CDF l m a) \<le> (1 :: ennreal)"
      using False laplace_CDF_def by auto
    show "1 - ennreal (laplace_CDF l m a) = (\<integral>\<^sup>+x :: real\<in>{a<..}. ennreal (laplace_density l m x)\<partial>lborel)"
      using eqA ennreal_1 ennreal_minus laplace_CDF_nonneg by metis
  qed

  have "1 = (\<integral>\<^sup>+ x. ennreal (laplace_density l m x) \<partial>lborel)"
    using nn_integral_laplace_density_mass_1 pos by auto
  also have "... = (\<integral>\<^sup>+ x\<in>{..a}. ennreal (laplace_density l m x) \<partial>lborel) + (\<integral>\<^sup>+ x\<in> {a<..} . ennreal (laplace_density l m x) \<partial>lborel)"
    using nn_integral_lborel_split nn_integral_interval_greaterThan_atLeast by auto
  finally have eqB: "1 = (\<integral>\<^sup>+ x\<in>{..a}. ennreal (laplace_density l m x) \<partial>lborel) + (\<integral>\<^sup>+ x\<in> {a<..} . ennreal (laplace_density l m x) \<partial>lborel)".

  from eqA2 eqB
  have "(\<integral>\<^sup>+ x \<in> {a<..}. ennreal (laplace_density l m x) \<partial>lborel) + laplace_CDF l m a = (\<integral>\<^sup>+ x\<in>{..a}. ennreal (laplace_density l m x) \<partial>lborel) + (\<integral>\<^sup>+ x\<in> {a<..} . ennreal (laplace_density l m x) \<partial>lborel)"
    by auto
  thus ?thesis
    using eqA by fastforce
qed

lemma emeasure_laplace_density:
  assumes "0 < l"
  shows "emeasure (density lborel (laplace_density l m)) {.. a} = laplace_CDF l m a"
  by (auto simp: emeasure_density nn_integral_laplace_density assms)

subsection \<open> Moments \<close>

lemma laplace_moment_0_a:
  assumes pos[arith]: "0 < l"
    and posa[arith]: "0 \<le> a"
  shows "has_bochner_integral lborel (\<lambda> x. (indicator {0..a} x *\<^sub>R (laplace_density l 0 x)))(1/2 - exp(-a / l) /2)"
proof(rule has_bochner_integral_nn_integral)
  show "(\<lambda>x. indicat_real {0..a} x *\<^sub>R laplace_density l 0 x) \<in> borel_measurable lborel"
    by measurable
  show "AE x in lborel. 0 \<le> indicat_real {0..a} x *\<^sub>R laplace_density l 0 x"
    by auto
  show "0 \<le>1 / 2 - exp (- a / l) / 2"
    by(auto simp add: pos posa)
  have "(\<integral>\<^sup>+ x \<in> {0..}. ennreal (laplace_density l 0 x) \<partial>lborel) = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel) + (\<integral>\<^sup>+ x \<in> {a..}. ennreal (laplace_density l 0 x) \<partial>lborel)"
    by(rule nn_set_integral_lborel_split_AtLeast,auto)
  hence "1/2 = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel) + (1 - laplace_CDF l 0 a)"
    by(auto simp: nn_integral_laplace_density_pos_center[of l 0,OF pos] nn_integral_laplace_density_pos[of l 0 a,OF pos posa])
  also have "... = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel) + (1 - (1 - exp(- a / l) / 2))"
    unfolding laplace_CDF_def by auto
  finally have "ennreal (1/2) - exp(- a / l) / 2 = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel) + (1 - (1 - exp(- a / l) / 2)) - exp(- a / l) / 2"
    by (metis ennreal_divide_numeral ennreal_numeral numeral_One zero_le_numeral) (* takes long time *)
  hence "ennreal (1/2) - exp(- a / l) / 2 = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel)"
    by auto
  hence eq0a: "1/2 - exp(- a / l) / 2 = (\<integral>\<^sup>+ x \<in> {0..a}. ennreal (laplace_density l 0 x) \<partial>lborel)"
    by (metis (full_types) ennreal_minus exp_ge_zero zero_le_divide_iff zero_le_numeral)
  also have "... = (\<integral>\<^sup>+ x. ennreal (indicat_real {0..a} x *\<^sub>R laplace_density l 0 x) \<partial>lborel)"
    by (auto simp: mult.commute nn_integral_set_ennreal)
  finally show "(\<integral>\<^sup>+ x. ennreal (indicat_real {0..a} x *\<^sub>R laplace_density l 0 x) \<partial>lborel) = (1/2 - exp(- a / l) / 2)"
    by presburger
qed

lemma laplace_moment_0_pos:
  assumes pos[arith]: "0 < l"
  shows "has_bochner_integral lborel (\<lambda> x. (indicator {0..} x *\<^sub>R (laplace_density l 0 x)))(1/2 :: real)"
proof(rule has_bochner_integral_nn_integral)
  have "(\<integral>\<^sup>+ x. ennreal (laplace_density l 0 x * indicat_real {0..} x) \<partial>lborel) = 1 / 2"
    using nn_integral_laplace_density_pos_center
    by (auto simp: nn_integral_set_ennreal)
  thus"(\<integral>\<^sup>+ x. ennreal (indicat_real {0..} x *\<^sub>R laplace_density l 0 x) \<partial>lborel) = ennreal (1 / 2)"
    by (auto simp: divide_ennreal_def mult.commute)
  show "(\<lambda>x. indicat_real {0..} x *\<^sub>R laplace_density l 0 x) \<in> borel_measurable lborel"
    by measurable
  show "0 \<le> (1/2 :: real)"
    by auto
  show "AE x in lborel. 0 \<le> indicat_real {0..} x *\<^sub>R laplace_density l 0 x"
    by auto
qed

lemma laplace_moment_0:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "has_bochner_integral lborel (\<lambda> x. (indicator {0..} x *\<^sub>R ((laplace_density l 0 x) * x^k)))(fact k * l^k/2)"
    and "(\<lambda>a. LBINT x. indicator {0..a} x *\<^sub>R ((laplace_density l 0 x) * x^k)) \<longlonglongrightarrow> (LBINT y. (indicator {0..} y *\<^sub>R ((laplace_density l 0 y) * y^k)))"
proof(induction k)
  let ?f ="\<lambda> (k :: nat) (x :: real). (1/(2 * l)) * (exp(- x / l) * x^k)"
  show cond0: "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ 0)) (fact 0 * l ^ 0 / 2)"
    using laplace_moment_0_pos by auto
  show cond1: "(\<lambda>x. LBINT xa. indicat_real {0..real x} xa *\<^sub>R (laplace_density l 0 xa * xa ^ 0)) \<longlonglongrightarrow> (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ 0))"
  proof(rule tendstoI, subst eventually_at_top_linorder, intro exI allI impI)
    fix e :: real and n :: nat
    assume pose: "0 < e"
    assume ineqn: "nat(floor (l * ln (1 / (2 * e)))) + 1 \<le> n"
    hence posn: "0 \<le> real n"by auto
    from ineqn have ineqn2: "l * ln (1 / (2 * e)) < real n"
      by linarith
    show "dist (LBINT xa. indicat_real {0..real n} xa *\<^sub>R (laplace_density l 0 xa * xa ^ 0)) (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ 0)) < e"
    proof(unfold dist_real_def)
      have eq1: "(LBINT y. indicat_real {0..} y * laplace_density l 0 y) = 1/2"
        using has_bochner_integral_integral_eq cond0 by force
      hence eq2: "(LBINT x. indicat_real {0..real n} x * laplace_density l 0 x) = 1/2 - exp(- real n / l) /2"
        using has_bochner_integral_integral_eq[OF laplace_moment_0_a[of l"real n", OF pos posn] ] by auto
      from eq1 eq2 dist_real_def have "\<bar>(LBINT x. indicat_real {0..real n} x * laplace_density l 0 x) - (LBINT y. indicat_real {0..} y * laplace_density l 0 y)\<bar> = exp(- real n / l) /2"
      proof -
        have f1: "(LBINT r. indicat_real {0..real n} r * laplace_density l 0 r) - (LBINT r. indicat_real {0..} r * laplace_density l 0 r) < 0"
          by (auto simp: eq1 eq2)
        have f2: "exp (- real n / l) / 2 = - ((LBINT r. indicat_real {0..real n} r * laplace_density l 0 r) - (LBINT r. indicat_real {0..} r * laplace_density l 0 r))"
          using eq1 eq2 by linarith
        show ?thesis
          using f2 f1 by auto
      qed
      also have "... < exp(ln (2 * e)) /2"
      proof-
        have "l * ln (1 / (2 * e)) < real n"
          using ineqn2 by auto
        hence "l * ln (1 / (2 * e)) / l < real n / l"
          using pos divide_strict_right_mono by blast
        hence "ln (inverse(2 * e)) < real n / l"
          by (auto simp: inverse_eq_divide)
        hence "-ln (2 * e) < real n / l"
          by (metis ln_inverse mult_pos_pos pose zero_less_numeral)
        hence "ln (2 * e) > - real n / l"
          by auto
        thus ?thesis by auto
      qed
      also have "... = e"
        by (auto simp: pose)
      finally show "\<bar>(LBINT xa. indicat_real {0..real n} xa *\<^sub>R (laplace_density l 0 xa * xa ^ 0)) - (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ 0))\<bar> < e"by auto
    qed
  qed

  fix k :: nat
  assume khasBoh: "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ k)) (fact k * l ^ k / 2)" and kconverge: "(\<lambda>x. LBINT xa. indicat_real {0..real x} xa *\<^sub>R (laplace_density l 0 xa * xa ^ k)) \<longlonglongrightarrow> (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ k))"
  have kconverge2: "(\<lambda>x. LBINT xa. 1 / (2 * l) * (exp (- xa / l) * xa ^ k) * indicat_real {0..real x} xa) \<longlonglongrightarrow>(LBINT y. indicat_real {0..} y * (laplace_density l 0 y * y ^ k))"
  proof(subst tendsto_cong)
    show "(\<lambda>x. LBINT xa. indicat_real {0..real x} xa * (laplace_density l 0 xa * xa ^ k)) \<longlonglongrightarrow> (LBINT y. indicat_real {0..} y * (laplace_density l 0 y * y ^ k))"
      using kconverge by auto
    have eq1: "\<And>x. (LBINT xa. 1 / (2 * l) * (exp (- xa / l) * xa ^ k) * indicat_real {0..real x} xa) = (LBINT xa. indicat_real {0..real x} xa * (laplace_density l 0 xa * xa ^ k))"
      unfolding laplace_density_def by(rule Bochner_Integration.integral_cong,auto simp: split: split_indicator)
    thus "\<forall>\<^sub>F x in sequentially. (LBINT xa. 1 / (2 * l) * (exp (- xa / l) * xa ^ k) * indicat_real {0..real x} xa) = (LBINT xa. indicat_real {0..real x} xa * (laplace_density l 0 xa * xa ^ k))"
      by(rule eventually_sequentiallyI)
  qed
  have "(LBINT y. indicat_real {0..} y * (laplace_density l 0 y * y ^ k)) = (LBINT x. 1 / (2 * l) * (exp (- x / l) * x ^ k) * indicat_real {0..} x)"
    unfolding laplace_density_def by(rule Bochner_Integration.integral_cong,auto simp: split: split_indicator)
  hence kconverge3: "(\<lambda>x. LBINT xa. 1 / (2 * l) * (exp (- xa / l) * xa ^ k) * indicat_real {0..real x} xa) \<longlonglongrightarrow>(LBINT x. 1 / (2 * l) * (exp (- x / l) * x ^ k) * indicat_real {0..} x)"
    using kconverge2 by presburger

  from khasBoh have A0: "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (?f k x)) (fact k * l ^ k / 2)"
    by(subst has_bochner_integral_cong, auto intro: simp: assms laplace_density_def split:split_indicator)
  have A01: "integrable lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (?f k x))"
    using has_bochner_integral_iff A0 by blast
  have A02: "(LBINT x. indicat_real {0..} x *\<^sub>R (?f k x)) = (fact k * l ^ k / 2)"
    using has_bochner_integral_iff A0 by blast

  let ?AF ="\<lambda> (x :: real). x^(Suc k)"
  let ?Ag ="\<lambda> (x :: real). exp(- x / l)"
  let ?Af ="\<lambda> (x :: real). (Suc k) * x^k"
  let ?AG ="\<lambda> (x :: real). (- l) * exp(- x / l)"

  have FgfSuc: "(\<lambda> x :: real. (1/(2 * l)) * (?AF x * ?Ag x)) = ?f(Suc k)"
    by (auto simp: mult.commute)
  have fgSucf: "(\<lambda> x :: real. (1/(2 * l)) * (?Af x * ?Ag x)) = (\<lambda> x :: real. (Suc k) * ?f k x)"
    by fastforce
  have fglSucf: "(\<lambda> x :: real. (1/(2 * l)) * (?Af x * ?AG x)) = (\<lambda> x :: real. (- l) * (Suc k) * ?f k x)"
    by fastforce
  have cont_f: "\<And>x. isCont ?Af x"
    by auto
  have cont_g: "\<And>x. isCont ?Ag x"
    by auto
  have drv_F: "\<And>x. DERIV ?AF x :> ?Af x"
  proof-
    fix x :: real
    show "DERIV ?AF x :> ?Af x"
      by (metis DERIV_pow add_0 add_Suc add_diff_cancel_left')
  qed
  have drv_G: "\<And>x. DERIV ?AG x :> ?Ag x"
  proof-
    fix x :: real
    have "(exp o (\<lambda>x. (- x / l)) has_real_derivative exp (- x / l) * (- 1 / l)) (at x)"
    proof(rule DERIV_chain)
      show "(exp has_real_derivative exp (- x / l)) (at (- x / l))"by auto
      show "((\<lambda>x. - x / l) has_real_derivative - 1 / l) (at x)"
        using DERIV_cdivide DERIV_ident DERIV_mirror by blast
    qed
    hence drv_G2: "((\<lambda>x. - l * (exp o (\<lambda>x. (- x / l)))x) has_real_derivative - l * (exp (- x / l) * (- 1 / l))) (at x)"
      by(rule DERIV_cmult)
    thus"DERIV ?AG x :> ?Ag x"
    proof-
      have "(\<lambda>x. - l * (exp o (\<lambda>x. (- x / l)))x) = ?AG"
        unfolding comp_def by auto
      moreover have "- l * (exp (- x / l) * (- 1 / l)) = ?Ag x"
        by auto
      ultimately show ?thesis
        using drv_G2 by auto
    qed
  qed

  {
    fix a :: real assume posa: "0 \<le> a"
    have "integrable lborel (\<lambda>x.((?AF x) * (?Ag x) + (?Af x) * (?AG x)) * indicator {0 .. a} x)"
      by(intro integral_by_parts_integrable cont_f cont_g drv_F drv_G posa)
    hence A2: "integrable lborel (\<lambda>x. (?f(Suc k) x + (- l) * (Suc k) * (?f k x)) * indicator {0 .. a} x)"
      by(auto simp:field_simps)
    hence "integrable lborel (\<lambda>x. ((?f(Suc k) x + (- l) * (Suc k) * (?f k x)) * indicator {0 .. a} x) - ((- l) * (Suc k) * (?f k x) * indicator {0 .. a} x))"
    proof-
      show "integrable lborel (\<lambda>x. ((?f(Suc k) x + (- l) * (Suc k) * (?f k x)) * indicator {0 .. a} x) - ((- l) * (Suc k) * (?f k x) * indicator {0 .. a} x))"
      proof(intro Bochner_Integration.integrable_diff A2 posa)
        have A03: "integrable lborel (\<lambda>x. (indicator {0 ..} x) *(?f k x) * indicator {0 .. a} x)"
        proof(rule integrable_real_mult_indicator)
          show "{0..a} \<in> sets lborel"by auto
          show "integrable lborel (\<lambda>x. indicat_real {0..} x * (?f k x))"
            using A01 by auto
        qed
        have A04: "integrable lborel (\<lambda>x. (?f k x) * indicator {0 .. a} x)"
        proof-
          have "(\<lambda>x. (indicator {0 ..} x) *(?f k x) * indicator {0 .. a} x) = (\<lambda>x. (?f k x) * indicator {0 .. a} x)"
            by(auto simp:field_simps split: split_indicator)
          thus ?thesis
            using A03 by auto
        qed
        hence "integrable lborel (\<lambda>x. (- l) * (Suc k) *((?f k x) * indicat_real {0..a} x))"
          by(intro integrable_mult_right A04)
        thus "integrable lborel (\<lambda>x. (- l) * (Suc k) * (?f k x) * indicat_real {0..a} x)"
          by(auto simp:field_simps split: split_indicator)
      qed
    qed
    hence "integrable lborel (\<lambda>x. (?f(Suc k) x * indicator {0 .. a} x))"
      by (auto simp:field_simps)
  } note integrabledSuck = this

  {
    fix a :: real assume posa: "0 \<le> a"
    have "(\<integral>x. (?AF x * ?Ag x) * indicator {0 .. a} x \<partial>lborel) = ?AF a * ?AG a - ?AF 0 * ?AG 0 - \<integral>x. (?Af x * ?AG x) * indicator {0 .. a} x \<partial>lborel"
      by(intro integral_by_parts cont_f cont_g drv_F drv_G posa)
    hence "(\<integral>x. ?f(Suc k) x * indicator {0 .. a} x \<partial>lborel) = (1/(2 * l)) *(?AF a * ?AG a - ?AF 0 * ?AG 0) - \<integral>x. (- l) * (Suc k) * (?f k x) * indicator {0 .. a} x \<partial>lborel"
      by (auto simp:field_simps)
    also have "... = (1/(2 * l)) *(?AF a * ?AG a - ?AF 0 * ?AG 0) - (- l) * \<integral>x. (Suc k) * (?f k x) * indicator {0 .. a} x \<partial>lborel"
      using integral_scaleR_right by auto
    also have "... = (1/(2 * l)) *(?AF a * ?AG a - ?AF 0 * ?AG 0) + l * \<integral>x. (Suc k) * ((?f k x) * indicator {0 .. a} x) \<partial>lborel"
      by (auto simp:field_simps)
    also have "... = (1/(2 * l)) *(?AF a * ?AG a - ?AF 0 * ?AG 0) + l * (Suc k) * \<integral>x. (?f k x) * indicator {0 .. a} x \<partial>lborel"
      using integral_scaleR_right by auto
    finally have "(\<integral>x. ?f(Suc k) x * indicator {0 .. a} x \<partial>lborel) = (1/(2 * l)) *(?AF a * ?AG a - ?AF 0 * ?AG 0) + l * (Suc k) * \<integral>x. (?f k x) * indicator {0 .. a} x \<partial>lborel".
  } note integralfSuck = this

  let ?H ="\<lambda> (i :: nat). \<lambda> x :: real. ?f(Suc k) x * indicator {0 .. i} x"
  have Hi: "\<And>i. integrable lborel (?H i)"
    using exp_ge_zero exp_total integrabledSuck by force

  have Hmono: "AE x in lborel. mono (\<lambda>n. ?H n x)"
    by(auto simp: mono_def split: split_indicator)

  have Intervallim: "\<And>x. (\<lambda>xa. indicat_real {0..real xa} x) \<longlonglongrightarrow> indicat_real {0..} x"
  proof-
    fix x::real show "(\<lambda>xa. indicat_real {0..real xa} x) \<longlonglongrightarrow> indicat_real {0..} x"
    proof(unfold tendsto_def eventually_sequentially,intro allI impI)
      fix S :: "real set" assume "open S" and inInt: "indicat_real {0..} x \<in> S"
      show "\<exists>N. \<forall>n\<ge>N. indicat_real {0..real n} x \<in> S"
      proof(cases"x < 0")
        case True
        thus ?thesis
          using inInt by auto
      next
        case False
        hence "1 \<in> S"
          using inInt by auto
        hence "\<forall>n \<ge> nat(floor x + 1). indicat_real {0..real n} x \<in> S"
          using False
          by (metis add1_zle_eq atLeastAtMost_iff atLeast_iff floor_less_cancel floor_of_nat inInt indicator_simps(1) indicator_simps(2) less_eq_real_def nat_le_iff)
        thus ?thesis by auto
      qed
    qed
  qed

  have Hlim: "AE x in lborel. (\<lambda>i. ?H i x) \<longlonglongrightarrow> ?f(Suc k) x * indicator {0 ..} x"
    by(intro AE_I2 tendsto_intros Intervallim)

  {
    fix k :: nat and x :: real
    assume posx: "0 \<le> x"
    have 1: "{0 :: nat..k} = {0..<(Suc k)}"
      by auto
    have ineq1: "inverse(fact k) *\<^sub>R ((x / l) ^ k) \<le> (\<Sum>n< (Suc k). inverse(fact n) *\<^sub>R ((x / l) ^ n))"
      by(rule sum_nonneg_leq_bound[of"{0..k}"],auto simp: lessThan_atLeast0 posx 1)
    have ineq2: "0 \<le> (\<Sum>n. inverse(fact (n + (Suc k))) *\<^sub>R ((x / l) ^ (n + (Suc k))))"
    proof(rule suminf_nonneg)
      show "summable (\<lambda>n. (x / l) ^ (n + (Suc k)) /\<^sub>R fact (n + (Suc k)))"
        by(subst summable_iff_shift, rule summable_exp_generic)
      show "\<And>n. 0 \<le> (x / l) ^ (n + (Suc k)) /\<^sub>R fact (n + (Suc k))"
        by (auto simp: posx)
    qed
    from ineq1 ineq2 have "inverse(fact k) *\<^sub>R ((x / l) ^k) \<le> (\<Sum>n<(Suc k). inverse(fact n) *\<^sub>R ((x / l) ^ n)) + (\<Sum>n. inverse(fact (n +(Suc k))) *\<^sub>R ((x / l) ^ (n + (Suc k))))"
      by linarith
    also have "... = exp(x / l)"
      using exp_first_terms[of"x / l" "(Suc k)"] by auto
    finally have "inverse(fact k) * ((x / l) ^ k) \<le> exp(x / l)" by auto
    hence "(x / l) ^k / fact k \<le> exp(x / l)"
      by(auto simp: field_simps)
    hence ineq3: "(x / l) ^k \<le> exp(x / l) * fact k"
      by(auto simp: pos_divide_le_eq)
    have "(x / l) ^k * exp(-x / l) = (x / l) ^k / exp(x / l)"
      by (auto simp: exp_minus field_class.field_divide_inverse)
    also have "... \<le> exp(x / l) * fact k / exp(x / l)"
      using ineq3 by (metis divide_right_mono exp_ge_zero)
    finally have "(x / l) ^ k * exp(-x / l) \<le> fact k"by auto
  } note expineq = this

  have Hilim01: "(\<lambda>i :: nat. (1/(2 * l)) *(?AF i * ?AG i - ?AF 0 * ?AG 0) + l * (Suc k) * \<integral>x. (?f k x) * indicator {0 .. i} x \<partial>lborel) \<longlonglongrightarrow> (1/(2 * l)) *(0 - ?AF 0 * ?AG 0) + l * (Suc k) * \<integral>x. (?f k x) * indicator {0 ..} x \<partial>lborel"
  proof(intro tendsto_intros integralfSuck)
    {
      fix k :: nat
      have "(\<lambda>x. (real x / l) ^ k * (exp (- real x / l))) \<longlonglongrightarrow> 0"
      proof(rule tendstoI, subst eventually_at_top_linorder,rule exI)
        fix e :: real assume pose: "0 < e"
        show "\<forall>n \<ge> (\<lambda> e :: real. nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1) e. dist ((real n / l) ^ k * exp (- real n / l)) 0 < e"
        proof(intro allI impI)
          fix n :: nat
          assume assmsn: "nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1 \<le> n"
          hence npos: "0 < real n"by auto
          have "((real n / l) * ((real n / l) ^ k) * exp(- (real n) / l)) \<le> fact (Suc k)"
            using expineq[of"real n" "(Suc k)"] by auto
          hence ineq1: "((real n / l) ^ k * exp(- (real n) / l)) \<le> fact (Suc k) / (real n / l) "
            using pos npos le_divide_eq mult.commute divide_pos_pos
            by (metis vector_space_over_itself.scale_scale)
          also have "... \<le> fact (Suc k) / (real (nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1) / l) "
            using ineq1 assmsn pos by (auto simp: frac_le)
          also have "... < fact (Suc k) / (fact (Suc k) / e) "
          proof(rule divide_strict_left_mono)
            show "(0 :: real) < fact (Suc k)"by auto
            show "(0 :: real) < real (nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1) / l * (fact (Suc k) / e)"
              by (auto simp: pos pose)
            have "fact (Suc k) / e \<le> (l * fact (Suc k) / e) / l"
              by auto
            also have "... < real (nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1) / l"
            proof -
              have "l * fact (Suc k) / e < real (nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1)"
                by linarith
              thus ?thesis
                using divide_strict_right_mono pos by blast
            qed
            finally show "fact (Suc k) / e < real (nat \<lfloor>l * fact (Suc k) / e\<rfloor> + 1) / l".
          qed
          also have "... = e"
            by auto
          finally have ineq3: "((real n / l) ^ k * exp(- real n / l)) < e".
          thus"dist ((real n / l) ^ k * exp (- real n / l)) 0 < e"
            by auto
        qed
      qed
    } note limit1 = this

    have eqlim: "(\<lambda>x. real x ^ Suc k * (- l * exp (- real x / l))) = (\<lambda>x. ((l^Suc k) * (- l)) * (((real x / l) ^ Suc k) * exp (- real x / l)))"
      by (auto simp add: power_divide)
    have "(\<lambda>x. ((l^Suc k) * (- l)) * (((real x / l) ^ Suc k) * exp (- real x / l))) \<longlonglongrightarrow> (((l^Suc k) * (- l)) * 0)"
    proof(intro tendsto_intros)
      show "(\<lambda>x. (real x / l) ^ Suc k * exp (- real x / l)) \<longlonglongrightarrow> 0"
        using limit1[of"Suc k"] by auto
    qed
    with eqlim show "(\<lambda>x. real x ^ Suc k * (- l * exp (- real x / l))) \<longlonglongrightarrow> 0"by auto

    show "(\<lambda>x. LBINT xa. 1 / (2 * l) * (exp (- xa / l) * xa ^ k) * indicat_real {0..real x} xa) \<longlonglongrightarrow> (LBINT x. 1 / (2 * l) * (exp (- x / l) * x ^ k) * indicat_real {0..} x)"
      using kconverge3 by auto
  qed
  have "(1/(2 * l)) * (0 - ?AF 0 * ?AG 0) + l * (Suc k) * (\<integral>x. (?f k x) * indicator {0 ..} x \<partial>lborel) = (1/(2 * l)) * (0 - ?AF 0 * ?AG 0) + l * (Suc k) * (\<integral>x. indicator {0 ..} x *\<^sub>R (?f k x) \<partial>lborel)"
  proof -
    have "\<forall>r. 1 / (2 * l) * (exp (- r / l) * r ^ k) * indicat_real {0..} r = indicat_real {0..} r * (1 / (2 * l) * (exp (- r / l) * r ^ k))"
      by auto
    thus ?thesis
      using real_scaleR_def by presburger
  qed
  also have "... =(1/(2 * l)) * (0 - ?AF 0 * ?AG 0) + l * (Suc k) * (fact k * l ^ k / 2)"
    by (metis A02)
  also have "... = l * (Suc k) * (fact k * l ^ k / 2)"
    by auto
  also have "... = (Suc k) * (fact k) * l * l ^ k / 2"
    by(auto simp: field_simps)
  also have "... = fact (Suc k) * l ^ Suc k / 2"
    by(auto simp: field_simps)
  finally have Hilim02: "(1/(2 * l)) * (0 - ?AF 0 * ?AG 0) + l * (Suc k) * (\<integral>x. (?f k x) * indicator {0 ..} x \<partial>lborel) = (fact (Suc k)) * l ^ (Suc k) / 2".

  have Hilim: "(\<lambda>i :: nat. \<integral>x. ?H i x \<partial>lborel) \<longlonglongrightarrow> (fact (Suc k)) * l ^ (Suc k) / 2"
  proof-
    have "(\<lambda>i :: nat. \<integral>x. ?H i x \<partial>lborel) = (\<lambda>i :: nat. (1/(2 * l)) *(?AF i * ?AG i - ?AF 0 * ?AG 0) + l * (Suc k) * \<integral>x. (?f k x) * indicator {0 .. i} x \<partial>lborel)"
      using integralfSuck by auto
    thus ?thesis
      using Hilim01 Hilim02 by metis
  qed

  have Hu: "(\<lambda> x. ?f(Suc k) x * indicator {0 ..} x) \<in> borel_measurable lborel"
    by measurable

  thus cond3: "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ Suc k)) (fact (Suc k) * l ^ Suc k / 2)"
  proof(subst has_bochner_integral_cong)
    show boch2: "has_bochner_integral lborel (\<lambda>x. ?f(Suc k) x * indicator {0 ..} x) (fact (Suc k) * l ^ Suc k / 2)"
      by(rule has_bochner_integral_monotone_convergence[OF Hi Hmono Hlim Hilim Hu])
    show "lborel = lborel"by auto
    fix x :: real assume "x \<in> space lborel"
    show "indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ Suc k) = 1 / (2 * l) * (exp (- x / l) * x ^ Suc k) * indicat_real {0..} x"
      unfolding laplace_density_def by(auto simp: field_simps split: split_indicator)
  next
    show "fact (Suc k) * l ^ Suc k / 2 = fact (Suc k) * l ^ Suc k / 2"by auto
  qed

  show "(\<lambda>x. LBINT xa. indicat_real {0..real x} xa *\<^sub>R (laplace_density l 0 xa * xa ^ Suc k)) \<longlonglongrightarrow> (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ Suc k))"
  proof-
    have eq1: "(\<lambda>i :: nat. \<integral>x. ?H i x \<partial>lborel) = (\<lambda>x. LBINT xa. indicat_real {0..real x} xa * (laplace_density l 0 xa * (xa * xa ^ k)))"
    proof fix i :: nat show "(LBINT x. 1 / (2 * l) * (exp (- x / l) * x ^ Suc k) * indicat_real {0..real i} x) = (LBINT xa. indicat_real {0..real i} xa * (laplace_density l 0 xa * (xa * xa ^ k)))"
        by(rule Bochner_Integration.integral_cong,unfold laplace_density_def, auto split: split_indicator)
    qed
    have "(LBINT y. indicat_real {0..} y * (laplace_density l 0 y * (y ^ (Suc k)))) = ((1 + real k) * fact k * (l * l ^ k) / 2)"
      using cond3 has_bochner_integral_integral_eq by force
    also have "... = (fact (Suc k)) * l ^ (Suc k) / 2"
      by auto
    finally have eq2: "(LBINT y. indicat_real {0..} y * (laplace_density l 0 y * (y ^ (Suc k)))) = (fact (Suc k)) * l ^ (Suc k) / 2".

    from Hilim eq2[THEN sym] eq1 show "(\<lambda>x. LBINT xa. indicat_real {0..real x} xa *\<^sub>R (laplace_density l 0 xa * xa ^ Suc k)) \<longlonglongrightarrow> (LBINT y. indicat_real {0..} y *\<^sub>R (laplace_density l 0 y * y ^ Suc k))"
      by auto
  qed
qed

lemma laplace_moment_even:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "has_bochner_integral lborel (\<lambda> x. ((laplace_density l m x) * (x - m)^(2 * k)))(fact (2 * k) * l^(2 * k))"
proof-
  have "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 x) * x^(2 * k)))(2 *\<^sub>R (fact (2 * k) * l^(2 * k) /2))"
  proof(rule has_bochner_integral_even_function)
    show "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ (2 * k))) (fact (2 * k) * l ^ (2 * k) / 2)"
      using laplace_moment_0(1)[of l"(2 * k)"] pos by auto
    show "\<And>x. laplace_density l 0 (- x) * (- x) ^ (2 * k) = laplace_density l 0 x * x ^ (2 * k)"
      unfolding laplace_density_def by auto
  qed
  hence "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 (x - m)) * (x - m)^(2 * k)))(2 *\<^sub>R (fact (2 * k) * l^(2 * k) /2))"
    by(subst lborel_has_bochner_integral_real_affine_iff[where c ="1 :: real" and t ="m"],auto)
  thus ?thesis
    using laplace_density_shift[of l m"-m",simplified] by auto
qed

lemma laplace_moment_odd:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "has_bochner_integral lborel (\<lambda> x. ((laplace_density l m x) * (x - m)^(2 * k + 1)))(0)"
proof-
  have "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 x) * x^(2 * k + 1)))(0)"
  proof(rule has_bochner_integral_odd_function)
    show "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ (2 * k + 1))) (fact (2 * k + 1) * l ^ (2 * k + 1) / 2)"
      using laplace_moment_0(1)[of l"(2 * k + 1)"] pos by auto
    show "\<And>x. laplace_density l 0 (- x) * (- x) ^ (2 * k + 1) = - (laplace_density l 0 x * x ^ (2 * k + 1))"
      unfolding laplace_density_def by auto
  qed
  hence "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 (x - m)) * (x - m)^(2 * k + 1)))(0)"
    by(subst lborel_has_bochner_integral_real_affine_iff[where c ="1 :: real" and t ="m"],auto)
  thus ?thesis
    using laplace_density_shift[of l m"-m",simplified] by auto
qed

lemma laplace_moment_abs_odd:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "has_bochner_integral lborel (\<lambda> x. ((laplace_density l m x) * \<bar>x - m\<bar>^(2 * k + 1)))(fact (2 * k + 1) * l ^ (2 * k + 1))"
proof-
  have "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 x) * \<bar>x\<bar>^(2 * k + 1)))(2 *\<^sub>R (fact (2 * k + 1) * l^(2 * k + 1) /2))"
  proof(rule has_bochner_integral_even_function)
    have "has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * x ^ (2 * k + 1)))(fact (2 * k + 1) * l ^ (2 * k + 1) / 2)"
      using laplace_moment_0(1)[of l"(2 * k + 1)"] pos by auto
    thus"has_bochner_integral lborel (\<lambda>x. indicat_real {0..} x *\<^sub>R (laplace_density l 0 x * \<bar>x\<bar> ^ (2 * k + 1)))(fact (2 * k + 1) * l ^ (2 * k + 1) / 2)"
      by(subst has_bochner_integral_cong,auto)
    show "\<And>x. laplace_density l 0 (- x) * \<bar>- x\<bar> ^ (2 * k + 1) = laplace_density l 0 x * \<bar>x\<bar> ^ (2 * k + 1)"
      unfolding laplace_density_def by auto
  qed
  hence "has_bochner_integral lborel (\<lambda> x. ((laplace_density l 0 (x - m)) * \<bar>x - m\<bar>^(2 * k + 1)))(2 *\<^sub>R (fact (2 * k + 1) * l^(2 * k + 1) /2))"
    by(subst lborel_has_bochner_integral_real_affine_iff[where c ="1 :: real" and t ="m"],auto)
  thus ?thesis
    using laplace_density_shift[of l m"-m",simplified] by auto
qed

lemma integral_laplace_moment_even:
  assumes pos[arith]: "0 < l"
  shows "integral\<^sup>L lborel (\<lambda>x.(laplace_density l m x) * (x - m)^(2 * k)) = fact (2 * k) * l^(2 * k)"
  using laplace_moment_even[of l m k] pos by (auto simp: has_bochner_integral_integral_eq)

lemma integral_laplace_moment_odd:
  assumes pos[arith]: "0 < l"
  shows "integral\<^sup>L lborel (\<lambda>x.(laplace_density l m x) * (x - m)^(2 * k + 1)) = 0"
  using laplace_moment_odd[of l m k] pos by (auto simp: has_bochner_integral_integral_eq)

lemma integral_laplace_moment_abs_odd:
  assumes pos[arith]: "0 < l"
  shows "integral\<^sup>L lborel (\<lambda>x.(laplace_density l m x) * \<bar>x - m\<bar>^(2 * k + 1)) =fact (2 * k + 1) * l^(2 * k + 1)"
  using laplace_moment_abs_odd[of l m k] pos by (auto simp: has_bochner_integral_integral_eq)

lemma integrable_laplace_moment:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "integrable lborel (\<lambda> x. ((laplace_density l m x) * (x - m)^(k)))"
proof cases
  assume "even k"thus ?thesis
    using integrable.intros[OF laplace_moment_even] by (auto elim: evenE)
next
  assume "odd k"thus ?thesis
    using integrable.intros[OF laplace_moment_odd] by (auto elim: oddE)
qed

lemma integrable_laplace_moment_abs:
  fixes k :: nat
  assumes pos[arith]: "0 < l"
  shows "integrable lborel (\<lambda> x. ((laplace_density l m x) * \<bar> x - m \<bar>^(k)))"
proof cases
  assume "even k"thus ?thesis
    using integrable.intros[OF laplace_moment_even] by (auto simp add: power_even_abs elim: evenE)
next
  assume "odd k"thus ?thesis
    using integrable.intros[OF laplace_moment_abs_odd] by (auto elim: oddE)
qed

lemma integrable_laplace_density[simp, intro]:
  assumes pos[arith]: "0 < l"
  shows "integrable lborel (laplace_density l m)"
  using integrable_laplace_moment[of l m 0,OF pos] by auto

lemma integral_laplace_density[simp, intro]:
  assumes pos[arith]: "0 < l"
  shows "(\<integral>x. laplace_density l m x \<partial>lborel) = 1"
  using integral_laplace_moment_even[of l m 0,OF pos] by auto

subsection \<open>The Probability Space Distributed by Laplace Distribution\<close>

lemma prob_space_laplacian_density:
  assumes pos[arith]: "0 < l"
  shows "prob_space (density lborel (laplace_density l m))"
proof
  show "emeasure (density lborel (laplace_density l m)) (space (density lborel (laplace_density l m))) = 1"
    by(auto simp:emeasure_laplace_density_mass_1[OF pos])
qed

lemma (in prob_space) laplace_distributed_le:
  assumes D: "distributed M lborel X (laplace_density l m)"
    and [simp, arith]: "0 < l"
  shows "\<P>(x in M. X x \<le> a) = laplace_CDF l m a"
proof-
  have "emeasure M {x \<in> space M. X x \<le> a} = emeasure (distr M lborel X) {.. a}"
    using distributed_measurable[OF D]
    by (subst emeasure_distr) (auto intro!: arg_cong2[where f=emeasure])
  also have "... = emeasure (density lborel (laplace_density l m)) {.. a}"
    unfolding distributed_distr_eq_density[OF D] by auto
  also have "... = laplace_CDF l m a"
    using emeasure_laplace_density assms by auto
  finally show ?thesis
    by (auto simp: emeasure_eq_measure)
qed

lemma (in prob_space) laplace_distributed_gt:
  assumes D: "distributed M lborel X (laplace_density l m)"
    and [simp, arith]: "0 < l"
  shows "\<P>(x in M. X x > a) = 1 - laplace_CDF l m a"
proof-
  have "1 - laplace_CDF l m a = 1- \<P>(x in M. X x \<le> a)"
    using laplace_distributed_le assms by auto
  also have "... = prob (space M - {x \<in> space M. X x \<le> a})"
    using distributed_measurable[OF D]
    by (auto simp: prob_compl)
  also have "... = \<P>(x in M. X x > a)"
    by (auto intro!: arg_cong[where f=prob] simp: not_le)
  finally show ?thesis
    by auto
qed

end