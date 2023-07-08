theory Life_Table
  imports Survival_Model
begin

section \<open>Life Table\<close>

text \<open>Define a life table axiomatically.\<close>

locale life_table =
  fixes l :: "real \<Rightarrow> real" ("$l'__" [101] 200)
  assumes l_0_pos: "0 < l 0"
    and l_neg_nil: "\<And>x. x \<le> 0 \<Longrightarrow> l x = l 0"
    and l_PInfty_0: "(l \<longlongrightarrow> 0) at_top "
    and l_antimono: "antimono l"
    and l_right_continuous: "\<And>x. continuous (at_right x) l"
begin

subsection \<open>Basic Properties of Life Table\<close>

definition death :: "real \<Rightarrow> real \<Rightarrow> real" ("$d'_{_&_}" [0,0] 200)
  where "$d_{t&x} \<equiv> $l_x - $l_(x+t)"
    \<comment> \<open>the number of deaths between ages x and x+t\<close>
    \<comment> \<open>The parameter t is usually nonnegative, but theoretically it can be negative.\<close>

abbreviation death1 :: "real \<Rightarrow> real" ("$d'__" [101] 200)
  where "$d_x \<equiv> $d_{1&x}"

lemma l_0_neq_0[simp]: "$l_0 \<noteq> 0"
  using l_0_pos by simp

lemma l_nonneg[simp]: "$l_x \<ge> 0" for x::real
  using l_antimono l_PInfty_0 by (rule antimono_at_top_le)

lemma l_bounded[simp]: "$l_x \<le> $l_0" for x::real
  using l_neg_nil l_antimono by (smt (verit) antimonoD)

lemma l_measurable[measurable, simp]: "l \<in> borel_measurable borel"
  by (rule borel_measurable_antimono, rule l_antimono)

lemma l_integrable_Icc: "set_integrable lborel {a..b} l" for a b :: real
  unfolding set_integrable_def
  apply (rule integrableI_bounded_set[where A="{a..b}" and B="$l_0"], simp_all)
  using emeasure_compact_finite by auto

corollary l_integrable_on_Icc: "l integrable_on {a..b}" for a b :: real
  using l_integrable_Icc by (rewrite integrable_on_iff_set_integrable_nonneg[THEN sym]; simp)

lemma d_0_0: "$d_{0&x} = 0" for x::real
  unfolding death_def by simp

lemma d_nonneg[simp]: "$d_{t&x} \<ge> 0" if "t \<ge> 0" for t x :: real
  using l_antimono that unfolding death_def antimono_def by simp

lemma dx_l: "$d_x = $l_x - $l_(x+1)" for x::real
  unfolding death_def by simp

lemma add_d: "$d_{t&x} + $d_{t' & x+t} = $d_{t+t' & x}" for t t' :: real
  unfolding death_def by (smt (verit))

lemma l_normal_antimono: "antimono (\<lambda>x. $l_x / $l_0)"
  using divide_le_cancel l_0_pos l_antimono unfolding antimono_def by fastforce

lemma compl_l_normal_right_continuous: "continuous (at_right x) (\<lambda>x. 1 - $l_x / $l_0)" for x::real
    using l_0_pos l_right_continuous by (intro continuous_intros; simp)

lemma compl_l_normal_NInfty_0: "((\<lambda>x. 1 - $l_x / $l_0) \<longlongrightarrow> 0) at_bot"
    apply (rewrite tendsto_cong[where g="\<lambda>_. 0"], simp_all)
    by (smt (verit) div_self eventually_at_bot_linorder l_0_pos l_neg_nil)

lemma compl_l_normal_PInfty_1: "((\<lambda>x. 1 - $l_x / $l_0) \<longlongrightarrow> 1) at_top"
    using l_0_pos l_PInfty_0 by (intro tendsto_eq_intros) simp_all+

lemma compl_l_real_distribution: "real_distribution (interval_measure (\<lambda>x. 1 - $l_x / $l_0))"
  using l_normal_antimono compl_l_normal_right_continuous
    compl_l_normal_NInfty_0 compl_l_normal_PInfty_1
  by (intro real_distribution_interval_measure; simp add: antimono_def)

subsection \<open>Construction of Survival Model from Life Table\<close>

definition life_table_measure :: "real measure" ("\<MM>")
  where "\<MM> \<equiv> interval_measure (\<lambda>x. 1 - $l_x / $l_0)"

lemma prob_space_actuary_MM: "prob_space_actuary \<MM>"
  unfolding life_table_measure_def using compl_l_real_distribution real_distribution_def
  by (intro prob_space_actuary.intro) force

definition survival_model_X :: "real \<Rightarrow> real" ("X") where "X \<equiv> \<lambda>x. x"

lemma survival_model_MM_X: "survival_model \<MM> X"
proof -
  let ?F = "\<lambda>x. 1 - $l_x / $l_0"
  show "survival_model \<MM> X"
    unfolding life_table_measure_def survival_model_X_def
  proof (rule survival_model.intro)
    show "prob_space_actuary (interval_measure ?F)"
      using prob_space_actuary_MM unfolding life_table_measure_def by simp
    show "survival_model_axioms (interval_measure ?F) (\<lambda>x. x)"
    proof (rule survival_model_axioms.intro, simp_all)
      have [simp]: "{\<xi>::real. \<xi> \<le> 0} = {..0}" by blast
      have "measure (interval_measure (\<lambda>x. 1 - $l_x / $l_0)) {..0} = 0"
        using l_normal_antimono compl_l_normal_right_continuous compl_l_normal_NInfty_0
        by (rewrite measure_interval_measure_Iic, simp_all add: antimono_def)
      hence "emeasure (interval_measure (\<lambda>x. 1 - $l_x / $l_0)) {..0} = ennreal 0"
        apply (rewrite finite_measure.emeasure_eq_measure, simp_all)
        using compl_l_real_distribution prob_space_def real_distribution_def by blast
      thus "almost_everywhere (interval_measure (\<lambda>x. 1 - $l_x / $l_0)) (\<lambda>x. 0 < x)"
        apply (rewrite AE_iff_null, simp)
        by (rewrite not_less) auto
    qed
  qed
qed

end

sublocale life_table \<subseteq> survival_model \<MM> X
  by (rule survival_model_MM_X)

context life_table
begin

interpretation distrX_RD: real_distribution "distr \<MM> borel X"
  using MM_PS.real_distribution_distr by simp

subsubsection \<open>Relations between Life Table and Survival Function for X\<close>

lemma ccdfX_l_normal: "ccdf (distr \<MM> borel X) = (\<lambda>x. $l_x / $l_0)"
proof (rule ext)
  let ?F = "\<lambda>x. 1 - $l_x / $l_0"
  interpret F_FBM: finite_borel_measure "interval_measure ?F"
    using compl_l_real_distribution real_distribution.finite_borel_measure_M by blast
  show "\<And>x. ccdf (distr \<MM> borel X) x = $l_x / $l_0"
    unfolding ccdf_def life_table_measure_def survival_model_X_def
    apply (rewrite measure_distr, simp_all)
    using l_normal_antimono compl_l_normal_right_continuous
      compl_l_normal_NInfty_0 compl_l_normal_PInfty_1
    by (rewrite F_FBM.measure_interval_measure_Ioi; simp add: antimono_def)
qed

corollary deriv_ccdfX_l: "deriv (ccdf (distr \<MM> borel X)) x = deriv l x / $l_0"
  if "l differentiable at x" for x::real
  using differentiable_eq_field_differentiable_real that
  by (rewrite ccdfX_l_normal, rewrite deriv_cdivide_right; simp)

notation death_pt ("$\<psi>")

lemma l_0_equiv: "$l_x = 0 \<longleftrightarrow> x \<ge> $\<psi>" for x::real
  using ccdfX_l_normal ccdfX_0_equiv by simp

lemma d_old_0: "$d_{t&x} = 0" if "x \<ge> $\<psi>" "t \<ge> 0" for x t :: real
  unfolding death_def using l_0_equiv that by (smt (verit) le_ereal_le)

lemma d_l_equiv: "$d_{t&x} = $l_x \<longleftrightarrow> x+t \<ge> $\<psi>" for x t :: real
  unfolding death_def using l_0_equiv by simp

lemma continuous_ccdfX_l: "continuous F (ccdf (distr \<MM> borel X)) \<longleftrightarrow> continuous F l"
  for F :: "real filter"
proof -
  have "continuous F (ccdf (distr \<MM> borel X)) \<longleftrightarrow> continuous F (\<lambda>x. $l_x / $l_0)"
    using ccdfX_l_normal by simp
  also have "\<dots> \<longleftrightarrow> continuous F l" using continuous_cdivide_iff l_0_neq_0 by blast
  finally show ?thesis .
qed

lemma has_real_derivative_ccdfX_l:
  "(ccdf (distr \<MM> borel X) has_real_derivative D) (at x) \<longleftrightarrow>
    (l has_real_derivative $l_0 * D) (at x)"
  for D x :: real
proof -
  have "(ccdf (distr \<MM> borel X) has_real_derivative D) (at x) \<longleftrightarrow>
    ((\<lambda>x. $l_x / $l_0) has_real_derivative D) (at x)"
    by (rule has_field_derivative_cong_eventually; simp add: ccdfX_l_normal)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. $l_0 * ($l_x / $l_0)) has_real_derivative $l_0 * D) (at x)"
    by (rule DERIV_cmult_iff, simp)
  also have "\<dots> \<longleftrightarrow> (l has_real_derivative $l_0 * D) (at x)" by simp
  finally show ?thesis .
qed

corollary differentiable_ccdfX_l:
  "ccdf (distr \<MM> borel X) differentiable (at x) \<longleftrightarrow> l differentiable (at x)"
  for D x :: real
  using has_real_derivative_ccdfX_l
  by (metis l_0_neq_0 mult.commute nonzero_divide_eq_eq real_differentiable_def)

lemma PX_l_normal: "\<P>(\<xi> in \<MM>. X \<xi> > x) = $l_x / $l_0" for x::real
  using MM_PS.ccdf_distr_P ccdfX_l_normal X_RV  by (metis (mono_tags, lifting) Collect_cong)

lemma set_integrable_ccdfX_l:
  "set_integrable lborel A (ccdf (distr \<MM> borel X)) \<longleftrightarrow> set_integrable lborel A l"
  if "A \<in> sets lborel" for A :: "real set"
proof -
  have "set_integrable lborel A (ccdf (distr \<MM> borel X)) \<longleftrightarrow>
    set_integrable lborel A (\<lambda>x. $l_x / $l_0)"
    by (rule set_integrable_cong; simp add: ccdfX_l_normal)
  also have "\<dots> \<longleftrightarrow> set_integrable lborel A l" by simp
  finally show ?thesis .
qed

corollary integrable_ccdfX_l: "integrable lborel (ccdf (distr \<MM> borel X)) \<longleftrightarrow> integrable lborel l"
  using set_integrable_ccdfX_l[where A=UNIV] by (simp add: set_integrable_def)

lemma integrable_on_ccdfX_l:
  "ccdf (distr \<MM> borel X) integrable_on A \<longleftrightarrow> l integrable_on A" for A :: "real set"
proof -
  have "ccdf (distr \<MM> borel X) integrable_on A \<longleftrightarrow> (\<lambda>x. $l_x / $l_0) integrable_on A"
    by (rule integrable_cong) (simp add: ccdfX_l_normal)
  also have "\<dots> \<longleftrightarrow> l integrable_on A"
    using integrable_on_cdivide_iff[of "$l_0" l] by simp
  finally show ?thesis .
qed

subsubsection \<open>Relations between Life Table and Cumulative Distributive Function for X\<close>

lemma cdfX_l_normal: "cdf (distr \<MM> borel X) = (\<lambda>x. 1 - $l_x / $l_0)" for x::real
  using ccdfX_l_normal distrX_RD.cdf_ccdf distrX_RD.prob_space by presburger

lemma deriv_cdfX_l: "deriv (cdf (distr \<MM> borel X)) x = - deriv l x / $l_0"
  if "l differentiable at x" for x::real
  using distrX_RD.cdf_ccdf differentiable_eq_field_differentiable_real that differentiable_ccdfX_l
    deriv_diff deriv_ccdfX_l that by simp

lemma continuous_cdfX_l: "continuous F (cdf (distr \<MM> borel X)) \<longleftrightarrow> continuous F l"
  for F :: "real filter"
  using distrX_RD.continuous_cdf_ccdf continuous_ccdfX_l by simp

lemma has_real_derivative_cdfX_l:
  "(cdf (distr \<MM> borel X) has_real_derivative D) (at x) \<longleftrightarrow>
    (l has_real_derivative - ($l_0 * D)) (at x)"
  for D x :: real
  using distrX_RD.has_real_derivative_cdf_ccdf has_real_derivative_ccdfX_l by simp

lemma differentiable_cdfX_l:
  "cdf (distr \<MM> borel X) differentiable (at x) \<longleftrightarrow> l differentiable (at x)" for D x :: real
  using differentiable_eq_field_differentiable_real distrX_RD.differentiable_cdf_ccdf
    differentiable_ccdfX_l by simp

lemma PX_compl_l_normal: "\<P>(\<xi> in \<MM>. X \<xi> \<le> x) = 1 - $l_x / $l_0" for x::real
  using PX_l_normal by (metis MM_PS.prob_compl X_compl_gt_le X_gt_event)

subsubsection \<open>Relations between Life Table and Survival Function for T(x)\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

notation futr_life ("T")

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct, simp_all add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma lx_neq_0[simp]: "$l_x \<noteq> 0"
  using l_0_equiv x_lt_psi linorder_not_less by blast

corollary lx_pos[simp]: "$l_x > 0"
  using lx_neq_0 l_nonneg by (smt (verit))

lemma ccdfTx_l_normal: "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = $l_(x+t) / $l_x"
  if "t \<ge> 0" for t::real
  using ccdfTx_PX PX_l_normal l_0_neq_0 that by simp

lemma deriv_ccdfTx_l:
  "deriv (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t = deriv (\<lambda>t. $l_(x+t) / $l_x) t"
  if "t > 0" "l differentiable at (x+t)" for t::real
proof -
  have "\<forall>\<^sub>F s in nhds t. ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) s = $l_(x+s) / $l_x"
    apply (rewrite eventually_nhds_metric)
    using that ccdfTx_l_normal dist_real_def by (intro exI[of _ t]) auto
  thus ?thesis by (rule deriv_cong_ev) simp
qed

lemma continuous_at_within_ccdfTx_l:
  "continuous (at t within {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) \<longleftrightarrow>
    continuous (at (x+t) within {x..}) l"
  if "t \<ge> 0" for t::real
  using continuous_ccdfX_ccdfTx that continuous_ccdfX_l by force

lemma isCont_ccdfTx_l:
  "isCont (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t \<longleftrightarrow> isCont l (x+t)" if "t > 0" for t::real
  using that continuous_ccdfX_l isCont_ccdfX_ccdfTx by force

lemma has_real_derivative_ccdfTx_l:
  "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative D) (at t) \<longleftrightarrow>
    (l has_real_derivative $l_x * D) (at (x+t))"
  if "t > 0" for t D :: real
proof -
  have "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative D) (at t) \<longleftrightarrow>
    (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative
    ($l_x / $l_0 * D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
    using PX_l_normal by force
  also have "\<dots> = (ccdf (distr \<MM> borel X) has_real_derivative ($l_x / $l_0 * D)) (at (x+t))"
    using has_real_derivative_ccdfX_ccdfTx that by simp
  also have "\<dots> = (l has_real_derivative ($l_x * D)) (at (x+t))"
    using has_real_derivative_ccdfX_l by simp
  finally show ?thesis .
qed

lemma differentiable_ccdfTx_l:
  "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t \<longleftrightarrow> l differentiable (at (x+t))"
  if "t > 0" for t::real
  using differentiable_ccdfX_ccdfTx differentiable_ccdfX_l that by force

lemma PTx_l_normal: "\<P>(\<xi> in \<MM>. T x \<xi> > t \<bar> T x \<xi> > 0) = $l_(x+t) / $l_x" if "t \<ge> 0" for t::real
  using ccdfTx_l_normal that by (simp add: ccdfTx_cond_prob)

subsubsection \<open>Relations between Life Table and Cumulative Distributive Function for T(x)\<close>

lemma cdfTx_compl_l_normal: "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 1 - $l_(x+t) / $l_x"
  if "t \<ge> 0" for t::real
  using distrTx_RD.cdf_ccdf ccdfTx_l_normal that distrTx_RD.prob_space by auto

lemma deriv_cdfTx_l:
  "deriv (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t = - deriv (\<lambda>t. $l_(x+t) / $l_x) t"
  if "t > 0" "l differentiable at (x+t)" for t::real
  using deriv_ccdfTx_l differentiable_cdfX_cdfTx differentiable_cdfX_l distrTx_RD.deriv_cdf_ccdf
    that by fastforce

lemma continuous_at_within_cdfTx_l:
  "continuous (at t within {0..}) (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) \<longleftrightarrow>
    continuous (at (x+t) within {x..}) l"
  if "t \<ge> 0" for t::real
  using that continuous_cdfX_l continuous_cdfX_cdfTx by force

lemma isCont_cdfTx_l:
  "isCont (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t \<longleftrightarrow> isCont l (x+t)" if "t > 0" for t::real
  using that continuous_cdfX_l isCont_cdfX_cdfTx by force

lemma has_real_derivative_cdfTx_l:
  "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative D) (at t) \<longleftrightarrow>
    (l has_real_derivative - $l_x * D) (at (x+t))"
  if "t > 0" for t D :: real
  using has_real_derivative_ccdfTx_l that distrTx_RD.has_real_derivative_cdf_ccdf by auto

lemma differentiable_cdfTx_l:
  "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t \<longleftrightarrow> l differentiable (at (x+t))"
  if "t > 0" for t::real
  using differentiable_cdfX_l that differentiable_cdfX_cdfTx by auto

lemma PTx_compl_l_normal: "\<P>(\<xi> in \<MM>. T x \<xi> \<le> t \<bar> T x \<xi> > 0) = 1- $l_(x+t) / $l_x"
  if "t \<ge> 0" for t::real
  using cdfTx_compl_l_normal that by (simp add: cdfTx_cond_prob)

subsubsection \<open>Life Table and Actuarial Notations\<close>

notation survive ("$p'_{_&_}" [0,0] 200)
notation survive_1 ("$p'__" [101] 200)
notation die ("$q'_{_&_}" [0,0] 200)
notation die_1 ("$q'__" [101] 200)
notation die_defer ("$q'_{_\<bar>_&_}" [0,0,0] 200)
notation die_defer_1 ("$q'_{_\<bar>&_}" [0,0] 200)
notation life_expect ("$e`\<circ>'__" [101] 200)
notation temp_life_expect ("$e`\<circ>'_{_:_}" [0,0] 200)
notation curt_life_expect ("$e'__" [101] 200)
notation temp_curt_life_expect ("$e'_{_:_}" [0,0] 200)

lemma p_l: "$p_{t&x} = $l_(x+t) / $l_x" if "t \<ge> 0" for t::real
  unfolding survive_def using ccdfTx_l_normal that by simp

corollary p_1_l: "$p_x = $l_(x+1) / $l_x"
  using p_l by simp

lemma isCont_p_l: "isCont (\<lambda>s. $p_{s&x}) t \<longleftrightarrow> isCont l (x+t)" if "t > 0" for t::real
proof -
  have "\<forall>\<^sub>F s in nhds t. $p_{s&x} = $l_(x+s) / $l_x"
    apply (rewrite eventually_nhds_metric)
    apply (rule exI[of _ t], auto simp add: that)
    by (rewrite p_l; simp add: dist_real_def)
  hence "isCont (\<lambda>s. $p_{s&x}) t \<longleftrightarrow> isCont (\<lambda>s. $l_(x+s) / $l_x) t" by (rule isCont_cong)
  also have "\<dots> \<longleftrightarrow> isCont (\<lambda>s. $l_(x+s)) t" using continuous_cdivide_iff lx_neq_0 by metis
  also have "\<dots> \<longleftrightarrow> isCont l (x+t)" using isCont_shift by (force simp add: add.commute)
  finally show ?thesis .
qed

lemma p_PTx_ge_l_isCont: "$p_{t&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> t \<bar> T x \<xi> > 0)"
  if "isCont l (x+t)" "t > 0" for t::real
  using p_PTx_ge_ccdf_isCont that continuous_ccdfX_l by force

lemma q_defer_l: "$q_{f\<bar>t&x} = ($l_(x+f) - $l_(x+f+t)) / $l_x" if "f \<ge> 0" "t \<ge> 0" for f t :: real
  apply (rewrite q_defer_p, simp_all add: that)
  using that by (rewrite p_l, simp)+ (smt (verit) diff_divide_distrib)

corollary q_defer_d_l: "$q_{f\<bar>t&x} = $d_{t & x+f} / $l_x" if "f \<ge> 0" "t \<ge> 0" for f t :: real
  using q_defer_l that death_def by simp

corollary q_defer_1_d_l: "$q_{f\<bar>&x} = $d_(x+f) / $l_x" if "f \<ge> 0" for f::real
  using q_defer_d_l that by simp

corollary q_d_l: "$q_{t&x} = $d_{t&x} / $l_x" if "t \<ge> 0" for t::real
  using q_defer_d_l[of 0] that by simp

corollary q_1_d_l: "$q_x = $d_x / $l_x"
  using q_d_l by simp

lemma LBINT_p_l: "LBINT t:A. $p_{t&x} = (LBINT t:A. $l_(x+t)) / $l_x"
  if "A \<subseteq> {0..}" "A \<in> sets lborel" for A :: "real set"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
proof -
  have [simp]: "\<And>t. t \<in> A \<Longrightarrow> $p_{t&x} = $l_(x+t) / $l_x" using p_l that by blast
  hence "LBINT t:A. $p_{t&x} = LBINT t:A. $l_(x+t) / $l_x"
    using that by (rewrite set_lebesgue_integral_cong[where g="\<lambda>t. $l_(x+t) / $l_x"]; simp)
  also have "\<dots> = (LBINT t:A. $l_(x+t)) / $l_x" by (rewrite set_integral_divide_zero) simp
  finally show ?thesis .
qed

corollary e_LBINT_l: "$e`\<circ>_x = (LBINT t:{0..}. $l_(x+t)) / $l_x"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
  by (simp add: e_LBINT_p LBINT_p_l)

corollary e_LBINT_l_Icc: "$e`\<circ>_x = (LBINT t:{0..n}. $l_(x+t)) / $l_x" if "x+n \<ge> $\<psi>" for n::real
  using e_LBINT_p_Icc by (rewrite LBINT_p_l[THEN sym]; simp add: that)

lemma temp_e_LBINT_l: "$e`\<circ>_{x:n} = (LBINT t:{0..n}. $l_(x+t)) / $l_x" if "n \<ge> 0" for n::real
  using temp_e_LBINT_p by (rewrite LBINT_p_l[THEN sym]; simp add: that)

lemma integral_p_l: "integral A (\<lambda>t. $p_{t&x}) = (integral A (\<lambda>t. $l_(x+t))) / $l_x"
  if "A \<subseteq> {0..}" "A \<in> sets lborel" for A :: "real set"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
  using that apply (rewrite set_borel_integral_eq_integral_nonneg[THEN sym], simp_all)
  apply (simp add: survive_def)
  apply (rewrite set_borel_integral_eq_integral_nonneg[THEN sym], simp_all)
  by (rule LBINT_p_l; simp)

corollary e_integral_l: "$e`\<circ>_x = integral {0..} (\<lambda>t. $l_(x+t)) / $l_x"
  if "(\<lambda>t. $l_(x+t)) integrable_on {0..}"
  by (simp add: e_integral_p integral_p_l)

corollary e_integral_l_Icc:
  "$e`\<circ>_x = integral {0..n} (\<lambda>t. $l_(x+t)) / $l_x" if "x+n \<ge> $\<psi>" for n::real
  using e_integral_p_Icc by (rewrite integral_p_l[THEN sym]; simp add: that)

lemma temp_e_integral_l:
  "$e`\<circ>_{x:n} = integral {0..n} (\<lambda>t. $l_(x+t)) / $l_x" if "n \<ge> 0" for n::real
  using temp_e_integral_p by (rewrite integral_p_l[THEN sym]; simp add: that)

lemma curt_e_sum_l: "$e_x = (\<Sum>k. $l_(x+k+1)) / $l_x"
  if "summable (\<lambda>k. $l_(x+k+1))" "\<And>k::nat. isCont l (x+k+1)"
proof -
  have "summable (\<lambda>k. $p_{k+1&x})"
    apply (rewrite p_l, simp)
    apply (rule summable_divide)
    by (rewrite add.assoc[THEN sym], simp add: that)
  moreover have "\<And>k::nat. isCont (\<lambda>t. $p_{t&x}) (k+1)"
    using isCont_p_l that by (simp add: add.assoc)
  ultimately show ?thesis
    apply (rewrite curt_e_sum_p, simp_all)
    using p_l by (smt (verit) of_nat_0_le_iff suminf_cong suminf_divide that(1))
qed

lemma curt_e_sum_l_finite: "$e_x = (\<Sum>k<n. $l_(x+k+1)) / $l_x"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont l (x+k+1)" "x+n+1 > $\<psi>" for n::nat
  apply (rewrite curt_e_sum_p_finite[of x n], simp_all add: that)
  using isCont_p_l that apply (simp add: add.assoc)
  apply (rewrite sum_divide_distrib, rule sum.cong, simp)
  using p_l by (smt (verit) of_nat_0_le_iff)

lemma temp_curt_e_sum_p: "$e_{x:n} = (\<Sum>k<n. $l_(x+k+1)) / $l_x"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont l (x+k+1)" for n::nat
  apply (rewrite temp_curt_e_sum_p[of x n], simp_all add: that)
  using isCont_p_l that apply (simp add: add.assoc)
  apply (rewrite sum_divide_distrib, rule sum.cong, simp)
  using p_l by (smt (verit) of_nat_0_le_iff)

end

lemma l_p: "$l_x / $l_0 = $p_{x&0}" for x::real
  using ccdfX_l_normal ccdfX_p by force

end

subsection \<open>Piecewise Differentiable Life Table\<close>

locale smooth_life_table = life_table +
  assumes l_piecewise_differentiable[simp]: "l piecewise_differentiable_on UNIV"
begin

lemma smooth_survival_function_MM_X: "smooth_survival_function \<MM> X"
proof (rule smooth_survival_function.intro)
  show "survival_model \<MM> X" by (rule survival_model_axioms)
  show "smooth_survival_function_axioms \<MM> X"
  proof
    show "ccdf (distr \<MM> borel X) piecewise_differentiable_on UNIV"
      apply (rewrite ccdfX_l_normal)
      apply (rewrite divide_inverse, rewrite mult.commute)
      using l_piecewise_differentiable piecewise_differentiable_scaleR[of l] by simp
  qed
qed

end

sublocale smooth_life_table \<subseteq> smooth_survival_function \<MM> X
  by (rule smooth_survival_function_MM_X)

context smooth_life_table
begin

notation force_mortal ("$\<mu>'__" [101] 200)

lemma l_continuous[simp]: "continuous_on UNIV l"
  using l_piecewise_differentiable piecewise_differentiable_on_imp_continuous_on by fastforce

lemma l_nondifferentiable_finite_set[simp]: "finite {x. \<not> l differentiable at x}"
  using differentiable_ccdfX_l ccdfX_nondifferentiable_finite_set by simp

lemma l_differentiable_borel_set[measurable, simp]: "{x. l differentiable at x} \<in> sets borel"
  using differentiable_ccdfX_l ccdfX_differentiable_borel_set by simp

lemma l_differentiable_AE: "AE x in lborel. l differentiable at x"
  using differentiable_ccdfX_l ccdfX_differentiable_AE by simp

lemma deriv_l_measurable[measurable]: "deriv l \<in> borel_measurable borel"
proof -
  let ?S = "{x. \<not> l differentiable at x}"
  have "\<And>x. x \<notin> ?S \<Longrightarrow> $l_0 * deriv (ccdf (distr \<MM> borel X)) x = deriv l x"
    using deriv_ccdfX_l by simp
  thus ?thesis
    apply -
    by (rule measurable_discrete_difference
        [where X="?S" and f="\<lambda>x. $l_0 * deriv (ccdf (distr \<MM> borel X)) x"])
      (simp_all add: countable_finite)
qed

lemma pdfX_l_normal:
  "pdfX x = (if l differentiable at x then - deriv l x / $l_0 else 0)" for x::real
  unfolding pdfX_def
  using differentiable_eq_field_differentiable_real differentiable_cdfX_l deriv_cdfX_l by simp

lemma mu_deriv_l: "$\<mu>_x = - deriv l x / $l_x" if "l differentiable at x" for x::real
  using mu_pdfX that ccdfX_l_normal that pdfX_l_normal by (simp add: differentiable_cdfX_l)

lemma mu_nonneg_differentiable_l: "$\<mu>_x \<ge> 0" if "l differentiable at x" for x::real
  using differentiable_cdfX_l mu_nonneg_differentiable that by simp

lemma mu_deriv_ln_l:
  "$\<mu>_x = - deriv (\<lambda>x. ln ($l_x)) x" if "l differentiable at x" "x < $\<psi>" for x::real
proof -
  have "\<forall>\<^sub>F x in nhds x. ln ($l_x / $l_0) = ln ($l_x) - ln ($l_0)"
  proof (cases \<open>$\<psi> < \<infinity>\<close>)
    case True
    thus ?thesis
      apply (rewrite eventually_nhds_metric)
      apply (intro exI[of _ "real_of_ereal $\<psi> - x"], auto)
      using that True not_inftyI apply fastforce
      apply (rewrite ln_div, simp_all)
      using lx_pos dist_real_def not_inftyI that(2) by fastforce
  next
    case False
    hence "\<And>x. $l_x > 0" using l_0_equiv by force
    thus ?thesis by (intro always_eventually, rewrite ln_div; simp)
  qed
  hence "deriv (\<lambda>x. ln ($l_x / $l_0)) x = deriv (\<lambda>x. ln ($l_x)) x"
    apply (rewrite deriv_cong_ev[of _ "\<lambda>x. ln ($l_x) - ln ($l_0)"], simp_all)
    apply (rewrite deriv_diff, simp_all)
    unfolding field_differentiable_def using has_derivative_ln that
    by (metis DERIV_deriv_iff_real_differentiable differentiable_def lx_pos)
  thus ?thesis using ccdfX_l_normal mu_deriv_ln that differentiable_ccdfX_l by force
qed

lemma deriv_l_shift: "deriv l (x+t) = deriv (\<lambda>t. $l_(x+t)) t"
  if "l differentiable at (x+t)" for x t :: real
  using deriv_shift differentiable_eq_field_differentiable_real that by simp

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

lemma p_mu_l: "$p_{t&x} * $\<mu>_(x+t) = - deriv l (x+t) / $l_x"
  if "l differentiable at (x+t)" "t > 0" "x+t < $\<psi>" for t::real
  using p_l mu_deriv_l that by simp

lemma p_mu_l_AE: "AE s in lborel. 0 < s \<and> x+s < $\<psi> \<longrightarrow> $p_{s&x} * $\<mu>_(x+s) = - deriv l (x+s) / $l_x"
proof  -
  have "AE s in lborel. l differentiable at (x+s)"
    apply (rule AE_borel_affine[of 1 "\<lambda>u. l differentiable at u" x, simplified])
    unfolding pred_def using l_differentiable_AE by simp_all
  moreover have "AE s in lborel.
    l differentiable at (x+s) \<longrightarrow> 0 < s \<and> x+s < $\<psi> \<longrightarrow> $p_{s&x} * $\<mu>_(x+s) = - deriv l (x+s) / $l_x"
    using p_mu_l by (intro AE_I2) simp
  ultimately show ?thesis by (rule AE_mp)
qed

lemma LBINT_l_mu_q: "(LBINT s:{f<..f+t}. $l_(x+s) * $\<mu>_(x+s)) / $l_x = $q_{f\<bar>t&x}"
  if "t \<ge> 0" "f \<ge> 0"
proof -
  have "\<And>s. s\<in>{f<..f+t} \<Longrightarrow> $p_{s&x} = $l_(x+s) / $l_x" using p_l that by simp
  hence "$q_{f\<bar>t&x} = LBINT s:{f<..f+t}. $l_(x+s) / $l_x * $\<mu>_(x+s)"
    using LBINT_p_mu_q 
    by (smt (verit) greaterThanAtMost_borel set_lebesgue_integral_cong sets_lborel that x_lt_psi)
  also have "\<dots> = (LBINT s:{f<..f+t}. $l_(x+s) * $\<mu>_(x+s)) / $l_x"
    using set_integral_divide_zero by simp
  finally show ?thesis by simp
qed

lemma set_integrable_l_mu: "set_integrable lborel {f<..f+t} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s))"
  if "t \<ge> 0" "f \<ge> 0"
proof -
  have "set_integrable lborel {f<..f+t} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x)"
    using p_l set_integrable_p_mu that
    by (rewrite set_integrable_cong[where f'="\<lambda>s. $p_{s&x} * $\<mu>_(x+s)"]) simp_all+
  thus ?thesis by simp
qed

lemma l_mu_has_integral_q_defer:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x) has_integral $q_{f\<bar>t&x}) {f..f+t}" if "t \<ge> 0" "f \<ge> 0"
  using p_l that p_mu_has_integral_q_defer_Icc
  by (rewrite has_integral_cong[of _ _ "\<lambda>s. $p_{s&x} * $\<mu>_(x+s)"]; simp)

corollary l_mu_has_integral_q:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x) has_integral $q_{t&x}) {0..t}" if "t \<ge> 0"
  using l_mu_has_integral_q_defer[where f=0] that by simp

lemma l_mu_has_integral_d:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s)) has_integral $d_{t & x+f}) {f..f+t}" if "t \<ge> 0" "f \<ge> 0"
proof -
  have "((\<lambda>s. $l_x * ($p_{s&x} * $\<mu>_(x+s))) has_integral $l_x * $q_{f\<bar>t&x}) {f..f+t}"
    apply (rule has_integral_mult_right)
    by (rule p_mu_has_integral_q_defer_Icc; simp add: that)
  thus ?thesis
    using that apply (rewrite in asm q_defer_d_l, simp_all)
    apply (rewrite has_integral_cong[where g="\<lambda>s. $l_x * ($p_{s&x} * $\<mu>_(x + s))"])
    by (rewrite p_l; simp)
qed

corollary l_mu_has_integral_d_1:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s)) has_integral $d_(x+f)) {f..f+1}" if "t \<ge> 0" "f \<ge> 0"
  using l_mu_has_integral_d[where t=1] that by simp

lemma e_LBINT_l: "$e`\<circ>_x = (LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
proof -
  have "\<And>s. s\<in>{0..} \<Longrightarrow> $p_{s&x} = $l_(x+s) / $l_x" using p_l by simp
  hence "$e`\<circ>_x = LBINT s:{0..}. $l_(x+s) / $l_x * $\<mu>_(x+s) * s"
    using e_LBINT_p_mu
    by (smt (verit) atLeast_borel set_lebesgue_integral_cong sets_lborel x_lt_psi)
  also have "\<dots> = (LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
    using set_integral_divide_zero by simp
  finally show ?thesis .
qed

lemma e_integral_l: "$e`\<circ>_x = integral {0..} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
proof -
  have "AE s in lborel. $\<mu>_(x+s) \<ge> 0" by (rule AE_translation, rule mu_nonneg_AE)
  hence "LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s = integral {0..} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) * s)"
    by (intro set_borel_integral_eq_integral_nonneg_AE; force)
  thus ?thesis using e_LBINT_l by simp
qed

end

lemma deriv_x_p_mu_l: "deriv (\<lambda>y. $p_{t&y}) x = $p_{t&x} * ($\<mu>_x - $\<mu>_(x+t))"
  if "l differentiable at x" "l differentiable at (x+t)" "t \<ge> 0" "x < $\<psi>" for x t :: real
  using deriv_x_p_mu that differentiable_ccdfX_l by blast

lemma e_has_derivative_mu_e_l: "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if "\<And>x. x\<in>{a<..<b} \<Longrightarrow> set_integrable lborel {x..} l" "l differentiable at x"
    "x\<in>{a<..<b}" "b \<le> $\<psi>"
  for a b x :: real
  using e_has_derivative_mu_e that differentiable_ccdfX_l set_integrable_ccdfX_l by force

corollary e_has_derivative_mu_e_l': "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if "\<And>x. x\<in>{a<..<b} \<Longrightarrow> l integrable_on {x..}" "l differentiable at x" "x\<in>{a<..<b}" "b \<le> $\<psi>"
  for a b x :: real
  using that apply (intro e_has_derivative_mu_e_l[where a=a], simp_all)
  using l_nonneg by (rewrite integrable_on_iff_set_integrable_nonneg; simp)

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

lemma curt_e_sum_l_smooth: "$e_x = (\<Sum>k. $l_(x+k+1)) / $l_x" if "summable (\<lambda>k. $l_(x+k+1))"
proof -
  have "summable (\<lambda>k. $p_{k+1&x})" using that by (rewrite p_l; simp add: add.assoc)
  hence "$e_x = (\<Sum>k. $p_{k+1&x})" using curt_e_sum_p_smooth by simp
  also have "\<dots> = (\<Sum>k. $l_(x+k+1) / $l_x)" by (rewrite p_l; simp add: add.assoc)
  also have "\<dots> = (\<Sum>k. $l_(x+k+1)) / $l_x" by (simp add: suminf_divide that)
  finally show ?thesis .
qed

lemma curt_e_sum_l_finite_smooth: "$e_x = (\<Sum>k<n. $l_(x+k+1)) / $l_x" if "x+n+1 > $\<psi>" for n::nat
  apply (rewrite curt_e_sum_p_finite_smooth[of x n], simp_all add: that)
  apply (rewrite p_l, simp_all)
  by (smt (verit) sum.cong sum_divide_distrib)

lemma temp_curt_e_sum_l_smooth: "$e_{x:n} = (\<Sum>k<n. $l_(x+k+1)) / $l_x" for n::nat
  apply (rewrite temp_curt_e_sum_p_smooth[of x n], simp)
  apply (rewrite p_l, simp_all)
  by (smt (verit) sum.cong sum_divide_distrib)

end

end

subsection \<open>Finite Life Table\<close>

locale finite_life_table = life_table +
  assumes l_finite: "\<exists>x::real. $l_x = 0"
begin

lemma finite_survival_function_MM_X: "finite_survival_function \<MM> X"
proof (rule finite_survival_function.intro)
  show "survival_model \<MM> X" by (rule survival_model_MM_X)
  show "finite_survival_function_axioms \<MM> X"
    unfolding finite_survival_function_axioms_def using l_finite death_pt_def by fastforce
qed

end

sublocale finite_life_table \<subseteq> finite_survival_function \<MM> X
  by (rule finite_survival_function_MM_X)

context finite_life_table
begin

notation ult_age ("$\<omega>")

lemma l_omega_0: "$l_$\<omega> = 0"
  using ccdfX_l_normal ccdfX_omega_0 by simp

lemma l_0_equiv_nat: "$l_x = 0 \<longleftrightarrow> x \<ge> $\<omega>" for x::nat
  using ccdfX_l_normal ccdfX_0_equiv_nat by simp

lemma d_l_equiv_nat: "$d_{t&x} = $l_x \<longleftrightarrow> x+t \<ge> $\<omega>" for x t :: nat
  by (metis d_l_equiv of_nat_add psi_le_iff_omega_le)

corollary d_1_omega_l: "$d_($\<omega>-1) = $l_($\<omega>-1)"
  using d_l_equiv_nat[of 1 "$\<omega>-1"] omega_pos by simp

context 
  fixes x::nat
  assumes x_lt_omega[simp]: "x < $\<omega>"
begin

lemma curt_e_sum_l_finite_nat: "$e_x = (\<Sum>k<n. $l_(x+k+1)) / $l_x"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont l (x+k+1)" "x+n \<ge> $\<omega>" for n::nat
  apply (rewrite curt_e_sum_l_finite[of x n], simp)
  using that le_ereal_less psi_le_omega apply (metis of_nat_1 of_nat_add, force)
  by (simp add: add.commute)

end

end

end
