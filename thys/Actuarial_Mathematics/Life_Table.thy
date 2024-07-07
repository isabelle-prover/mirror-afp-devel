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

lemma l_0_neq_0[simp]: "$l_0 \<noteq> 0"
  using l_0_pos by simp

lemma l_nonneg[simp]: "$l_x \<ge> 0" for x::real
  using l_antimono l_PInfty_0 by (rule antimono_at_top_le)

lemma l_bounded[simp]: "$l_x \<le> $l_0" for x::real
  using l_neg_nil l_antimono by (smt (verit) antimonoD)

lemma l_measurable[measurable, simp]: "l \<in> borel_measurable borel"
  by (rule borel_measurable_antimono, rule l_antimono)

lemma l_left_continuous_nonpos: "continuous (at_left x) l" if "x \<le> 0" for x::real
proof -
  have "$l_x = $l_0" using l_neg_nil that by blast
  moreover have "continuous (at_left x) (\<lambda>_. $l_0)" by simp
  moreover have "eventually (\<lambda>y. $l_y = $l_0) (at_left x)"
    apply (rule eventually_at_leftI[of "x-1"], simp_all)
    using that l_neg_nil by (smt (verit))
  ultimately show ?thesis by (rewrite continuous_at_within_cong[where g="\<lambda>_. $l_0"]; simp)
qed

lemma l_integrable_Icc: "set_integrable lborel {a..b} l" for a b :: real
  unfolding set_integrable_def
  apply (rule integrableI_bounded_set[where A="{a..b}" and B="$l_0"], simp_all)
  using emeasure_compact_finite by auto

corollary l_integrable_on_Icc: "l integrable_on {a..b}" for a b :: real
  using l_integrable_Icc by (rewrite integrable_on_iff_set_integrable_nonneg[THEN sym]; simp)

lemma l_integrable_Icc_shift: "set_integrable lborel {a..b} (\<lambda>t. $l_(x+t))" for a b x :: real
  using set_integrable_Icc_shift l_integrable_Icc by (metis (full_types) add_diff_cancel_right')

corollary l_integrable_on_Icc_shift: "(\<lambda>t. $l_(x+t)) integrable_on {a..b}" for x a b :: real
  using l_integrable_Icc_shift by (rewrite integrable_on_iff_set_integrable_nonneg[THEN sym]; simp)

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

definition total :: "real \<Rightarrow> real" ("$T'__" [101] 200) where "$T_x \<equiv> LBINT y:{x..}. $l_y"
  \<comment> \<open>the number of lives older than the ones aged \<open>x\<close>\<close>
  \<comment> \<open>The parameter \<open>x\<close> must be nonnegative.\<close>

lemma T_nonneg[simp]: "$T_x \<ge> 0" for x::real
  unfolding total_def by simp

definition "total_finite \<equiv> set_integrable lborel {0..} l"

lemma total_finite_iff_set_integrable_Ici:
  "total_finite \<longleftrightarrow> set_integrable lborel {x..} l" for x::real
  unfolding total_finite_def using set_integrable_Ici_equiv l_integrable_Icc by blast

lemma total_finite_iff_integrable_on_Ici: "total_finite \<longleftrightarrow> l integrable_on {x..}" for x::real
  using total_finite_iff_set_integrable_Ici integrable_on_iff_set_integrable_nonneg l_nonneg
  by (metis atLeast_borel l_measurable measurable_lborel2 sets_lborel)

lemma total_finite_iff_summable: "total_finite \<longleftrightarrow> summable (\<lambda>k. $l_(x+k))" for x::real
  apply (rewrite total_finite_iff_set_integrable_Ici)
  apply (rule set_integrable_iff_summable[of x, simplified], simp_all)
  using l_antimono unfolding antimono_def monotone_on_def by simp

lemma T_tendsto_0: "((\<lambda>x. $T_x) \<longlongrightarrow> 0) at_top" if total_finite
proof -
  have "\<And>x. x \<ge> 0 \<Longrightarrow> $T_x = $T_0 - (LBINT y:{0..x}. $l_y)"
  proof -
    fix x::real assume asm: "x \<ge> 0"
    let ?A = "{x..}" and ?B = "{0..x}"
    have "{0..} = ?A \<union> ?B" using asm by auto
    thus "$T_x = $T_0 - (LBINT y:{0..x}. $l_y)"
      unfolding total_def apply (rewrite eq_diff_eq)
      using that total_finite_iff_set_integrable_Ici l_integrable_Icc
      apply (rewrite set_integral_Un_AE[THEN sym], simp_all)
      using AE_lborel_singleton add_0 asm le_add_same_cancel2 le_numeral_extra(3) by force
  qed
  hence "\<forall>\<^sub>F x in at_top. $T_x = $T_0 - (LBINT y:{0..x}. $l_y)"
    by (rule eventually_at_top_linorderI[of 0])
  moreover have "((\<lambda>x. LBINT y:{0..x}. $l_y) \<longlongrightarrow> $T_0) at_top"
    using that unfolding total_def total_finite_def
    by (intro tendsto_set_lebesgue_integral_at_top; simp)
  ultimately show ?thesis
    apply (rewrite tendsto_cong, simp_all)
    using LIM_zero_iff' by force
qed

definition lives :: "real \<Rightarrow> real \<Rightarrow> real" ("$L'_{_&_}" [0,0] 200)
  where "$L_{n&x} \<equiv> LBINT y:{x..x+n}. $l_y"
    \<comment> \<open>the number of lives between ages \<open>x\<close> and \<open>x+n\<close>\<close>
    \<comment> \<open>The parameter \<open>x\<close> must be nonnegative.\<close>
    \<comment> \<open>The parameter \<open>n\<close> is usually nonnegative, but theoretically it can be negative.\<close>

abbreviation lives_1 :: "real \<Rightarrow> real" ("$L'__" [101] 200)
  where "$L_x \<equiv> $L_{1&x}"

lemma l_has_integral_L: "(l has_integral $L_{n&x}) {x..x+n}" for x n :: real
  unfolding lives_def by (rule has_integral_set_integral_real) (rule l_integrable_Icc)

lemma L_neg_0[simp]: "$L_{n&x} = 0" if "n < 0" for x n :: real
  unfolding lives_def using that by (rewrite to "{}" atLeastatMost_empty; simp)

lemma L_nonneg[simp]: "$L_{n&x} \<ge> 0" for x n :: real
  unfolding lives_def by simp

lemma L_T: "$L_{n&x} = $T_x - $T_(x+n)" if "total_finite" "n \<ge> 0" for x n :: real
proof -
  have "{x..x+n}\<union>{x+n..} = {x..}" using that by force
  moreover have
    "(LBINT y:{x..x+n}\<union>{x+n..}. $l_y) = (LBINT y:{x..x+n}. $l_y) + (LBINT y:{x+n..}. $l_y)"
  proof -
    have "AE y in lborel. \<not> (y \<in> {x..x+n} \<and> y \<in> {x+n..})" by (rule AE_I'[where N="{x+n}"]; force)
    moreover have "set_integrable lborel {x..x+n} l" by (rule l_integrable_Icc)
    moreover have "set_integrable lborel {x+n..} l"
      using that total_finite_iff_set_integrable_Ici by simp
    ultimately show ?thesis by (intro set_integral_Un_AE; simp)
  qed
  ultimately show ?thesis unfolding total_def lives_def by simp
qed

lemma L_sums_T: "(\<lambda>k. $L_(x+k)) sums $T_x" if total_finite for x::real
proof -
  have "(\<lambda>k::nat. $T_(x+k)) \<longlonglongrightarrow> 0"
    using T_tendsto_0
    apply (rule filterlim_compose[where f="\<lambda>k::nat. x+k" and g=total], simp add: that)
    using filterlim_real_sequentially filterlim_tendsto_add_at_top by blast
  hence "(\<lambda>k. $T_(x+k) - $T_(x + Suc k)) sums $T_x"
    by (simp) (rule telescope_sums'[of "\<lambda>k. $T_(x+k)" 0, simplified])
  thus ?thesis using that L_T by (rewrite sums_cong, simp_all) smt
qed

definition death :: "real \<Rightarrow> real \<Rightarrow> real" ("$d'_{_&_}" [0,0] 200)
  where "$d_{t&x} \<equiv> max 0 ($l_x - $l_(x+t))"
    \<comment> \<open>the number of deaths between ages \<open>x\<close> and \<open>x+t\<close>\<close>
    \<comment> \<open>The parameter \<open>t\<close> is usually nonnegative, but theoretically it can be negative.\<close>

abbreviation death1 :: "real \<Rightarrow> real" ("$d'__" [101] 200)
  where "$d_x \<equiv> $d_{1&x}"

lemma death_def_nonneg: "$d_{t&x} = $l_x - $l_(x+t)" if "t \<ge> 0" for t x :: real
  using that l_antimono unfolding death_def antimono_def by simp

lemma d_nonpos_0: "$d_{t&x} = 0" if "t \<le> 0" for t x :: real
  using that l_antimono unfolding death_def antimono_def by simp

corollary d_0_0: "$d_{0&x} = 0" for x::real
  using d_nonpos_0 by simp

lemma d_nonneg[simp]: "$d_{t&x} \<ge> 0" for t x :: real
  unfolding death_def by simp

lemma dx_l: "$d_x = $l_x - $l_(x+1)" for x::real
  using death_def_nonneg by simp

lemma sum_dx_l: "(\<Sum>k<n. $d_(x+k)) = $l_x - $l_(x+n)" for x::real and n::nat
proof (induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thus ?case
    using dx_l
    by (metis Set_Interval.comm_monoid_add_class.sum.lessThan_Suc
        add_diff_cancel_left' diff_diff_eq2 of_nat_Suc)
qed

corollary d_sums_l: "(\<lambda>k. $d_(x+k)) sums $l_x" for x::real
  unfolding sums_def
  apply (rewrite sum_dx_l)
  apply (rule tendsto_diff[where b=0, simplified], simp)
  using l_PInfty_0 filterlim_compose filterlim_real_sequentially filterlim_tendsto_add_at_top
    tendsto_const by blast

lemma add_d: "$d_{t&x} + $d_{t' & x+t} = $d_{t+t' & x}" if "t \<ge> 0" "t' \<ge> 0" for t t' :: real
  using death_def_nonneg that by (smt (verit))

definition die_central :: "real \<Rightarrow> real \<Rightarrow> real" ("$m'_{_&_}" [0,0] 200)
  where "$m_{n&x} \<equiv> $d_{n&x} / $L_{n&x}"
    \<comment> \<open>central death rate\<close>

abbreviation die_central_1 :: "real \<Rightarrow> real" ("$m'__" [101] 200)
  where "$m_x \<equiv> $m_{1&x}"

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
    proof -
      have [simp]: "{\<xi>::real. \<xi> \<le> 0} = {..0}" by blast
      have "measure (interval_measure (\<lambda>x. 1 - $l_x / $l_0)) {..0} = 0"
        using l_normal_antimono compl_l_normal_right_continuous compl_l_normal_NInfty_0
        by (rewrite measure_interval_measure_Iic, simp_all add: antimono_def)
      hence "emeasure (interval_measure (\<lambda>x. 1 - $l_x / $l_0)) {..0} = ennreal 0"
        apply (rewrite finite_measure.emeasure_eq_measure, simp_all)
        using compl_l_real_distribution prob_space_def real_distribution_def by blast
      thus ?thesis
        apply (intro survival_model_axioms.intro, simp)
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

subsubsection \<open>Relations between Life Table and Survival Function for \<open>X\<close>\<close>

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

lemma d_l_equiv: "$d_{t&x} = $l_x \<longleftrightarrow> x+t \<ge> $\<psi>" if "t \<ge> 0" for x t :: real
  using death_def_nonneg l_0_equiv that by simp

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

subsubsection \<open>Relations between Life Table and Cumulative Distributive Function for \<open>X\<close>\<close>

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

subsubsection \<open>Relations between Life Table and Survival Function for \<open>T(x)\<close>\<close>

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

subsubsection \<open>Relations between Life Table and Cumulative Distributive Function for \<open>T(x)\<close>\<close>

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

lemma total_finite_iff_p_set_integrable_Ici:
  "total_finite \<longleftrightarrow> set_integrable lborel {0..} (\<lambda>t. $p_{t&x})"
  apply (rewrite set_integrable_cong_AE[where g="\<lambda>t. $l_(x+t) / $l_x"]; simp)
  using survive_def apply simp
  using p_l apply (intro AE_I2, simp)
  by (metis l_integrable_Icc_shift set_integrable_Ici_equiv set_integrable_Ici_shift
      total_finite_iff_set_integrable_Ici)

lemma p_PTx_ge_l_isCont: "$p_{t&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> t \<bar> T x \<xi> > 0)"
  if "isCont l (x+t)" "t > 0" for t::real
  using p_PTx_ge_ccdf_isCont that continuous_ccdfX_l by force

lemma q_defer_l: "$q_{f\<bar>t&x} = ($l_(x+f) - $l_(x+f+t)) / $l_x" if "f \<ge> 0" "t \<ge> 0" for f t :: real
  apply (rewrite q_defer_p, simp_all add: that)
  using that by (rewrite p_l, simp)+ (smt (verit) diff_divide_distrib)

corollary q_defer_d_l: "$q_{f\<bar>t&x} = $d_{t & x+f} / $l_x" if "f \<ge> 0" "t \<ge> 0" for f t :: real
  using q_defer_l that death_def_nonneg by simp

corollary q_defer_1_d_l: "$q_{f\<bar>&x} = $d_(x+f) / $l_x" if "f \<ge> 0" for f::real
  using q_defer_d_l that by simp

lemma q_d_l: "$q_{t&x} = $d_{t&x} / $l_x" for t::real
proof (cases \<open>t \<ge> 0\<close>)
  case True
  thus ?thesis using q_defer_d_l[of 0] by simp
next
  case False
  thus ?thesis using q_nonpos_0 d_nonpos_0 by simp
qed

corollary q_1_d_l: "$q_x = $d_x / $l_x"
  using q_d_l by simp

lemma LBINT_p_l: "(LBINT t:A. $p_{t&x}) = (LBINT t:A. $l_(x+t)) / $l_x"
  if "A \<subseteq> {0..}" "A \<in> sets lborel" for A :: "real set"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
proof -
  have [simp]: "\<And>t. t \<in> A \<Longrightarrow> $p_{t&x} = $l_(x+t) / $l_x" using p_l that by blast
  hence "(LBINT t:A. $p_{t&x}) = (LBINT t:A. $l_(x+t) / $l_x)"
    using that by (rewrite set_lebesgue_integral_cong[where g="\<lambda>t. $l_(x+t) / $l_x"]; simp)
  also have "\<dots> = (LBINT t:A. $l_(x+t)) / $l_x" by (rewrite set_integral_divide_zero) simp
  finally show ?thesis .
qed

corollary e_LBINT_l: "$e`\<circ>_x = (LBINT t:{0..}. $l_(x+t)) / $l_x"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
  by (simp add: e_LBINT_p LBINT_p_l)

corollary e_LBINT_l_Icc: "$e`\<circ>_x = (LBINT t:{0..n}. $l_(x+t)) / $l_x" if "x+n \<ge> $\<psi>" for n::real
  using e_LBINT_p_Icc by (rewrite LBINT_p_l[THEN sym]; simp add: that)

lemma temp_e_LBINT_l: "$e`\<circ>_{x:n} = (LBINT t:{0..n}. $l_(x+t)) / $l_x" if "n \<ge> 0" for n::real
  using temp_e_LBINT_p by (rewrite LBINT_p_l[THEN sym]; simp add: that)

lemma integral_p_l: "integral A (\<lambda>t. $p_{t&x}) = (integral A (\<lambda>t. $l_(x+t))) / $l_x"
  if "A \<subseteq> {0..}" "A \<in> sets lborel" for A :: "real set"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
  using that apply (rewrite set_borel_integral_eq_integral_nonneg[THEN sym], simp_all)
  apply (simp add: survive_def)
  apply (rewrite set_borel_integral_eq_integral_nonneg[THEN sym], simp_all)
  by (rule LBINT_p_l; simp)

corollary e_integral_l: "$e`\<circ>_x = integral {0..} (\<lambda>t. $l_(x+t)) / $l_x"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the integral diverges.\<close>
  by (simp add: e_integral_p integral_p_l)

corollary e_integral_l_Icc:
  "$e`\<circ>_x = integral {0..n} (\<lambda>t. $l_(x+t)) / $l_x" if "x+n \<ge> $\<psi>" for n::real
  using e_integral_p_Icc by (rewrite integral_p_l[THEN sym]; simp add: that)

lemma e_pos_total_finite: "$e`\<circ>_x > 0" if total_finite
  using e_pos total_finite_iff_p_set_integrable_Ici that by simp

lemma temp_e_integral_l:
  "$e`\<circ>_{x:n} = integral {0..n} (\<lambda>t. $l_(x+t)) / $l_x" if "n \<ge> 0" for n::real
  using temp_e_integral_p by (rewrite integral_p_l[THEN sym]; simp add: that)

lemma curt_e_sum_l: "$e_x = (\<Sum>k. $l_(x+k+1)) / $l_x" if total_finite "\<And>k::nat. isCont l (x+k+1)"
proof -
  have "summable (\<lambda>k. $l_(x+(k+1::nat)))"
    using that total_finite_iff_summable by (rewrite summable_iff_shift[of "\<lambda>k. $l_(x+k)" 1]) simp
  moreover hence "summable (\<lambda>k. $p_{k+1&x})" by (rewrite p_l, simp_all add: add.commute)
  moreover have "\<And>k::nat. isCont (\<lambda>t. $p_{t&x}) (k+1)"
    using isCont_p_l that by (simp add: add.assoc)
  ultimately show ?thesis
    apply (rewrite curt_e_sum_p, simp_all)
    apply (rewrite p_l, simp)
    by (rewrite suminf_divide) (simp add: add.commute, simp add: add.assoc)
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

lemma e_T_l: "$e`\<circ>_x = $T_x / $l_x"
  unfolding total_def
  apply (rewrite e_LBINT_l, simp_all)
  by (metis add_cancel_left_left diff_add_cancel lborel_set_integral_Ici_shift)

lemma temp_e_L_l: "$e`\<circ>_{x:n} = $L_{n&x} / $l_x" if "n \<ge> 0" for n::real
  unfolding lives_def using that
  apply (rewrite temp_e_LBINT_l, simp_all)
  using diff_self add_diff_cancel_left' lborel_set_integral_Icc_shift by metis

lemma m_q_e: "$m_{n&x} = $q_{n&x} / $e`\<circ>_{x:n}" if "n \<ge> 0" for n::real
proof -
  have "$m_{n&x} = ($d_{n&x} / $l_x) / ($L_{n&x} / $l_x)" unfolding die_central_def by simp
  thus ?thesis using q_d_l temp_e_L_l that by simp
qed

end

lemma l_p: "$l_x / $l_0 = $p_{x&0}" for x::real
  using ccdfX_l_normal ccdfX_p by force

lemma e_p_e_total_finite: "$e`\<circ>_x = $e`\<circ>_{x:n} + $p_{n&x} * $e`\<circ>_(x+n)"
  if total_finite "n \<ge> 0" "x+n < $\<psi>" for x n :: real
  using e_p_e that total_finite_iff_p_set_integrable_Ici by (smt (verit) ereal_less_le)

proposition x_ex_const_equiv_total_finite: "x + $e`\<circ>_x = y + $e`\<circ>_y \<longleftrightarrow> $q_{y-x&x} = 0"
  if total_finite "x \<le> y" "y < $\<psi>" for x y :: real
  using x_ex_const_equiv that total_finite_iff_p_set_integrable_Ici p_set_integrable_shift
  by blast

corollary x_ex_const_iff_l_const: "x + $e`\<circ>_x = y + $e`\<circ>_y \<longleftrightarrow> $l_x = $l_y"
  if total_finite "x \<le> y" "y < $\<psi>" for x y :: real
  using x_ex_const_equiv_total_finite that
  by (smt (verit, ccfv_threshold) divide_cancel_right ereal_less_le
      l_0_equiv life_table.death_def_nonneg life_table.q_d_l life_table_axioms q_1_equiv)

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
    thus ?thesis
      by (simp add: ln_divide_pos)
  qed
  hence "deriv (\<lambda>x. ln ($l_x / $l_0)) x = deriv (\<lambda>x. ln ($l_x)) x"
    apply (rewrite deriv_cong_ev[of _ "\<lambda>x. ln ($l_x) - ln ($l_0)"], simp_all)
    apply (rewrite deriv_diff, simp_all)
    unfolding field_differentiable_def using that
    by (metis DERIV_ln_divide_chain lx_pos real_differentiable_def)
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
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
proof -
  have "\<And>s. s\<in>{f<..f+t} \<Longrightarrow> $p_{s&x} = $l_(x+s) / $l_x" using p_l that by simp
  hence "$q_{f\<bar>t&x} = (LBINT s:{f<..f+t}. $l_(x+s) / $l_x * $\<mu>_(x+s))"
    using LBINT_p_mu_q_defer 
    by (smt (verit) greaterThanAtMost_borel set_lebesgue_integral_cong sets_lborel that x_lt_psi)
  also have "\<dots> = (LBINT s:{f<..f+t}. $l_(x+s) * $\<mu>_(x+s)) / $l_x"
    using set_integral_divide_zero by simp
  finally show ?thesis by simp
qed

lemma set_integrable_l_mu: "set_integrable lborel {f<..f+t} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s))"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
proof -
  have "set_integrable lborel {f<..f+t} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x)"
    using p_l set_integrable_p_mu that
    by (rewrite set_integrable_cong[where f'="\<lambda>s. $p_{s&x} * $\<mu>_(x+s)"]) simp_all+
  thus ?thesis by simp
qed

lemma l_mu_has_integral_q_defer:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x) has_integral $q_{f\<bar>t&x}) {f..f+t}"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
  using p_l that p_mu_has_integral_q_defer_Icc
  by (rewrite has_integral_cong[of _ _ "\<lambda>s. $p_{s&x} * $\<mu>_(x+s)"]; simp)

corollary l_mu_has_integral_q:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s) / $l_x) has_integral $q_{t&x}) {0..t}" if "t \<ge> 0" for t::real
  using l_mu_has_integral_q_defer[where f=0] that by simp

lemma l_mu_has_integral_d:
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s)) has_integral $d_{t & x+f}) {f..f+t}"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
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
  "((\<lambda>s. $l_(x+s) * $\<mu>_(x+s)) has_integral $d_(x+f)) {f..f+1}" if "t \<ge> 0" "f \<ge> 0" for t f :: real
  using l_mu_has_integral_d[where t=1] that by simp

lemma e_LBINT_l: "$e`\<circ>_x = (LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the life expectation diverges.\<close>
proof -
  have "\<And>s. s\<in>{0..} \<Longrightarrow> $p_{s&x} = $l_(x+s) / $l_x" using p_l by simp
  hence "$e`\<circ>_x = (LBINT s:{0..}. $l_(x+s) / $l_x * $\<mu>_(x+s) * s)"
    using e_LBINT_p_mu
    by (smt (verit) atLeast_borel set_lebesgue_integral_cong sets_lborel x_lt_psi)
  also have "\<dots> = (LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
    using set_integral_divide_zero by simp
  finally show ?thesis .
qed

lemma e_integral_l: "$e`\<circ>_x = integral {0..} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) * s) / $l_x"
  \<comment> \<open>Note that \<open>0 = 0\<close> holds when the life expectation diverges.\<close>
proof -
  have "AE s in lborel. $\<mu>_(x+s) \<ge> 0" by (rule AE_translation, rule mu_nonneg_AE)
  hence "(LBINT s:{0..}. $l_(x+s) * $\<mu>_(x+s) * s) = integral {0..} (\<lambda>s. $l_(x+s) * $\<mu>_(x+s) * s)"
    by (intro set_borel_integral_eq_integral_nonneg_AE; force)
  thus ?thesis using e_LBINT_l by simp
qed

lemma m_LBINT_p_mu: "$m_{n&x} = (LBINT t:{0<..n}. $p_{t&x} * $\<mu>_(x+t)) / (LBINT t:{0..n}. $p_{t&x})"
  if "n \<ge> 0" for n::real
  using that
  apply (rewrite m_q_e, simp_all)
  apply (rewrite LBINT_p_mu_q[simplified], simp_all)
  by (rewrite temp_e_LBINT_p; simp)

lemma m_integral_p_mu:
  "$m_{n&x} = integral {0..n} (\<lambda>t. $p_{t&x} * $\<mu>_(x+t)) / integral {0..n} (\<lambda>t. $p_{t&x})"
  if "n \<ge> 0" for n::real
  using that
  apply (rewrite m_q_e, simp_all)
  apply (rewrite integral_unique[OF p_mu_has_integral_q_Icc])
    apply simp_all[2]
  by (rewrite temp_e_integral_p; simp)

end

lemma deriv_x_p_mu_l: "deriv (\<lambda>y. $p_{t&y}) x = $p_{t&x} * ($\<mu>_x - $\<mu>_(x+t))"
  if "l differentiable at x" "l differentiable at (x+t)" "t \<ge> 0" "x < $\<psi>" for x t :: real
  using deriv_x_p_mu that differentiable_ccdfX_l by blast

lemma e_has_derivative_mu_e_l: "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if total_finite "l differentiable at x" "x\<in>{a<..<b}" "b \<le> $\<psi>" for a b x :: real
  using total_finite_iff_set_integrable_Ici that
    e_has_derivative_mu_e differentiable_ccdfX_l set_integrable_ccdfX_l
  by force

corollary e_has_derivative_mu_e_l': "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if total_finite "l differentiable at x" "x\<in>{a<..<b}" "b \<le> $\<psi>" for a b x :: real
  using that by (intro e_has_derivative_mu_e_l[where a=a]; simp)

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

lemma curt_e_sum_l_smooth: "$e_x = (\<Sum>k. $l_(x+k+1)) / $l_x" if total_finite
proof -
  have [simp]: "summable (\<lambda>k. $l_(x+k+1))"
    using total_finite_iff_summable[of "x+1"] that
    by (metis (no_types, lifting) add.commute add.left_commute summable_def sums_cong)
  hence "summable (\<lambda>k. $p_{k+1&x})" by (rewrite p_l; simp add: add.assoc)
  hence "$e_x = (\<Sum>k. $p_{k+1&x})" using curt_e_sum_p_smooth by simp
  also have "\<dots> = (\<Sum>k. $l_(x+k+1) / $l_x)" by (rewrite p_l; simp add: add.assoc)
  also have "\<dots> = (\<Sum>k. $l_(x+k+1)) / $l_x" by (rewrite suminf_divide; simp)
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

subsection \<open>Interpolations\<close>

context life_table
begin

definition "linear_interpolation \<equiv>
  \<forall>(x::nat)(t::real). 0 \<le> t \<and> t \<le> 1 \<longrightarrow> $l_(x+t) = (1-t)*$l_x + t*$l_(x+1)"

lemma linear_l: "$l_(x+t) = (1-t)*$l_x + t*$l_(x+1)"
  if linear_interpolation "0 \<le> t" "t \<le> 1" for x::nat and t::real
  using that unfolding linear_interpolation_def by (metis of_nat_1 of_nat_add)

lemma linear_l_d: "$l_(x+t) = $l_x - t*$d_x"
  if linear_interpolation "0 \<le> t" "t \<le> 1" for x::nat and t::real
  using death_def_nonneg that unfolding linear_interpolation_def
  by (smt (verit) distrib_left left_diff_distrib')

lemma linear_p_q: "$p_{t&x} = 1 - t*$q_x"
  if linear_interpolation "0 \<le> t" "t \<le> 1" "x < $\<psi>" for x::nat and t::real
  using that
  apply (rewrite p_l, simp_all)
  apply (rewrite q_d_l, simp_all)
  using divide_self[of "$l_(real x)"] linear_l_d
  by (smt (verit, ccfv_SIG) add_divide_distrib lx_neq_0)

lemma linear_q: "$q_{t&x} = t*$q_x"
  if linear_interpolation "0 \<le> t" "t \<le> 1" "x < $\<psi>" for x::nat and t::real
  using that linear_p_q p_q_1 by (smt (verit))

lemma linear_L_l_d: "$L_x = $l_x - $d_x / 2" if linear_interpolation for x::nat
proof -
  have "$L_(real x) = (LBINT t:{0..1}. $l_(real x + t))"
    unfolding lives_def using lborel_set_integral_Icc_shift[of "real x" "real x + 1" l "real x"]
    by (simp add: add.commute)
  also have "\<dots> = (LBINT t:{0..1}. $l_(real x) - t*$d_(real x))"
    using linear_l_d that by (intro set_lebesgue_integral_cong; simp)
  also have "\<dots> = $l_(real x) - $d_(real x) / 2"
  proof -
    have "(LBINT t:{0::real..1}. t) = 1/2"
      unfolding set_lebesgue_integral_def using integral_power[of 0 1 1] by (simp add: mult.commute)
    hence "(LBINT t:{0..1}. t*$d_(real x)) = $d_(real x) / 2" by auto
    moreover have "set_integrable lborel {0..1} (\<lambda>t. t*$d_(real x))"
      apply (rule set_integrable_mult_left[where f=id and a="$d_(real x)", simplified])
      unfolding set_integrable_def using integrable_power[of 0 1 1] by (simp add: mult.commute)
    moreover have "(LBINT t:{0::real..1}. $l_(real x)) = $l_(real x)"
      unfolding set_lebesgue_integral_def by simp
    ultimately show ?thesis using set_integrable_def by (rewrite set_integral_diff; force)
  qed
  finally show ?thesis .
qed

lemma linear_L_l_d' : "$L_x = $l_(x+1) + $d_x / 2" if linear_interpolation for x::nat
proof -
  have "$L_(real x) = $l_(real x) - $d_(real x) + $d_(real x) / 2" using that linear_L_l_d by simp
  also have "\<dots> = $l_(real (x+1)) + $d_(real x) / 2" using dx_l by (smt (verit) of_nat_1 of_nat_add)
  finally show ?thesis .
qed

lemma linear_l_continuous: "continuous_on UNIV l" if linear_interpolation
  unfolding continuous_on_def
proof
  fix u::real
  show "l \<midarrow>u\<rightarrow> $l_u"
  proof (cases \<open>u \<le> 0\<close>)
    case True
    hence "(l \<longlongrightarrow> $l_u) (at_left u)" using l_left_continuous_nonpos continuous_within by auto
    thus ?thesis
      apply (rule filterlim_split_at_real)
      using l_right_continuous continuous_within by auto
  next
    case False
    hence u_pos: "u > 0" by simp
    thus ?thesis
    proof (cases \<open>u = real_of_int \<lfloor>u\<rfloor>\<close>)
      case True
      from this u_pos obtain x::nat where ux: "u = Suc x"
        by (metis gr0_implies_Suc of_int_0_less_iff of_int_of_nat_eq pos_int_cases)
      have "((\<lambda>t. (1-t)*$l_(real x) + t*$l_(real x + 1)) \<longlongrightarrow> $l_(real x + 1)) (at_left 1)"
        apply (rewrite in "(_ \<longlongrightarrow> \<hole>) _" add_0[THEN sym], rule tendsto_add)
         apply (simp add: LIM_zero_iff' tendsto_mult_left_zero)
        by (rewrite in "(_ \<longlongrightarrow> \<hole>) _" mult_1[THEN sym], rule tendsto_mult_right) simp
      hence "((\<lambda>t. $l_(real x + t)) \<longlongrightarrow> $l_(real x + 1)) (at_left 1)"
        apply (rewrite tendsto_cong; simp)
        apply (rule eventually_at_leftI[of 0]; simp)
        using that by (rewrite linear_l; simp add: add.commute)
      moreover have "((\<lambda>t. $l_(real x + t)) \<longlongrightarrow> $l_(real x + 1)) (at_right 1)"
        using l_right_continuous apply (rule continuous_within_tendsto_compose, simp_all)
         apply (rule eventually_at_right_less)
        by (rule tendsto_intros, simp_all)
      ultimately show ?thesis
        apply (rewrite ux)+
        apply (rewrite filterlim_shift_iff[where d=x, THEN sym])
        by (rule filterlim_split_at_real; simp add: comp_def add.commute)
    next
      case False
      let ?x = "nat \<lfloor>u\<rfloor>"
      let ?t = "u - real ?x"
      let ?e = "min ?t (1 - ?t)"
      from False have "?t > 0" using u_pos by linarith
      moreover have "?t < 1" by linarith
      ultimately have e_pos: "?e > 0" by simp
      hence
        "\<forall>\<^sub>F v in nhds u. $l_v = (1 - (v - real ?x))*$l_(real ?x) + (v - real ?x)*$l_(real ?x + 1)"
      proof -
        { fix v::real assume vu_e: "dist v u < ?e"
          hence "v - real ?x \<ge> 0" using dist_real_def by force
          moreover have "v - real ?x \<le> 1" using dist_real_def vu_e by force
          ultimately have "$l_v = (1 - (v - real ?x))*$l_(real ?x) + (v - real ?x)*$l_(real ?x + 1)"
            using linear_l that by (smt (verit, ccfv_threshold) linear_interpolation_def) }
        thus ?thesis using eventually_nhds_metric e_pos by blast
      qed
      moreover have
        "isCont (\<lambda>v. (1 - (v - real ?x))*$l_(real ?x) + (v - real ?x)*$l_(real ?x + 1)) u"
        by (rule continuous_intros)+
      ultimately have "isCont l u" using isCont_cong by force
      thus ?thesis by (simp add: isContD)
    qed
  qed
qed

lemma linear_l_sums_T_l: "(\<lambda>k. $l_(x + Suc k)) sums ($T_x - $l_x / 2)"
  if linear_interpolation total_finite for x::nat
proof -
  have "\<And>k::nat. $l_(real (x + Suc k)) = $L_(real (x+k)) - $d_(real (x+k)) / 2"
    using linear_L_l_d' that by (smt (verit) Suc_eq_plus1 add_Suc_right)
  moreover have "(\<lambda>k::nat. $L_(real (x+k))) sums $T_x" using L_sums_T that by simp
  moreover have "(\<lambda>k::nat. $d_(real (x+k)) / 2) sums ($l_(real x) / 2)"
    using sums_divide d_sums_l by auto
  ultimately show ?thesis
    apply (rewrite sums_cong, simp)
    by (rule sums_diff; simp)
qed

corollary linear_T_suminf_l: "$T_x = (\<Sum>k. $l_(x+k+1)) + $l_x / 2"
  if linear_interpolation total_finite for x::nat
  using linear_l_sums_T_l that sums_unique by (smt (z3) Suc_eq_plus1 add_Suc_right suminf_cong)

lemma linear_mx_q: "$m_x = $q_x / (1 - $q_x / 2)" if linear_interpolation "x < $\<psi>" for x::nat
proof -
  have [simp]: "$l_(real x) \<noteq> 0" using that by simp
  have "$m_(real x) = $d_(real x) / ($l_(real x) - $d_(real x) / 2)"
    unfolding die_central_def using linear_L_l_d that by simp
  also have "\<dots> = ($d_(real x) / $l_(real x)) / (($l_(real x) - $d_(real x) / 2) / $l_(real x))"
    by simp
  also have "\<dots> = ($d_(real x) / $l_(real x)) / (1 - ($d_(real x) / $l_(real x)) / 2)"
    by (rewrite diff_divide_distrib) simp
  also have "\<dots> = $q_(real x) / (1 - $q_(real x) / 2)" using that q_d_l by simp
  finally show ?thesis .
qed

lemma linear_e_curt_e: "$e`\<circ>_x = $e_x + 1/2" 
  if linear_interpolation total_finite "x < $\<psi>" for x::nat
proof -
  have "$e`\<circ>_(real x) = ((\<Sum>k::nat. $l_(real (x+k+1))) + $l_(real x) / 2) / $l_(real x)"
    using e_T_l linear_T_suminf_l that by simp
  also have "\<dots> = (\<Sum>k::nat. $l_(real (x+k+1))) / $l_(real x) + ($l_(real x) / 2) / $l_(real x)"
    using add_divide_distrib by blast
  also have "\<dots> = $e_(real x) + 1/2"
    using that apply (rewrite curt_e_sum_l, simp_all)
    using linear_l_continuous by (rule continuous_on_interior, simp_all add: that add.commute)
  finally show ?thesis .
qed

end

context smooth_life_table
begin

lemma linear_l_has_derivative_at_frac:
  "((\<lambda>s. $l_(x+s)) has_real_derivative - $d_x) (at t)"
  if linear_interpolation "0 < t" "t < 1" for x::nat and t::real
proof -
  let ?x = "real x"
  have "((\<lambda>s. $l_?x - s*$d_?x) has_real_derivative (0 - $d_?x)) (at t)"
    apply (rule derivative_intros, simp)
    apply (rule DERIV_cmult_right[of id 1, simplified])
    by (metis DERIV_ident eq_id_iff)
  moreover have "\<forall>\<^sub>F s in nhds t. $l_(?x + s) = $l_?x - s*$d_?x"
  proof -
    let ?r = "min t (1-t)"
    have "?r > 0" using that by simp
    moreover
    { fix s assume "dist s t < ?r"
      hence "$l_(?x + s) = $l_?x - s*$d_?x" using linear_l_d that dist_real_def by force }
    ultimately show ?thesis using eventually_nhds_metric that by blast
  qed
  ultimately show ?thesis by (rewrite DERIV_cong_ev; simp)
qed

lemma linear_l_has_derivative_at_frac':
  "(l has_real_derivative - $d_x) (at y)"
  if linear_interpolation "x < y" "y < x+1" for x::nat and y::real
  apply (rewrite DERIV_at_within_shift[where x="y - real x" and z="real x" and S=UNIV, simplified])
  using linear_l_has_derivative_at_frac that by simp

lemma linear_l_differentiable_on_frac:
  "l differentiable_on {x<..<x+1}" if linear_interpolation for x::nat
proof -
  { fix y::real assume "y \<in> {real x <..< real (x+1)}"
    hence "l differentiable at y"
      using linear_l_has_derivative_at_frac' that real_differentiable_def by auto }
  thus ?thesis unfolding differentiable_on_def by (metis differentiable_at_withinI)
qed

lemma linear_l_has_right_derivative_at_nat:
  "(l has_real_derivative - $d_x) (at_right x)" if linear_interpolation for x::nat
proof -
  let ?x = "real x"
  have [simp]: "plus ?x ` {0<..} = {?x<..}"
    unfolding image_def greaterThan_def apply simp
    by (metis Groups.ab_semigroup_add_class.add.commute
        add_minus_cancel neg_less_iff_less real_0_less_add_iff)
  have "((\<lambda>s. $l_(?x + s)) has_real_derivative - $d_?x) (at_right 0)"
    apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>s. $l_?x - s*$d_?x"])
    using linear_l_d that apply (intro eventually_at_rightI[of 0 1], simp_all)
    apply (rule has_field_derivative_at_within)
    apply (rewrite diff_0[of "$d_?x", THEN sym])
    apply (rule DERIV_diff, simp)
    apply (rule DERIV_cmult_right[of id 1, simplified])
    by (metis DERIV_ident eq_id_iff)
  thus ?thesis
    by (rewrite DERIV_at_within_shift[where z="?x" and x=0 and S="{0<..}", simplified]) simp
qed

lemma linear_l_has_left_derivative_at_nat:
  "(l has_real_derivative - $d_(real x - 1)) (at_left x)" if linear_interpolation for x::nat
proof (cases x)
  case 0
  hence "(l has_real_derivative 0) (at_left (real x))"
    apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>_. $l_0"]; simp)
    apply (rule eventually_at_leftI[of "-1"]; simp)
    using l_neg_nil less_eq_real_def by blast
  moreover have "$d_(real x - 1) = 0" using 0 dx_l l_neg_nil less_eq_real_def by fastforce
  ultimately show ?thesis by auto
next
  case (Suc y)
  let ?x = "real x" and ?y = "real y"
  have [simp]: "?y + 1 = ?x" using Suc by simp
  have [simp]: "plus ?y ` {..<1} = {..<?x}"
    using Suc unfolding image_def lessThan_def apply simp
    by (metis (no_types, opaque_lifting) Groups.ab_semigroup_add_class.add.commute
        add_less_cancel_right diff_add_cancel)
  have "$l_?x = $l_real y - $d_real y" using Suc by (simp add: dx_l)
  moreover have " \<forall>\<^sub>F s in at_left 1. $l_(?y + s) = $l_?y - s*$d_?y"
    apply (rule eventually_at_leftI[of 0], simp_all)
    using Suc linear_l_d that by simp
  moreover have "((\<lambda>s. $l_?y - s*$d_?y) has_real_derivative - $d_?y) (at_left 1)"
    apply (rule has_field_derivative_at_within)
    apply (rewrite diff_0[of "$d_?y", THEN sym])
    apply (rule DERIV_diff, simp)
    apply (rule DERIV_cmult_right[of id 1, simplified])
    by (metis DERIV_ident eq_id_iff)
  ultimately have "((\<lambda>s. $l_(?y + s)) has_real_derivative - $d_?y) (at_left 1)"
    by (rewrite has_field_derivative_cong_eventually[where g="\<lambda>s. $l_?y - s*$d_?y"]; simp)
  thus ?thesis
    apply (rewrite DERIV_at_within_shift[where S="{..<1}" and z="?y" and x=1, simplified])
    using Suc by simp
qed

lemma linear_l_has_derivative_at_nat_iff_d:
  "(l has_real_derivative - $d_x) (at x) \<longleftrightarrow> $d_x = $d_(real x - 1)"
  if linear_interpolation for x::nat
proof -
  let ?x = "real x"
  have "(l has_real_derivative - $d_?x) (at ?x) \<longleftrightarrow>
    (l has_real_derivative - $d_?x) (at_right ?x) \<and>
    (l has_real_derivative - $d_?x) (at_left ?x)"
    using has_real_derivative_at_split by auto
  also have "\<dots> \<longleftrightarrow> $d_?x = $d_(?x - 1)" (is "?LHS = ?RHS")
  proof
    assume "?LHS"
    hence "(l has_real_derivative - $d_?x) (at_left ?x)" by simp
    moreover have "(l has_real_derivative - $d_(?x - 1)) (at_left ?x)"
      using that linear_l_has_left_derivative_at_nat by simp
    ultimately show "?RHS"
      using has_real_derivative_iff_has_vector_derivative vector_derivative_unique_within
        trivial_limit_at_left_real by (smt (verit, ccfv_SIG))
  next
    assume "?RHS"
    thus "?LHS"
      using that linear_l_has_right_derivative_at_nat linear_l_has_left_derivative_at_nat by metis
  qed
  finally show ?thesis .
qed

lemma linear_l_differentiable_at_nat_iff_d:
  "l differentiable at x \<longleftrightarrow> $d_x = $d_(real x - 1)"
  if linear_interpolation for x::nat
proof
  let ?x = "real x"
  assume "l differentiable at x"
  from this obtain D where DERIV_l: "(l has_real_derivative D) (at ?x)"
    using real_differentiable_def by blast
  hence "(l has_real_derivative D) (at_right ?x)"
    using has_field_derivative_at_within by blast
  moreover have "at ?x within {real x<..} \<noteq> \<bottom>" by simp
  moreover have "(l has_real_derivative - $d_?x) (at_right ?x)"
    using linear_l_has_right_derivative_at_nat that by simp
  ultimately have "D = - $d_?x"
    using that has_real_derivative_iff_has_vector_derivative vector_derivative_unique_within
    by blast
  thus "$d_?x = $d_(?x - 1)"
    using linear_l_has_derivative_at_nat_iff_d that DERIV_l by blast
next
  assume "$d_(real x) = $d_(real x - 1)"
  thus "l differentiable at (real x)"
    using linear_l_has_derivative_at_nat_iff_d that real_differentiable_def by blast
qed

lemma linear_l_limited: "$\<psi> < \<infinity>" if linear_interpolation
proof -
  let ?ND = "{y. \<not> l differentiable at y}"
  obtain xn::nat where xn_def: "Max ?ND < real xn" using reals_Archimedean2 by blast
  hence xn_dif: "\<And>x::nat. x \<ge> xn \<Longrightarrow> l differentiable at (real x)"
  proof -
    fix x::nat assume "x \<ge> xn"
    with xn_def have "real x > Max ?ND" by simp
    hence "real x \<notin> ?ND" using notI Max.coboundedI l_nondifferentiable_finite_set leD by blast
    thus "l differentiable at (real x)" by simp
  qed
  hence d_const: "\<And>x::nat. x \<ge> xn \<Longrightarrow> $d_(real x) = $d_(real xn)"
  proof -
    fix x::nat assume "x \<ge> xn"
    moreover have
      "\<And>y::nat. xn \<le> y \<Longrightarrow> $d_(real y) = $d_(real xn) \<Longrightarrow> $d_(real (Suc y)) = $d_(real xn)"
      using linear_l_differentiable_at_nat_iff_d that
      by (smt (verit, best) of_nat_Suc of_nat_le_iff xn_dif)
    ultimately show "$d_(real x) = $d_(real xn)"
      using nat_induct_at_least[where P="\<lambda>x::nat. $d_(real x) = $d_(real xn)"] by simp
  qed
  have "\<not> $d_(real xn) > 0"
  proof (rule notI)
    assume "$d_(real xn) > 0"
    from this obtain N::nat where N_def: "N * $d_(real xn) > $l_(real xn)"
      using reals_Archimedean3 by blast
    hence "$l_(real (xn+N)) < 0"
    proof -
      have "$l_(real (xn+N)) = $l_(real xn) - (\<Sum>k<N. $d_(real xn + real k))" using sum_dx_l by simp
      also have "\<dots> = $l_(real xn) - (\<Sum>k<N. $d_(real xn))"
        using d_const by (metis le_add1 of_nat_add)
      also have "\<dots> = $l_(real xn) - N * $d_(real xn)" by simp
      also have "\<dots> < 0" using N_def by simp
      finally show ?thesis .
    qed
    thus False by (smt (verit, ccfv_SIG) l_nonneg)
  qed
  hence dxn0: "$d_(real xn) = 0" by (smt (verit) d_nonneg)
  hence "\<And>x::nat. x \<ge> xn \<Longrightarrow> $l_(real x) = $l_(real xn)"
  proof -
    fix x::nat
    assume "xn \<le> x"
    moreover have
      "\<And>y::nat. xn \<le> y \<Longrightarrow> $l_(real y) = $l_(real xn) \<Longrightarrow> $l_(real (Suc y)) = $l_(real xn)"
      by (smt (verit, ccfv_threshold) dxn0 d_const dx_l of_nat_Suc)
    ultimately show "$l_(real x) = $l_(real xn)"
      using nat_induct_at_least[where P="\<lambda>x::nat. $l_(real x) = $l_(real xn)"] by simp
  qed
  hence "(\<lambda>x::nat. $l_(real x)) \<longlonglongrightarrow> $l_(real xn)"
    using eventually_sequentially by (intro tendsto_eventually) blast
  moreover have "(\<lambda>x::nat. $l_(real x)) \<longlonglongrightarrow> 0"
    using l_PInfty_0 by (simp add: filterlim_compose filterlim_real_sequentially)
  ultimately have "$l_(real xn) = 0" by (simp add: LIMSEQ_unique)
  thus ?thesis by force
qed

lemma linear_mu_q: "$\<mu>_(x+t) = $q_x / (1 - t*$q_x)"
  if linear_interpolation "l differentiable at (x+t)" "0 < t" "t < 1" "x+t < $\<psi>"
  for x::nat and t::real
proof -
  have [simp]: "ereal x < $\<psi>" using that by (simp add: ereal_less_le)
  have [simp]: "$l_(real x) \<noteq> 0" by simp
  have [simp]: "l field_differentiable at (real x + t)"
    using differentiable_eq_field_differentiable_real that by simp
  define d where "d \<equiv> min t (1-t)"
  have d_pos: "d > 0" unfolding d_def using that by simp
  have "$p_{t & real x} \<noteq> 0" using that by (simp add: ereal_less_le p_0_equiv)
  moreover have "(\<lambda>s. $p_{s & real x}) differentiable at t"
  proof -
    have "(\<lambda>s. $l_(real x + s) / $l_(real x)) field_differentiable at t"
      using that apply (intro derivative_intros)
       apply (rewrite add.commute, rewrite field_differentiable_shift[THEN sym])
      by (rewrite add.commute) simp_all
    thus ?thesis
      apply (rewrite differentiable_eq_field_differentiable_real)
      apply (rule field_differentiable_transform_within[where d=d], simp_all add: d_pos)
      apply (rewrite p_l, simp_all) unfolding d_def using dist_real_def by auto
  qed
  ultimately have "$\<mu>_(real x + t) = - deriv (\<lambda>s. $p_{s & real x}) t / $p_{t & real x}"
    using that deriv_t_p_mu by simp
  also have "\<dots> = $q_(real x) / (1 - t*$q_(real x))"
  proof -
    have "\<And>s. dist s t < d \<Longrightarrow> $p_{s & real x} = 1 - s*$q_(real x)"
    proof -
      fix s assume "dist s t < d"
      hence "0 \<le> s" "s \<le> 1" unfolding d_def using that dist_real_def by auto
      thus "$p_{s & real x} = 1 - s*$q_(real x)" by (intro linear_p_q; simp add: that)
    qed
    hence "deriv (\<lambda>s. $p_{s & real x}) t = deriv (\<lambda>s. 1 - s*$q_(real x)) t"
      using d_pos apply (intro deriv_cong_ev, simp_all)
      by (rewrite eventually_nhds_metric) auto
    also have "\<dots> = - $q_(real x)"
      apply (rewrite deriv_diff, simp_all)
      by (rule derivative_intros) auto
    finally have "deriv (\<lambda>s. $p_{s & real x}) t = - $q_(real x)" .
    thus ?thesis using linear_p_q that by simp
  qed
  finally show ?thesis .
qed

definition "exponential_interpolation \<equiv>
  \<forall>(x::nat)(t::real). x+1 < $\<psi> \<longrightarrow> 0 \<le> t \<and> t < 1 \<longrightarrow> $\<mu>_(x+t) = $\<mu>_x"
  \<comment> \<open>Without \<open>x+1 < $\<psi>\<close>, the smooth life table could not be limited.\<close>

lemma exponential_mu: "$\<mu>_(x+t) = $\<mu>_x"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t < 1" for x::nat and t::real
  using that unfolding exponential_interpolation_def by simp

corollary exponential_mu': "$\<mu>_y = $\<mu>_x"
  if exponential_interpolation "x \<le> y" "y < x+1" "x+1 < $\<psi>" for x::nat and y::real
proof -
  let ?t = "y - real x"
  have "0 \<le> ?t" and "?t < 1" using that by simp_all
  moreover have "$\<mu>_y = $\<mu>_(real x + ?t)" by simp
  ultimately show ?thesis using exponential_mu that by presburger
qed

lemma exponential_integral_mu: "integral {x..<x+t} (\<lambda>y. $\<mu>_y) = $\<mu>_x * t"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t \<le> 1" for x::nat and t::real
proof -
  have "integral {real x ..< real x + t} (\<lambda>y. $\<mu>_y) = 
    integral {real x ..< real x + t} (\<lambda>y. $\<mu>_(real x))"
    using exponential_mu' that by (intro integral_cong; simp)
  also have "\<dots> = integral {real x .. real x + t} (\<lambda>y. $\<mu>_(real x))"
    apply (rule integral_subset_negligible, force)
    using that by (rewrite Icc_minus_Ico; simp)
  also have "\<dots> = $\<mu>_x * t" using that by (rewrite integral_const_real) simp
  finally show "integral {real x ..< real x + t} (\<lambda>y. $\<mu>_y) = $\<mu>_(real x) * t" .
qed

lemma exponential_p_mu: "$p_x = exp (-$\<mu>_x)" if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof -
  have "$p_x = exp (- integral {real x ..< real x + 1} (\<lambda>y. $\<mu>_y))"
    using that apply (rewrite p_exp_integral_mu; simp add: add.commute)
    apply (rule integral_subset_negligible[THEN sym], force)
    by (rewrite Icc_minus_Ico; simp)
  also have "\<dots> = exp (- $\<mu>_(real x))" using that by (rewrite exponential_integral_mu; simp)
  finally show ?thesis .
qed

corollary exponential_mu_p: "$\<mu>_x = - ln ($p_x)" if exponential_interpolation "x+1 < $\<psi>" for x::nat
  using exponential_p_mu that by simp

corollary exponential_mu_xt_p: "$\<mu>_(x+t) = - ln ($p_x)"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t < 1" for x::nat and t::real
  using that exponential_mu exponential_mu_p by presburger

corollary exponential_q_mu: "$q_x = 1 - exp (-$\<mu>_x)"
  if exponential_interpolation "x+1 < $\<psi>" for x::nat
  using exponential_p_mu that p_q_1
  by (smt (verit, ccfv_SIG) ereal_less_le not_add_less1 of_nat_less_imp_less)

lemma exponential_p: "$p_{t&x} = ($p_x).^t"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t \<le> 1" for x::nat and t::real
proof -
  have [simp]: "real x + t < $\<psi>" using that ereal_less_le by auto
  have "$p_{t & real x} = exp (- integral {real x ..< real x + t} (\<lambda>y. $\<mu>_y))"
    using that apply (rewrite p_exp_integral_mu, simp_all)
    apply (rule integral_subset_negligible[THEN sym], force)
    by (rewrite Icc_minus_Ico; simp)
  also have "\<dots> = exp (- $\<mu>_(real x) * t)"
    using that by (rewrite exponential_integral_mu; simp)
  also have "\<dots> = ($p_(real x)).^t"
    using exponential_p_mu that
    by (smt (verit) exp_not_eq_zero exponential_mu_p mult.commute powr_def)
  finally show ?thesis .
qed

lemma exponential_q: "$q_{t&x} = 1 - (1 - $q_x).^t"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t \<le> 1" for x::nat and t::real
proof -
  have "$q_{t & real x} = 1 - $p_{t & real x}"
    using p_q_1 that by (smt (verit) ereal_less_le le_add1 of_nat_mono)
  also have "\<dots> = 1 - ($p_(real x)).^t" using that by (rewrite exponential_p; simp)
  also have "\<dots> = 1 - (1 - $q_(real x)).^t"
    using p_q_1 that by (smt (verit) ereal_less_le not_add_less1 of_nat_less_imp_less)
  finally show ?thesis .
qed

lemma exponential_l_p: "$l_(x+t) = $l_x * ($p_x).^t"
  if exponential_interpolation "x+1 < $\<psi>" "0 \<le> t" "t \<le> 1" for x::nat and t::real
proof -
  have "ereal (real x) < $\<psi>" using that ereal_less_le by auto
  hence "$l_(real x + t) = $l_x * $p_{t & real x}" using that by (rewrite p_l; simp)
  also have "\<dots> = $l_(real x) * ($p_(real x)).^t" using that by (rewrite exponential_p; simp)
  finally show ?thesis .
qed

lemma exponential_l_has_derivative_at_frac:
  "((\<lambda>s. $l_(x+s)) has_real_derivative (- $l_x * $\<mu>_x * ($p_x).^t)) (at t)"
  if exponential_interpolation "x+1 < $\<psi>" "0 < t" "t < 1" for x::nat and t::real
proof -
  let ?x = "real x"
  have "((\<lambda>s. ($p_?x).^s) has_real_derivative (- $\<mu>_?x * ($p_?x).^t)) (at t)"
    using that exponential_p_mu has_real_derivative_powr2
    by (metis Groups.ab_semigroup_mult_class.mult.commute exp_gt_zero ln_exp)
  hence "((\<lambda>s. $l_?x * ($p_?x).^s) has_real_derivative (- $l_?x * $\<mu>_?x * ($p_?x).^t)) (at t)"
    by (rewrite minus_mult_commute, rewrite mult.assoc) (rule DERIV_cmult)
  moreover have "\<forall>\<^sub>F s in nhds t. $l_(?x + s) = $l_?x * ($p_?x).^s"
  proof -
    let ?r = "min t (1-t)"
    have "?r > 0" using that by simp
    moreover have "\<And>s. dist s t < ?r \<Longrightarrow> $l_(?x + s) = $l_?x * ($p_?x).^s"
      using dist_real_def that exponential_l_p by force
    ultimately show ?thesis using eventually_nhds_metric by blast
  qed
  ultimately show ?thesis by (rewrite DERIV_cong_ev[where g="\<lambda>s. $l_?x * ($p_?x).^s"]; simp)
qed

lemma exponential_l_has_derivative_at_frac':
  "(l has_real_derivative (- $l_x * $\<mu>_x * ($p_x).^(y-x))) (at y)"
  if exponential_interpolation "x+1 < $\<psi>" "x < y" "y < x+1" for x::nat and y::real
  apply (rewrite DERIV_at_within_shift[where x="y - real x" and z="real x" and S=UNIV, simplified])
  using exponential_l_has_derivative_at_frac that by simp

lemma exponential_l_differentiable_on_frac:
  "l differentiable_on {x<..<x+1}" if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof -
  { fix y::real assume "y \<in> {real x <..< real (x+1)}"
    hence "l differentiable at y"
      using exponential_l_has_derivative_at_frac' that real_differentiable_def by auto }
  thus ?thesis unfolding differentiable_on_def by (metis differentiable_at_withinI)
qed

lemma exponential_l_has_right_derivative_at_nat:
  "(l has_real_derivative (- $l_x * $\<mu>_x)) (at_right x)"
  if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof -
  let ?x = "real x"
  have [simp]: "plus ?x ` {0<..} = {?x<..}"
    unfolding image_def greaterThan_def apply simp
    by (metis Groups.ab_semigroup_add_class.add.commute
        add_minus_cancel neg_less_iff_less real_0_less_add_iff)   
  have [simp]: "$p_x > 0" using exponential_p_mu that by auto
  hence [simp]: "$p_x \<noteq> 0" by force
  have "((\<lambda>s. $l_(?x + s)) has_real_derivative (- $l_?x * $\<mu>_?x)) (at_right 0)"
    apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>s. $l_?x * ($p_?x).^s"])
    using exponential_l_p that apply (intro eventually_at_rightI[of 0 1]; simp)
    using powr_zero_eq_one apply simp
    apply (rewrite minus_mult_commute, rule DERIV_cmult)
    apply (rule has_field_derivative_at_within)
    using that apply (rewrite exponential_mu_p; simp)
    using has_real_derivative_powr2[of "$p_x" 0] powr_zero_eq_one by force
  thus ?thesis
    by (rewrite DERIV_at_within_shift[where z="?x" and x=0 and S="{0<..}", simplified]) simp
qed

lemma exponential_l_has_left_derivative_at_nat:
  "(l has_real_derivative (- $l_x * $\<mu>_(real x - 1))) (at_left x)"
  if exponential_interpolation "x < $\<psi>" for x::nat
proof (cases x)
  case 0
  hence "(l has_real_derivative 0) (at_left (real x))"
    apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>_. $l_0"]; simp)
    apply (rule eventually_at_leftI[of "-1"]; simp)
    using l_neg_nil less_eq_real_def by blast
  moreover have "- $l_x * $\<mu>_(real x -1) = 0" using mu_unborn_0 0 by simp
  ultimately show ?thesis by auto
next
  let ?x = "real x"
  case (Suc y)
  let ?y = "real y"
  have [simp]: "?y + 1 = ?x" using Suc by simp
  hence [simp]: "ereal ?y < $\<psi>" using that by (smt (verit) ereal_less_le)
  have [simp]: "$p_?y > 0" using Suc exponential_p_mu that by auto
  have [simp]: "plus ?y ` {..<1} = {..<?x}"
    using Suc unfolding image_def lessThan_def apply simp
    by (metis (no_types, opaque_lifting) Groups.ab_semigroup_add_class.add.commute
        add_less_cancel_right diff_add_cancel)
  have "((\<lambda>t. ($p_?y).^t) has_real_derivative ($p_?y * -$\<mu>_?y)) (at_left 1)"
    apply (rule DERIV_subset[where s=UNIV]; simp)
    using that apply (rewrite exponential_mu_p; simp add: add.commute[of 1 "?y"])
    by (rule has_real_derivative_powr2[of "$p_?y" 1, simplified])
  hence "((\<lambda>t. $l_?y * ($p_?y).^t) has_real_derivative ($l_?y * $p_?y * -$\<mu>_?y)) (at_left 1)"
    by (metis DERIV_cmult mult_ac(1))
  moreover have "$l_?y * $p_?y = $l_?x" using Suc p_1_l by simp
  ultimately have "((\<lambda>t. $l_?y * ($p_?y).^t) has_real_derivative (- $l_?x * $\<mu>_?y)) (at_left 1)"
    by simp
  moreover have "\<forall>\<^sub>F t in at_left 1. $l_(?y + t) = $l_?y * ($p_?y).^t"
    apply (rule eventually_at_leftI[of 0]; simp)
    by (rewrite exponential_l_p; simp add: that add.commute[of 1 "?y"])
  ultimately have "((\<lambda>t. $l_(?y + t)) has_real_derivative (- $l_?x * $\<mu>_?y)) (at_left 1)"
    by (rewrite has_field_derivative_cong_eventually[where g="\<lambda>t. $l_?y * ($p_?y).^t"];
        simp add: p_1_l)
  thus ?thesis
    apply (rewrite DERIV_at_within_shift[where S="{..<1}" and z="?y" and x=1, simplified])
    using Suc by simp
qed

lemma exponential_l_has_derivative_at_nat_iff_mu:
  "(l has_real_derivative (- $l_x * $\<mu>_x)) (at x) \<longleftrightarrow> $\<mu>_x = $\<mu>_(real x - 1)"
  if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof -
  let ?x = "real x"
  have [simp]: "?x < $\<psi>" using that by (simp add: ereal_less_le)
  hence [simp]: "$l_?x \<noteq> 0" by simp
  have "(l has_real_derivative (- $l_?x * $\<mu>_?x)) (at ?x) \<longleftrightarrow>
    (l has_real_derivative (- $l_?x * $\<mu>_?x)) (at_right ?x) \<and>
    (l has_real_derivative (- $l_?x * $\<mu>_?x)) (at_left ?x)"
    using has_real_derivative_at_split by auto
  also have "\<dots> \<longleftrightarrow> - $l_?x * $\<mu>_?x = - $l_?x * $\<mu>_(?x - 1)" (is "?LHS \<longleftrightarrow> ?RHS")
  proof
    assume "?LHS"
    hence "(l has_real_derivative (- $l_?x * $\<mu>_?x)) (at_left ?x)" by simp
    moreover have "(l has_real_derivative (- $l_?x * $\<mu>_(?x - 1))) (at_left ?x)"
      using that exponential_l_has_left_derivative_at_nat by force
    ultimately show "?RHS"
      using has_real_derivative_iff_has_vector_derivative vector_derivative_unique_within
        trivial_limit_at_left_real by blast
  next
    assume "?RHS"
    thus "?LHS"
      using that exponential_l_has_right_derivative_at_nat exponential_l_has_left_derivative_at_nat
      by force
  qed
  also have "\<dots> \<longleftrightarrow> $\<mu>_?x = $\<mu>_(?x - 1)" by simp
  finally show ?thesis .
qed

lemma exponential_l_differentiable_at_nat_iff_mu:
  "l differentiable at x \<longleftrightarrow> $\<mu>_x = $\<mu>_(real x - 1)"
  if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof
  let ?x = "real x"
  assume "l differentiable at ?x"
  from this obtain D where DERIV_l: "(l has_real_derivative D) (at ?x)"
    using real_differentiable_def by blast
  hence "(l has_real_derivative D) (at_right ?x)"
    using has_field_derivative_at_within by blast
  moreover have "at ?x within {real x<..} \<noteq> \<bottom>" by simp
  moreover have "(l has_real_derivative (- $l_real x * $\<mu>_real x)) (at_right ?x)"
    using exponential_l_has_right_derivative_at_nat that by simp
  ultimately have "D = - $l_?x * $\<mu>_?x"
    using that has_real_derivative_iff_has_vector_derivative vector_derivative_unique_within
    by blast
  thus "$\<mu>_?x = $\<mu>_(?x - 1)"
    using exponential_l_has_derivative_at_nat_iff_mu that DERIV_l by blast
next
  assume "$\<mu>_(real x) = $\<mu>_(real x - 1)"
  thus "l differentiable at (real x)"
    using exponential_l_has_derivative_at_nat_iff_mu that real_differentiable_def by blast
qed

lemma exponential_L_d_mu: "$L_x = $d_x / $\<mu>_x"
  if exponential_interpolation "$\<mu>_x \<noteq> 0" "x+1 < $\<psi>" for x::nat
proof -
  have [simp]: "ereal (real x) < $\<psi>" using that ereal_less_le by simp
  have [simp]: "$l_(real x) \<noteq> 0" by simp
  have p_pos[simp]: "$p_(real x) > 0" using that by (simp add: exponential_p_mu)
  have [simp]: "$p_(real x) \<noteq> 1" using that exponential_p_mu by simp
  have "$L_(real x) = (LBINT t:{0..1}. $l_(real x + t))"
    unfolding lives_def by (rewrite lborel_set_integral_Icc_shift[where t=x]) simp
  also have "\<dots> = integral {0..1} (\<lambda>t. $l_(real x + t))"
    by (rule set_borel_integral_eq_integral_nonneg; simp)
  also have "\<dots> = integral {0..1} (\<lambda>t. $l_(real x) * ($p_(real x)).^t)"
    apply (rule integral_cong)
    using that by (rewrite exponential_l_p; simp)
  also have "\<dots> = $l_(real x) * integral {0..1} (\<lambda>t. ($p_(real x)).^t)"
    using integral_mult_right by blast
  also have "\<dots> = $l_(real x) * ($q_(real x) / - ln ($p_(real x)))"
  proof -
    have "integral {0..1} (\<lambda>t. ($p_(real x)).^t) = (($p_(real x)).^1 - 1) / ln ($p_(real x))"
      apply (rule integral_unique)
      by (intro has_integral_powr2_from_0; simp)
    also have "\<dots> = $q_(real x) / - ln ($p_(real x))"
      using p_pos apply (rewrite powr_one, linarith)
      using that by (rewrite in "_ - \<hole>" p_q_1[of x 1, THEN sym]; simp)
    finally show ?thesis by simp
  qed
  also have "\<dots> = $d_(real x) / $\<mu>_(real x)" using that exponential_mu_p by (rewrite q_d_l; simp)
  finally show ?thesis .
qed

lemma exponential_mx_mu: "$m_x = $\<mu>_x" if exponential_interpolation "x+1 < $\<psi>" for x::nat
proof (cases \<open>$\<mu>_(real x) = 0\<close>)
  have lx_neq0: "$l_(real x) \<noteq> 0" using ereal_less_le that by simp
  case True
  hence "$q_(real x) = 0" using exponential_q_mu that by simp
  hence "$d_(real x) = 0"
    using q_1_d_l that by (metis lx_neq0 d_old_0 divide_eq_0_iff linorder_not_less zero_le_one)
  hence "$m_(real x) = 0" unfolding die_central_def by simp
  also have "\<dots> = $\<mu>_(real x)" using True by simp
  finally show ?thesis .
next
  case False
  thus ?thesis unfolding die_central_def using exponential_L_d_mu that
    by (smt (verit) divide_eq_0_iff divide_mult_cancel exp_eq_one_iff exponential_q_mu
        linorder_not_less mu_beyond_0 nonzero_mult_div_cancel_left q_1_d_l)
qed

lemma exponential_d_mu_sums_T: "(\<lambda>k. $d_(x+k) / $\<mu>_(x+k)) sums $T_x"
  if exponential_interpolation total_finite "\<And>k::nat. $\<mu>_(x+k) \<noteq> 0" for x::nat
proof -
  have "\<not> $\<psi> < \<infinity>"
  proof
    assume "$\<psi> < \<infinity>"
    from this obtain y::nat where "$\<psi> < ereal (real y)" using less_PInf_Ex_of_nat by fastforce
    hence xy: "$\<psi> < ereal (real (x+y))" by (simp add: less_ereal_le)
    hence "$\<mu>_(real (x+y)) \<noteq> 0" using that by simp
    moreover have "$\<mu>_(real (x+y)) = 0" using xy mu_beyond_0 by simp
    ultimately show False ..
  qed
  hence "$\<psi> = \<infinity>" by simp
  moreover hence "\<And>k::nat. $d_(real (x+k)) / $\<mu>_(real (x+k)) = $L_(real (x+k))"
    using that by (rewrite exponential_L_d_mu; simp)
  ultimately show ?thesis
    apply (rewrite sums_cong; simp)
    by (rule L_sums_T, simp add: that)
qed

lemma exponential_e_d_l_mu: "(\<lambda>k. $d_(x+k) / ($l_x * $\<mu>_(x+k))) sums $e`\<circ>_x"
  if exponential_interpolation total_finite "\<And>k::nat. $\<mu>_(x+k) \<noteq> 0" for x::nat
proof -
  let ?x = "real x"
  have "\<not> ereal ?x \<ge> $\<psi>" using that mu_beyond_0 by (metis add_cancel_right_right)
  hence [simp]: "ereal ?x < $\<psi>" by simp
  have "(\<lambda>k. $d_(real (x+k)) / $\<mu>_(real (x+k)) / $l_?x) sums ($T_?x / $l_?x)"
    using sums_divide exponential_d_mu_sums_T that by force
  thus ?thesis by (rewrite e_T_l; simp add: mult.commute)
qed

end

subsection \<open>Limited Life Table\<close>

locale limited_life_table = life_table +
  assumes l_limited: "\<exists>x::real. $l_x = 0"
begin

lemma limited_survival_function_MM_X: "limited_survival_function \<MM> X"
proof (rule limited_survival_function.intro)
  show "survival_model \<MM> X" by (rule survival_model_MM_X)
  show "limited_survival_function_axioms \<MM> X"
    unfolding limited_survival_function_axioms_def using l_limited death_pt_def by fastforce
qed

end

sublocale limited_life_table \<subseteq> limited_survival_function \<MM> X
  by (rule limited_survival_function_MM_X)

context limited_life_table
begin

notation ult_age ("$\<omega>")

lemma l_omega_0: "$l_$\<omega> = 0"
  using ccdfX_l_normal ccdfX_omega_0 by simp

lemma l_0_equiv_nat: "$l_x = 0 \<longleftrightarrow> x \<ge> $\<omega>" for x::nat
  using ccdfX_l_normal ccdfX_0_equiv_nat by simp

lemma d_l_equiv_nat: "$d_{t&x} = $l_x \<longleftrightarrow> x+t \<ge> $\<omega>" if "t \<ge> 0" for x t :: nat
  by (metis d_l_equiv of_nat_0_le_iff of_nat_add psi_le_iff_omega_le)

corollary d_1_omega_l: "$d_($\<omega>-1) = $l_($\<omega>-1)"
  using d_l_equiv_nat[of 1 "$\<omega>-1"] omega_pos by simp

lemma limited_life_table_imp_total_finite: total_finite
proof -
  have "{0..} = {0 .. real $\<omega>} \<union> {real $\<omega> <..}" by force
  moreover have "set_integrable lborel {0 .. real $\<omega>} l" by (rule l_integrable_Icc)
  moreover have "set_integrable lborel {real $\<omega> <..} l"
    apply (rewrite set_integrable_cong[where f'="\<lambda>_. 0"], simp_all)
    using l_0_equiv_nat apply (meson l_0_equiv le_ereal_le order_le_less)
    unfolding set_integrable_def by simp
  ultimately have "set_integrable lborel {0..} l"
    using set_integrable_Un
    by (smt (verit, del_insts) Ici_subset_Ioi_iff add_mono_thms_linordered_field(1)
        atLeast_borel l_0_pos set_integrable_subset sets_lborel total_finite_iff_set_integrable_Ici)
  thus ?thesis unfolding total_finite_def by simp
qed

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
