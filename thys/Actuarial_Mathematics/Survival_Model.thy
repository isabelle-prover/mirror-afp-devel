theory Survival_Model
  imports "HOL-Library.Rewrite" "HOL-Library.Extended_Nonnegative_Real" "HOL-Library.Extended_Real"
    "HOL-Probability.Probability" Preliminaries
begin

section \<open>Survival Model\<close>

text \<open>
  The survival model is built on the probability space @{text "\<MM>"}.
  Additionally, the random variable @{text "X : space \<MM> \<rightarrow> \<real>"} is introduced,
  which represents the age at death.
\<close>

locale prob_space_actuary = MM_PS: prob_space \<MM> for \<MM> 
  \<comment> \<open>Since the letter M may be used as a commutation function,
      adopt the letter @{text "\<MM>"} instead as a notation for the measure space.\<close>

locale survival_model = prob_space_actuary +
  fixes X :: "'a \<Rightarrow> real"
  assumes X_RV[simp]: "MM_PS.random_variable (borel :: real measure) X"
    and X_pos_AE[simp]: "AE \<xi> in \<MM>. X \<xi> > 0"
begin

subsection \<open>General Theory of Survival Model\<close>

interpretation distrX_RD: real_distribution "distr \<MM> borel X"
  using MM_PS.real_distribution_distr by simp

lemma X_le_event[simp]: "{\<xi> \<in> space \<MM>. X \<xi> \<le> x} \<in> MM_PS.events"
  by measurable simp

lemma X_gt_event[simp]: "{\<xi> \<in> space \<MM>. X \<xi> > x} \<in> MM_PS.events"
  by measurable simp

lemma X_compl_le_gt: "space \<MM> - {\<xi> \<in> space \<MM>. X \<xi> \<le> x} = {\<xi> \<in> space \<MM>. X \<xi> > x}" for x::real
proof -
  have "space \<MM> - {\<xi> \<in> space \<MM>. X \<xi> \<le> x} = space \<MM> - (X -` {..x})" by blast
  also have "\<dots> = (X -` {x<..}) \<inter> space \<MM>" using vimage_compl_atMost by fastforce
  also have "\<dots> = {\<xi> \<in> space \<MM>. X \<xi> > x}" by blast
  finally show ?thesis .
qed

lemma X_compl_gt_le: "space \<MM> - {\<xi> \<in> space \<MM>. X \<xi> > x} = {\<xi> \<in> space \<MM>. X \<xi> \<le> x}" for x::real
  using X_compl_le_gt by blast

subsubsection \<open>Introduction of Survival Function for X\<close>

text \<open>Note that @{text "ccdf (distr \<MM> borel X)"} is the survival (distributive) function for X.\<close>

lemma ccdfX_0_1: "ccdf (distr \<MM> borel X) 0 = 1"
  apply (rewrite MM_PS.ccdf_distr_P, simp)
  using X_pos_AE MM_PS.prob_space
  using MM_PS.prob_Collect_eq_1 X_gt_event by presburger

lemma ccdfX_unborn_1: "ccdf (distr \<MM> borel X) x = 1" if "x \<le> 0"
proof (rule antisym)
  show "ccdf (distr \<MM> borel X) x \<le> 1" using MM_PS.ccdf_distr_P by simp
  show "ccdf (distr \<MM> borel X) x \<ge> 1"
  proof -
    have "ccdf (distr \<MM> borel X) x \<ge> ccdf (distr \<MM> borel X) 0"
      using finite_borel_measure.ccdf_nonincreasing distrX_RD.finite_borel_measure_M that by simp
    also have "ccdf (distr \<MM> borel X) 0 = 1" using ccdfX_0_1 that by simp
    finally show ?thesis .
  qed
qed

definition death_pt :: ereal ("$\<psi>")
  where "$\<psi> \<equiv> Inf (ereal ` {x \<in> \<real>. ccdf (distr \<MM> borel X) x = 0})"
    \<comment> \<open>This is my original notation,
        which is used to develop life insurance mathematics rigorously.\<close>

lemma psi_nonneg: "$\<psi> \<ge> 0"
  unfolding death_pt_def
proof (rule Inf_greatest)
  fix x'::ereal
  assume "x' \<in> ereal ` {x \<in> \<real>. ccdf (distr \<MM> borel X) x = 0}"
  then obtain x::real where "x' = ereal x" and "ccdf (distr \<MM> borel X) x = 0" by blast
  hence "ccdf (distr \<MM> borel X) 0 > ccdf (distr \<MM> borel X) x" using ccdfX_0_1 X_pos_AE by simp
  hence "x \<ge> 0"
    using mono_invE finite_borel_measure.ccdf_nonincreasing distrX_RD.finite_borel_measure_M X_RV
    by (smt(verit))
  thus "x' \<ge> 0" using \<open>x' = ereal x\<close> by simp
qed

lemma ccdfX_beyond_0: "ccdf (distr \<MM> borel X) x = 0" if "x > $\<psi>" for x::real
proof -
  have "ereal ` {y \<in> \<real>. ccdf (distr \<MM> borel X) y = 0} \<noteq> {}" using death_pt_def that by force
  hence "\<exists>y'\<in>(ereal ` {y \<in> \<real>. ccdf (distr \<MM> borel X) y = 0}). y' < ereal x"
    using that unfolding death_pt_def by (rule cInf_lessD)
  then obtain "y'"
    where "y' \<in> (ereal ` {y \<in> \<real>. ccdf (distr \<MM> borel X) y = 0})" and "y' < ereal x" by blast
  then obtain y::real
    where "y' = ereal y" and "ccdf (distr \<MM> borel X) y = 0" and "ereal y < ereal x" by blast
  hence "ccdf (distr \<MM> borel X) y = 0" and "y < x" by simp_all
  hence "ccdf (distr \<MM> borel X) x \<le> 0"
    using finite_borel_measure.ccdf_nonincreasing distrX_RD.finite_borel_measure_M X_RV
    by (metis order_less_le)
  thus ?thesis using finite_borel_measure.ccdf_nonneg distrX_RD.finite_borel_measure_M X_RV by smt
qed

lemma ccdfX_psi_0: "ccdf (distr \<MM> borel X) (real_of_ereal $\<psi>) = 0" if "$\<psi> < \<infinity>"
proof -
  have "\<bar>$\<psi>\<bar> \<noteq> \<infinity>" using that psi_nonneg by simp
  then obtain u::real where "$\<psi> = ereal u" using ereal_real' by blast
  hence "real_of_ereal $\<psi> = u" by simp
  moreover have "ccdf (distr \<MM> borel X) u = 0"
  proof -
    have "\<And>x::real. x \<noteq> u \<Longrightarrow> x \<in> {u<..} \<Longrightarrow> ccdf (distr \<MM> borel X) x = 0"
      by (rule ccdfX_beyond_0, simp add: \<open>$\<psi> = ereal u\<close>)
    hence "(ccdf (distr \<MM> borel X) \<longlongrightarrow> 0) (at_right u)"
      apply -
      by (rule iffD2[OF Lim_cong_within[where ?g="(\<lambda>x.0)"]], simp_all+)
    moreover have "(ccdf (distr \<MM> borel X) \<longlongrightarrow> ccdf (distr \<MM> borel X) u) (at_right u)"
      using finite_borel_measure.ccdf_is_right_cont distrX_RD.finite_borel_measure_M
        continuous_within X_RV by blast
    ultimately show ?thesis using tendsto_unique trivial_limit_at_right_real by blast
  qed
  ultimately show ?thesis by simp
qed

lemma ccdfX_0_equiv: "ccdf (distr \<MM> borel X) x = 0 \<longleftrightarrow> x \<ge> $\<psi>" for x::real
proof
  assume "ccdf (distr \<MM> borel X) x = 0"
  thus "ereal x \<ge> $\<psi>" unfolding death_pt_def by (simp add: INF_lower)
next
  assume "$\<psi> \<le> ereal x"
  hence "$\<psi> = ereal x \<or> $\<psi> < ereal x" unfolding less_eq_ereal_def by auto
  thus "ccdf (distr \<MM> borel X) x = 0"
  proof
    assume \<star>: "$\<psi> = ereal x"
    hence "$\<psi> < \<infinity>" by simp
    moreover have "real_of_ereal $\<psi> = x" using \<star> by simp
    ultimately show "ccdf (distr \<MM> borel X) x = 0" using ccdfX_psi_0 by simp
  next
    assume "$\<psi> < ereal x"
    thus "ccdf (distr \<MM> borel X) x = 0" by (rule ccdfX_beyond_0)
  qed
qed

lemma psi_pos[simp]: "$\<psi> > 0"
proof (rule not_le_imp_less, rule notI)
  show "$\<psi> \<le> (0::ereal) \<Longrightarrow> False"
  proof -
    assume "$\<psi> \<le> (0::ereal)"
    hence "ccdf (distr \<MM> borel X) 0 = 0" using ccdfX_0_equiv by (simp add: zero_ereal_def)
    moreover have "ccdf (distr \<MM> borel X) 0 = 1" using ccdfX_0_1 by simp
    ultimately show "False" by simp
  qed
qed

corollary psi_pos'[simp]: "$\<psi> > ereal 0"
  using psi_pos zero_ereal_def by presburger

subsubsection \<open>Introdution of Future-Lifetime Random Variable T(x)\<close>

definition alive :: "real \<Rightarrow> 'a set"
  where "alive x \<equiv> {\<xi> \<in> space \<MM>. X \<xi> > x}"

lemma alive_event[simp]: "alive x \<in> MM_PS.events" for x::real
  unfolding alive_def by simp

lemma X_alivex_measurable[measurable, simp]: "X \<in> borel_measurable (\<MM> \<downharpoonright> alive x)" for x::real
  unfolding cond_prob_space_def by (measurable; simp add: measurable_restrict_space1)

definition futr_life :: "real \<Rightarrow> ('a \<Rightarrow> real)" ("T")
  where "T x \<equiv> (\<lambda>\<xi>. X \<xi> - x)"
    \<comment> \<open>Note that @{text "T(x) : space \<MM> \<rightarrow> \<real>"} represents the time until death of a person aged x.\<close>

lemma T0_eq_X[simp]: "T 0 = X"
  unfolding futr_life_def by simp

lemma Tx_measurable[measurable, simp]: "T x \<in> borel_measurable \<MM>" for x::real
  unfolding futr_life_def by (simp add: borel_measurable_diff)

lemma Tx_alivex_measurable[measurable, simp]: "T x \<in> borel_measurable (\<MM> \<downharpoonright> alive x)" for x::real
  unfolding futr_life_def by (simp add: borel_measurable_diff)

lemma alive_T: "alive x = {\<xi> \<in> space \<MM>. T x \<xi> > 0}" for x::real
  unfolding alive_def futr_life_def by force

lemma alivex_Tx_pos[simp]: "0 < T x \<xi>" if "\<xi> \<in> space (\<MM> \<downharpoonright> alive x)" for x::real
  using MM_PS.space_cond_prob_space alive_T that by simp

lemma PT0_eq_PX_lborel: "\<P>(\<xi> in \<MM>. T 0 \<xi> \<in> A \<bar> T 0 \<xi> > 0) = \<P>(\<xi> in \<MM>. X \<xi> \<in> A)"
  if "A \<in> sets lborel" for A :: "real set"
  apply (rewrite MM_PS.cond_prob_AE_prob, simp_all)
  using that X_RV measurable_lborel1 predE pred_sets2 by blast

subsubsection \<open>Actuarial Notations on the Survival Model\<close>

definition survive :: "real \<Rightarrow> real \<Rightarrow> real" ("$p'_{_&_}" [0,0] 200)
  where "$p_{t&x} \<equiv> ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t"
    \<comment> \<open>the probability that a person aged x will survive for t years\<close>
    \<comment> \<open>Note that the function @{text "$p_{\<cdot>&x}"} is the survival function
        on @{text "(\<MM> \<downharpoonright> alive x)"} for the random variable T(x).\<close>
    \<comment> \<open>The parameter t is usually nonnegative, but theoretically it can be negative.\<close>
abbreviation survive_1 :: "real \<Rightarrow> real" ("$p'__" [101] 200)
  where "$p_x \<equiv> $p_{1&x}"
definition die :: "real \<Rightarrow> real \<Rightarrow> real" ("$q'_{_&_}" [0,0] 200)
  where "$q_{t&x} \<equiv> cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t"
    \<comment> \<open>the probability that a person aged x will die within t years\<close>
    \<comment> \<open>Note that the function @{text "$q_{\<cdot>&x}"} is the cumulative distributive function
        on @{text "(\<MM> \<downharpoonright> alive x)"} for the random variable T(x).\<close>
    \<comment> \<open>The parameter t is usually nonnegative, but theoretically it can be negative.\<close>
abbreviation die_1 :: "real \<Rightarrow> real" ("$q'__" [101] 200)
  where "$q_x \<equiv> $q_{1&x}"
definition die_defer :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" ("$q'_{_\<bar>_&_}" [0,0,0] 200)
  where "$q_{f\<bar>t&x} = \<bar>$q_{f+t&x} - $q_{f&x}\<bar>"
    \<comment> \<open>the probability that a person aged x will die within t years, deferred f years\<close>
    \<comment> \<open>The parameters f and t are usually nonnegative, but theoretically they can be negative.\<close>
abbreviation die_defer_1 :: "real \<Rightarrow> real \<Rightarrow> real" ("$q'_{_\<bar>&_}" [0,0] 200)
  where "$q_{f\<bar>&x} \<equiv> $q_{f\<bar>1&x}"
definition life_expect :: "real \<Rightarrow> real" ("$e`\<circ>'__" [101] 200)
  where "$e`\<circ>_x \<equiv> integral\<^sup>L (\<MM> \<downharpoonright> alive x) (T x)"
    \<comment> \<open>complete life expectation\<close>
    \<comment> \<open>Note that @{text "$e`\<circ>_x"} is calculated as 0
        when @{text "nn_integral (\<MM> \<downharpoonright> alve x) (T x) = \<infinity>"}.\<close>
definition temp_life_expect :: "real \<Rightarrow> real \<Rightarrow>real" ("$e`\<circ>'_{_:_}" [0,0] 200)
  where "$e`\<circ>_{x:n} \<equiv> integral\<^sup>L (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. min (T x \<xi>) n)"
    \<comment> \<open>temporary complete life expectation\<close>
definition curt_life_expect :: "real \<Rightarrow> real" ("$e'__" [101] 200)
  where "$e_x \<equiv> integral\<^sup>L (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. \<lfloor>T x \<xi>\<rfloor>)"
    \<comment> \<open>curtate life expectation\<close>
    \<comment> \<open>Note that @{text "$e_x"} is calculated as 0 when
        @{text "nn_integral (\<MM> \<downharpoonright> alive x) \<lfloor>T x\<rfloor> = \<infinity>"}.\<close>
definition temp_curt_life_expect :: "real \<Rightarrow> real \<Rightarrow> real" ("$e'_{_:_}" [0,0] 200)
  where "$e_{x:n} \<equiv> integral\<^sup>L (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. \<lfloor>min (T x \<xi>) n\<rfloor>)"
    \<comment> \<open>temporary curtate life expectation\<close>
    \<comment> \<open>In the definition n can be a real number, but in practice n is usually a natural number.\<close>

subsubsection \<open>Properties of Survival Function for T(x)\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

lemma PXx_pos[simp]: "\<P>(\<xi> in \<MM>. X \<xi> > x) > 0"
proof -
  have "\<P>(\<xi> in \<MM>. X \<xi> > x) = ccdf (distr \<MM> borel X) x"
    unfolding alive_def using MM_PS.ccdf_distr_P by simp
  also have "\<dots> > 0"
    using ccdfX_0_equiv distrX_RD.ccdf_nonneg x_lt_psi by (smt (verit) linorder_not_le)
  finally show ?thesis .
qed

lemma PTx_pos[simp]: "\<P>(\<xi> in \<MM>. T x \<xi> > 0) > 0"
  apply (rewrite alive_T[THEN sym])
  unfolding alive_def by simp

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct, simp_all add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma ccdfTx_cond_prob:
  "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = \<P>(\<xi> in \<MM>. T x \<xi> > t \<bar> T x \<xi> > 0)" for t::real
  apply (rewrite alivex_PS.ccdf_distr_P, simp)
  unfolding alive_def
  apply (rewrite MM_PS.cond_prob_space_cond_prob[THEN sym], simp_all add: pred_def)
  unfolding futr_life_def by simp

lemma ccdfTx_0_1: "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) 0 = 1"
  apply (rewrite ccdfTx_cond_prob)
  unfolding futr_life_def cond_prob_def
  by (smt (verit, best) Collect_cong PXx_pos divide_eq_1_iff)

lemma ccdfTx_nonpos_1: "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 1" if "t \<le> 0" for t :: real
  using antisym ccdfTx_0_1 that
  by (metis distrTx_RD.ccdf_bounded_prob distrTx_RD.ccdf_nonincreasing)

lemma ccdfTx_0_equiv: "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 0 \<longleftrightarrow> x+t \<ge> $\<psi>" for t::real
proof -
  have "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t =
    \<P>(\<xi> in \<MM>. X \<xi> > x+t \<and> X \<xi> > x) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    apply (rewrite ccdfTx_cond_prob)
    unfolding cond_prob_def futr_life_def by (smt (verit) Collect_cong)
  hence "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 0 \<longleftrightarrow>
    \<P>(\<xi> in \<MM>. X \<xi> > x+t \<and> X \<xi> > x) / \<P>(\<xi> in \<MM>. X \<xi> > x) = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> \<P>(\<xi> in \<MM>. X \<xi> > x+t \<and> X \<xi> > x) = 0"
    using x_lt_psi PXx_pos by (smt (verit) divide_eq_0_iff)
  also have "\<dots> \<longleftrightarrow> x+t \<ge> $\<psi>"
    using ccdfX_0_equiv MM_PS.ccdf_distr_P
    by (smt (verit) Collect_cong X_RV le_ereal_le linorder_not_le x_lt_psi)
  finally show ?thesis .
qed

lemma ccdfTx_continuous_on_nonpos[simp]:
  "continuous_on {..0} (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  by (metis atMost_iff ccdfTx_nonpos_1 continuous_on_cong continuous_on_const)

lemma ccdfTx_differentiable_on_nonpos[simp]:
  "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable_on {..0}"
  by (rewrite differentiable_on_cong[where f="\<lambda>_. 1"]; simp add: ccdfTx_nonpos_1)

lemma ccdfTx_has_real_derivative_0_at_neg:
  "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative 0) (at t)" if "t < 0" for t::real
  apply (rewrite has_real_derivative_iff_has_vector_derivative)
  apply (rule has_vector_derivative_transform_within_open[of "\<lambda>_. 1" _ _ "{..<0}"])
  using ccdfTx_nonpos_1 that by simp_all

lemma ccdfTx_integrable_Icc:
  "set_integrable lborel {a..b} (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))" for a b :: real
proof -
  have "(\<integral>\<^sup>+t. ennreal (indicat_real {a..b} t * ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t) \<partial>lborel)
    < \<top>"
  proof -
    have "(\<integral>\<^sup>+t. ennreal (indicat_real {a..b} t * ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t) \<partial>lborel)
      \<le> (\<integral>\<^sup>+t. ennreal (indicat_real {a..b} t) \<partial>lborel)"
      apply (rule nn_integral_mono)
      using distrTx_RD.ccdf_bounded
      by (simp add: distrTx_RD.ccdf_bounded_prob indicator_times_eq_if(1))
    also have "\<dots> = nn_integral lborel (indicator {a..b})" by (meson ennreal_indicator)
    also have "\<dots> = emeasure lborel {a..b}" by (rewrite nn_integral_indicator; simp)
    also have "\<dots> < \<top>"
      using emeasure_lborel_Icc_eq ennreal_less_top infinity_ennreal_def by presburger
    finally show ?thesis .
  qed
  thus ?thesis
    unfolding set_integrable_def
    apply (intro integrableI_nonneg, simp_all)
    using distrTx_RD.ccdf_nonneg by (intro always_eventually) auto
qed

corollary ccdfTx_integrable_on_Icc:
  "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) integrable_on {a..b}" for a b :: real
  using set_borel_integral_eq_integral ccdfTx_integrable_Icc by force

lemma ccdfTx_PX:
  "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = \<P>(\<xi> in \<MM>. X \<xi> > x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
  if "t \<ge> 0" for t::real
  apply (rewrite ccdfTx_cond_prob)
  unfolding cond_prob_def futr_life_def PXx_pos by (smt (verit) Collect_cong that)

lemma ccdfTx_ccdfX: "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t =
  ccdf (distr \<MM> borel X) (x + t) / ccdf (distr \<MM> borel X) x"
  if "t \<ge> 0" for t::real
  using ccdfTx_PX that MM_PS.ccdf_distr_P X_RV by presburger

lemma ccdfT0_eq_ccdfX: "ccdf (distr (\<MM> \<downharpoonright> alive 0) borel (T 0)) = ccdf (distr \<MM> borel X)"
proof
  fix x
  show "ccdf (distr (\<MM> \<downharpoonright> alive 0) borel (T 0)) x = ccdf (distr \<MM> borel X) x"
  proof (cases \<open>x \<ge> 0\<close>)
    case True
    thus ?thesis
      using survival_model.ccdfTx_ccdfX[where x=0] ccdfX_0_1 survival_model_axioms by fastforce
  next
    case False
    hence "x \<le> 0" by simp
    thus ?thesis
      apply (rewrite ccdfX_unborn_1, simp)
      by (rewrite survival_model.ccdfTx_nonpos_1; simp add: survival_model_axioms)
  qed
qed

lemma continuous_ccdfX_ccdfTx:
  "continuous (at (x+t) within {x..}) (ccdf (distr \<MM> borel X)) \<longleftrightarrow> 
    continuous (at t within {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  if "t \<ge> 0" for t::real
proof -
  let ?srvl = "ccdf (distr \<MM> borel X)"
  have [simp]: "\<P>(\<xi> in \<MM>. X \<xi> > x) \<noteq> 0" using PXx_pos by force
  have \<star>: "\<And>u. u \<ge> 0 \<Longrightarrow> ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) u =
    ?srvl (x + u) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    using survive_def MM_PS.ccdf_distr_P ccdfTx_PX that by simp
  have "continuous (at t within {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) \<longleftrightarrow>
    continuous (at t within {0..}) (\<lambda>u. ?srvl (x+u) / \<P>(\<xi> in \<MM>. x < X \<xi>))"
  proof -
    have "\<forall>\<^sub>F u in at t within {0..}. ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) u =
    ?srvl (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
      using \<star> by (rewrite eventually_at_topological, simp_all) blast
    thus ?thesis
      by (intro continuous_at_within_cong, simp_all add: \<star> that)
  qed
  also have "\<dots> \<longleftrightarrow> continuous (at t within {0..}) (\<lambda>u. ?srvl (x+u))"
    by (rewrite at "_ = \<hole>" continuous_cdivide_iff[of "\<P>(\<xi> in \<MM>. X \<xi> > x)"], simp_all)
  also have "\<dots> \<longleftrightarrow> continuous (at (x+t) within {x..}) ?srvl"
  proof
    let ?subx = "\<lambda>v. v-x"
    assume LHS: "continuous (at t within {0..}) (\<lambda>u. ?srvl (x+u))"
    hence "continuous (at (?subx (x+t)) within ?subx ` {x..}) (\<lambda>u. ?srvl (x+u))"
    proof -
      have "?subx ` {x..} = {0..}"
        by (metis (no_types, lifting) add.commute add_uminus_conv_diff diff_self
            image_add_atLeast image_cong)
      thus ?thesis using LHS by simp
    qed
    moreover have "continuous (at (x+t) within {x..}) ?subx" by (simp add: continuous_diff)
    ultimately have "continuous (at (x+t) within {x..}) (\<lambda>u. ?srvl (x + (?subx u)))"
      using continuous_within_compose2 by force
    thus "continuous (at (x+t) within {x..}) ?srvl" by simp
  next
    assume RHS: "continuous (at (x+t) within {x..}) ?srvl"
    hence "continuous (at ((plus x) t) within (plus x) ` {0..}) ?srvl" by simp
    moreover have "continuous (at t within {0..}) (plus x)" by (simp add: continuous_add)
    ultimately show "continuous (at t within {0..}) (\<lambda>u. ?srvl (x+u))"
      using continuous_within_compose2 by force
  qed
  finally show ?thesis by simp
qed

lemma isCont_ccdfX_ccdfTx:
  "isCont (ccdf (distr \<MM> borel X)) (x+t) \<longleftrightarrow>
    isCont (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t"
  if "t > 0" for t::real
proof -
  have "isCont (ccdf (distr \<MM> borel X)) (x+t) \<longleftrightarrow>
    continuous (at (x+t) within {x<..}) (ccdf (distr \<MM> borel X))"
    by (smt (verit) at_within_open greaterThan_iff open_greaterThan that)
  also have "\<dots> \<longleftrightarrow> continuous (at (x+t) within {x..}) (ccdf (distr \<MM> borel X))"
    by (meson Ioi_le_Ico calculation continuous_within_subset top_greatest)
  also have "\<dots> \<longleftrightarrow> continuous (at t within {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    using that continuous_ccdfX_ccdfTx by force
  also have "\<dots> \<longleftrightarrow> continuous (at t within {0<..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    by (metis Ioi_le_Ico at_within_open continuous_at_imp_continuous_at_within
        continuous_within_subset greaterThan_iff open_greaterThan that)
  also have "\<dots> \<longleftrightarrow> isCont (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t"
    by (metis at_within_open greaterThan_iff open_greaterThan that)
  finally show ?thesis .
qed

lemma has_real_derivative_ccdfX_ccdfTx:
  "((ccdf (distr \<MM> borel X)) has_real_derivative D) (at (x+t)) \<longleftrightarrow>
  ((ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) has_real_derivative (D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
  if "t > 0" for t D :: real
proof -
  have "((ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) has_real_derivative
    (D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t) \<longleftrightarrow>
    ((\<lambda>t. (ccdf (distr \<MM> borel X)) (x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)) has_real_derivative
    (D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
  proof -
    let ?d = "t/2"
    { fix u::real assume "dist u t < ?d"
      hence "u > 0" by (smt (verit) dist_real_def dist_triangle_half_r)
      hence "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) u =
        ccdf (distr \<MM> borel X) (x + u) / MM_PS.prob {\<xi>::'a \<in> space \<MM>. x < X \<xi>}"
        using survive_def MM_PS.ccdf_distr_P ccdfTx_PX that by simp }
    moreover have "?d > 0" using that by simp
    ultimately show ?thesis
      apply -
      apply (rule DERIV_cong_ev, simp)
       apply (rewrite eventually_nhds_metric, blast)
      by simp
  qed
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. (ccdf (distr \<MM> borel X)) (x+t)) has_real_derivative D) (at t)"
    using PXx_pos by (rewrite DERIV_cdivide_iff[of "\<P>(\<xi> in \<MM>. X \<xi> > x)", THEN sym]; force)
  also have "\<dots> \<longleftrightarrow> (ccdf (distr \<MM> borel X) has_real_derivative D) (at (x+t))"
    by (simp add: DERIV_shift add.commute)
  finally show ?thesis by simp
qed

lemma differentiable_ccdfX_ccdfTx:
  "(ccdf (distr \<MM> borel X)) differentiable at (x+t) \<longleftrightarrow>
  (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable at t"
  if "t > 0" for t::real
  apply (rewrite differentiable_eq_field_differentiable_real)+
  unfolding field_differentiable_def using has_real_derivative_ccdfX_ccdfTx that
  by (smt (verit, del_insts) PXx_pos nonzero_mult_div_cancel_left)

subsubsection \<open>Properties of @{text "$p_{t&x}"}\<close>

lemma p_0_1: "$p_{0&x} = 1"
  unfolding survive_def using ccdfTx_0_1 by simp

lemma p_nonneg[simp]: "$p_{t&x} \<ge> 0" for t::real
  unfolding survive_def using distrTx_RD.ccdf_nonneg by simp

lemma p_0_equiv: "$p_{t&x} = 0 \<longleftrightarrow> x+t \<ge> $\<psi>" for t::real
  unfolding survive_def by (rule ccdfTx_0_equiv)

lemma p_PTx: "$p_{t&x} = \<P>(\<xi> in \<MM>. T x \<xi> > t \<bar> T x \<xi> > 0)" for t::real
  unfolding survive_def using ccdfTx_cond_prob by simp

lemma p_PX: "$p_{t&x} = \<P>(\<xi> in \<MM>. X \<xi> > x + t) / \<P>(\<xi> in \<MM>. X \<xi> > x)" if "t \<ge> 0" for t::real
  unfolding survive_def using ccdfTx_PX that by simp

lemma p_mult: "$p_{t+t' & x} = $p_{t&x} * $p_{t' & x+t}"
  if "t \<ge> 0" "t' \<ge> 0" "x+t < $\<psi>" for t t' :: real
proof -
  have "$p_{t+t' & x} = \<P>(\<xi> in \<MM>. X \<xi> > x+t+t') / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    apply (rewrite p_PX; (simp add: that)?)
    by (rule disjI2, smt (verit, best) Collect_cong)
  also have "\<dots> = (\<P>(\<xi> in \<MM>. X \<xi> > x+t+t') / \<P>(\<xi> in \<MM>. X \<xi> > x+t)) *
    (\<P>(\<xi> in \<MM>. X \<xi> > x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x))"
    using that survival_model.PXx_pos survival_model_axioms by fastforce
  also have "\<dots> = $p_{t&x} * $p_{t' & x+t}"
    apply (rewrite p_PX, simp add: that)
    by (rewrite survival_model.p_PX, simp_all add: that survival_model_axioms)
  finally show ?thesis .
qed

lemma p_PTx_ge_ccdf_isCont: "$p_{t&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> t \<bar> T x \<xi> > 0)"
  if "isCont (ccdf (distr \<MM> borel X)) (x+t)" "t > 0" for t::real
  unfolding survive_def using that isCont_ccdfX_ccdfTx
  apply (rewrite alivex_PS.ccdf_continuous_distr_P_ge, simp_all)
  by (rewrite MM_PS.cond_prob_space_cond_prob, simp_all add: alive_T)

end

subsubsection \<open>Properties of Survival Function for X\<close>

lemma ccdfX_continuous_unborn[simp]: "continuous_on {..0} (ccdf (distr \<MM> borel X))"
  using ccdfTx_continuous_on_nonpos by (metis ccdfT0_eq_ccdfX psi_pos')

lemma ccdfX_differentiable_unborn[simp]: "(ccdf (distr \<MM> borel X)) differentiable_on {..0}"
  using ccdfTx_differentiable_on_nonpos by (metis ccdfT0_eq_ccdfX psi_pos')

lemma ccdfX_has_real_derivative_0_unborn:
  "(ccdf (distr \<MM> borel X) has_real_derivative 0) (at x)" if "x < 0" for x::real
  using ccdfTx_has_real_derivative_0_at_neg by (metis ccdfT0_eq_ccdfX psi_pos' that)

lemma ccdfX_integrable_Icc:
  "set_integrable lborel {a..b} (ccdf (distr \<MM> borel X))" for a b :: real
  using ccdfTx_integrable_Icc by (metis ccdfT0_eq_ccdfX psi_pos')

corollary ccdfX_integrable_on_Icc:
  "ccdf (distr \<MM> borel X) integrable_on {a..b}" for a b :: real
  using set_borel_integral_eq_integral ccdfX_integrable_Icc by force

lemma ccdfX_p: "ccdf (distr \<MM> borel X) x = $p_{x&0}" for x::real
  by (metis ccdfT0_eq_ccdfX survive_def psi_pos')

subsubsection \<open>Introduction of Cumulative Distributive Function for X\<close>

lemma cdfX_0_0: "cdf (distr \<MM> borel X) 0 = 0"
  using ccdfX_0_1 distrX_RD.ccdf_cdf distrX_RD.prob_space by fastforce

lemma cdfX_unborn_0: "cdf (distr \<MM> borel X) x = 0" if "x \<le> 0"
  using ccdfX_unborn_1 cdfX_0_0 distrX_RD.cdf_ccdf that by fastforce

lemma cdfX_beyond_1: "cdf (distr \<MM> borel X) x = 1" if "x > $\<psi>" for x::real
  using ccdfX_beyond_0 distrX_RD.cdf_ccdf that distrX_RD.prob_space by force

lemma cdfX_psi_1: "cdf (distr \<MM> borel X) (real_of_ereal $\<psi>) = 1" if "$\<psi> < \<infinity>"
  using ccdfX_psi_0 distrX_RD.cdf_ccdf distrX_RD.prob_space that by fastforce

lemma cdfX_1_equiv: "cdf (distr \<MM> borel X) x = 1 \<longleftrightarrow> x \<ge> $\<psi>" for x::real
  using ccdfX_0_equiv distrX_RD.cdf_ccdf distrX_RD.prob_space by force

subsubsection \<open>Properties of Cumulative Distributive Function for T(x)\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct, simp_all add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma cdfTx_cond_prob:
  "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = \<P>(\<xi> in \<MM>. T x \<xi> \<le> t \<bar> T x \<xi> > 0)" for t::real
  apply (rewrite distrTx_RD.cdf_ccdf, rewrite distrTx_RD.prob_space)
  apply (rewrite ccdfTx_cond_prob, simp)
  by (rewrite not_less[THEN sym], rewrite MM_PS.cond_prob_neg; simp)

lemma cdfTx_0_0: "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) 0 = 0"
  using ccdfTx_0_1 distrTx_RD.cdf_ccdf distrTx_RD.prob_space by force

lemma cdfTx_nonpos_0: "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 0" if "t \<le> 0" for t :: real
  using ccdfTx_nonpos_1 distrTx_RD.cdf_ccdf distrTx_RD.prob_space that by force

lemma cdfTx_1_equiv: "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = 1 \<longleftrightarrow> x+t \<ge> $\<psi>" for t::real
  using ccdfTx_0_equiv distrTx_RD.cdf_ccdf distrTx_RD.prob_space by force

lemma cdfTx_continuous_on_nonpos[simp]:
  "continuous_on {..0} (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  by (rewrite continuous_on_cong[where g="\<lambda>t. 0"]) (simp_all add: cdfTx_nonpos_0)+

lemma cdfTx_differentiable_on_nonpos[simp]:
  "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable_on {..0}"
  by (rewrite differentiable_on_cong[where f="\<lambda>t. 0"]; simp add: cdfTx_nonpos_0)

lemma cdfTx_has_real_derivative_0_at_neg:
  "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative 0) (at t)" if "t < 0" for t::real
  apply (rewrite has_real_derivative_iff_has_vector_derivative)
  apply (rule has_vector_derivative_transform_within_open[of "\<lambda>_. 0" _ _ "{..<0}"])
  using cdfTx_nonpos_0 that by simp_all

lemma cdfTx_integrable_Icc:
  "set_integrable lborel {a..b} (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))" for a b :: real
proof -
  have "set_integrable lborel {a..b} (\<lambda>_. 1::real)"
    unfolding set_integrable_def
    using emeasure_compact_finite by (simp, intro integrable_real_indicator; force)
  thus ?thesis
    apply (rewrite distrTx_RD.cdf_ccdf, rewrite distrTx_RD.prob_space)
    using ccdfTx_integrable_Icc by (rewrite set_integral_diff; simp)
qed

corollary cdfTx_integrable_on_Icc:
  "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) integrable_on {a..b}" for a b :: real
  using cdfTx_integrable_Icc set_borel_integral_eq_integral by force

lemma cdfTx_PX:
  "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t = \<P>(\<xi> in \<MM>. x < X \<xi> \<and> X \<xi> \<le> x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
  for t::real
  apply (rewrite cdfTx_cond_prob)
  unfolding cond_prob_def futr_life_def PXx_pos by (smt (verit) Collect_cong)

lemma cdfT0_eq_cdfX: "cdf (distr (\<MM> \<downharpoonright> alive 0) borel (T 0)) = cdf (distr \<MM> borel X)"
proof
  interpret alive0_PS: prob_space "\<MM> \<downharpoonright> alive 0"
    apply (rule MM_PS.cond_prob_space_correct, simp)
    using PXx_pos alive_def psi_pos' by presburger
  interpret distrT0_RD: real_distribution "distr (\<MM> \<downharpoonright> alive 0) borel (T 0)" by simp
  show "\<And>x. cdf (distr (\<MM> \<downharpoonright> alive 0) borel (T 0)) x = cdf (distr \<MM> borel X) x"
    using ccdfT0_eq_ccdfX distrX_RD.ccdf_cdf distrT0_RD.ccdf_cdf
    by (smt (verit, best) distrT0_RD.prob_space distrX_RD.prob_space psi_pos')
qed

lemma continuous_cdfX_cdfTx:
  "continuous (at (x+t) within {x..}) (cdf (distr \<MM> borel X)) \<longleftrightarrow>
    continuous (at t within {0..}) (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  if "t \<ge> 0" for t::real
proof -
  have "continuous (at (x+t) within {x..}) (cdf (distr \<MM> borel X)) \<longleftrightarrow>
    continuous (at (x+t) within {x..}) (ccdf (distr \<MM> borel X))"
    by (rule distrX_RD.continuous_cdf_ccdf)
  also have "\<dots> \<longleftrightarrow> continuous (at t within {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    using continuous_ccdfX_ccdfTx that by simp
  also have "\<dots> \<longleftrightarrow> continuous (at t within {0..}) (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    using distrTx_RD.continuous_cdf_ccdf by simp
  finally show ?thesis .
qed

lemma isCont_cdfX_cdfTx:
  "isCont (cdf (distr \<MM> borel X)) (x+t) \<longleftrightarrow>
  isCont (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t"
  if "t > 0" for t::real
  apply (rewrite distrX_RD.isCont_cdf_ccdf)
  apply (rewrite isCont_ccdfX_ccdfTx, simp_all add: that)
  by (rule distrTx_RD.isCont_cdf_ccdf[THEN sym])

lemma has_real_derivative_cdfX_cdfTx:
  "((cdf (distr \<MM> borel X)) has_real_derivative D) (at (x+t)) \<longleftrightarrow>
  ((cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) has_real_derivative (D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
  if "t > 0" for t D :: real
proof -
  have "((cdf (distr \<MM> borel X)) has_real_derivative D) (at (x+t)) \<longleftrightarrow>
    (ccdf (distr \<MM> borel X) has_real_derivative -D) (at (x+t))"
    using distrX_RD.has_real_derivative_cdf_ccdf by force
  also have "\<dots> \<longleftrightarrow>
    ((ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) has_real_derivative (-D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
    using has_real_derivative_ccdfX_ccdfTx that by simp
  also have "\<dots> \<longleftrightarrow>
    ((cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) has_real_derivative (D / \<P>(\<xi> in \<MM>. X \<xi> > x))) (at t)"
    by (simp add: distrTx_RD.has_real_derivative_cdf_ccdf)
  finally show ?thesis .
qed

lemma differentiable_cdfX_cdfTx:
  "(cdf (distr \<MM> borel X)) differentiable at (x+t) \<longleftrightarrow>
  (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable at t"
  if "t > 0" for t::real
  apply (rewrite differentiable_eq_field_differentiable_real)+
  unfolding field_differentiable_def using has_real_derivative_cdfX_cdfTx that
  by (meson differentiable_ccdfX_ccdfTx distrTx_RD.finite_borel_measure_axioms
      distrX_RD.finite_borel_measure_axioms finite_borel_measure.differentiable_cdf_ccdf
      real_differentiable_def x_lt_psi)

subsubsection \<open>Properties of @{text "$q_{t&x}"}\<close>

lemma q_0_0: "$q_{0&x} = 0"
  unfolding die_def using cdfTx_0_0 by simp

lemma q_nonneg[simp]: "$q_{t&x} \<ge> 0" for t::real
  unfolding die_def using distrTx_RD.cdf_nonneg by simp

lemma q_1_equiv: "$q_{t&x} = 1 \<longleftrightarrow> x+t \<ge> $\<psi>" for t::real
  unfolding die_def using cdfTx_1_equiv by simp

lemma q_PTx: "$q_{t&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<le> t \<bar> T x \<xi> > 0)" for t::real
  unfolding die_def using cdfTx_cond_prob by simp

lemma q_PX: "$q_{t&x} = \<P>(\<xi> in \<MM>. x < X \<xi> \<and> X \<xi> \<le> x + t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
  unfolding die_def using cdfTx_PX by simp

lemma q_defer_0_q[simp]: "$q_{0\<bar>t&x} = $q_{t&x}" for t::real
  unfolding die_defer_def using q_0_0 by simp

lemma q_defer_0_0: "$q_{f\<bar>0&x} = 0" for f::real
  unfolding die_defer_def by simp

lemma q_defer_nonneg[simp]: "$q_{f\<bar>t&x} \<ge> 0" for f t :: real
  unfolding die_defer_def by simp

lemma q_defer_q: "$q_{f\<bar>t&x} = $q_{f+t & x} - $q_{f&x}" if "t \<ge> 0" for f t :: real
  unfolding die_defer_def die_def using distrTx_RD.cdf_nondecreasing that by simp

lemma q_defer_PTx: "$q_{f\<bar>t&x} = \<P>(\<xi> in \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t \<bar> T x \<xi> > 0)"
  if "t \<ge> 0" for f t :: real
proof -
  have "$q_{f\<bar>t&x} = $q_{f+t & x} - $q_{f&x}" using q_defer_q that by simp
  also have "\<dots> = \<P>(\<xi> in \<MM>. T x \<xi> \<le> f + t \<bar> T x \<xi> > 0) - \<P>(\<xi> in \<MM>. T x \<xi> \<le> f \<bar> T x \<xi> > 0)"
    using q_PTx by simp
  also have "\<dots> = \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f + t) - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f)"
    using MM_PS.cond_prob_space_cond_prob alive_T by simp
  also have "\<dots> = \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). f < T x \<xi> \<and> T x \<xi> \<le> f + t)"
  proof -
    have "{\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f + t} - {\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f} =
      {\<xi> \<in> space (\<MM> \<downharpoonright> alive x). f < T x \<xi> \<and> T x \<xi> \<le> f + t}"
      using that by force
    hence "alivex_PS.prob
      ({\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f + t} - {\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f}) =
      \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). f < T x \<xi> \<and> T x \<xi> \<le> f + t)"
      by simp
    moreover have "{\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f} \<subseteq> {\<xi> \<in> space (\<MM> \<downharpoonright> alive x). T x \<xi> \<le> f + t}"
      using that by force
    ultimately show ?thesis by (rewrite alivex_PS.finite_measure_Diff[THEN sym]; simp)
  qed
  also have "\<dots> = \<P>(\<xi> in \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t \<bar> T x \<xi> > 0)"
    using MM_PS.cond_prob_space_cond_prob alive_T by simp
  finally show ?thesis .
qed

lemma q_defer_PX: "$q_{f\<bar>t&x} = \<P>(\<xi> in \<MM>. x + f < X \<xi> \<and> X \<xi> \<le> x + f + t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
  if "f \<ge> 0" "t \<ge> 0" for f t :: real
proof -
  have "$q_{f\<bar>t&x} = \<P>(\<xi> in \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t \<and> T x \<xi> > 0) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
    apply (rewrite q_defer_PTx; (simp add: that)?)
    unfolding cond_prob_def by simp
  also have "\<dots> = \<P>(\<xi> in \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
  proof -
    have "\<And>\<xi>. \<xi> \<in> space \<MM> \<Longrightarrow> f < T x \<xi> \<and> T x \<xi> \<le> f + t \<and> T x \<xi> > 0 \<longleftrightarrow> f < T x \<xi> \<and> T x \<xi> \<le> f + t"
      using that by auto
    hence "{\<xi> \<in> space \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t \<and> T x \<xi> > 0} =
      {\<xi> \<in> space \<MM>. f < T x \<xi> \<and> T x \<xi> \<le> f + t}" by blast
    thus ?thesis by simp
  qed
  also have "\<dots> = \<P>(\<xi> in \<MM>. x + f < X \<xi> \<and> X \<xi> \<le> x + f + t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    unfolding futr_life_def by (smt (verit) Collect_cong)
  finally show ?thesis .
qed

lemma q_defer_old_0: "$q_{f\<bar>t&x} = 0" if "x+f \<ge> $\<psi>" "t \<ge> 0" for f t :: real
proof -
  have "$q_{f\<bar>t&x} = $q_{f+t & x} - $q_{f&x}" using q_defer_q that by simp
  moreover have "$q_{f+t & x} = 1" using q_1_equiv that le_ereal_le by auto
  moreover have "$q_{f&x} = 1" using q_1_equiv that by simp
  ultimately show ?thesis by simp
qed

end

subsubsection \<open>Properties of Cumulative Distributive Function for X\<close>

lemma cdfX_continuous_unborn[simp]: "continuous_on {..0} (cdf (distr \<MM> borel X))"
  using cdfTx_continuous_on_nonpos by (metis cdfT0_eq_cdfX psi_pos')

lemma cdfX_differentiable_unborn[simp]: "(cdf (distr \<MM> borel X)) differentiable_on {..0}"
  using cdfTx_differentiable_on_nonpos by (metis cdfT0_eq_cdfX psi_pos')

lemma cdfX_has_real_derivative_0_unborn:
  "(cdf (distr \<MM> borel X) has_real_derivative 0) (at x)" if "x < 0" for x::real
  using cdfTx_has_real_derivative_0_at_neg by (metis cdfT0_eq_cdfX psi_pos' that)

lemma cdfX_integrable_Icc:
  "set_integrable lborel {a..b} (cdf (distr \<MM> borel X))" for a b :: real
  using cdfTx_integrable_Icc by (metis cdfT0_eq_cdfX psi_pos')

corollary cdfX_integrable_on_Icc:
  "cdf (distr \<MM> borel X) integrable_on {a..b}" for a b :: real
  using cdfX_integrable_Icc set_borel_integral_eq_integral by force

lemma cdfX_q: "cdf (distr \<MM> borel X) x = $q_{x&0}" if "x \<ge> 0" for x::real
  by (metis cdfT0_eq_cdfX die_def psi_pos')

subsubsection \<open>Relations between @{text "$p_{t&x}"} and @{text "$q_{t&x}"}\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct, simp_all add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma p_q_1: "$p_{t&x} + $q_{t&x} = 1" for t::real
  unfolding survive_def die_def using distrTx_RD.add_cdf_ccdf
  by (smt (verit) distrTx_RD.prob_space x_lt_psi)

lemma q_defer_p: "$q_{f\<bar>t&x} = $p_{f&x} - $p_{f+t & x}" if "t \<ge> 0" for f t :: real
  using q_defer_q p_q_1 that x_lt_psi by smt

lemma q_defer_p_q_defer: "$p_{f&x} * $q_{f'\<bar>t & x+f} = $q_{f+f'\<bar>t & x}"
  if "x+f < $\<psi>" "f \<ge> 0" "f' \<ge> 0" "t \<ge> 0" for f f' t :: real
proof -
  have "$p_{f&x} * $q_{f'\<bar>t & x+f} =
    \<P>(\<xi> in \<MM>. X \<xi> > x+f) / \<P>(\<xi> in \<MM>. X \<xi> > x) *
    \<P>(\<xi> in \<MM>. x+f+f' < X \<xi> \<and> X \<xi> \<le> x+f+f'+t) / \<P>(\<xi> in \<MM>. X \<xi> > x+f)"
    apply (rewrite p_PX, (simp_all add: that)[2])
    by (rewrite survival_model.q_defer_PX, simp_all add: that survival_model_axioms)
  also have "\<dots> = \<P>(\<xi> in \<MM>. x+f+f' < X \<xi> \<and> X \<xi> \<le> x+f+f'+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    using survival_model.PXx_pos[of \<MM> X "x+f"] nonzero_mult_div_cancel_left that
    by (smt (verit, ccfv_SIG) survival_model_axioms times_divide_eq_left times_divide_eq_right)
  also have "\<dots> = $q_{f+f'\<bar>t & x}"
    by (rewrite q_defer_PX; simp add: that group_cancel.add1)
  finally show ?thesis .
qed

lemma q_defer_pq: "$q_{f\<bar>t&x} = $p_{f&x} * $q_{t & x+f}"
  if "x+f < $\<psi>" "t \<ge> 0" "f \<ge> 0" for f t :: real
  using q_defer_p_q_defer[where f'=0] that
  by (simp add: survival_model.q_defer_0_q survival_model_axioms)

subsubsection \<open>Properties of Life Expectation\<close>

lemma e_nonneg: "$e`\<circ>_x \<ge> 0"
  unfolding life_expect_def
  by (rule Bochner_Integration.integral_nonneg, simp add: less_eq_real_def)

lemma e_P: "$e`\<circ>_x =
  MM_PS.expectation (\<lambda>\<xi>. indicator (alive x) \<xi> * T x \<xi>) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
  unfolding life_expect_def
  by (rewrite MM_PS.integral_cond_prob_space_nn, auto simp add: alive_T)

proposition nn_integral_T_p:
  "(\<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+t\<in>{0..}. ennreal ($p_{t&x}) \<partial>lborel"
  apply (rewrite alivex_PS.expectation_nonneg_tail, simp_all add: less_imp_le)
  apply (rule nn_integral_cong)
  unfolding survive_def using distrTx_RD.prob_space distrTx_RD.ccdf_cdf by presburger

lemma nn_integral_T_pos: "(\<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) > 0"
proof -
  let ?f = "\<lambda>t. - ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t"
  have "\<And>t u. t \<le> u \<Longrightarrow> ?f t \<le> ?f u" using distrTx_RD.ccdf_nonincreasing by simp
  moreover have "continuous (at_right 0) ?f"
    using distrTx_RD.ccdf_is_right_cont by (intro continuous_intros)
  ultimately have "\<forall>e>0. \<exists>d>0. ?f (0 + d) - ?f 0 < e"
    using continuous_at_right_real_increasing by simp
  hence "\<exists>d>0. ?f (0 + d) - ?f 0 < 1/2" by (smt (verit, del_insts) field_sum_of_halves)
  from this obtain d where d_pos: "d > 0" and "$p_{d&x} \<ge> 1/2"
    using p_0_1 unfolding survive_def by auto
  hence "\<And>t. t\<in>{0..d} \<Longrightarrow> $p_{t&x} \<ge> 1/2"
    unfolding survive_def using distrTx_RD.ccdf_nonincreasing by force
  hence "\<integral>\<^sup>+t\<in>{0..d}. ennreal ($p_{t&x}) \<partial>lborel \<ge> \<integral>\<^sup>+t\<in>{0..d}. ennreal (1/2) \<partial>lborel"
    apply (intro nn_set_integral_mono, simp_all)
    unfolding survive_def using Tx_alivex_measurable apply force
    by (rule AE_I2) (smt (verit) ennreal_half ennreal_leI half_bounded_equal)
  moreover have "\<integral>\<^sup>+t\<in>{0..}. ennreal ($p_{t&x}) \<partial>lborel \<ge> \<integral>\<^sup>+t\<in>{0..d}. ennreal ($p_{t&x}) \<partial>lborel"
    by (rule nn_set_integral_set_mono) simp
  moreover have "\<integral>\<^sup>+t\<in>{0..d}. ennreal (1/2) \<partial>lborel > 0"
    apply (rewrite nn_integral_cmult_indicator, simp_all)
    using d_pos emeasure_lborel_Icc ennreal_zero_less_mult_iff by fastforce
  ultimately show ?thesis using nn_integral_T_p by simp
qed

proposition e_LBINT_p: "$e`\<circ>_x = LBINT t:{0..}. $p_{t&x}"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
  unfolding life_expect_def apply (rewrite integral_eq_nn_integral, simp_all add: less_imp_le)
  unfolding set_lebesgue_integral_def apply (rewrite integral_eq_nn_integral, simp_all)
   apply (measurable, simp add: survive_def)
  by (rewrite nn_integral_T_p) (simp add: indicator_mult_ennreal mult.commute)

corollary e_integral_p: "$e`\<circ>_x = integral {0..} (\<lambda>t. $p_{t&x})"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
proof -
  have "$e`\<circ>_x = LBINT t:{0..}. $p_{t&x}" using e_LBINT_p by simp
  also have "\<dots> = integral {0..} (\<lambda>t. $p_{t&x})"
    apply (rule set_borel_integral_eq_integral_nonneg, simp_all)
    unfolding survive_def by simp
  finally show ?thesis .
qed

lemma e_LBINT_p_Icc: "$e`\<circ>_x = LBINT t:{0..n}. $p_{t&x}" if "x+n \<ge> $\<psi>" for n::real
proof -
  have [simp]: "{0..n} \<inter> {n<..} = {}" using ivl_disj_int_one(7) by blast
  have [simp]: "{0..n} \<union> {n<..} = {0..}"
    by (smt (verit) ereal_less_le ivl_disj_un_one(7) leD that x_lt_psi)
  have [simp]: "\<And>t. n < t \<Longrightarrow> 0 \<le> t" using that x_lt_psi by (smt (verit) ereal_less_le leD)
  have [simp]: "\<And>t. n < t \<Longrightarrow> $\<psi> \<le> ereal (x+t)" using that by (simp add: le_ereal_le)
  have gt_n_0: "has_bochner_integral lborel (\<lambda>t. indicat_real {n<..} t * $p_{t&x}) 0"
    apply (rewrite has_bochner_integral_cong[where N=lborel and g="\<lambda>t.0" and y=0], simp_all)
    using p_0_equiv that x_lt_psi
     apply (smt (verit, ccfv_SIG) greaterThan_iff indicator_simps le_ereal_le linorder_not_le)
    by (rule has_bochner_integral_zero)
  hence gt_n: "set_integrable lborel {n<..} (\<lambda>t. $p_{t&x})"
    unfolding set_integrable_def using integrable.simps by auto
  moreover have le_n: "set_integrable lborel {0..n} (\<lambda>t. $p_{t&x})"
    unfolding survive_def by (intro ccdfTx_integrable_Icc) simp
  ultimately have "set_integrable lborel ({0..n} \<union> {n<..}) (\<lambda>t. $p_{t&x})"
    using set_integrable_Un by force
  hence "set_integrable lborel {0..} (\<lambda>t. $p_{t&x})" by force
  thus ?thesis
    apply (rewrite e_LBINT_p, simp)
    apply (rewrite set_integral_Un[of "{0..n}" "{n<..}", simplified], simp_all add: gt_n le_n)
    unfolding set_lebesgue_integral_def using gt_n_0 has_bochner_integral_integral_eq by fastforce
qed

lemma e_integral_p_Icc: "$e`\<circ>_x = integral {0..n} (\<lambda>t. $p_{t&x})" if "x+n \<ge> $\<psi>" for n::real
  using that apply (rewrite e_LBINT_p_Icc, simp_all)
  using ccdfTx_integrable_Icc unfolding survive_def
  by (rewrite set_borel_integral_eq_integral; simp)

lemma temp_e_P: "$e`\<circ>_{x:n} =
  MM_PS.expectation (\<lambda>\<xi>. indicator (alive x) \<xi> * min (T x \<xi>) n) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
  if "n \<ge> 0" for n::real
  unfolding temp_life_expect_def
  by (rewrite MM_PS.integral_cond_prob_space_nn; simp add: alive_T that)

lemma temp_e_LBINT_p: "$e`\<circ>_{x:n} = LBINT t:{0..n}. $p_{t&x}" if "n \<ge> 0" for n::real
proof -
  let ?minTxn = "\<lambda>\<xi>. min (T x \<xi>) n"
  let ?F = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  let ?Fn = "cdf (distr (\<MM> \<downharpoonright> alive x) borel ?minTxn)"
  interpret distrTxn_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel ?minTxn" by (simp add: that)
  have [simp]: "\<And>\<xi>. \<xi> \<in> space (\<MM> \<downharpoonright> alive x) \<Longrightarrow> 0 \<le> T x \<xi>" by (smt (verit) alivex_Tx_pos)
  have "(\<integral>\<^sup>+\<xi>. ennreal (min (T x \<xi>) n) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+t\<in>{0..}. ennreal (1 - ?Fn t) \<partial>lborel"
    by (rewrite alivex_PS.expectation_nonneg_tail; simp add: that)
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0..}. (ennreal (1 - ?F t) * indicator {..<n} t) \<partial>lborel"
    apply (rule nn_integral_cong)
    by (rewrite alivex_PS.cdf_distr_min; simp add: indicator_mult_ennreal mult.commute)
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0..<n}. ennreal (1 - ?F t) \<partial>lborel"
    apply (rule nn_integral_cong) using nn_integral_set_ennreal
    by (smt (verit, best) Int_def atLeastLessThan_def ennreal_mult_right_cong
        indicator_simps mem_Collect_eq mult.commute mult_1)
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0..n}. ennreal (1 - ?F t) \<partial>lborel"
  proof -
    have "sym_diff {0..<n} {0..n} = {n}" using that by force
    thus ?thesis by (intro nn_integral_null_delta; force)
  qed
  also have "\<dots> = ennreal (LBINT t:{0..n}. $p_{t&x})"
  proof -
    have "set_integrable lborel {0..n} (\<lambda>t. $p_{t&x})"
      unfolding survive_def by (intro ccdfTx_integrable_Icc) simp
    thus ?thesis
      unfolding set_lebesgue_integral_def unfolding set_integrable_def
      apply (rewrite nn_integral_eq_integral[THEN sym]; simp)
      apply (rule nn_integral_cong, simp)
      unfolding survive_def using distrTx_RD.ccdf_cdf distrTx_RD.prob_space nn_integral_set_ennreal
      by (simp add: indicator_mult_ennreal mult.commute)
  qed
  finally have "(\<integral>\<^sup>+\<xi>. ennreal (min (T x \<xi>) n) \<partial>(\<MM> \<downharpoonright> alive x)) =
    ennreal (LBINT t:{0..n}. $p_{t&x})" .
  thus ?thesis
    unfolding temp_life_expect_def
    apply (rewrite integral_eq_nn_integral; simp add: that)
    apply (rewrite enn2real_ennreal; simp?)
    unfolding set_lebesgue_integral_def by (simp add: that)
qed

lemma temp_e_integral_p: "$e`\<circ>_{x:n} = integral {0..n} (\<lambda>t. $p_{t&x})" if "n \<ge> 0" for n::real
  using that apply (rewrite temp_e_LBINT_p, simp_all)
  using ccdfTx_integrable_Icc unfolding survive_def
  by (rewrite set_borel_integral_eq_integral; simp)

lemma e_eq_temp: "$e`\<circ>_x = $e`\<circ>_{x:n}" if "n \<ge> 0" "x+n \<ge> $\<psi>" for n::real
  using that e_LBINT_p_Icc temp_e_LBINT_p by simp

lemma curt_e_P: "$e_x =
  MM_PS.expectation (\<lambda>\<xi>. indicator (alive x) \<xi> * \<lfloor>T x \<xi>\<rfloor>) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
  unfolding curt_life_expect_def
  apply (rewrite MM_PS.integral_cond_prob_space_nn; simp add: alive_T)
  by (metis (no_types, lifting) Bochner_Integration.integral_cong indicator_simps of_int_0 of_int_1)

lemma curt_e_sum_P: "$e_x = (\<Sum>k. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
  if "summable (\<lambda>k. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
proof -
  let ?F_flrTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (\<lambda>\<xi>. \<lfloor>T x \<xi>\<rfloor>))"
  have [simp]: "\<And>\<xi>. \<xi> \<in> space (\<MM> \<downharpoonright> alive x) \<Longrightarrow> 0 \<le> T x \<xi>" by (smt (verit) alivex_Tx_pos)
  have "integral\<^sup>N (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. ennreal \<lfloor>T x \<xi>\<rfloor>) = \<integral>\<^sup>+t\<in>{0..}. ennreal (1 - ?F_flrTx t) \<partial>lborel"
    by (rewrite alivex_PS.expectation_nonneg_tail; simp)
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0::real..}. ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<ge> \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0) \<partial>lborel"
  proof -
    { fix t::real assume "t \<ge> 0"
      hence "1 - ?F_flrTx t = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> real_of_int \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0)"
      proof -
        have "1 - ?F_flrTx t = 1 - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> < real_of_int \<lfloor>t\<rfloor> + 1)"
          by (rewrite alivex_PS.cdf_distr_floor_P; simp)
        also have "\<dots> = 1 - \<P>(\<xi> in \<MM>. T x \<xi> < real_of_int \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0)"
          using alive_T by (rewrite MM_PS.cond_prob_space_cond_prob; simp)
        also have "\<dots> = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> real_of_int \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0)"
          by (rewrite not_le[THEN sym], rewrite MM_PS.cond_prob_neg; simp)
        finally show ?thesis .
      qed }
    thus ?thesis
      apply -
      by (rule nn_set_integral_cong2, rule AE_I2) simp
  qed
  also have "\<dots> = (\<Sum>k. \<integral>\<^sup>+t\<in>{k..<k+1}. ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<ge> \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0) \<partial>lborel)"
    apply (rewrite nn_integral_disjoint_family[THEN sym]; simp)
     apply (rewrite add.commute, rule Ico_nat_disjoint)
    by (rewrite Ico_nat_union[THEN sym], simp add: add.commute)
  also have "\<dots> = (\<Sum>k. \<integral>\<^sup>+t\<in>{k..<k+1::nat}. ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0) \<partial>lborel)"
  proof -
    { fix k::nat and t::real
      assume "real k \<le> t" and "t < 1 + real k"
      hence "real_of_int \<lfloor>t\<rfloor> = real k"
        by (metis add.commute floor_eq2 of_int_of_nat_eq)
      hence "\<P>(\<xi> in \<MM>. T x \<xi> \<ge> real_of_int \<lfloor>t\<rfloor> + 1 \<bar> T x \<xi> > 0) =
      \<P>(\<xi> in \<MM>. T x \<xi> \<ge> 1 + real k \<bar> T x \<xi> > 0)"
        by (simp add: add.commute) }
    thus ?thesis
      apply -
      apply (rule suminf_cong, rule nn_set_integral_cong2, rule AE_I2)
      by (rule impI) simp
  qed
  also have "\<dots> = (\<Sum>k. ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
    by (rewrite nn_integral_cmult_indicator; simp add: add.commute)
  also have "\<dots> = ennreal (\<Sum>k. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
    by (rewrite suminf_ennreal2; simp add: that)
  finally have "integral\<^sup>N (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. ennreal \<lfloor>T x \<xi>\<rfloor>) =
    ennreal (\<Sum>k. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))" .
  hence "integral\<^sup>L (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. \<lfloor>T x \<xi>\<rfloor>) = (\<Sum>k. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
    apply (rewrite integral_eq_nn_integral; simp)
    apply (rewrite enn2real_ennreal; simp add: add.commute)
    apply (rule suminf_nonneg; simp?)
    by (rewrite add.commute, simp add: that)
  thus ?thesis unfolding curt_life_expect_def by (simp add: add.commute)
qed

lemma curt_e_sum_P_finite: "$e_x = (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
  if "x+n+1 > $\<psi>" for n::nat
proof -
  from that have psi_fin: "$\<psi> < \<infinity>" by force
  let ?P = "\<lambda>k::nat. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0)"
  let ?P_fin = "\<lambda>k::nat. if k\<in>{..<n} then ?P k else 0"
  have "\<And>k. ?P k = ?P_fin k"
  proof -
    fix k
    show "?P k = ?P_fin k"
    proof (cases \<open>k \<in> {..<n}\<close>)
      case True
      thus ?thesis by simp
    next
      case False
      hence "\<not> k < n" by simp
      hence "x + k + 1 > real_of_ereal $\<psi>"
        using that psi_nonneg real_of_ereal_ord_simps(4) by fastforce
      hence "{\<xi> \<in> space \<MM>. T x \<xi> \<ge> k + 1 \<and> T x \<xi> > 0} \<subseteq> {\<xi> \<in> space \<MM>. X \<xi> > real_of_ereal $\<psi>}"
        unfolding futr_life_def using that less_ereal_le of_nat_1 of_nat_add by force
      hence "\<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<and> T x \<xi> > 0) \<le> \<P>(\<xi> in \<MM>. X \<xi> > real_of_ereal $\<psi>)"
        by (intro MM_PS.finite_measure_mono, simp_all)
      also have "\<dots> = 0" using MM_PS.ccdf_distr_P X_RV ccdfX_psi_0 psi_fin by presburger
      finally have "\<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<and> T x \<xi> > 0) = 0" using measure_le_0_iff by blast
      hence "?P k = 0" unfolding cond_prob_def by (simp add: add.commute)
      thus ?thesis by simp
    qed
  qed
  moreover have "?P_fin sums (\<Sum>k<n. ?P k)" using sums_If_finite_set by force
  ultimately have \<star>: "?P sums (\<Sum>k<n. ?P k)" using sums_cong by simp
  moreover hence "summable ?P" using sums_summable by blast
  ultimately have "?P sums $e_x" using curt_e_sum_P by force
  hence "$e_x = (\<Sum>k<n. ?P k)" by (rewrite sums_unique2[of "?P"]; simp add: \<star>)
  thus ?thesis by (simp add: add.commute)
qed

lemma curt_e_sum_p: "$e_x = (\<Sum>k. $p_{k+1&x})"
  if "summable (\<lambda>k. $p_{k+1&x})" "\<And>k::nat. isCont (\<lambda>t. $p_{t&x}) (k+1)"
proof -
  have "\<And>k::nat. $p_{k+1&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0)"
    apply (rewrite p_PTx_ge_ccdf_isCont, simp_all)
    using that(2) isCont_ccdfX_ccdfTx unfolding survive_def by simp
  thus ?thesis using that p_PTx_ge_ccdf_isCont curt_e_sum_P by presburger
qed

lemma curt_e_rec: "$e_x = $p_x * (1 + $e_(x+1))"
  if "summable (\<lambda>k. $p_{k+1&x})" "\<And>k::nat. isCont (\<lambda>t. $p_{t&x}) (real k + 1)" "x+1 < $\<psi>"
proof -
  have px_neq_0[simp]: "$p_x \<noteq> 0" using p_0_equiv that by auto
  have "(\<lambda>k. $p_{k+1&x}) sums $e_x"
    using that apply (rewrite curt_e_sum_p, simp_all add: add.commute)
    by (rule summable_sums, simp add: that)
  hence "(\<lambda>k. $p_x * $p_{k&x+1}) sums $e_x"
    apply (rewrite sums_cong[where g="\<lambda>k. $p_{k+1&x}"]; simp?)
    using p_mult by (smt (verit) of_nat_0_le_iff that(3) x_lt_psi)
  hence "(\<lambda>k. $p_{k&x+1}) sums ($e_x / $p_x)"
    using sums_mult_D that by (smt (verit, best) linorder_not_le p_0_equiv sums_cong x_lt_psi)
  hence p_e_p: "(\<lambda>k. $p_{Suc k & x+1}) sums ($e_x / $p_x - $p_{0&x+1})"
    using sums_split_initial_segment[where n=1] by force
  moreover have "(\<lambda>k. $p_{Suc k & x+1}) sums $e_(x+1)"
  proof -
    have [simp]: "summable (\<lambda>k::nat. $p_{real k + 1 & x + 1})"
      apply (intro sums_summable[where l="$e_x / $p_x - $p_{0&x+1}"])
      using p_e_p by (simp add: add.commute)
    have [simp]: "\<And>k::nat. isCont (\<lambda>t. $p_{t&x+1}) (real k + 1)"
    proof -
      fix k::nat
      have "isCont (\<lambda>t. $p_x * $p_{t-1&x+1}) (real k + 2)"
      proof -
        let ?S="{real k + 1 <..< real k + 3}"
        have "open ?S" by simp
        moreover have "real k + 2 \<in> ?S" by simp
        moreover have "\<And>t. t \<in> ?S \<Longrightarrow> $p_x * $p_{t-1&x+1} = $p_{t&x}"
          using p_mult
          by (smt (verit, del_insts) greaterThanLessThan_iff of_nat_0_le_iff that(3) x_lt_psi)
        ultimately show ?thesis
          apply (rewrite isCont_cong[where g="\<lambda>t. $p_{t&x}"])
           apply (rewrite eventually_nhds, blast)
          using that by (smt (verit) of_nat_1 of_nat_add)
      qed
      hence "isCont (\<lambda>t. $p_x * $p_{t-1&x+1} / $p_x) (real k + 2)"
        by (intro isCont_divide[where g="\<lambda>t. $p_x"], auto)
      hence "isCont ((\<lambda>t. $p_{t-1&x+1}) \<circ> (\<lambda>t. t+1)) (real k + 1)"
        by simp (rule continuous_at_compose, simp_all add: add.commute)
      thus "isCont (\<lambda>t. $p_{t&x+1}) (real k + 1)" unfolding comp_def by simp
    qed
    show ?thesis
      apply (rewrite survival_model.curt_e_sum_p; simp add: survival_model_axioms that)
      using summable_sums by (rewrite add.commute) force
  qed
  ultimately have "$e_x / $p_x - $p_{0&x+1} = $e_(x+1)" by (rule sums_unique2)
  thus ?thesis
    using p_0_1 that
    by (smt (verit) px_neq_0 divide_mult_cancel mult.commute mult_cancel_left2 p_mult that(3))
qed

lemma curt_e_sum_p_finite: "$e_x = (\<Sum>k<n. $p_{k+1&x})"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont (\<lambda>t. $p_{t&x}) (real k + 1)" "x+n+1 > $\<psi>" for n::nat
proof -
  have "\<And>k::nat. k < n \<Longrightarrow> $p_{k+1&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0)"
    apply (rewrite p_PTx_ge_ccdf_isCont, simp_all)
    using that isCont_ccdfX_ccdfTx unfolding survive_def by (smt (verit) of_nat_0_le_iff x_lt_psi)
  thus ?thesis using that p_PTx_ge_ccdf_isCont curt_e_sum_P_finite by simp
qed

lemma temp_curt_e_P: "$e_{x:n} =
  MM_PS.expectation (\<lambda>\<xi>. indicator (alive x) \<xi> * \<lfloor>min (T x \<xi>) n\<rfloor>) / \<P>(\<xi> in \<MM>. T x \<xi> > 0)"
  if "n \<ge> 0" for n::real
  unfolding temp_curt_life_expect_def
  apply (rewrite MM_PS.integral_cond_prob_space_nn; simp add: alive_T that)
  apply (rule disjI2, rule Bochner_Integration.integral_cong; simp)
  using indicator_simps of_int_0 of_int_1 by smt

lemma temp_curt_e_sum_P: "$e_{x:n} = (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))" for n::nat
proof -
  let ?F_flrminTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (\<lambda>\<xi>. \<lfloor>min (T x \<xi>) n\<rfloor>))"
  have [simp]: "\<And>\<xi>. \<xi> \<in> space (\<MM> \<downharpoonright> alive x) \<Longrightarrow> 0 \<le> T x \<xi>" by (smt (verit) alivex_Tx_pos)
  have "integral\<^sup>N (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. ennreal \<lfloor>min (T x \<xi>) n\<rfloor>) =
    (\<integral>\<^sup>+t\<in>{0..}. ennreal (1 - ?F_flrminTx t) \<partial>lborel)"
    by (rewrite alivex_PS.expectation_nonneg_tail; simp)
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0::real..}. ennreal
    ((1 - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> < \<lfloor>t\<rfloor> + 1)) * of_bool (\<lfloor>t\<rfloor> + 1 \<le> n)) \<partial>lborel"
  proof -
    have "\<And>t. t \<ge> 0 \<Longrightarrow> ennreal (1 - ?F_flrminTx t) =
      ennreal ((1 - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> < \<lfloor>t\<rfloor> + 1)) * of_bool (\<lfloor>t\<rfloor> + 1 \<le> n))"
    proof -
      fix t::real assume "t \<ge> 0"
      thus "ennreal (1 - ?F_flrminTx t) =
        ennreal ((1 - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> < \<lfloor>t\<rfloor> + 1)) * of_bool (\<lfloor>t\<rfloor> + 1 \<le> n))"
      proof (cases \<open>\<lfloor>t\<rfloor> + 1 \<le> n\<close>)
        case True
        thus ?thesis
          apply (rewrite alivex_PS.cdf_distr_floor_P; simp)
          using min_less_iff_disj
          by (smt (verit, ccfv_SIG) Collect_cong
              floor_eq floor_less_cancel floor_of_nat of_int_floor_le)
      next
        case False
        thus ?thesis
          apply (rewrite alivex_PS.cdf_distr_floor_P; simp)
          using min_less_iff_disj
          by (smt (verit, ccfv_SIG) Collect_cong MM_PS.space_cond_prob_space alive_T alive_event
              alivex_PS.prob_space mem_Collect_eq of_int_of_nat_eq of_nat_less_of_int_iff)
      qed
    qed
    thus ?thesis
      by (intro nn_set_integral_cong2, intro AE_I2) auto
  qed
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0..<n}. ennreal (1 - \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> < \<lfloor>t\<rfloor> + 1)) \<partial>lborel"
  proof -
    { fix t::real
      have "(\<lfloor>t\<rfloor> + 1 \<le> n) = (t < n)" by linarith
      hence "\<And>r::real.
        ennreal (r * of_bool (\<lfloor>t\<rfloor> + 1 \<le> n)) * indicator {0..} t = ennreal r * indicator {0..<n} t"
        unfolding atLeastLessThan_def by (simp add: indicator_inter_arith) }
    thus ?thesis by simp
  qed
  also have "\<dots> = \<integral>\<^sup>+t\<in>{0..<n}. ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> \<lfloor>t\<rfloor> + 1) \<partial>lborel"
    by (rewrite alivex_PS.prob_neg[THEN sym]; simp add: not_less)
  also have "\<dots> = (\<Sum>k<n. \<integral>\<^sup>+t\<in>{k..<k+1}. ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> \<lfloor>t\<rfloor> + 1) \<partial>lborel)"
    apply (rewrite  Ico_nat_union_finite[of n, THEN sym])
    apply (rewrite nn_integral_disjoint_family_on_finite; simp add: add.commute)
    apply (rule disjoint_family_on_mono[of _ "{0..}"]; simp)
    by (rewrite add.commute, rule Ico_nat_disjoint)
  also have "\<dots> = (\<Sum>k<n. ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
  proof -
    { fix k::nat
      assume "k < n"
      hence "\<integral>\<^sup>+t\<in>{k..<(1 + real k)}.
        ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> real_of_int \<lfloor>t\<rfloor> + 1) \<partial>lborel =
        \<P>(\<xi> in \<MM>. T x \<xi> \<ge> 1 + real k \<bar> T x \<xi> > 0)" (is "?LHS = ?RHS")
      proof -
        have "?LHS = \<integral>\<^sup>+t\<in>{k..<(1 + real k)}. ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> k + 1) \<partial>lborel"
        proof -
          { fix t::real
            assume "k \<le> t" "t < 1 + real k"
            hence "real_of_int \<lfloor>t\<rfloor> = real k" by (smt (verit) floor_eq2 of_int_of_nat_eq)
            hence "\<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> real_of_int \<lfloor>t\<rfloor> + 1) =
              \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> 1 + real k)"
              by (simp add: add.commute) }
          thus ?thesis by (intro nn_set_integral_cong2, intro AE_I2) auto
        qed
        also have "\<dots> = ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<ge> k + 1)"
          by (rewrite nn_integral_cmult_indicator; simp)
        also have "\<dots> = ?RHS"
          by (rewrite MM_PS.cond_prob_space_cond_prob, simp_all add: alive_T)
        finally show ?thesis .
      qed }
    thus ?thesis by (intro sum.cong) auto
  qed
  also have "\<dots> = ennreal (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))" by simp
  finally have "integral\<^sup>N (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. ennreal \<lfloor>min (T x \<xi>) n\<rfloor>) =
    ennreal (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))" .
  hence "integral\<^sup>L (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. \<lfloor>min (T x \<xi>) n\<rfloor>) =
    (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
    apply (intro nn_integral_eq_integrable[THEN iffD1, THEN conjunct2]; simp)
    using MM_PS.cond_prob_nonneg by (meson sum_nonneg)
  thus ?thesis unfolding temp_curt_life_expect_def by simp
qed

corollary curt_e_eq_temp: "$e_x = $e_{x:n}" if "x+n+1 > $\<psi>" for n::nat
  using curt_e_sum_P_finite temp_curt_e_sum_P that by simp

lemma temp_curt_e_sum_p: "$e_{x:n} = (\<Sum>k<n. $p_{k+1&x})"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont (\<lambda>t. $p_{t&x}) (real k + 1)" for n::nat
proof -
  have "\<And>k::nat. k < n \<Longrightarrow> $p_{k+1&x} = \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0)"
    apply (rewrite p_PTx_ge_ccdf_isCont, simp_all)
    using that isCont_ccdfX_ccdfTx unfolding survive_def by (smt (verit) of_nat_0_le_iff x_lt_psi)
  thus ?thesis
    apply (rewrite temp_curt_e_sum_P)
    by (rule sum.cong) simp_all
qed

lemma temp_curt_e_rec: "$e_{x:n} = $p_x * (1 + $e_{x+1:n-1})"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont (\<lambda>t. $p_{t&x}) (real k + 1)" "x+1 < $\<psi>" "n \<noteq> 0" for n::nat
proof -
  have [simp]: "$p_x \<noteq> 0" using p_0_equiv that by auto
  have [simp]: "\<And>k. k < n-1 \<Longrightarrow> isCont (\<lambda>t. $p_{t&x+1}) (real k + 1)"
  proof -
    fix k::nat assume k_n: "k < n-1"
    have "isCont (\<lambda>t. $p_x * $p_{t-1&x+1}) (real k + 2)"
    proof -
      let ?S="{real k + 1 <..< real k + 3}"
      have "open ?S" by simp
      moreover have "real k + 2 \<in> ?S" by simp
      moreover have "\<And>t. t \<in> ?S \<Longrightarrow> $p_x * $p_{t-1&x+1} = $p_{t&x}"
        using p_mult
        by (smt (verit, del_insts) greaterThanLessThan_iff of_nat_0_le_iff that(2) x_lt_psi)
      ultimately show ?thesis
        apply (rewrite isCont_cong[where g="\<lambda>t. $p_{t&x}"])
         apply (rewrite eventually_nhds, blast)
        using that k_n by (smt (verit) less_diff_conv of_nat_1 of_nat_add)
    qed
    hence "isCont (\<lambda>t. $p_x * $p_{t-1&x+1} / $p_x) (real k + 2)"
      by (intro isCont_divide[where g="\<lambda>t. $p_x"], auto)
    hence "isCont ((\<lambda>t. $p_{t-1&x+1}) \<circ> (\<lambda>t. t+1)) (real k + 1)"
      by simp (rule continuous_at_compose, simp_all add: add.commute)
    thus "isCont (\<lambda>t. $p_{t&x+1}) (real k + 1)" unfolding comp_def by simp
  qed
  have "$p_x * (1 + $e_{x+1:n-1}) = $p_x * (1 + (\<Sum>k<(n-1). $p_{k+1&x+1}))"
    by (rewrite survival_model.temp_curt_e_sum_p; simp add: survival_model_axioms that)
  also have "\<dots> = $p_x + (\<Sum>k<(n-1). $p_x * $p_{k+1&x+1})"
    apply (rewrite distrib_left, simp)
    by (rewrite vector_space_over_itself.scale_sum_right, simp)
  also have "\<dots> = $p_x + (\<Sum>k<(n-1). $p_{k+2&x})"
    apply (rewrite sum.cong, simp_all add: add.commute)
    using p_mult by (smt (verit) of_nat_0_le_iff that(2) x_lt_psi)
  also have "\<dots> = (\<Sum>k<Suc(n-1). $p_{k+1&x})"
    apply (rewrite lessThan_atLeast0)+
    by (rewrite sum.atLeast0_lessThan_Suc_shift) simp
  also have "\<dots> = $e_{x:n}" using that by (rewrite temp_curt_e_sum_p; simp)
  finally show ?thesis by simp
qed

end

end

subsection \<open>Piecewise Differentiable Survival Function\<close>

locale smooth_survival_function = survival_model +
  assumes ccdfX_piecewise_differentiable[simp]:
    "(ccdf (distr \<MM> borel X)) piecewise_differentiable_on UNIV"

begin

interpretation distrX_RD: real_distribution "distr \<MM> borel X"
  using MM_PS.real_distribution_distr by simp

subsubsection \<open>Properties of Survival Function for X\<close>

lemma ccdfX_continuous[simp]: "continuous_on UNIV (ccdf (distr \<MM> borel X))"
  using ccdfX_piecewise_differentiable piecewise_differentiable_on_imp_continuous_on by fastforce

corollary ccdfX_borel_measurable[measurable]: "ccdf (distr \<MM> borel X) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI) simp

lemma ccdfX_nondifferentiable_finite_set[simp]:
  "finite {x. \<not> ccdf (distr \<MM> borel X) differentiable at x}"
proof -
  obtain S where
    fin: "finite S" and "\<And>x. x \<notin> S \<Longrightarrow> (ccdf (distr \<MM> borel X)) differentiable at x"
    using ccdfX_piecewise_differentiable unfolding piecewise_differentiable_on_def by blast
  hence "{x. \<not> ccdf (distr \<MM> borel X) differentiable at x} \<subseteq> S" by blast
  thus ?thesis using finite_subset fin by blast
qed

lemma ccdfX_differentiable_open_set: "open {x. ccdf (distr \<MM> borel X) differentiable at x}"
  using ccdfX_nondifferentiable_finite_set finite_imp_closed
  by (metis (mono_tags, lifting) Collect_cong open_Collect_neg)

lemma ccdfX_differentiable_borel_set[measurable, simp]:
  "{x. ccdf (distr \<MM> borel X) differentiable at x} \<in> sets borel"
  using ccdfX_differentiable_open_set by simp

lemma ccdfX_differentiable_AE:
  "AE x in lborel. (ccdf (distr \<MM> borel X)) differentiable at x"
  apply (rule AE_I'[of "{x. \<not> ccdf (distr \<MM> borel X) differentiable at x}"], simp_all)
  using ccdfX_nondifferentiable_finite_set by (simp add: finite_imp_null_set_lborel)

lemma deriv_ccdfX_measurable[measurable]: "deriv (ccdf (distr \<MM> borel X)) \<in> borel_measurable borel"
proof -
  have "set_borel_measurable borel UNIV (deriv (ccdf (distr \<MM> borel X)))"
    by (rule piecewise_differentiable_on_deriv_measurable_real; simp)
  thus ?thesis unfolding set_borel_measurable_def by simp
qed

subsubsection \<open>Properties of Cumulative Distributive Function for X\<close>

lemma cdfX_piecewise_differentiable[simp]:
  "(cdf (distr \<MM> borel X)) piecewise_differentiable_on UNIV"
  by (rewrite distrX_RD.cdf_ccdf) (rule piecewise_differentiable_diff; simp)

lemma cdfX_continuous[simp]: "continuous_on UNIV (cdf (distr \<MM> borel X))"
  using cdfX_piecewise_differentiable piecewise_differentiable_on_imp_continuous_on by fastforce

corollary cdfX_borel_measurable[measurable]: "cdf (distr \<MM> borel X) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI) simp

lemma cdfX_nondifferentiable_finite_set[simp]:
  "finite {x. \<not> cdf (distr \<MM> borel X) differentiable at x}"
  using distrX_RD.differentiable_cdf_ccdf ccdfX_nondifferentiable_finite_set by simp

lemma cdfX_differentiable_open_set: "open {x. cdf (distr \<MM> borel X) differentiable at x}"
  using distrX_RD.differentiable_cdf_ccdf ccdfX_differentiable_open_set by simp

lemma cdfX_differentiable_borel_set[measurable, simp]:
  "{x. cdf (distr \<MM> borel X) differentiable at x} \<in> sets borel"
  using cdfX_differentiable_open_set by simp

lemma cdfX_differentiable_AE:
  "AE x in lborel. (cdf (distr \<MM> borel X)) differentiable at x"
  using ccdfX_differentiable_AE distrX_RD.differentiable_cdf_ccdf AE_iffI by simp

lemma deriv_cdfX_measurable[measurable]: "deriv (cdf (distr \<MM> borel X)) \<in> borel_measurable borel"
proof -
  have "set_borel_measurable borel UNIV (deriv (cdf (distr \<MM> borel X)))"
    by (rule piecewise_differentiable_on_deriv_measurable_real; simp)
  thus ?thesis unfolding set_borel_measurable_def by simp
qed

subsubsection \<open>Introduction of Probability Density Functions of X and T(x)\<close>

definition pdfX :: "real \<Rightarrow> real"
  where "pdfX x \<equiv> if cdf (distr \<MM> borel X) differentiable at x
    then deriv (cdf (distr \<MM> borel X)) x else 0"
    \<comment> \<open>This function is defined to be always nonnegative for future application.\<close>

definition pdfT :: "real \<Rightarrow> real \<Rightarrow> real"
  where "pdfT x t \<equiv> if cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t
    then deriv (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t else 0"
    \<comment> \<open>This function is defined to be always nonnegative for future application.\<close>

lemma pdfX_measurable[measurable]: "pdfX \<in> borel_measurable borel"
proof -
  let ?cdfX = "cdf (distr \<MM> borel X)"
  have "countable {x. \<not> ?cdfX differentiable at x}"
    using cdfX_nondifferentiable_finite_set uncountable_infinite by force
  thus ?thesis
    unfolding pdfX_def
    apply -
    by (rule measurable_discrete_difference
        [where X="{x. \<not> ?cdfX differentiable at x}" and f="deriv ?cdfX"]; simp)
qed

lemma distributed_pdfX: "distributed \<MM> lborel X pdfX"
proof -
  let ?cdfX = "cdf (distr \<MM> borel X)"
  obtain S where fin: "finite S" and diff: "\<And>t. t \<notin> S \<Longrightarrow> ?cdfX differentiable at t"
    using cdfX_piecewise_differentiable unfolding piecewise_differentiable_on_def by blast
  { fix t::real assume t_notin: "t \<notin> S"
    have "?cdfX differentiable at t" using diff t_notin by simp
    hence "(?cdfX has_real_derivative pdfX t) (at t)"
      unfolding pdfX_def using DERIV_deriv_iff_real_differentiable by auto }
  thus ?thesis
    by (intro MM_PS.distributed_deriv_cdf[where S=S]; simp add: fin)
qed

lemma pdfT0_X: "pdfT 0 = pdfX"
  unfolding pdfT_def pdfX_def using cdfT0_eq_cdfX psi_pos' by fastforce

subsubsection \<open>Properties of Survival Function for T(x)\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct; simp add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma ccdfTx_continuous_on_nonneg[simp]:
  "continuous_on {0..} (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  apply (rewrite continuous_on_eq_continuous_within, auto)
  apply (rewrite continuous_ccdfX_ccdfTx[THEN sym], auto)
  by (metis UNIV_I ccdfX_continuous continuous_at_imp_continuous_at_within
      continuous_on_eq_continuous_within)

lemma ccdfTx_continuous[simp]: "continuous_on UNIV (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
proof -
  have [simp]: "{..0::real} \<union> {0..} = UNIV" by auto
  have "continuous_on {..0} (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    by (rule ccdfTx_continuous_on_nonpos) simp
  moreover have "continuous_on {0..} (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))" by simp
  ultimately have "continuous_on ({..0} \<union> {0..}) (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
    by (intro continuous_on_closed_Un) simp_all
  thus ?thesis by simp
qed

corollary ccdfTx_borel_measurable[measurable]:
  "ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI) simp

lemma ccdfTx_nondifferentiable_finite_set[simp]:
  "finite {t. \<not> ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}"
proof -
  let ?P = "\<lambda>t. ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t"
  have "{t. t < 0 \<and> \<not> ?P t} = {}"
  proof (rule equals0I)
    fix t assume asm: "t \<in> {t. t < 0 \<and> \<not> ?P t}"
    hence "?P t" using ccdfTx_has_real_derivative_0_at_neg real_differentiable_def x_lt_psi by blast
    with asm show False by simp
  qed
  hence "{t. \<not> ?P t} \<subseteq> insert 0 {t. t > 0 \<and> \<not> ?P t}" by force
  moreover have "finite {t. t > 0 \<and> \<not> ?P t}"
  proof -
    have "{t. \<not> ccdf (distr \<MM> borel X) differentiable at (x+t)} =
      plus (-x) ` {s. \<not> ccdf (distr \<MM> borel X) differentiable at s}"
      by force
    hence "finite {t. \<not> ccdf (distr \<MM> borel X) differentiable at (x+t)}"
      using ccdfX_nondifferentiable_finite_set by simp
    thus ?thesis
      using finite_subset differentiable_ccdfX_ccdfTx
      by (metis (no_types, lifting) mem_Collect_eq subsetI x_lt_psi)
  qed
  ultimately show ?thesis using finite_subset by auto
qed

lemma ccdfTx_differentiable_open_set:
  "open {t. ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}"
  using ccdfTx_nondifferentiable_finite_set finite_imp_closed
  by (metis (mono_tags, lifting) Collect_cong open_Collect_neg)

lemma ccdfTx_differentiable_borel_set[measurable, simp]:
  "{t. ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t} \<in> sets borel"
  using ccdfTx_differentiable_open_set by simp

lemma ccdfTx_differentiable_AE:
  "AE t in lborel. (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable at t"
  apply (rule AE_I'[of "{t. \<not> ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}"]; simp?)
  using ccdfTx_nondifferentiable_finite_set by (simp add: finite_imp_null_set_lborel)

lemma ccdfTx_piecewise_differentiable[simp]:
  "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) piecewise_differentiable_on UNIV"
proof -
  have "\<forall>t\<in>UNIV-{t. \<not> ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}.
    ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t"
    by auto
  thus ?thesis
    unfolding piecewise_differentiable_on_def
    using ccdfTx_continuous ccdfTx_nondifferentiable_finite_set by blast
qed

lemma deriv_ccdfTx_measurable[measurable]:
  "deriv (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) \<in> borel_measurable borel"
proof -
  have "set_borel_measurable borel UNIV (deriv (ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))))"
    by (rule piecewise_differentiable_on_deriv_measurable_real; simp)
  thus ?thesis unfolding set_borel_measurable_def by simp
qed

subsubsection \<open>Properties of Cumulative Distributive Function for T(x)\<close>

lemma cdfTx_continuous[simp]:
  "continuous_on UNIV (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
  using distrTx_RD.cdf_ccdf ccdfTx_continuous by (simp add: continuous_on_eq_continuous_within)

corollary cdfTx_borel_measurable[measurable]:
  "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI) simp

lemma cdfTx_nondifferentiable_finite_set[simp]:
  "finite {t. \<not> cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}"
  using distrTx_RD.differentiable_cdf_ccdf by simp

lemma cdfTx_differentiable_open_set:
  "open {t. cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t}"
  using distrTx_RD.differentiable_cdf_ccdf ccdfTx_differentiable_open_set by simp

lemma cdfTx_differentiable_borel_set[measurable, simp]:
  "{t. cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t} \<in> sets borel"
  using cdfTx_differentiable_open_set by simp

lemma cdfTx_differentiable_AE:
  "AE t in lborel. (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable at t"
  by (rewrite distrTx_RD.differentiable_cdf_ccdf, simp add: ccdfTx_differentiable_AE)

lemma cdfTx_piecewise_differentiable[simp]:
  "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) piecewise_differentiable_on UNIV"
  using piecewise_differentiable_diff piecewise_differentiable_const ccdfTx_piecewise_differentiable
  by (rewrite distrTx_RD.cdf_ccdf) blast

lemma deriv_cdfTx_measurable[measurable]:
  "deriv (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) \<in> borel_measurable borel"
proof -
  have "set_borel_measurable borel UNIV (deriv (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))))"
    by (rule piecewise_differentiable_on_deriv_measurable_real; simp)
  thus ?thesis unfolding set_borel_measurable_def by simp
qed

subsubsection \<open>Properties of Probability Density Function of T(x)\<close>

lemma pdfTx_nonneg: "pdfT x t \<ge> 0" for t::real
proof -
  fix t
  show "pdfT x t \<ge> 0"
  proof (cases \<open>cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t\<close>)
    case True
    have "mono_on UNIV (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)))"
      unfolding mono_on_def using distrTx_RD.cdf_nondecreasing by blast
    moreover have "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative pdfT x t) (at t)"
      unfolding pdfT_def using True DERIV_deriv_iff_real_differentiable by presburger
    ultimately show ?thesis by (rule mono_on_imp_deriv_nonneg) simp
  next
    case False
    thus ?thesis unfolding pdfT_def by simp
  qed
qed

lemma pdfTx_neg_0: "pdfT x t = 0" if "t < 0" for t::real
proof -
  let ?e = "-t/2"
  have "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) has_real_derivative 0) (at t)"
    apply (rewrite DERIV_cong_ev[of t t _ "\<lambda>_. 0" 0 0], simp_all add: that)
    apply (rewrite eventually_nhds)
    apply (rule exI[of _ "ball t ?e"], auto simp add: that)
    by (rule cdfTx_nonpos_0; simp add: dist_real_def)
  thus ?thesis unfolding pdfT_def by (meson DERIV_imp_deriv)
qed

lemma pdfTx_0_0: "pdfT x 0 = 0"
proof (cases \<open>cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at 0\<close>)
  case True
  let ?cdfx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  have "(?cdfx has_real_derivative 0) (at 0)"
  proof -
    from True obtain c where cdfx_deriv: "(?cdfx has_real_derivative c) (at 0)"
      unfolding differentiable_def using has_real_derivative by blast
    hence "(?cdfx has_real_derivative c) (at 0 within {..0})"
      by (rule has_field_derivative_at_within)
    moreover have "(?cdfx has_real_derivative 0) (at 0 within {..0})"
    proof -
      have "\<forall>\<^sub>F t in at 0 within {..0}. ?cdfx t = 0"
      proof -
        { fix t assume "t \<in> {..0::real}" "t \<noteq> 0" "dist t 0 < 1"
          hence "?cdfx t = 0" using cdfTx_nonpos_0 x_lt_psi by blast }
        hence "\<exists>d>0::real. \<forall>t\<in>{..0}. t\<noteq>0 \<and> dist t 0 < d \<longrightarrow> ?cdfx t = 0" by (smt (verit))
        thus ?thesis by (rewrite eventually_at) simp
      qed
      moreover have "?cdfx 0 = 0"
      proof -
        have "continuous (at 0 within {..0}) ?cdfx"
          using True differentiable_imp_continuous_within differentiable_subset by blast
        thus ?thesis by (simp add: cdfTx_nonpos_0)
      qed
      ultimately show ?thesis
        by (rewrite has_field_derivative_cong_eventually[of _ "\<lambda>_. 0::real" 0 "{..0}" 0]; simp)
    qed
    ultimately have "c = 0"
      using has_real_derivative_iff_has_vector_derivative
      apply (intro vector_derivative_unique_within[of 0 "{..0}" ?cdfx c 0]; blast?)
      by (rewrite at_within_eq_bot_iff)
        (metis closure_lessThan islimpt_in_closure limpt_of_closure
          trivial_limit_at_left_real trivial_limit_within)
    thus "(?cdfx has_real_derivative 0) (at 0)" using cdfx_deriv by simp
  qed
  thus ?thesis unfolding pdfT_def by (meson DERIV_imp_deriv)
next
  case False
  thus ?thesis unfolding pdfT_def by simp
qed

lemma pdfTx_nonpos_0: "pdfT x t = 0" if "t \<le> 0" for t::real
  using pdfTx_neg_0 pdfTx_0_0 that by force

lemma pdfTx_beyond_0: "pdfT x t = 0" if "x+t \<ge> $\<psi>" for t::real
proof (cases \<open>t \<le> 0\<close>)
  case True
  thus ?thesis using pdfTx_nonpos_0 by simp
next
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  case False
  hence t_pos: "t > 0" by simp
  thus ?thesis
  proof -
    have "(?cdfTx has_real_derivative 0) (at_right t)"
      apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>_. 1"], simp_all)
       apply (rewrite eventually_at_right_field)
      using that cdfTx_1_equiv
      by (intro exI[of _"t+1"], auto simp add: le_ereal_less less_eq_ereal_def)
    thus ?thesis unfolding pdfT_def
      by (meson has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within
          DERIV_deriv_iff_real_differentiable trivial_limit_at_right_real
          vector_derivative_unique_within)
  qed
qed

lemma pdfTx_pdfX: "pdfT x t = pdfX (x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)" if "t > 0" for t::real
proof (cases \<open>cdf (distr \<MM> borel X) differentiable at (x+t)\<close>)
  case True
  let ?cdfX = "cdf (distr \<MM> borel X)"
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  have [simp]: "?cdfTx differentiable at t" using differentiable_cdfX_cdfTx that True by simp
  have "pdfT x t = deriv ?cdfTx t" unfolding pdfT_def using that differentiable_cdfX_cdfTx by simp
  hence "(?cdfTx has_field_derivative (pdfT x t)) (at t)"
    using True DERIV_deriv_iff_real_differentiable by simp
  moreover have "\<And>u. dist u t < t \<Longrightarrow>
    ?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x) - (1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1) = ?cdfTx u"
  proof -
    fix u::real
    assume "dist u t < t"
    hence [simp]: "u > 0" using dist_real_def by fastforce
    have "?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x) - (1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1) = 
      (1 - \<P>(\<xi> in \<MM>. X \<xi> > x+u)) / \<P>(\<xi> in \<MM>. X \<xi> > x) - (1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1)"
      using MM_PS.ccdf_distr_P X_RV distrX_RD.cdf_ccdf distrX_RD.prob_space by presburger
    also have "\<dots> = 1 - \<P>(\<xi> in \<MM>. X \<xi> > x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
      by (simp add: diff_divide_distrib)
    also have "\<dots> = ?cdfTx u"
      apply (rewrite ccdfTx_PX[THEN sym], simp_all add: less_eq_real_def)
      using distrTx_RD.cdf_ccdf distrTx_RD.prob_space by presburger
    finally show "?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x) - (1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1) = ?cdfTx u" .
  qed
  ultimately have "((\<lambda>u. ?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x) - (1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1))
    has_field_derivative (pdfT x t)) (at t)"
    apply -
    by (rule has_field_derivative_transform_within[where d=t]; simp add: that)
  hence "((\<lambda>u. ?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x)) has_field_derivative (pdfT x t)) (at t)"
    unfolding has_field_derivative_def
    using has_derivative_add_const[where c="1 / \<P>(\<xi> in \<MM>. X \<xi> > x) - 1"] by force
  hence "((\<lambda>u. ?cdfX (x+u) / \<P>(\<xi> in \<MM>. X \<xi> > x) * \<P>(\<xi> in \<MM>. X \<xi> > x)) has_field_derivative
    pdfT x t * \<P>(\<xi> in \<MM>. X \<xi> > x)) (at t)"
    using DERIV_cmult_right[where c="\<P>(\<xi> in \<MM>. X \<xi> > x)"] by force
  hence "((\<lambda>u. ?cdfX (x+u)) has_field_derivative pdfT x t * \<P>(\<xi> in \<MM>. X \<xi> > x)) (at t)"
    unfolding has_field_derivative_def using has_derivative_transform PXx_pos x_lt_psi
    by (smt (verit) Collect_cong UNIV_I nonzero_mult_div_cancel_right times_divide_eq_left)
  hence "(?cdfX has_field_derivative pdfT x t * \<P>(\<xi> in \<MM>. X \<xi> > x)) (at (x+t))"
    using DERIV_at_within_shift by force
  moreover have "(?cdfX has_field_derivative deriv ?cdfX (x+t)) (at (x+t))"
    using True DERIV_deriv_iff_real_differentiable by blast
  ultimately have "pdfT x t * \<P>(\<xi> in \<MM>. X \<xi> > x) = deriv ?cdfX (x+t)"
    by (simp add: DERIV_imp_deriv)
  thus "pdfT x t = pdfX (x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)"
    unfolding pdfX_def using True
    by simp (metis PXx_pos nonzero_mult_div_cancel_right x_lt_psi zero_less_measure_iff)
next
  case False
  hence [simp]: "\<not> cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) differentiable at t"
    using differentiable_cdfX_cdfTx that by simp
  thus "pdfT x t = pdfX (x+t) / \<P>(\<xi> in \<MM>. X \<xi> > x)" unfolding pdfT_def pdfX_def using False by simp
qed

lemma pdfTx_measurable[measurable]: "pdfT x \<in> borel_measurable borel"
proof -
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  have "countable {x. \<not> ?cdfTx differentiable at x}"
    using cdfX_nondifferentiable_finite_set uncountable_infinite by force
  thus ?thesis
    unfolding pdfT_def
    apply -
    by (rule measurable_discrete_difference
        [where X="{x. \<not> ?cdfTx differentiable at x}" and f="deriv ?cdfTx"]; simp)
qed

lemma distributed_pdfTx: "distributed (\<MM> \<downharpoonright> alive x) lborel (T x) (pdfT x)"
proof -
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  obtain S where fin: "finite S" and diff: "\<And>t. t \<notin> S \<Longrightarrow> ?cdfTx differentiable at t"
    using cdfTx_piecewise_differentiable unfolding piecewise_differentiable_on_def by blast
  { fix t::real assume t_notin: "t \<notin> S"
    have "?cdfTx differentiable at t" using diff t_notin by simp
    hence "(?cdfTx has_real_derivative pdfT x t) (at t)"
      unfolding pdfT_def using DERIV_deriv_iff_real_differentiable by force }
  thus ?thesis
    by (intro alivex_PS.distributed_deriv_cdf[where S=S]; simp add: fin)
qed

lemma nn_integral_pdfTx_1: "(\<integral>\<^sup>+s. pdfT x s \<partial>lborel) = 1"
proof -
  have "(\<integral>\<^sup>+s. pdfT x s \<partial>lborel) = emeasure (density lborel (pdfT x)) UNIV"
    by (rewrite emeasure_density) simp_all
  also have "\<dots> = emeasure (distr (\<MM> \<downharpoonright> alive x) lborel (T x)) UNIV"
    using distributed_pdfTx unfolding distributed_def by simp
  also have "\<dots> = 1"
    by (metis distrTx_RD.emeasure_space_1 distrTx_RD.space_eq_univ distr_cong sets_lborel)
  finally show ?thesis .
qed

corollary has_bochner_integral_pdfTx_1: "has_bochner_integral lborel (pdfT x) 1"
  by (rule has_bochner_integral_nn_integral; simp add: pdfTx_nonneg nn_integral_pdfTx_1)

corollary LBINT_pdfTx_1: "LBINT s. pdfT x s = 1"
  using has_bochner_integral_pdfTx_1 by (simp add: has_bochner_integral_integral_eq)

corollary pdfTx_has_integral_1: "(pdfT x has_integral 1) UNIV"
  by (rule nn_integral_has_integral; simp add: pdfTx_nonneg nn_integral_pdfTx_1)

lemma set_nn_integral_pdfTx_1: "\<integral>\<^sup>+s\<in>{0..}. pdfT x s \<partial>lborel = 1"
  apply (rewrite nn_integral_pdfTx_1[THEN sym])
  apply (rule nn_integral_cong)
  using pdfTx_nonpos_0
  by (metis atLeast_iff ennreal_0 indicator_simps(1) linorder_le_cases
      mult.commute mult_1 mult_zero_left)

corollary has_bochner_integral_pdfTx_1_nonpos:
  "has_bochner_integral lborel (\<lambda>s. pdfT x s * indicator {0..} s) 1"
  apply (rule has_bochner_integral_nn_integral, simp_all)
  using pdfTx_nonneg apply simp
  using set_nn_integral_pdfTx_1 by (simp add: nn_integral_set_ennreal)

corollary set_LBINT_pdfTx_1: "(LBINT s:{0..}. pdfT x s) = 1"
  unfolding set_lebesgue_integral_def
  using has_bochner_integral_pdfTx_1_nonpos has_bochner_integral_integral_eq
  apply (simp, rewrite mult.commute)
  by (smt (verit) Bochner_Integration.integral_cong has_bochner_integral_integral_eq)

corollary pdfTx_has_integral_1_nonpos: "(pdfT x has_integral 1) {0..}"
proof -
  have "set_integrable lebesgue {0..} (pdfT x)"
    unfolding set_integrable_def
    apply (rewrite integrable_completion, simp_all)
    using has_bochner_integral_pdfTx_1_nonpos by (rewrite mult.commute, rule integrable.intros)
  moreover have "LINT s:{0..}|lebesgue. pdfT x s = 1"
    using set_LBINT_pdfTx_1 unfolding set_lebesgue_integral_def
    by (rewrite integral_completion; simp)
  ultimately show ?thesis using has_integral_set_lebesgue by force
qed

lemma set_nn_integral_pdfTx_PTx: "\<integral>\<^sup>+s\<in>A. pdfT x s \<partial>lborel = \<P>(\<xi> in \<MM>. T x \<xi> \<in> A \<bar> T x \<xi> > 0)"
  if "A \<in> sets lborel" for A :: "real set"
proof -
  have [simp]: "A \<in> sets borel" using that by simp
  have "\<integral>\<^sup>+s\<in>A. pdfT x s \<partial>lborel = emeasure (density lborel (pdfT x)) A"
    using that by (rewrite emeasure_density; force)
  also have "\<dots> = emeasure (distr (\<MM> \<downharpoonright> alive x) lborel (T x)) A"
    using distributed_pdfTx unfolding distributed_def by simp
  also have "\<dots> = ennreal \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). T x \<xi> \<in> A)"
    apply (rewrite emeasure_distr, simp_all)
    apply (rewrite finite_measure.emeasure_eq_measure, simp)
    by (smt (verit) Collect_cong vimage_eq Int_def)
  also have "\<dots> = ennreal \<P>(\<xi> in \<MM>. T x \<xi> \<in> A \<bar> T x \<xi> > 0)"
    unfolding alive_def
    apply (rewrite MM_PS.cond_prob_space_cond_prob[THEN sym], simp_all add: pred_def futr_life_def)
    using borel_measurable_diff X_RV that by measurable
  finally show ?thesis .
qed

lemma pdfTx_set_integrable: "set_integrable lborel A (pdfT x)" if "A \<in> sets lborel"
  unfolding set_integrable_def
  using that pdfTx_nonneg apply (intro integrableI_nonneg, simp_all)
  apply (rewrite mult.commute)
  using set_nn_integral_pdfTx_PTx that
  by (metis (no_types, lifting) ennreal_indicator ennreal_less_top ennreal_mult' nn_integral_cong)

lemma set_integral_pdfTx_PTx: "LBINT s:A. pdfT x s = \<P>(\<xi> in \<MM>. T x \<xi> \<in> A \<bar> T x \<xi> > 0)"
  if "A \<in> sets lborel" for A :: "real set"
  unfolding set_lebesgue_integral_def
  apply (rewrite integral_eq_nn_integral)
  using that apply (simp_all add: pdfTx_nonneg)
  apply (rewrite indicator_mult_ennreal[THEN sym], rewrite mult.commute)
  by (rewrite set_nn_integral_pdfTx_PTx; simp)

lemma pdfTx_has_integral_PTx: "(pdfT x has_integral \<P>(\<xi> in \<MM>. T x \<xi> \<in> A \<bar> T x \<xi> > 0)) A"
  if "A \<in> sets lborel" for A :: "real set"
proof -
  have "((\<lambda>s. pdfT x s * indicat_real A s) has_integral \<P>(\<xi> in \<MM>. T x \<xi> \<in> A \<bar> T x \<xi> > 0)) UNIV"
    using that pdfTx_nonneg apply (intro nn_integral_has_integral, simp_all)
    using set_nn_integral_pdfTx_PTx that by (simp add: nn_integral_set_ennreal)
  thus ?thesis
    by (smt (verit) has_integral_cong has_integral_restrict_UNIV
        indicator_eq_0_iff indicator_simps(1) mult_cancel_left2 mult_eq_0_iff)
qed

corollary pdfTx_has_integral_PTx_Icc:
  "(pdfT x has_integral \<P>(\<xi> in \<MM>. a \<le> T x \<xi> \<and> T x \<xi> \<le> b \<bar> T x \<xi> > 0)) {a..b}" for a b :: real
  using pdfTx_has_integral_PTx[of "{a..b}"] by simp

corollary pdfTx_integrable_on_Icc: "pdfT x integrable_on {a..b}" for a b :: real
  using pdfTx_has_integral_PTx_Icc by auto

end

subsubsection \<open>Properties of Probability Density Function of X\<close>

lemma pdfX_nonneg: "pdfX x \<ge> 0" for x::real
  using pdfTx_nonneg pdfT0_X psi_pos' by smt

lemma pdfX_nonpos_0: "pdfX x = 0" if "x \<le> 0" for x::real
  using pdfTx_nonpos_0 pdfT0_X psi_pos' that by smt 

lemma pdfX_beyond_0: "pdfX x = 0" if "x \<ge> $\<psi>" for x::real
  using pdfTx_beyond_0 pdfT0_X psi_pos' that by smt

lemma nn_integral_pdfX_1: "integral\<^sup>N lborel pdfX = 1"
  using nn_integral_pdfTx_1 pdfT0_X psi_pos' by metis

corollary has_bochner_integral_pdfX_1: "has_bochner_integral lborel pdfX 1"
  by (rule has_bochner_integral_nn_integral; simp add: pdfX_nonneg nn_integral_pdfX_1)

corollary LBINT_pdfX_1: "LBINT s. pdfX s = 1"
  using has_bochner_integral_pdfX_1 by (simp add: has_bochner_integral_integral_eq)

corollary pdfX_has_integral_1: "(pdfX has_integral 1) UNIV"
  by (rule nn_integral_has_integral; simp add: pdfX_nonneg nn_integral_pdfX_1)

lemma set_nn_integral_pdfX_PX: "set_nn_integral lborel A pdfX = \<P>(\<xi> in \<MM>. X \<xi> \<in> A)"
  if "A \<in> sets lborel" for A :: "real set"
  using PT0_eq_PX_lborel that
  by (rewrite pdfT0_X[THEN sym], rewrite set_nn_integral_pdfTx_PTx; simp)

lemma pdfX_set_integrable: "set_integrable lborel A pdfX" if "A \<in> sets lborel" for A :: "real set"
  using pdfTx_set_integrable pdfT0_X psi_pos' that by smt

lemma set_integral_pdfX_PX: "LBINT s:A. pdfX s = \<P>(\<xi> in \<MM>. X \<xi> \<in> A)"
  if "A \<in> sets lborel" for A :: "real set"
  using PT0_eq_PX_lborel that by (rewrite pdfT0_X[THEN sym], rewrite set_integral_pdfTx_PTx; simp)

lemma pdfX_has_integral_PX: "(pdfX has_integral \<P>(\<xi> in \<MM>. X \<xi> \<in> A)) A"
  if "A \<in> sets lborel" for A :: "real set"
  using that apply (rewrite pdfT0_X[THEN sym], rewrite PT0_eq_PX_lborel[THEN sym], simp)
  by (rule pdfTx_has_integral_PTx; simp)

corollary pdfX_has_integral_PX_Icc: "(pdfX has_integral \<P>(\<xi> in \<MM>. a \<le> X \<xi> \<and> X \<xi> \<le> b)) {a..b}"
  for a b :: real
  using pdfX_has_integral_PX[of "{a..b}"] by simp

corollary pdfX_integrable_on_Icc: "pdfX integrable_on {a..b}" for a b :: real
  using pdfX_has_integral_PX_Icc by auto

subsubsection \<open>Relations between Life Expectation and Probability Density Function\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct; simp add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

proposition nn_integral_T_pdfT:
  "(\<integral>\<^sup>+\<xi>. ennreal (g (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * g s) \<partial>lborel"
  if "g \<in> borel_measurable lborel" for g :: "real \<Rightarrow> real"
proof -
  have "(\<integral>\<^sup>+\<xi>. ennreal (g (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+s. ennreal (pdfT x s) * ennreal (g s) \<partial>lborel"
  proof -
    have "distributed (\<MM> \<downharpoonright> alive x) lborel (T x) (\<lambda>s. ennreal (pdfT x s))"
      by (intro distributed_pdfTx) simp
    moreover have "(\<lambda>s. ennreal (g s)) \<in> borel_measurable borel" using that by measurable
    ultimately show ?thesis by (rewrite distributed_nn_integral; simp)
  qed
  also have "\<dots> = \<integral>\<^sup>+s. ennreal (pdfT x s * g s) \<partial>lborel" using ennreal_mult' pdfTx_nonneg by force
  also have "\<dots> = \<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * g s) \<partial>lborel"
    apply (rule nn_integral_cong, simp)
    by (metis atLeast_iff ennreal_0 indicator_simps linorder_not_le mult_1 mult_commute_abs
        mult_zero_left pdfTx_neg_0 x_lt_psi)
  finally show ?thesis .
qed

lemma expectation_LBINT_pdfT_nonneg:
  "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) = LBINT s:{0..}. pdfT x s * g s"
  if "\<And>s. s \<ge> 0 \<Longrightarrow> g s \<ge> 0" "g \<in> borel_measurable lborel" for g :: "real \<Rightarrow> real"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
  using that apply (rewrite integral_eq_nn_integral, simp)
   apply (rule AE_I2, metis alivex_Tx_pos less_imp_le)
  unfolding set_lebesgue_integral_def apply (rewrite integral_eq_nn_integral, simp_all)
   apply (rule AE_I2,
      metis indicator_pos_le pdfTx_nonpos_0 x_lt_psi zero_le_mult_iff zero_le_square pdfTx_nonneg)
  by (rewrite nn_integral_T_pdfT) (simp_all add: indicator_mult_ennreal mult.commute)

corollary expectation_integral_pdfT_nonneg:
  "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) = integral {0..} (\<lambda>s. pdfT x s * g s)"
  if "\<And>s. s \<ge> 0 \<Longrightarrow> g s \<ge> 0" "g \<in> borel_measurable lborel" for g :: "real \<Rightarrow> real"
  \<comment> \<open>Note that 0 = 0 holds when the integral diverges.\<close>
proof -
  have "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) = LBINT s:{0..}. pdfT x s * g s"
    using expectation_LBINT_pdfT_nonneg that by simp
  also have "\<dots> = integral {0..} (\<lambda>s. pdfT x s * g s)"
    using that pdfTx_nonneg by (intro set_borel_integral_eq_integral_nonneg; simp)
  finally show ?thesis .
qed

proposition expectation_LBINT_pdfT:
  "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) = LBINT s:{0..}. pdfT x s * g s"
  if "set_integrable lborel {0..} (\<lambda>s. pdfT x s * g s)" "g \<in> borel_measurable lborel"
  for g :: "real \<Rightarrow> real"
proof -
  have pg_fin: "(\<integral>\<^sup>+\<xi>. ennreal (g (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x)) \<noteq> \<infinity>"
    using that apply (rewrite nn_integral_T_pdfT, simp)
    using that unfolding set_integrable_def apply (rewrite in asm real_integrable_def, simp)
    by (simp add: indicator_mult_ennreal mult.commute)
  moreover have mg_fin: "(\<integral>\<^sup>+\<xi>. ennreal (- g (T x \<xi>)) \<partial>(\<MM> \<downharpoonright> alive x)) \<noteq> \<infinity>"
    using that apply (rewrite nn_integral_T_pdfT[of "\<lambda>s. - g s"], simp)
    using that unfolding set_integrable_def apply (rewrite in asm real_integrable_def, simp)
    by (simp add: indicator_mult_ennreal mult.commute)
  ultimately have [simp]: "integrable (\<MM> \<downharpoonright> alive x) (\<lambda>\<xi>. g (T x \<xi>))"
    using that by (rewrite real_integrable_def; simp)
  have "(\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * max 0 (g s)) \<partial>lborel) = 
    (\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * g s) \<partial>lborel)"
    using SPMF.ennreal_max_0 ennreal_mult' pdfTx_nonneg x_lt_psi by presburger
  also have "\<dots> < \<infinity>"
    using pg_fin nn_integral_T_pdfT that top.not_eq_extremum by auto
  finally have "(\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * max 0 (g s)) \<partial>lborel) < \<infinity>" .
  hence [simp]: "set_integrable lborel {0..} (\<lambda>s. pdfT x s * max 0 (g s))"
    unfolding set_integrable_def using that apply (intro integrableI_nonneg, simp_all)
    using pdfTx_nonneg apply (intro AE_I2, force)
    by (metis (no_types, lifting) indicator_mult_ennreal mult.commute nn_integral_cong)
  have "(\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * max 0 (- g s)) \<partial>lborel) =
    (\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * - g s) \<partial>lborel)"
    using SPMF.ennreal_max_0 ennreal_mult' pdfTx_nonneg x_lt_psi by presburger
  also have "\<dots> < \<infinity>"
    using mg_fin nn_integral_T_pdfT[of "\<lambda>s. - g s"] that top.not_eq_extremum by force
  finally have "(\<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * max 0 (- g s)) \<partial>lborel) < \<infinity>" .
  hence [simp]: "set_integrable lborel {0..} (\<lambda>s. pdfT x s * max 0 (- g s))"
    unfolding set_integrable_def using that apply (intro integrableI_nonneg, simp_all)
    using pdfTx_nonneg apply (intro AE_I2, force)
    by (metis (no_types, lifting) indicator_mult_ennreal mult.commute nn_integral_cong)
  have "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) =
    alivex_PS.expectation (\<lambda>\<xi>. max 0 (g (T x \<xi>))) - alivex_PS.expectation (\<lambda>\<xi>. max 0 (- g (T x \<xi>)))"
    by (rewrite Bochner_Integration.integral_cong
        [where N="\<MM> \<downharpoonright> alive x" and g="\<lambda>\<xi>. max 0 (g (T x \<xi>)) - max 0 (- g (T x \<xi>))"]; simp)
  moreover have "alivex_PS.expectation (\<lambda>\<xi>. max 0 (g (T x \<xi>))) =
    (LBINT s:{0..}. pdfT x s * max 0 (g s))"
    using that by (rewrite expectation_LBINT_pdfT_nonneg[where g="\<lambda>s. max 0 (g s)"]) simp_all
  moreover have "alivex_PS.expectation (\<lambda>\<xi>. max 0 (- g (T x \<xi>))) =
    (LBINT s:{0..}. pdfT x s * max 0 (- g s))"
    using that by (rewrite expectation_LBINT_pdfT_nonneg[where g="\<lambda>s. max 0 (- g s)"]) simp_all
  ultimately have "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) =
    (LBINT s:{0..}. pdfT x s * max 0 (g s)) - (LBINT s:{0..}. pdfT x s *  max 0 (- g s))" by simp
  also have "\<dots> = LBINT s:{0..}. (pdfT x s * max 0 (g s) - pdfT x s * max 0 (- g s))"
    by (rewrite set_integral_diff; simp)
  also have "\<dots> = LBINT s:{0..}. pdfT x s * (max 0 (g s) - max 0 (- g s))"
    by (simp add: right_diff_distrib)
  also have "\<dots> = LBINT s:{0..}. pdfT x s * g s"
    using minus_max_eq_min
    by (metis (no_types, opaque_lifting) diff_zero max_def min_def minus_diff_eq)
  finally show ?thesis .
qed

corollary expectation_integral_pdfT:
  "alivex_PS.expectation (\<lambda>\<xi>. g (T x \<xi>)) = integral {0..} (\<lambda>s. pdfT x s * g s)"
  if "(\<lambda>s. pdfT x s * g s) absolutely_integrable_on {0..}" "g \<in> borel_measurable lborel"
  for g :: "real \<Rightarrow> real"
proof -
  have [simp]: "set_integrable lborel {0..} (\<lambda>s. pdfT x s * g s)"
    using that by (rewrite absolutely_integrable_on_iff_set_integrable; simp)
  show ?thesis
    apply (rewrite set_borel_integral_eq_integral(2)[THEN sym], simp)
    using that by (rewrite expectation_LBINT_pdfT; simp)
qed

corollary e_LBINT_pdfT: "$e`\<circ>_x = LBINT s:{0..}. pdfT x s * s"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
  unfolding life_expect_def using expectation_LBINT_pdfT_nonneg by force

corollary e_integral_pdfT: "$e`\<circ>_x = integral {0..} (\<lambda>s. pdfT x s * s)"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
  unfolding life_expect_def using expectation_integral_pdfT_nonneg by force

end

corollary e_LBINT_pdfX: "$e`\<circ>_0 = (LBINT x:{0..}. pdfX x * x)"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
  using e_LBINT_pdfT pdfT0_X psi_pos' by presburger

corollary e_integral_pdfX: "$e`\<circ>_0 = integral {0..} (\<lambda>x. pdfX x * x)"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
  using e_integral_pdfT pdfT0_X psi_pos' by presburger

subsubsection \<open>Introduction of Force of Mortality\<close>

definition force_mortal :: "real \<Rightarrow> real" ("$\<mu>'__" [101] 200)
  where "$\<mu>_x \<equiv> MM_PS.hazard_rate X x"

lemma mu_pdfX: "$\<mu>_x = pdfX x / ccdf (distr \<MM> borel X) x"
  if "(cdf (distr \<MM> borel X)) differentiable at x" for x::real
  unfolding force_mortal_def pdfX_def
  by (rewrite MM_PS.hazard_rate_deriv_cdf, simp_all add: that)

lemma mu_unborn_0: "$\<mu>_x = 0" if "x < 0" for x::real
  apply (rewrite mu_pdfX)
  using cdfX_has_real_derivative_0_unborn real_differentiable_def that apply blast
  using pdfX_nonpos_0 that by auto

lemma mu_beyond_0: "$\<mu>_x = 0" if "x \<ge> $\<psi>" for x::real
  \<comment> \<open>Note that division by 0 is defined as 0 in Isabelle/HOL.\<close>
  unfolding force_mortal_def using MM_PS.hazard_rate_0_ccdf_0 ccdfX_0_equiv that by simp

lemma mu_nonneg_differentiable: "$\<mu>_x \<ge> 0"
  if "(cdf (distr \<MM> borel X)) differentiable at x" for x::real
  apply (rewrite mu_pdfX, simp add: that)
  using pdfX_nonneg distrX_RD.ccdf_nonneg by simp

lemma mu_nonneg_AE: "AE x in lborel. $\<mu>_x \<ge> 0"
  using cdfX_differentiable_AE mu_nonneg_differentiable by auto

lemma mu_measurable[measurable]: "(\<lambda>x. $\<mu>_x) \<in> borel_measurable borel"
proof -
  obtain S where
    "finite S" and "\<And>x. x \<notin> S \<Longrightarrow> (cdf (distr \<MM> borel X)) differentiable at x"
    using cdfX_piecewise_differentiable unfolding piecewise_differentiable_on_def by blast
  thus ?thesis
    apply (rewrite measurable_discrete_difference
        [where f="\<lambda>x. pdfX x / ccdf (distr \<MM> borel X) x" and X=S], simp_all)
    by (simp_all add: MM_PS.ccdf_distr_measurable borel_measurable_divide countable_finite mu_pdfX)
qed

lemma mu_deriv_ccdf: "$\<mu>_x = - deriv (ccdf (distr \<MM> borel X)) x / ccdf (distr \<MM> borel X) x"
  if "(ccdf (distr \<MM> borel X)) differentiable at x" "x < $\<psi>" for x::real
  unfolding force_mortal_def
  by (rewrite MM_PS.hazard_rate_deriv_ccdf; simp add: that)

lemma mu_deriv_ln: "$\<mu>_x = - deriv (\<lambda>x. ln (ccdf (distr \<MM> borel X) x)) x"
  if "(ccdf (distr \<MM> borel X)) differentiable at x" "x < $\<psi>" for x::real
  unfolding force_mortal_def
  apply (rewrite MM_PS.hazard_rate_deriv_ln_ccdf, simp_all add: that)
  using ccdfX_0_equiv that by force

lemma p_exp_integral_mu: "$p_{t&x} = exp (- integral {x..x+t} (\<lambda>y. $\<mu>_y))"
  if "x \<ge> 0" "t \<ge> 0" "x+t < $\<psi>"
proof -
  have [simp]: "x < $\<psi>" using that by (meson add_increasing2 ereal_less linorder_not_le)
  have "$p_{t&x} = (ccdf (distr \<MM> borel X) (x+t)) / (ccdf (distr \<MM> borel X) x)"
    apply (rewrite p_PX, simp_all add: that)
    by (rewrite MM_PS.ccdf_distr_P, simp)+ simp
  also have "\<dots> = exp (- integral {x..x+t} (MM_PS.hazard_rate X))"
    apply (rule MM_PS.ccdf_exp_cumulative_hazard, simp_all add: that)
    using ccdfX_piecewise_differentiable piecewise_differentiable_on_subset apply blast
    using ccdfX_continuous continuous_on_subset apply blast
    using ccdfX_0_equiv that ereal_less_le linorder_not_le by force
  also have "\<dots> = exp (- integral {x..x+t} (\<lambda>y. $\<mu>_y))" unfolding force_mortal_def by simp
  finally show ?thesis .
qed

corollary ccdfX_exp_integral_mu: "ccdf (distr \<MM> borel X) x = exp (- integral {0..x} (\<lambda>y. $\<mu>_y))"
  if "0 \<le> x \<and> x < $\<psi>" for x::real
  by (rewrite p_exp_integral_mu[where t=x and x=0, simplified, THEN sym]; simp add: that ccdfX_p)

subsubsection \<open>Properties of Force of Mortality\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

interpretation alivex_PS: prob_space "\<MM> \<downharpoonright> alive x"
  by (rule MM_PS.cond_prob_space_correct; simp add: alive_def)

interpretation distrTx_RD: real_distribution "distr (\<MM> \<downharpoonright> alive x) borel (T x)" by simp

lemma hazard_rate_Tx_mu: "alivex_PS.hazard_rate (T x) t = $\<mu>_(x+t)"
  if "t \<ge> 0" "x+t < $\<psi>" for t::real
proof -
  have [simp]: "\<P>(\<xi> in \<MM>. X \<xi> > x) > 0" by force
  moreover have [simp]: "\<P>(\<xi> in \<MM>. X \<xi> > x + t) > 0" using that by force
  moreover have [simp]: "{\<xi> \<in> space (\<MM> \<downharpoonright> alive x). X \<xi> > x + t} = {\<xi> \<in> space \<MM>. X \<xi> > x + t}"
    unfolding alive_def using that by (rewrite MM_PS.space_cond_prob_space, simp_all, force)
  hence [simp]: "{\<xi> \<in> space (\<MM> \<downharpoonright> alive x). X \<xi> > x + t} \<in> MM_PS.events" by simp
  ultimately have \<star>[simp]: "\<P>(\<xi> in (\<MM> \<downharpoonright> alive x). X \<xi> > x + t) > 0"
    unfolding alive_def
    apply (rewrite MM_PS.cond_prob_space_cond_prob[THEN sym], (simp_all add: pred_def)[3])
    unfolding cond_prob_def by (smt (verit) Collect_cong divide_pos_pos)
  have "alivex_PS.hazard_rate (T x) t =
    Lim (at_right 0) (\<lambda>dt. \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). t < T x \<xi> \<and> T x \<xi> \<le> t + dt \<bar> T x \<xi> > t) / dt)"
    unfolding alivex_PS.hazard_rate_def by simp
  also have "\<dots> = Lim (at_right 0)
    (\<lambda>dt. \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t) / dt)"
    apply (rule Lim_cong, rule eventually_at_rightI[of 0 1], simp_all)
    unfolding futr_life_def cond_prob_def using Collect_cong by smt
  also have "\<dots> =
    Lim (at_right 0) (\<lambda>dt. \<P>(\<xi> in \<MM>. x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t) / dt)"
  proof -
    have "\<And>dt. \<P>(\<xi> in (\<MM> \<downharpoonright> alive x). x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t) =
      \<P>(\<xi> in \<MM>. x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t)"
    proof -
      fix dt
      let ?rngX = "\<lambda>\<xi>. x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt"
      have "\<P>(\<xi> in (\<MM> \<downharpoonright> alive x). ?rngX \<xi> \<bar> X \<xi> > x + t) =
        \<P>(\<xi> in ((\<MM> \<downharpoonright> alive x) \<downharpoonright> {\<eta> \<in> space (\<MM> \<downharpoonright> alive x). X \<eta> > x + t}). ?rngX \<xi>)"
        using \<star> by (rewrite alivex_PS.cond_prob_space_cond_prob) simp_all
      also have "\<dots> = \<P>(\<xi> in (\<MM> \<downharpoonright> {\<eta> \<in> space \<MM>. X \<eta> > x + t}). ?rngX \<xi>)"
      proof -
        have "(\<MM> \<downharpoonright> alive x) \<downharpoonright> {\<eta> \<in> space (\<MM> \<downharpoonright> alive x). X \<eta> > x + t} =
          \<MM> \<downharpoonright> {\<eta> \<in> space (\<MM> \<downharpoonright> alive x). X \<eta> > x + t}"
          apply (rewrite MM_PS.cond_cond_prob_space, simp_all)
          unfolding alive_def using that by force
        also have "\<dots> = \<MM> \<downharpoonright> {\<eta> \<in> space \<MM>. X \<eta> > x + t}" by simp
        finally have "(\<MM> \<downharpoonright> alive x) \<downharpoonright> {\<eta> \<in> space (\<MM> \<downharpoonright> alive x). X \<eta> > x + t} =
          \<MM> \<downharpoonright> {\<eta> \<in> space \<MM>. X \<eta> > x + t}" .
        thus ?thesis by simp
      qed
      also have "\<dots> = \<P>(\<xi> in \<MM>. x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t)"
        by (rewrite MM_PS.cond_prob_space_cond_prob, simp_all add: pred_def sets.sets_Collect_conj)
      finally show "\<P>(\<xi> in (\<MM> \<downharpoonright> alive x). ?rngX \<xi> \<bar> X \<xi> > x + t) =
        \<P>(\<xi> in \<MM>. x + t < X \<xi> \<and> X \<xi> \<le> x + t + dt \<bar> X \<xi> > x + t)" .
    qed
    thus ?thesis
      apply -
      by (rule Lim_cong, rule eventually_at_rightI[of 0 1]; simp)
  qed
  also have "\<dots> = $\<mu>_(x+t)" unfolding force_mortal_def MM_PS.hazard_rate_def by simp
  finally show ?thesis .
qed

lemma pdfTx_p_mu: "pdfT x t = $p_{t&x} * $\<mu>_(x+t)"
  if "(cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) differentiable at t" "t > 0" for t::real
proof (cases \<open>x+t < $\<psi>\<close>)
  case True
  hence [simp]: "t \<ge> 0" and "(ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t \<noteq> 0" 
    using that p_0_equiv unfolding survive_def by auto
  have "deriv (cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))) t =
    ccdf (distr (\<MM> \<downharpoonright> alive x) borel (T x)) t * alivex_PS.hazard_rate (T x) t"
    by (rule alivex_PS.deriv_cdf_hazard_rate; simp add: that)
  thus ?thesis unfolding survive_def pdfT_def using hazard_rate_Tx_mu True that by simp
next
  case False
  hence "x+t \<ge> $\<psi>" by simp
  thus ?thesis using pdfTx_beyond_0 mu_beyond_0 by simp
qed

lemma deriv_t_p_mu: "deriv (\<lambda>s. $p_{s&x}) t = - $p_{t&x} * $\<mu>_(x+t)"
  if "(\<lambda>s. $p_{s&x}) differentiable at t" "t > 0" for t::real
proof -
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  have diff: "?cdfTx differentiable at t"
    using that distrTx_RD.differentiable_cdf_ccdf unfolding survive_def by blast
  hence "deriv ?cdfTx t = $p_{t&x} * $\<mu>_(x+t)" using that pdfTx_p_mu pdfT_def by simp
  moreover have "deriv ?cdfTx t = - deriv (\<lambda>s. $p_{s&x}) t"
    using that diff distrTx_RD.deriv_cdf_ccdf unfolding survive_def by presburger
  ultimately show ?thesis by simp
qed

lemma pdfTx_p_mu_AE: "AE s in lborel. s > 0 \<longrightarrow> pdfT x s = $p_{s&x} * $\<mu>_(x+s)"
proof -
  let ?cdfX = "cdf (distr \<MM> borel X)"
  let ?cdfTx = "cdf (distr (\<MM> \<downharpoonright> alive x) borel (T x))"
  from cdfX_differentiable_AE obtain N
    where diff: "\<And>r. r \<in> space lborel - N \<Longrightarrow> ?cdfX differentiable at r"
      and null: "N \<in> null_sets lborel"
    using AE_E3 by blast
  let ?N' = "{s. x+s \<in> N}"
  have "?N' \<in> null_sets lborel"
    using null_sets_translation[of N "-x", simplified] null by (simp add: add.commute)
  moreover have "{s \<in> space lborel. \<not> (s > 0 \<longrightarrow> pdfT x s = $p_{s&x} * $\<mu>_(x+s))} \<subseteq> ?N'"
  proof (rewrite Compl_subset_Compl_iff[THEN sym], safe)
    fix s::real
    assume "s \<in> space lborel" and "x+s \<notin> N" and "s > 0"
    thus "pdfT x s = $p_{s&x} * $\<mu>_(x+s)"
      apply (intro pdfTx_p_mu, simp_all)
      by (rewrite differentiable_cdfX_cdfTx[THEN sym]; simp add: diff)
  qed
  ultimately show ?thesis using AE_I'[of ?N'] by simp
qed

lemma LBINT_p_mu_q: "LBINT s:{f<..f+t}. $p_{s&x} * $\<mu>_(x+s) = $q_{f\<bar>t&x}"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
proof -
  have "LBINT s:{f<..f+t}. $p_{s&x} * $\<mu>_(x+s) = LBINT s:{f<..f+t}. pdfT x s"
    apply (rule set_lebesgue_integral_cong_AE; simp)
     apply (simp add: survive_def)
    using pdfTx_p_mu_AE apply (rule AE_mp)
    using that by (intro always_eventually; simp add: ereal_less_le)
  also have "\<dots> = enn2real (\<integral>\<^sup>+s\<in>{f<..f+t}. ennreal (pdfT x s) \<partial>lborel)"
  proof -
    have "\<integral>\<^sup>+s\<in>{f<..f+t}. ennreal (pdfT x s) \<partial>lborel < \<top>"
    proof -
      have "\<integral>\<^sup>+s\<in>{f<..f+t}. ennreal (pdfT x s) \<partial>lborel \<le> \<integral>\<^sup>+s. ennreal (pdfT x s) \<partial>lborel"
        by (smt (verit) indicator_simps le_zero_eq linorder_le_cases
            mult.right_neutral mult_zero_right nn_integral_mono)
      also have "\<dots> < \<top>" using nn_integral_pdfTx_1 by simp
      finally show ?thesis .
    qed
    thus ?thesis
      unfolding set_lebesgue_integral_def
      by (rewrite enn2real_nn_integral_eq_integral[where g="\<lambda>s. pdfT x s * indicator {f<..f+t} s"])
        (simp_all add: pdfTx_nonneg mult.commute ennreal_indicator ennreal_mult')
  qed
  also have "\<dots> = measure (density lborel (pdfT x)) {f<..f+t}"
    unfolding measure_def by (rewrite emeasure_density; simp)
  also have "\<dots> = measure (distr (\<MM> \<downharpoonright> alive x) lborel (T x)) {f<..f+t}"
    using distributed_pdfTx unfolding distributed_def by simp
  also have "\<dots> =
    cdf (distr (\<MM> \<downharpoonright> alive x) lborel (T x)) (f+t) - cdf (distr (\<MM> \<downharpoonright> alive x) lborel (T x)) f"
    using that finite_borel_measure.cdf_diff_eq2
    by (smt (verit) distrTx_RD.finite_borel_measure_axioms distr_cong sets_lborel)
  also have "\<dots> = $q_{f\<bar>t&x}"
    using q_defer_q die_def that by (metis distr_cong sets_lborel x_lt_psi)
  finally show ?thesis .
qed

lemma set_integrable_p_mu: "set_integrable lborel {f<..f+t} (\<lambda>s. $p_{s&x} * $\<mu>_(x+s))"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
proof -
  have "(\<lambda>s. $p_{s&x}) \<in> borel_measurable borel" unfolding survive_def by simp
  moreover have "AE s in lborel. f < s \<and> s \<le> f + t \<longrightarrow> $p_{s&x} * $\<mu>_(x+s) = pdfT x s"
    using pdfTx_p_mu_AE apply (rule AE_mp)
    using that by (intro always_eventually; simp add: ereal_less_le)
  moreover have "set_integrable lborel {f<..f+t} (pdfT x)" using pdfTx_set_integrable by simp
  ultimately show ?thesis by (rewrite set_integrable_cong_AE[where g="pdfT x"]; simp)
qed

lemma p_mu_has_integral_q_defer_Ioc:
  "((\<lambda>s. $p_{s&x} * $\<mu>_(x+s)) has_integral $q_{f\<bar>t&x}) {f<..f+t}"
  if "t \<ge> 0" "f \<ge> 0" for t f :: real
  apply (rewrite LBINT_p_mu_q[THEN sym], simp_all add: that)
  apply (rewrite set_borel_integral_eq_integral, simp add: set_integrable_p_mu that)
  by (rewrite has_integral_integral[THEN sym];
      simp add: set_borel_integral_eq_integral set_integrable_p_mu that)

lemma p_mu_has_integral_q_defer_Icc:
  "((\<lambda>s. $p_{s&x} * $\<mu>_(x+s)) has_integral $q_{f\<bar>t&x}) {f..f+t}" if "t \<ge> 0" "f \<ge> 0" for t f :: real
proof -
  have "negligible {f}" by simp
  hence [simp]: "negligible ({f..f+t} - {f<..f+t})"
    by (smt (verit) Diff_iff atLeastAtMost_iff greaterThanAtMost_iff insertI1
        negligible_sing negligible_subset subsetI)
  have [simp]: "negligible ({f<..f+t} - {f..f+t})" by (simp add: subset_eq)
  show ?thesis
    apply (rewrite has_integral_spike_set_eq[where T="{f<..f+t}"])
      apply (rule negligible_subset[of "{f..f+t} - {f<..f+t}"], simp, blast)
     apply (rule negligible_subset[of "{f<..f+t} - {f..f+t}"], simp, blast)
    using p_mu_has_integral_q_defer_Ioc that by simp
qed

corollary p_mu_has_integral_q_Icc:
  "((\<lambda>s. $p_{s&x} * $\<mu>_(x+s)) has_integral $q_{t&x}) {0..t}" if "t \<ge> 0" for t::real
  using p_mu_has_integral_q_defer_Icc[where f=0] that by simp

corollary p_mu_integrable_on_Icc:
  "(\<lambda>s. $p_{s&x} * $\<mu>_(x+s)) integrable_on {0..t}" if "t \<ge> 0" for t::real
  using p_mu_has_integral_q_Icc that by auto

lemma e_ennreal_p_mu: "(\<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) =
  \<integral>\<^sup>+s\<in>{0..}. ennreal ($p_{s&x} * $\<mu>_(x+s) * s) \<partial>lborel"
proof -
  have [simp]: "sym_diff {0..} {0<..} = {0::real}" by force
  have "(\<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)) = \<integral>\<^sup>+s\<in>{0..}. ennreal (pdfT x s * s) \<partial>lborel"
    by (rewrite nn_integral_T_pdfT[where g="\<lambda>s. s"]; simp)
  also have "\<dots> = \<integral>\<^sup>+s\<in>{0<..}. ennreal (pdfT x s * s) \<partial>lborel"
    by (rewrite nn_integral_null_delta; force)
  also have "\<dots> = \<integral>\<^sup>+s\<in>{0<..}. ennreal ($p_{s&x} * $\<mu>_(x+s) * s) \<partial>lborel"
    apply (rule nn_integral_cong_AE)
    using pdfTx_p_mu_AE apply (rule AE_mp, intro AE_I2) by force
  also have "\<dots> = \<integral>\<^sup>+s\<in>{0..}. ennreal ($p_{s&x} * $\<mu>_(x+s) * s) \<partial>lborel"
    by (rewrite nn_integral_null_delta[THEN sym]; force)
  finally show ?thesis .
qed

lemma e_LBINT_p_mu: "$e`\<circ>_x = LBINT s:{0..}. $p_{s&x} * $\<mu>_(x+s) * s"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
proof -
  let ?f = "\<lambda>s. $p_{s&x} * $\<mu>_(x+s) * s"
  have [simp]: "(\<lambda>s. ?f s * indicat_real {0..} s) \<in> borel_measurable borel"
    by measurable (simp_all add: survive_def)
  hence [simp]: "(\<lambda>s. indicat_real {0..} s * ?f s) \<in> borel_measurable borel"
    by (meson measurable_cong mult.commute)
  have [simp]: "AE s in lborel. ?f s * indicat_real {0..} s \<ge> 0"
  proof -
    have "AE s in lborel. pdfT x s * s * indicat_real {0..} s \<ge> 0"
      using pdfTx_nonneg pdfTx_nonpos_0 x_lt_psi
      by (intro AE_I2) (smt (verit, del_insts) indicator_pos_le mult_eq_0_iff mult_nonneg_nonneg)
    thus ?thesis
      apply (rule AE_mp)
      using pdfTx_p_mu_AE apply (rule AE_mp)
      by (rule AE_I2) (metis atLeast_iff indicator_simps(2) mult_eq_0_iff order_le_less)
  qed
  hence [simp]: "AE s in lborel. indicat_real {0..} s * ?f s \<ge> 0"
    by (metis (no_types, lifting) AE_cong mult.commute)
  show ?thesis
  proof (cases \<open>integrable (\<MM> \<downharpoonright> alive x) (T x)\<close>)
    case True
    hence "ennreal ($e`\<circ>_x) = \<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)"
      unfolding life_expect_def apply (rewrite nn_integral_eq_integral, simp_all)
      by (smt (verit) AE_I2 alivex_Tx_pos)
    also have "\<dots> = \<integral>\<^sup>+s. ennreal (?f s * indicat_real {0..} s) \<partial>lborel"
      by (simp add: nn_integral_set_ennreal e_ennreal_p_mu)
    also have "\<dots> = ennreal (LBINT s:{0..}. ?f s)"
    proof -
      have "integrable lborel (\<lambda>s. ?f s * indicat_real {0..} s)"
      proof -
        have "(\<integral>\<^sup>+s. ennreal (?f s * indicat_real {0..} s) \<partial>lborel) < \<infinity>"
          by (metis calculation ennreal_less_top infinity_ennreal_def)
        thus ?thesis by (intro integrableI_nonneg; simp)
      qed
      thus ?thesis
        unfolding set_lebesgue_integral_def
        by (rewrite nn_integral_eq_integral, simp_all) (meson mult.commute)
    qed
    finally have "ennreal ($e`\<circ>_x) = ennreal (LBINT s:{0..}. ?f s)" .
    moreover have "LBINT s:{0..}. ?f s \<ge> 0"
      unfolding set_lebesgue_integral_def by (rule integral_nonneg_AE) simp
    ultimately show ?thesis using e_nonneg by simp
  next
    case False
    hence "$e`\<circ>_x = 0" unfolding life_expect_def using not_integrable_integral_eq by force
    also have "\<dots> = LBINT s:{0..}. ?f s"
    proof -
      have "\<infinity> = \<integral>\<^sup>+\<xi>. ennreal (T x \<xi>) \<partial>(\<MM> \<downharpoonright> alive x)"
        using nn_integral_nonneg_infinite False
        by (smt (verit) AE_cong Tx_alivex_measurable alivex_PS.AE_prob_1 alivex_PS.prob_space
            alivex_Tx_pos nn_integral_cong)
      hence "0 = enn2real (\<integral>\<^sup>+s\<in>{0..}. ennreal (?f s) \<partial>lborel)" using e_ennreal_p_mu by simp
      also have "\<dots> = LBINT s:{0..}. ?f s"
        unfolding set_lebesgue_integral_def apply (rewrite integral_eq_nn_integral, simp_all)
        by (simp add: indicator_mult_ennreal mult.commute)
      finally show ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

lemma e_integral_p_mu: "$e`\<circ>_x = integral {0..} (\<lambda>s. $p_{s&x} * $\<mu>_(x+s) * s)"
  \<comment> \<open>Note that 0 = 0 holds when the life expectation diverges.\<close>
proof -
  have "LBINT s:{0..}. $p_{s&x} * $\<mu>_(x+s) * s = integral {0..} (\<lambda>s. $p_{s&x} * $\<mu>_(x+s) * s)"
  proof -
    have "AE s in lborel. s \<ge> 0 \<longrightarrow> $p_{s&x} * $\<mu>_(x+s) * s \<ge> 0"
    proof -
      have "AE s in lborel. $\<mu>_(x+s) \<ge> 0" by (rule AE_translation, rule mu_nonneg_AE)
      with p_nonneg show ?thesis by force
    qed
    moreover have "(\<lambda>s. $p_{s&x} * $\<mu>_(x+s) * s) \<in> borel_measurable borel"
      unfolding survive_def by simp
    ultimately show ?thesis by (intro set_borel_integral_eq_integral_nonneg_AE; simp)
  qed
  thus ?thesis using e_LBINT_p_mu by simp
qed

end

lemma p_has_real_derivative_x_ccdfX:
  "((\<lambda>y. $p_{t&y}) has_real_derivative
    ((deriv svl (x+t) * svl x - svl (x+t) * deriv svl x) / (svl x)\<^sup>2)) (at x)"
  if "svl \<equiv> ccdf (distr \<MM> borel X)" "svl differentiable at x" "svl differentiable at (x+t)"
    "t \<ge> 0" "x < $\<psi>" for x t :: real
proof -
  have "open {y. svl differentiable at y}" using ccdfX_differentiable_open_set that by simp
  with that obtain e0 where e0_pos: "e0 > 0" and ball_e0: "ball x e0 \<subseteq> {y. svl differentiable at y}"
    using open_contains_ball by blast
  define e where "e \<equiv> if $\<psi> < \<infinity> then min e0 (real_of_ereal $\<psi> - x) else e0"
  have "e > 0 \<and> ball x e \<subseteq> {y. svl y \<noteq> 0 \<and> svl differentiable at y}"
  proof (cases \<open>$\<psi> < \<infinity>\<close>)
    case True
    hence "e > 0"
    proof -
      have "real_of_ereal $\<psi> - x > 0" using not_inftyI True that by force
      with e0_pos show ?thesis unfolding e_def using True by simp
    qed
    moreover have "ball x e \<subseteq> {y. svl y \<noteq> 0}"
    proof -
      have "e \<le> real_of_ereal $\<psi> - x" unfolding e_def using True by simp
      hence "ball x e \<subseteq> {..< real_of_ereal $\<psi>}" unfolding ball_def dist_real_def by force
      thus ?thesis using that ccdfX_0_equiv
        using True ereal_less_real_iff psi_nonneg by auto
    qed
    moreover have "ball x e \<subseteq> {y. svl differentiable at y}"
    proof -
      have "e \<le> e0" unfolding e_def using True by simp
      hence "ball x e \<subseteq> ball x e0" by force
      with ball_e0 show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  next
    case False
    hence "ball x e \<subseteq> {y. svl y \<noteq> 0}" using ccdfX_0_equiv that by simp
    with False show ?thesis unfolding e_def using e0_pos ball_e0 by force
  qed
  hence e_pos: "e > 0" and ball_e: "ball x e \<subseteq> {y. svl y \<noteq> 0 \<and> svl differentiable at y}" by auto
  hence ball_svl: "\<And>y. y \<in> ball x e \<Longrightarrow> svl y \<noteq> 0 \<and> svl field_differentiable at y"
    using differentiable_eq_field_differentiable_real by blast
  hence "\<And>y. y \<in> ball x e \<Longrightarrow> $p_{t&y} = svl (y+t) / svl y"
    unfolding survive_def using that ccdfX_0_equiv by (rewrite ccdfTx_ccdfX, simp_all) force
  moreover from ball_svl have "((\<lambda>y. svl (y+t) / svl y) has_real_derivative
    ((deriv svl (x+t) * svl x - svl (x+t) * deriv svl x) / (svl x)\<^sup>2)) (at x)"
    apply (rewrite power2_eq_square)
    apply (rule DERIV_divide)
    using DERIV_deriv_iff_real_differentiable DERIV_shift that apply blast
    using that DERIV_deriv_iff_real_differentiable apply simp
    by (simp add: e_pos)
  ultimately show ?thesis
    using e_pos
    apply (rewrite has_field_derivative_cong_eventually[where g="\<lambda>y. svl (y+t) / svl y"], simp_all)
    by (smt (verit) dist_commute eventually_at)
qed

lemma p_has_real_derivative_x_p_mu:
  "((\<lambda>y. $p_{t&y}) has_real_derivative $p_{t&x} * ($\<mu>_x - $\<mu>_(x+t))) (at x)"
  if "ccdf (distr \<MM> borel X) differentiable at x" "ccdf (distr \<MM> borel X) differentiable at (x+t)"
    "t \<ge> 0" "x < $\<psi>" for x t :: real
proof (cases \<open>x+t < $\<psi>\<close>)
  case True
  let ?svl = "ccdf (distr \<MM> borel X)"
  have [simp]: "?svl x \<noteq> 0" using that ccdfX_0_equiv by (smt (verit) le_ereal_le linorder_not_le)
  have [simp]: "?svl field_differentiable at (x+t)"
    using that differentiable_eq_field_differentiable_real by simp
  have "((\<lambda>y. $p_{t&y}) has_real_derivative
    ((deriv ?svl (x+t) * ?svl x - ?svl (x+t) * deriv ?svl x) / (?svl x)\<^sup>2)) (at x)"
    using p_has_real_derivative_x_ccdfX that by simp
  moreover have "(deriv ?svl (x+t) * ?svl x - ?svl (x+t) * deriv ?svl x) / (?svl x)\<^sup>2 =
    $p_{t&x} * ($\<mu>_x - $\<mu>_(x+t))" (is "?LHS = ?RHS")
  proof -
    have "deriv ?svl (x+t) = deriv (\<lambda>y. ?svl (y+t)) x"
      using that by (metis DERIV_deriv_iff_real_differentiable DERIV_imp_deriv DERIV_shift)
    hence "?LHS = (deriv (\<lambda>y. ?svl (y+t)) x * ?svl x - ?svl (x+t) * deriv ?svl x) / (?svl x)\<^sup>2"
      by simp
    also have "\<dots> = (deriv (\<lambda>y. ?svl (y+t)) x - ?svl (x+t) * deriv ?svl x / ?svl x) / ?svl x"
      by (simp add: add_divide_eq_if_simps(4) power2_eq_square)
    also have "\<dots> = (- ?svl (x+t) * $\<mu>_(x+t) + ?svl (x+t) * $\<mu>_x) / ?svl x"
    proof -
      have "deriv (\<lambda>y. ?svl (y+t)) x = - ?svl (x+t) * $\<mu>_(x+t)"
        apply (rewrite add.commute, rewrite deriv_shift[THEN sym], rewrite add.commute, simp)
        using add.commute that by (metis MM_PS.deriv_ccdf_hazard_rate X_RV force_mortal_def)
      moreover have "- ?svl (x+t) * deriv ?svl x / ?svl x = ?svl (x+t) * $\<mu>_x"
        using that by (simp add: MM_PS.deriv_ccdf_hazard_rate force_mortal_def)
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = ?svl (x+t) * ($\<mu>_x - $\<mu>_(x+t)) / ?svl x" by (simp add: mult_diff_mult)
    also have "\<dots> = ?RHS" unfolding survive_def using ccdfTx_ccdfX that by simp
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by simp
next
  case False
  hence ptx_0: "$p_{t&x} = 0" using p_0_equiv that by simp
  moreover have "((\<lambda>y. $p_{t&y}) has_real_derivative 0) (at x)"
  proof -
    have "\<And>y. x < y \<Longrightarrow> y < $\<psi> \<Longrightarrow> $p_{t&y} = 0"
      using False p_0_equiv that by (smt (verit, ccfv_SIG) ereal_less_le linorder_not_le)
    hence "\<forall>\<^sub>F x in at_right x. $p_{t&x} = 0"
      apply (rewrite eventually_at_right_field)
      using that by (meson ereal_dense2 ereal_le_less less_eq_ereal_def less_ereal.simps)
    hence "((\<lambda>y. $p_{t&y}) has_real_derivative 0) (at_right x)"
      using ptx_0 by (rewrite has_field_derivative_cong_eventually[where g="\<lambda>_. 0"]; simp)
    thus ?thesis
      using vector_derivative_unique_within p_has_real_derivative_x_ccdfX that
      by (metis has_field_derivative_at_within has_real_derivative_iff_has_vector_derivative
          trivial_limit_at_right_real)
  qed
  ultimately show ?thesis by simp
qed

corollary deriv_x_p_mu: "deriv (\<lambda>y. $p_{t&y}) x = $p_{t&x} * ($\<mu>_x - $\<mu>_(x+t))"
  if "ccdf (distr \<MM> borel X) differentiable at x" "ccdf (distr \<MM> borel X) differentiable at (x+t)"
    "t \<ge> 0" "x < $\<psi>" for x t :: real
  using that p_has_real_derivative_x_p_mu DERIV_imp_deriv by blast

lemma e_has_derivative_mu_e: "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if "\<And>x. x\<in>{a<..<b} \<Longrightarrow> set_integrable lborel {x..} (ccdf (distr \<MM> borel X))"
    "ccdf (distr \<MM> borel X) differentiable at x" "x\<in>{a<..<b}" "b \<le> $\<psi>"
  for a b x :: real
proof -
  let ?svl = "ccdf (distr \<MM> borel X)"
  have x_lt_psi[simp]: "x < $\<psi>" using that ereal_le_less by simp
  hence svlx_neq0[simp]: "?svl x \<noteq> 0" by (simp add: ccdfX_0_equiv linorder_not_le)
  define d ::real where "d \<equiv> min (b-x) (x-a)"
  have d_pos: "d > 0" unfolding d_def using that ereal_less_real_iff by force
  have e_svl: "\<And>y. y < $\<psi> \<Longrightarrow> $e`\<circ>_y = (LBINT t:{0..}. ?svl (y+t)) / ?svl y"
    apply (rewrite e_LBINT_p, simp)
    apply (rewrite set_integral_divide_zero[THEN sym])
    apply (rule set_lebesgue_integral_cong, simp_all)
    unfolding survive_def using ccdfTx_ccdfX by force
  have "((\<lambda>y. LBINT t:{0..}. ?svl (y+t)) has_real_derivative (- ?svl x)) (at x)"
  proof -
    { fix y assume "dist y x < d"
      hence y_ab: "y \<in> {a<..<b}" unfolding d_def dist_real_def by force
      hence "set_integrable lborel {y..} ?svl" using that by simp
      hence "set_integrable lborel (einterval y \<infinity>) ?svl"
        by (rewrite set_integrable_discrete_difference[where X="{y}"]; simp) force
      moreover have "\<And>u. ((\<lambda>u. u-y) has_real_derivative (1-0)) (at u)"
        by (rule derivative_intros) auto
      moreover have "\<And>u. y < u \<Longrightarrow> isCont (\<lambda>t. ?svl (y+t)) (u-y)"
        apply (rewrite add.commute, rewrite isCont_shift, simp)
        using ccdfX_continuous continuous_on_eq_continuous_within by blast
      moreover have "((ereal \<circ> (\<lambda>u. u-y) \<circ> real_of_ereal) \<longlongrightarrow> 0) (at_right (ereal y))"
        by (smt (verit, ccfv_SIG) LIM_zero Lim_cong_within ereal_tendsto_simps1(2)
            ereal_tendsto_simps2(1) tendsto_ident_at zero_ereal_def)
      moreover have "((ereal \<circ> (\<lambda>u. u-y) \<circ> real_of_ereal) \<longlongrightarrow> \<infinity>) (at_left \<infinity>)"
      proof -
        have "\<And>r u. r+y+1 \<le> u \<Longrightarrow> r < u-y" by auto
        hence "\<And>r. \<forall>\<^sub>F u in at_top. r < u - y" by (rule eventually_at_top_linorderI)
        thus ?thesis by (rewrite ereal_tendsto_simps, rewrite tendsto_PInfty) simp
      qed
      ultimately have "(LBINT t=0..\<infinity>. ?svl (y+t)) = (LBINT u=y..\<infinity>. ?svl (y+(u-y)) * 1)"
        using distrX_RD.ccdf_nonneg by (intro interval_integral_substitution_nonneg(2); simp)
      moreover have "(LBINT t:{0..}. ?svl (y+t)) = (LBINT t=0..\<infinity>. ?svl (y+t))"
        unfolding interval_lebesgue_integral_def einterval_def apply simp
        by (rule set_integral_discrete_difference[where X="{0}"]; force)
      moreover have "(LBINT u=y..\<infinity>. ?svl (y+(u-y))*1) = (LBINT u:{y..}. ?svl u)"
        unfolding interval_lebesgue_integral_def einterval_def apply simp
        by (rule set_integral_discrete_difference[where X="{y}"]; force)
      ultimately have "(LBINT t:{0..}. ?svl (y+t)) = (LBINT u:{y..}. ?svl u)" by simp }
    hence "\<forall>\<^sub>F y in nhds x. LBINT t:{0..}. ?svl (y+t) = LBINT u:{y..}. ?svl u"
      using d_pos by (rewrite eventually_nhds_metric) auto
    moreover have "((\<lambda>y. LBINT u:{y..}. ?svl u) has_real_derivative (- ?svl x)) (at x)"
    proof -
      have "((\<lambda>y. integral {y..b} ?svl) has_real_derivative (- ?svl x)) (at x within {a..b})"
        using that apply (intro integral_has_real_derivative'; simp)
        using ccdfX_continuous continuous_on_subset by blast
      hence "((\<lambda>y. integral {y..b} ?svl) has_real_derivative (- ?svl x)) (at x)"
        using that apply (rewrite at_within_open[where S="{a<..<b}", THEN sym], simp_all)
        by (rule DERIV_subset[where s="{a..b}"]) auto
      moreover have "\<forall>\<^sub>F y in nhds x. LBINT u:{y..b}. ?svl u = integral {y..b} ?svl"
        apply (rewrite eventually_nhds_metric)
        using d_pos by (metis ccdfX_integrable_Icc set_borel_integral_eq_integral(2))
      ultimately have "((\<lambda>y. LBINT u:{y..b}. ?svl u) has_real_derivative (- ?svl x)) (at x)"
        by (rewrite DERIV_cong_ev; simp)
      hence "((\<lambda>y. (LBINT u:{y..b}. ?svl u) + (LBINT u:{b<..}. ?svl u)) has_real_derivative
        (- ?svl x)) (at x)"
        by (rewrite to "- ?svl x + 0" add_0_right[THEN sym], rule DERIV_add; simp)
      moreover have "\<forall>\<^sub>F y in nhds x.
        LBINT u:{y..}. ?svl u = (LBINT u:{y..b}. ?svl u) + (LBINT u:{b<..}. ?svl u)"
      proof -
        { fix y assume "dist y x < d"
          hence y_ab: "y \<in> {a<..<b}" unfolding d_def dist_real_def by force
          hence "set_integrable lborel {y..} ?svl" using that by simp
          hence "set_integrable lborel {y..b} ?svl" "set_integrable lborel {b<..} ?svl"
            apply (rule set_integrable_subset, simp_all)+
            using y_ab by force
          moreover have "{y..b} \<inter> {b<..} = {}" "{y..} = {y..b} \<union> {b<..}" using y_ab by force+
          ultimately have "LBINT u:{y..}. ?svl u = (LBINT u:{y..b}. ?svl u) + (LBINT u:{b<..}. ?svl u)"
            using set_integral_Un by simp }
        thus ?thesis using d_pos by (rewrite eventually_nhds_metric) blast
      qed
      ultimately show ?thesis by (rewrite has_field_derivative_cong_ev; simp)
    qed
    ultimately show ?thesis by (rewrite DERIV_cong_ev; simp)
  qed
  moreover have "(?svl has_real_derivative (deriv ?svl x)) (at x)"
    using that DERIV_deriv_iff_real_differentiable by blast
  ultimately have "((\<lambda>y. (LBINT t:{0..}. ?svl (y+t)) / ?svl y) has_real_derivative
    ((- ?svl x) * ?svl x - (LBINT t:{0..}. ?svl (x+t)) * deriv ?svl x) / (?svl x * ?svl x)) (at x)"
    by (rule DERIV_divide) simp
  moreover have "eventually (\<lambda>y. (LBINT t:{0..}. ?svl (y+t)) / ?svl y = $e`\<circ>_y) (at x)"
  proof -
    { fix y assume "dist y x < d" "y \<noteq> x"
      hence "y < $\<psi>"
        unfolding dist_real_def d_def using that ereal_le_less by fastforce
      hence "$e`\<circ>_y = (LBINT t:{0..}. ?svl (y+t)) / ?svl y" by (rule e_svl) }
    thus ?thesis
      apply (rewrite eventually_at_filter, rewrite eventually_nhds_metric)
      using d_pos that by metis
  qed
  ultimately have "((\<lambda>y. $e`\<circ>_y) has_real_derivative
    ((- ?svl x) * ?svl x - (LBINT t:{0..}. ?svl (x+t)) * deriv ?svl x) / (?svl x * ?svl x)) (at x)"
    using e_svl by (rewrite has_field_derivative_cong_eventually[THEN sym]; simp)
  moreover have
    "((- ?svl x) * ?svl x - (LBINT t:{0..}. ?svl (x+t)) * deriv ?svl x) / (?svl x * ?svl x) =
      $\<mu>_x * $e`\<circ>_x - 1" (is "?LHS = ?RHS")
  proof -
    have "?LHS = -1 + (LBINT t:{0..}. ?svl (x+t)) / ?svl x * (- deriv ?svl x / ?svl x)"
      by simp (smt (verit) svlx_neq0 add_divide_distrib divide_eq_minus_1_iff
          mult_minus_left real_divide_square_eq)
    also have "\<dots> = -1 + $e`\<circ>_x * $\<mu>_x" using e_svl mu_deriv_ccdf that by force
    also have "\<dots> = ?RHS" by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

corollary e_has_derivative_mu_e': "((\<lambda>x. $e`\<circ>_x) has_real_derivative ($\<mu>_x * $e`\<circ>_x - 1)) (at x)"
  if "\<And>x. x\<in>{a<..<b} \<Longrightarrow> ccdf (distr \<MM> borel X) integrable_on {x..}"
    "ccdf (distr \<MM> borel X) differentiable at x" "x\<in>{a<..<b}" "b \<le> $\<psi>"
  for a b x :: real
  using that apply (intro e_has_derivative_mu_e[where a=a], simp_all)
  using distrX_RD.ccdf_nonneg by (rewrite integrable_on_iff_set_integrable_nonneg; simp)

subsubsection \<open>Properties of Curtate Life Expectation\<close>

context
  fixes x::real
  assumes x_lt_psi[simp]: "x < $\<psi>"
begin

lemma isCont_p_nat: "isCont (\<lambda>t. $p_{t&x}) (k + (1::real))" for k::nat
proof -
  fix k::nat
  have "continuous_on {0<..} (\<lambda>t. $p_{t&x})"
    unfolding survive_def
    using ccdfTx_continuous_on_nonneg continuous_on_subset Ioi_le_Ico x_lt_psi by blast
  hence "\<forall>t\<in>{0<..}. isCont (\<lambda>t. $p_{t&x}) t"
    using continuous_on_eq_continuous_at open_greaterThan by blast
  thus "isCont (\<lambda>t. $p_{t&x}) (real k+1)" by force
qed

lemma curt_e_sum_p_smooth: "$e_x = (\<Sum>k. $p_{k+1&x})" if "summable (\<lambda>k. $p_{k+1&x})"
  using curt_e_sum_p isCont_p_nat that by simp

lemma curt_e_rec_smooth: "$e_x = $p_x * (1 + $e_(x+1))" if "summable (\<lambda>k. $p_{k+1&x})" "x+1 < $\<psi>"
  using curt_e_rec isCont_p_nat that by simp

lemma curt_e_sum_p_finite_smooth: "$e_x = (\<Sum>k<n. $p_{k+1&x})" if "x+n+1 > $\<psi>" for n::nat
  using curt_e_sum_p_finite isCont_p_nat that by simp

lemma temp_curt_e_sum_p_smooth: "$e_{x:n} = (\<Sum>k<n. $p_{k+1&x})" for n::nat
  using temp_curt_e_sum_p isCont_p_nat by simp

lemma temp_curt_e_rec_smooth: "$e_{x:n} = $p_x * (1 + $e_{x+1:n-1})"
  if "x+1 < $\<psi>" "n \<noteq> 0" for n::nat
  using temp_curt_e_rec isCont_p_nat that by simp

end

end

subsection \<open>Finite Survival Function\<close>

locale finite_survival_function = survival_model +
  assumes psi_finite[simp]: "$\<psi> < \<infinity>"
begin

definition ult_age :: nat ("$\<omega>")
  where "$\<omega> \<equiv> LEAST x::nat. ccdf (distr \<MM> borel X) x = 0"
    \<comment> \<open>the conventional notation for ultimate age\<close>

lemma ccdfX_ceil_psi_0: "ccdf (distr \<MM> borel X) \<lceil>real_of_ereal $\<psi>\<rceil> = 0"
proof -
  have "real_of_ereal $\<psi> \<le> \<lceil>real_of_ereal $\<psi>\<rceil>" by simp
  thus ?thesis using ccdfX_0_equiv psi_finite ccdfX_psi_0 le_ereal_le by presburger
qed

lemma ccdfX_omega_0: "ccdf (distr \<MM> borel X) $\<omega> = 0"
  unfolding ult_age_def
proof (rule LeastI_ex)
  have "\<lceil>real_of_ereal $\<psi>\<rceil> \<ge> 0" using psi_nonneg real_of_ereal_pos by fastforce
  thus "\<exists>x::nat. ccdf (distr \<MM> borel X) (real x) = 0"
    using ccdfX_ceil_psi_0 by (metis of_int_of_nat_eq zero_le_imp_eq_int)
qed

corollary psi_le_omega: "$\<psi> \<le> $\<omega>"
  using ccdfX_0_equiv ccdfX_omega_0 by blast

corollary omega_pos: "$\<omega> > 0"
  using psi_le_omega order.strict_iff_not by fastforce

lemma omega_ceil_psi: "$\<omega> = \<lceil>real_of_ereal $\<psi>\<rceil>"
proof (rule antisym)
  let ?cpsi = "\<lceil>real_of_ereal $\<psi>\<rceil>"
  have \<star>: "?cpsi \<ge> 0" using psi_nonneg real_of_ereal_pos by fastforce
  moreover have "ccdf (distr \<MM> borel X) ?cpsi = 0" by (rule ccdfX_ceil_psi_0)
  ultimately have "$\<omega> \<le> nat ?cpsi"
    unfolding ult_age_def using wellorder_Least_lemma of_nat_nat by smt
  thus "int $\<omega> \<le> ?cpsi" using le_nat_iff \<star> by blast
next
  show "\<lceil>real_of_ereal $\<psi>\<rceil> \<le> int $\<omega>"
    using psi_le_omega by (simp add: ceiling_le_iff real_of_ereal_ord_simps(2))
qed

lemma ccdfX_0_equiv_nat: "ccdf (distr \<MM> borel X) x = 0 \<longleftrightarrow> x \<ge> $\<omega>" for x::nat
proof
  assume "ccdf (distr \<MM> borel X) (real x) = 0"
  thus "x \<ge> $\<omega>" unfolding ult_age_def using wellorder_Least_lemma by fastforce
next
  assume "x \<ge> $\<omega>"
  hence "ereal (real x) \<ge> $\<psi>" using psi_le_omega le_ereal_le of_nat_mono by blast
  thus "ccdf (distr \<MM> borel X) (real x) = 0" using ccdfX_0_equiv by simp
qed

lemma psi_le_iff_omega_le: "$\<psi> \<le> x \<longleftrightarrow> $\<omega> \<le> x" for x::nat
  using ccdfX_0_equiv ccdfX_0_equiv_nat by presburger

context 
  fixes x::nat
  assumes x_lt_omega[simp]: "x < $\<omega>"
begin

lemma x_lt_psi[simp]: "x < $\<psi>"
  using x_lt_omega psi_le_iff_omega_le by (meson linorder_not_less)

lemma p_0_1_nat: "$p_{0&x} = 1"
  using p_0_1 by simp

lemma p_0_equiv_nat: "$p_{t&x} = 0 \<longleftrightarrow> x+t \<ge> $\<omega>" for t::nat
  using psi_le_iff_omega_le p_0_equiv by (metis of_nat_add x_lt_psi)

lemma q_0_0_nat: "$q_{0&x} = 0"
  using p_q_1 p_0_1_nat by (smt (verit) x_lt_psi)

lemma q_1_equiv_nat: "$q_{t&x} = 1 \<longleftrightarrow> x+t \<ge> $\<omega>" for t::nat
  using p_q_1 p_0_equiv_nat by (smt (verit) x_lt_psi)

lemma q_defer_old_0_nat: "$q_{f\<bar>t&x} = 0" if "$\<omega> \<le> x+f" for f t :: nat
  using q_defer_old_0 psi_le_iff_omega_le that by (metis of_nat_0_le_iff of_nat_add x_lt_psi)

lemma curt_e_sum_P_finite_nat: "$e_x = (\<Sum>k<n. \<P>(\<xi> in \<MM>. T x \<xi> \<ge> k + 1 \<bar> T x \<xi> > 0))"
  if "x+n \<ge> $\<omega>" for n::nat
  apply (rule curt_e_sum_P_finite, simp)
  using that psi_le_iff_omega_le by (smt (verit) le_ereal_less of_nat_add)

lemma curt_e_sum_p_finite_nat: "$e_x = (\<Sum>k<n. $p_{k+1&x})"
  if "\<And>k::nat. k < n \<Longrightarrow> isCont (\<lambda>t. $p_{t&x}) (real k + 1)" "x+n \<ge> $\<omega>" for n::nat
  apply (rule curt_e_sum_p_finite, simp_all add: that)
  using that psi_le_iff_omega_le by (smt (verit) le_ereal_less of_nat_add)

end

lemma q_omega_1: "$q_($\<omega>-1) = 1"
  using q_1_equiv_nat
  by (metis diff_less dual_order.refl le_diff_conv of_nat_1 omega_pos zero_less_one)

end

end
