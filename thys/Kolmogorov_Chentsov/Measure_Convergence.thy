(* Title:      Kolmogorov_Chentsov/Measure_Convergence.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Convergence in measure"

theory Measure_Convergence
  imports "HOL-Probability.Probability"
begin

text \<open> We use measure rather than emeasure because ennreal is not a metric space, which we need to
  reason about convergence. By intersecting with the set of finite measure A, we don't run into issues
  where infinity is collapsed to 0.

  For finite measures this definition is equal to the definition without set A -- see below. \<close>

definition tendsto_measure :: "'b measure \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,metric_space}))
   \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "tendsto_measure M X l F \<equiv> (\<forall>n. X n \<in> borel_measurable M) \<and> l \<in> borel_measurable M \<and>
  (\<forall>\<epsilon> > 0. \<forall>A \<in> fmeasurable M.
  ((\<lambda>n. measure M ({\<omega> \<in> space M. dist (X n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlongrightarrow> 0) F)"

abbreviation (in prob_space) tendsto_prob  (infixr "\<longlongrightarrow>\<^sub>P" 55) where
  "(f \<longlongrightarrow>\<^sub>P l) F \<equiv> tendsto_measure M f l F"

lemma tendsto_measure_measurable[measurable_dest]:
  "tendsto_measure M X l F \<Longrightarrow> X n \<in> borel_measurable M"
  unfolding tendsto_measure_def by meson

lemma tendsto_measure_measurable_lim[measurable_dest]:
  "tendsto_measure M X l F \<Longrightarrow> l \<in> borel_measurable M"
  unfolding tendsto_measure_def by meson

lemma tendsto_measure_mono: "F \<le> F' \<Longrightarrow> tendsto_measure M f l F' \<Longrightarrow> tendsto_measure M f l F"
  unfolding tendsto_measure_def by (simp add: tendsto_mono)

lemma tendsto_measureI:
  assumes [measurable]: "\<And>n. X n \<in> borel_measurable M" "l \<in> borel_measurable M"
    and "\<And>\<epsilon> A. \<epsilon> > 0 \<Longrightarrow> A \<in> fmeasurable M \<Longrightarrow>
    ((\<lambda>n. measure M ({\<omega> \<in> space M. dist (X n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlongrightarrow> 0) F"
  shows "tendsto_measure M X l F"
  unfolding tendsto_measure_def using assms by fast

lemma (in finite_measure) finite_tendsto_measureI:
  assumes [measurable]: "\<And>n. f' n \<in> borel_measurable M" "f \<in> borel_measurable M"
    and "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>}) \<longlongrightarrow> 0) F"
  shows "tendsto_measure M f' f F"
proof (intro tendsto_measureI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  then have prob_conv: "((\<lambda>n. measure M {\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)}) \<longlongrightarrow> 0) F"
    using assms by simp
  fix A assume "A \<in> fmeasurable M"
  have "\<And>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)}) \<ge> 
            measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)"
    by (rule finite_measure_mono; measurable)
  then show "((\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)) \<longlongrightarrow> 0) F"
    by (simp add: tendsto_0_le[OF prob_conv, where K=1])
qed measurable

lemma (in finite_measure) finite_tendsto_measureD:
  assumes [measurable]: "tendsto_measure M f' f F"
  shows "(\<forall>\<epsilon> > 0. ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>}) \<longlongrightarrow> 0) F)"
proof -
  from assms have "((\<lambda>n. measure M ({\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>} \<inter> space M)) \<longlongrightarrow> 0) F"
    if "\<epsilon> > 0" for \<epsilon>
    unfolding tendsto_measure_def using that fmeasurable_eq_sets by blast
  then show ?thesis
    by (simp add: sets.Int_space_eq2[symmetric, where M=M])
qed

lemma (in finite_measure) tendsto_measure_leq:
  assumes [measurable]: "\<And>n. f' n \<in> borel_measurable M" "f \<in> borel_measurable M"
  shows "tendsto_measure M f' f F \<longleftrightarrow>
   (\<forall>\<epsilon> > 0. ((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) \<ge> \<epsilon>}) \<longlongrightarrow> 0) F)" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI, goal_cases)
  case 1
  {
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) > \<epsilon>/2}) \<longlongrightarrow> 0) F"
      using finite_tendsto_measureD[OF 1] half_gt_zero by blast
    then have "((\<lambda>n. measure M {\<omega> \<in> space M. dist (f' n \<omega>) (f \<omega>) \<ge> \<epsilon>}) \<longlongrightarrow> 0) F"
      apply (rule metric_tendsto_imp_tendsto)
      using \<open>\<epsilon> > 0\<close> by (auto intro!: eventuallyI finite_measure_mono)
  }
  then show ?case
    by simp
next
  case 2
  {
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have *: "((\<lambda>n. \<P>(\<omega> in M. \<epsilon> \<le> dist (f' n \<omega>) (f \<omega>))) \<longlongrightarrow> 0) F"
      using 2 by blast
    then have "((\<lambda>n. \<P>(\<omega> in M. \<epsilon> < dist (f' n \<omega>) (f \<omega>))) \<longlongrightarrow> 0) F"
      apply (rule metric_tendsto_imp_tendsto)
      using \<open>\<epsilon> > 0\<close> by (auto intro!: eventuallyI finite_measure_mono)
  }
  then show ?case
    by (simp add: finite_tendsto_measureI[OF assms])
qed

abbreviation "LIMSEQ_measure M f l \<equiv> tendsto_measure M f l sequentially"

lemma LIMSEQ_measure_def: "LIMSEQ_measure M f l \<longleftrightarrow>
  (\<forall>n. f n \<in> borel_measurable M) \<and> (l \<in> borel_measurable M) \<and>
   (\<forall>\<epsilon> > 0. \<forall>A \<in> fmeasurable M.
   (\<lambda>n. measure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0)"
  unfolding tendsto_measure_def ..

lemma LIMSEQ_measureD:
  assumes "LIMSEQ_measure M f l" "\<epsilon> > 0" "A \<in> fmeasurable M"
  shows "(\<lambda>n. measure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0"
  using assms LIMSEQ_measure_def by blast

lemma fmeasurable_inter: "\<lbrakk>A \<in> sets M; B \<in> fmeasurable M\<rbrakk> \<Longrightarrow> A \<inter> B \<in> fmeasurable M"
proof (intro fmeasurableI, goal_cases measurable finite)
  case measurable
  then show ?case by simp
next
  case finite
  then have "emeasure M (A \<inter> B) \<le> emeasure M B"
    by (simp add: emeasure_mono)
  also have "emeasure M B < \<infinity>"
    using finite(2)[THEN fmeasurableD2] by (simp add: top.not_eq_extremum)
  finally show ?case .
qed

lemma LIMSEQ_measure_emeasure:
  assumes "LIMSEQ_measure M f l" "\<epsilon> > 0" "A \<in> fmeasurable M"
    and [measurable]: "\<And>i. f i \<in> borel_measurable M" "l \<in> borel_measurable M" 
  shows "(\<lambda>n. emeasure M ({\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A)) \<longlonglongrightarrow> 0"
proof -
  have fmeasurable: "{\<omega> \<in> space M. dist (f n \<omega>) (l \<omega>) > \<epsilon>} \<inter> A \<in> fmeasurable M" for n
    by (rule fmeasurable_inter; simp add: assms(3))
  then show ?thesis
    apply (simp add: emeasure_eq_measure2 ennreal_tendsto_0_iff)
    using LIMSEQ_measure_def assms by blast
qed

lemma measure_Lim_within_LIMSEQ:
  fixes a :: "'a :: first_countable_topology"
  assumes "\<And>t. X t \<in> borel_measurable M" "L \<in> borel_measurable M"
  assumes "\<And>S. \<lbrakk>(\<forall>n. S n \<noteq> a \<and> S n \<in> T); S \<longlonglongrightarrow> a\<rbrakk> \<Longrightarrow> LIMSEQ_measure M (\<lambda>n. X (S n)) L"
  shows "tendsto_measure M X L (at a within T)"
  apply (intro tendsto_measureI[OF assms(1,2)])
  unfolding tendsto_measure_def[where l=L] tendsto_def apply safe
  apply (rule sequentially_imp_eventually_within)
  using assms unfolding LIMSEQ_measure_def tendsto_def by presburger

definition tendsto_AE :: "'b measure \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c :: topological_space) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "tendsto_AE M f' l F \<longleftrightarrow> (AE \<omega> in M. ((\<lambda>n. f' n \<omega>) \<longlongrightarrow> l \<omega>) F)"

lemma LIMSEQ_ae_pointwise: "(\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x) \<Longrightarrow> tendsto_AE M f l sequentially"
  unfolding tendsto_AE_def by simp

lemma tendsto_AE_within_LIMSEQ:
  fixes a :: "'a :: first_countable_topology"
  assumes "\<And>S. \<lbrakk>(\<forall>n. S n \<noteq> a \<and> S n \<in> T); S \<longlonglongrightarrow> a\<rbrakk> \<Longrightarrow> tendsto_AE M (\<lambda>n. X (S n)) L sequentially"
  shows "tendsto_AE M X L (at a within T)"
  oops

lemma LIMSEQ_dominated_convergence:
  fixes X :: "nat \<Rightarrow> real"
  assumes "X \<longlonglongrightarrow> L" "(\<And>n. Y n \<le> X n)" "(\<And>n. Y n \<ge> L)"
  shows "Y \<longlonglongrightarrow> L"
proof (rule metric_LIMSEQ_I)
  have "X n \<ge> L" for n
    using assms(2,3)[of n] by linarith
  fix r :: real assume "0 < r"
  then obtain N where "\<forall>n\<ge>N. dist (X n) L < r"
    using metric_LIMSEQ_D[OF assms(1) \<open>0 < r\<close>]  by blast
  then have N: "\<forall>n\<ge>N. X n - L < r"
    using \<open>\<And>n. L \<le> X n\<close> by (auto simp: dist_real_def)
  have "\<forall>n\<ge>N. Y n - L < r"
  proof clarify
    fix n assume \<open>n \<ge> N\<close>
    then have "X n - L < r"
      using N by blast
    then show "Y n - L < r"
      using assms(2)[of n] by auto
  qed
  then show "\<exists>no. \<forall>n\<ge>no. dist (Y n) L < r"
    apply (intro exI[where x=N])
    using assms(3) dist_real_def by auto
qed

text \<open> Klenke remark 6.4 \<close>
lemma measure_conv_imp_AE_sequentially: 
  assumes [measurable]: "\<And>n. f' n \<in> borel_measurable M" "f \<in> borel_measurable M"
    and "tendsto_AE M f' f sequentially"
  shows "LIMSEQ_measure M f' f"
proof (unfold tendsto_measure_def, safe)
  fix \<epsilon> :: real assume "0 < \<epsilon>"
  fix A assume A[measurable]: "A \<in> fmeasurable M"
  text \<open> From AE convergence we know there's a null set where f' doesn't converge \<close>
  obtain N where N: "N \<in> null_sets M" "{\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>} \<subseteq> N"
    using assms unfolding tendsto_AE_def by (simp add: eventually_ae_filter, blast)
  then have measure_0: "measure M {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>} = 0"
    by (meson measure_eq_0_null_sets measure_notin_sets null_sets_subset)
  text \<open> D is a sequence of sets that converges to N \<close>
  define D where "D \<equiv> \<lambda>n. {\<omega> \<in> space M. \<exists>m \<ge> n. dist (f' m \<omega>) (f \<omega>) > \<epsilon>}"
  have "\<And>n. D n \<in> sets M"
    unfolding D_def by measurable
  then have [measurable]: "\<And>n. D n \<inter> A \<in> sets M"
    by simp
  have "(\<Inter>n. D n) \<in> sets M"
    unfolding D_def by measurable
  then have measurable_D_A: "(\<Inter>n. D n \<inter> A) \<in> sets M"
    by simp
  have "(\<Inter>n. D n) \<subseteq> {\<omega> \<in> space M. \<not> (\<lambda>n. (f' n \<omega>)) \<longlonglongrightarrow> f \<omega>}"
  proof (intro subsetI)
    fix x assume "x \<in> (\<Inter>n. D n)"
    then have "x \<in> space M" "\<And>n. \<exists>m \<ge> n. \<epsilon> < dist (f' m x) (f x)"
      unfolding D_def by simp_all
    then have "\<not> (\<lambda>n. f' n x) \<longlonglongrightarrow> f x"
      by (simp add: LIMSEQ_def) (meson \<open>0 < \<epsilon>\<close> not_less_iff_gr_or_eq order_less_le)
    then show "x \<in> {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>}"
      using \<open>x \<in> space M\<close> by blast
  qed
  then have "measure M (\<Inter>n. D n) = 0"
    by (metis (no_types, lifting) N \<open>\<Inter> (range D) \<in> sets M\<close> measure_eq_0_null_sets null_sets_subset subset_trans)
  then have "measure M (\<Inter>n. D n \<inter> A) = 0"
  proof -
    have "emeasure M (\<Inter>n. D n \<inter> A) \<le> emeasure M (\<Inter>n. D n)"
      apply (rule emeasure_mono)
       apply blast
      unfolding D_def apply measurable
      done
    then show ?thesis
      by (smt (verit, del_insts) N Sigma_Algebra.measure_def \<open>measure M (\<Inter> (range D)) = 0\<close>
          \<open>\<Inter> (range D) \<in> sets M\<close> \<open>\<Inter> (range D) \<subseteq> {\<omega> \<in> space M. \<not> (\<lambda>n. f' n \<omega>) \<longlonglongrightarrow> f \<omega>}\<close> 
          dual_order.trans enn2real_mono ennreal_zero_less_top measure_nonneg null_setsD1 null_sets_subset)
  qed
  moreover have "(\<lambda>n. measure M (D n \<inter> A)) \<longlonglongrightarrow> measure M (\<Inter>n. D n \<inter> A)"
    apply (rule Lim_measure_decseq)
    using A(1) \<open>\<And>n. D n \<in> sets M\<close> apply blast
    subgoal 
      apply (intro monotoneI) 
      apply clarsimp
      apply (simp add: D_def) 
      by (meson order_trans)
    apply (simp add: A \<open>\<And>n. D n \<in> sets M\<close> fmeasurableD2 fmeasurable_inter)
    done
  ultimately have measure_D_0: "(\<lambda>n. measure M (D n \<inter> A)) \<longlonglongrightarrow> 0"
    by presburger
  have "\<And>n. {\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A \<subseteq> (D n \<inter> A)"
    unfolding D_def by blast
  then have "\<And>n. emeasure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A) \<le> emeasure M (D n \<inter> A)"
    by (rule emeasure_mono) measurable
  then have "\<And>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A) \<le> measure M (D n \<inter> A)"
    unfolding measure_def apply (rule enn2real_mono)
    by (meson A \<open>\<And>n. D n \<in> sets M\<close> fmeasurableD2 fmeasurable_inter top.not_eq_extremum)
  then show "(\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f' n \<omega>) (f \<omega>)} \<inter> A)) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_dominated_convergence[OF measure_D_0])
qed simp_all

corollary LIMSEQ_measure_pointwise:
  assumes "\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> f' x" "\<And>n. f n \<in> borel_measurable M" "f' \<in> borel_measurable M"
  shows "LIMSEQ_measure M f f'"
  by (simp add: LIMSEQ_ae_pointwise measure_conv_imp_AE_sequentially assms)

lemma Lim_measure_pointwise:
  fixes a :: "'a :: first_countable_topology"
  assumes "\<And>x. ((\<lambda>n. f n x) \<longlongrightarrow> f' x)(at a within T)" "\<And>n. f n \<in> borel_measurable M" "f' \<in> borel_measurable M"
  shows "tendsto_measure M f f' (at a within T)"
proof (intro measure_Lim_within_LIMSEQ)
  fix S assume "\<forall>n. S n \<noteq> a \<and> S n \<in> T" "S \<longlonglongrightarrow> a"
  then have "(\<lambda>n. f (S n) x) \<longlonglongrightarrow> f' x" for x
    using assms(1) by (simp add: tendsto_at_iff_sequentially o_def)
  then show "LIMSEQ_measure M (\<lambda>n. f (S n)) f'"
    by (simp add: LIMSEQ_measure_pointwise assms(2,3))
qed (simp_all add: assms)

corollary measure_conv_imp_AE_at_within:
  fixes x :: "'a :: first_countable_topology"
  assumes [measurable]: "\<And>n. f' n \<in> borel_measurable M" "f \<in> borel_measurable M"
    and "tendsto_AE M f' f (at x within S)"
  shows "tendsto_measure M f' f (at x within S)"
proof (rule measure_Lim_within_LIMSEQ[OF assms(1,2)])
  fix s assume *: "\<forall>n. s n \<noteq> x \<and> s n \<in> S" "s \<longlonglongrightarrow> x"
  have AE_seq: "AE \<omega> in M. \<forall>X. (\<forall>i. X i \<in> S - {x}) \<longrightarrow> X \<longlonglongrightarrow> x \<longrightarrow> ((\<lambda>n. f' n \<omega>) \<circ> X) \<longlonglongrightarrow> f \<omega>"
    using assms(3) by (simp add: tendsto_AE_def tendsto_at_iff_sequentially)
  then have "AE \<omega> in M. (\<forall>i. s i \<in> S - {x}) \<longrightarrow> s \<longlonglongrightarrow> x \<longrightarrow> ((\<lambda>n. f' n \<omega>) \<circ> s) \<longlonglongrightarrow> f \<omega>"
    by force
  then have "AE \<omega> in M. ((\<lambda>n. f' n \<omega>) \<circ> s) \<longlonglongrightarrow> f \<omega>"
    using * by force
  then have "tendsto_AE M (\<lambda>n. f' (s n)) f sequentially"
    unfolding tendsto_AE_def comp_def by blast
  then show "LIMSEQ_measure M (\<lambda>n. f' (s n)) f"
    by (rule measure_conv_imp_AE_sequentially[OF assms(1,2)])
qed

text \<open> Klenke remark 6.5 \<close>
lemma (in sigma_finite_measure) LIMSEQ_measure_unique_AE:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,metric_space}"
  assumes [measurable]: "\<And>n. f n \<in> borel_measurable M" "l \<in> borel_measurable M" "l' \<in> borel_measurable M"
    and "LIMSEQ_measure M f l" "LIMSEQ_measure M f l'"
  shows "AE x in M. l x = l' x"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where A: "\<And>i. A i \<in> fmeasurable M" "(\<Union>i. A i) = space M"
    by (metis fmeasurableI infinity_ennreal_def rangeI sigma_finite subset_eq top.not_eq_extremum)
  have "\<And>m \<epsilon>. {x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m \<in> fmeasurable M"
    by (intro fmeasurable_inter; simp add: A)
  then have emeasure_leq: "emeasure M ({x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m) \<le>
     emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) +
     emeasure M ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)" if "\<epsilon> > 0" for n m \<epsilon>
  proof -
    have [measurable]:
      "{x \<in> space M. \<epsilon> / 2 < dist (l x) (f n x)} \<inter> A m \<in> sets M"
      "{x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m \<in> sets M"
      using A by (measurable; auto)+
    have "dist (l x) (l' x) \<le> dist (l x) (f n x) + dist (f n x) (l' x)" for x
      by (simp add: dist_triangle)
    then have "{x. dist (l x) (l' x) > \<epsilon>} \<subseteq> {x. dist (l x) (f n x) > \<epsilon>/2} \<union> {x. dist (f n x) (l' x) > \<epsilon>/2}"
      by (safe, smt (verit, best) field_sum_of_halves)
    then have "{x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m \<subseteq> 
    ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) \<union> ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)"
      by blast
    then have "emeasure M ({x \<in> space M. dist (l x) (l' x) > \<epsilon>} \<inter> A m) \<le>
     emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m \<union> {x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)"
      apply (rule emeasure_mono)
      using A by measurable
    also have "... \<le> emeasure M ({x \<in> space M. dist (l x) (f n x) > \<epsilon>/2} \<inter> A m) +
     emeasure M ({x \<in> space M. dist (f n x) (l' x) > \<epsilon>/2} \<inter> A m)"
      apply (rule emeasure_subadditive)
      using A by measurable
    finally show ?thesis .
  qed

  moreover have tendsto_zero: "(\<lambda>n. emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) \<longlonglongrightarrow> 0"
    if \<open>\<epsilon> > 0\<close> for \<epsilon> m
    apply (rule tendsto_add_zero)
     apply (rule LIMSEQ_measure_emeasure[OF assms(4)])
        prefer 5 apply (rule LIMSEQ_measure_emeasure[OF assms(5)])
    using that A apply simp_all
    done
  have dist_\<epsilon>_emeasure: "emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) = 0" 
    if \<open>\<epsilon> > 0\<close> for \<epsilon> m
  proof (rule ccontr)
    assume "emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) \<noteq> 0"
    then obtain e where e: "e > 0" "emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) \<ge> e"
      using not_gr_zero by blast
    have "\<exists>no. \<forall>n\<ge>no. (emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) < e"
    proof -
      have measure_tendsto_0: "(\<lambda>n. measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) \<longlonglongrightarrow> 0"
        apply (rule tendsto_add_zero)
        using A(1) LIMSEQ_measure_def assms(4,5) half_gt_zero that by blast+
      have "enn2real e > 0"
        by (metis (no_types, lifting) A(1) e(1) e(2) emeasure_neq_0_sets enn2real_eq_0_iff 
            enn2real_nonneg fmeasurableD2 fmeasurable_inter inf_right_idem linorder_not_less nless_le top.not_eq_extremum)
      then obtain no where "\<forall>n\<ge>no. (measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l x)} \<inter> A m)
       + measure M ({x \<in> space M. \<epsilon> / 2 < dist (f n x) (l' x)} \<inter> A m)) < enn2real e"
        using LIMSEQ_D[OF measure_tendsto_0 \<open>enn2real e > 0\<close>] by (simp) blast
      then show ?thesis
        apply (safe intro!: exI[where x=no])
        by (smt (verit, del_insts) A(1) Sigma_Algebra.measure_def add_eq_0_iff_both_eq_0 
            emeasure_eq_measure2 emeasure_neq_0_sets enn2real_mono enn2real_plus enn2real_top 
            ennreal_0 ennreal_zero_less_top fmeasurable_inter inf_sup_ord(2) le_iff_inf
            linorder_not_less top.not_eq_extremum zero_less_measure_iff)
    qed
    then obtain N where N: "emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f N x) (l x)} \<inter> A m)
       + emeasure M ({x \<in> space M. \<epsilon> / 2 < dist (f N x) (l' x)} \<inter> A m) < e"
      by auto
    then have "emeasure M ({x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m) < e"
      by (smt (verit, del_insts) emeasure_leq[OF that] Collect_cong dist_commute e(2) leD order_less_le_trans)
    then show False
      using e(2) by auto
  qed
  have "emeasure M ({x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m) = 0" for m
  proof -
    have sets: "range (\<lambda>n. {x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m) \<subseteq> sets M"
      using A by force
    have "(\<Union>n. {x \<in> space M. 1/2^n < dist (l x) (l' x)}) = {x \<in> space M. 0 < dist (l x) (l' x)}"
      apply (intro subset_antisym subsetI)
       apply force
      apply simp
      by (metis one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76) zero_less_dist_iff)
    moreover have "emeasure M ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m) = 0" for n
      using dist_\<epsilon>_emeasure by simp
    then have suminf_zero: "(\<Sum>n. emeasure M ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m)) = 0"
      by auto
    then have "emeasure M (\<Union>n. ({x \<in> space M. 1/2^n < dist (l x) (l' x)} \<inter> A m)) \<le> 0"
      apply (subst suminf_zero[symmetric])
      apply (rule emeasure_subadditive_countably)
      by (simp add: emeasure_subadditive_countably sets)
    ultimately show ?thesis
      by simp
  qed
  then have "(\<Sum>m. emeasure M ({x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m)) = 0"
    by simp
  then have "emeasure M (\<Union>m. {x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m) = 0"
  proof -
    let ?S = "\<lambda>m. {x \<in> space M. 0 < dist (l x) (l' x)} \<inter> A m"
    have "emeasure M (\<Union>m. ?S m) \<le> (\<Sum>m. emeasure M (?S m))"
      apply (rule emeasure_subadditive_countably)
      using \<open>\<And>m \<epsilon>. {x \<in> space M. \<epsilon> < dist (l x) (l' x)} \<inter> A m \<in> fmeasurable M\<close> by blast
    then show ?thesis
      using \<open>(\<Sum>m. emeasure M (?S m)) = 0\<close> by force
  qed
  then have "emeasure M {x \<in> space M. 0 < dist (l x) (l' x)} = 0"
    using A by simp
  then show ?thesis
    by (auto simp add: AE_iff_null)
qed

corollary (in sigma_finite_measure) LIMSEQ_ae_unique_AE:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,metric_space}"
  assumes "\<And>n. f n \<in> borel_measurable M" "l \<in> borel_measurable M" "l' \<in> borel_measurable M"
    and "tendsto_AE M f l sequentially" "tendsto_AE M f l' sequentially"
  shows "AE x in M. l x = l' x"
proof -
  have "LIMSEQ_measure M f l" "LIMSEQ_measure M f l'"
    using assms measure_conv_imp_AE_sequentially by blast+
  then show ?thesis
    using assms(1-3) LIMSEQ_measure_unique_AE by blast
qed

lemma (in sigma_finite_measure) tendsto_measure_at_within_eq_AE:
  fixes f :: "'b :: first_countable_topology \<Rightarrow> 'a \<Rightarrow> 'c :: {second_countable_topology,metric_space}"
  assumes f_measurable: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> borel_measurable M"
    and l_measurable: "l \<in> borel_measurable M" "l' \<in> borel_measurable M"
    and tendsto: "tendsto_measure M f l (at t within S)" "tendsto_measure M f l' (at t within S)"
    and not_bot: "(at t within S) \<noteq> \<bottom>"
  shows "AE x in M. l x = l' x"
proof -
  from not_bot have "t islimpt S"
    using trivial_limit_within by blast
  then obtain s :: "nat \<Rightarrow> 'b" where s: "\<And>i. s i \<in> S - {t}" "s \<longlonglongrightarrow> t"
    using islimpt_sequential by meson
  then have fs_measurable: "\<And>n. f (s n) \<in> borel_measurable M"
    using f_measurable by blast
  have *: "LIMSEQ_measure M (\<lambda>n. f (s n)) l"
    if "l \<in> borel_measurable M" "tendsto_measure M f l (at t within S)" for l
  proof (intro tendsto_measureI[OF fs_measurable that(1)], goal_cases)
    case (1 \<epsilon> A)
    then have "((\<lambda>n. measure M ({\<omega> \<in> space M. \<epsilon> < dist (f n \<omega>) (l \<omega>)} \<inter> A)) \<longlongrightarrow> 0)(at t within S)"
      using that(2) 1 tendsto_measure_def by blast
    then show ?case
      apply (rule filterlim_compose[where f=s])
      by (smt (verit, del_insts) DiffD1 DiffD2 eventuallyI filterlim_at insertI1 s)
  qed
  show ?thesis
    apply (rule LIMSEQ_measure_unique_AE[OF fs_measurable l_measurable])
    using * tendsto l_measurable by simp_all
qed
end
