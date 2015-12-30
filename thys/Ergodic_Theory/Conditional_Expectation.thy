(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Conditional_Expectation
imports Complex_Main  "~~/src/HOL/Probability/Radon_Nikodym" "~~/src/HOL/Probability/Probability_Measure"
        SG_Library_Complement
begin

section {*Conditional expectation*}

subsection {*Restricting a measure to a sub-sigma-algebra*}

definition subalgebra::"'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "subalgebra M F = ((space F = space M) \<and> (sets F \<subseteq> sets M))"

lemma sub_measure_space:
 assumes i: "subalgebra M F"
  shows "measure_space (space M) (sets F) (emeasure M)"
proof -
  have "sigma_algebra (space M) (sets F)"
    by (metis i measure_space measure_space_def subalgebra_def)
  moreover have "positive (sets F) (emeasure M)"
    using Sigma_Algebra.positive_def by auto
  moreover have "countably_additive (sets F) (emeasure M)"
    by (meson countably_additive_def emeasure_countably_additive i order_trans subalgebra_def subsetCE)
  ultimately show ?thesis unfolding measure_space_def by simp
qed

definition restr_to_subalg::"'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
  "restr_to_subalg M F = measure_of (space M) (sets F) (emeasure M)"

lemma space_restr_to_subalg:
  "space (restr_to_subalg M F) = space M"
 unfolding restr_to_subalg_def by (simp add: space_measure_of_conv)

lemma sets_restr_to_subalg [measurable_cong]:
  assumes "subalgebra M F"
  shows "sets (restr_to_subalg M F) = sets F"
unfolding restr_to_subalg_def by (metis sets.sets_measure_of_eq assms subalgebra_def)

lemma emeasure_restr_to_subalg:
  assumes "subalgebra M F"
          "A \<in> sets F"
  shows "emeasure (restr_to_subalg M F) A = emeasure M A"
unfolding restr_to_subalg_def
by (metis assms subalgebra_def emeasure_measure_of_conv sub_measure_space sets.sigma_sets_eq)

lemma null_sets_restr_to_subalg:
  assumes "subalgebra M F"
  shows "null_sets (restr_to_subalg M F) = null_sets M \<inter> sets F"
proof
  {
    fix x assume *: "x \<in> null_sets (restr_to_subalg M F)"
    then have "x \<in> null_sets M \<inter> sets F"
      by (metis Int_iff assms emeasure_restr_to_subalg null_setsD1 null_setsD2 null_setsI sets_restr_to_subalg subalgebra_def subsetD)
  }
  then show "null_sets (restr_to_subalg M F) \<subseteq> null_sets M \<inter> sets F" by auto
next
  {
    fix x assume *: "x \<in> null_sets M \<inter> sets F"
    then have "x \<in> null_sets (restr_to_subalg M F)"
       by (metis Int_iff assms null_setsD1 null_setsI sets_restr_to_subalg emeasure_restr_to_subalg[OF assms])
  }
  then show "null_sets M \<inter> sets F \<subseteq> null_sets (restr_to_subalg M F)" by auto
qed

lemma AE_restr_to_subalg:
  assumes "subalgebra M F"
          "AE x in (restr_to_subalg M F). P x"
  shows "AE x in M. P x"
proof -
  obtain A where A: "\<And>x. x \<in> space (restr_to_subalg M F) - A \<Longrightarrow> P x" "A \<in> null_sets (restr_to_subalg M F)"
    using AE_E3[OF assms(2)] by auto
  then have "A \<in> null_sets M" using null_sets_restr_to_subalg[OF assms(1)] by auto
  moreover have "\<And>x. x \<in> space M - A \<Longrightarrow> P x"
    using space_restr_to_subalg A(1) by fastforce
  ultimately show ?thesis
    unfolding eventually_ae_filter by auto
qed

lemma AE_restr_to_subalg2:
  assumes "subalgebra M F"
          "AE x in M. P x" and [measurable]: "P \<in> measurable F (count_space UNIV)"
 shows "AE x in (restr_to_subalg M F). P x"
proof -
  def U \<equiv> "{x \<in> space M. \<not>(P x)}"
  then have *: "U = {x \<in> space F. \<not>(P x)}" using assms(1) by (simp add: subalgebra_def)
  then have "U \<in> sets F" by simp
  then have "U \<in> sets M" using assms(1) by (meson subalgebra_def subsetD)
  then have "U \<in> null_sets M" unfolding U_def using assms(2) using AE_iff_measurable by blast
  then have "U \<in> null_sets (restr_to_subalg M F)" using null_sets_restr_to_subalg[OF assms(1)] `U \<in> sets F` by auto
  then show ?thesis using * by (metis (no_types, lifting) Collect_mono U_def eventually_ae_filter space_restr_to_subalg)
qed

lemma prob_space_restr_to_subalg:
  assumes "subalgebra M F"
          "prob_space M"
   shows "prob_space (restr_to_subalg M F)"
by (metis (no_types, lifting) assms(1) assms(2) emeasure_restr_to_subalg prob_space.emeasure_space_1 prob_spaceI
    sets.top space_restr_to_subalg subalgebra_def)

lemma finite_measure_restr_to_subalg:
  assumes "subalgebra M F"
          "finite_measure M"
   shows "finite_measure (restr_to_subalg M F)"
by (metis (no_types, lifting) assms emeasure_restr_to_subalg finite_measure.finite_emeasure_space
    finite_measureI sets.top space_restr_to_subalg subalgebra_def)

lemma measurable_in_subalg:
  assumes "subalgebra M F"
          "f \<in> measurable F N"
  shows "f \<in> measurable (restr_to_subalg M F) N"
by (metis measurable_cong_sets assms(2) sets_restr_to_subalg[OF assms(1)])

lemma measurable_from_subalg:
  assumes "subalgebra M F"
          "f \<in> measurable F N"
  shows "f \<in> measurable M N"
using assms unfolding measurable_def subalgebra_def by auto

text{*The following is the direct transposition of \verb+nn_integral_subalgebra+
(from \verb+Nonnegative_Lebesgue_Integration+) in the
current notations, with the removal of the useless assumption $f \geq 0$.*}

lemma nn_integral_subalgebra2:
  assumes "subalgebra M F" and
          [measurable]: "f \<in> borel_measurable F"
  shows "(\<integral>\<^sup>+ x. f x \<partial>(restr_to_subalg M F)) = (\<integral>\<^sup>+ x. f x \<partial>M)"
proof -
  def g \<equiv> "\<lambda>x. max (f x) 0"
  have "(\<integral>\<^sup>+ x. f x \<partial>(restr_to_subalg M F)) = (\<integral>\<^sup>+ x. g x \<partial>(restr_to_subalg M F))"
    using g_def by (simp add: g_def max_def_raw nn_integral_cong_pos)
  also have "... = (\<integral>\<^sup>+ x. g x \<partial>M)"
  proof (rule nn_integral_subalgebra)
    have "g \<in> borel_measurable F" using g_def by simp
    then show "g \<in> borel_measurable (restr_to_subalg M F)" using measurable_in_subalg[OF assms(1)] by auto
    show "sets (restr_to_subalg M F) \<subseteq> sets M"  by (metis sets_restr_to_subalg[OF assms(1)] assms(1) subalgebra_def)
    fix A assume "A \<in> sets (restr_to_subalg M F)"
    then show "emeasure (restr_to_subalg M F) A = emeasure M A" by (metis sets_restr_to_subalg[OF assms(1)] emeasure_restr_to_subalg[OF assms(1)])
  qed (auto simp add: g_def assms space_restr_to_subalg sets_restr_to_subalg[OF assms(1)])
  also have "... =  (\<integral>\<^sup>+ x. f x \<partial>M)" using g_def by (simp add: g_def max_def_raw nn_integral_cong_pos)
  finally show ?thesis by simp
qed

text{*The following is the direct transposition of \verb+integral_subalgebra+
(from \verb+Bochner_Integration+) in the current notations.*}

lemma integral_subalgebra2:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "subalgebra M F" and
    [measurable]: "f \<in> borel_measurable F"
  shows "(\<integral>x. f x \<partial>(restr_to_subalg M F)) = (\<integral>x. f x \<partial>M)"
by (rule integral_subalgebra,
    metis measurable_in_subalg[OF assms(1)] assms(2),
    auto simp add: assms space_restr_to_subalg sets_restr_to_subalg  emeasure_restr_to_subalg,
    meson assms(1) subalgebra_def subset_eq)

lemma integrable_from_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "subalgebra M F"
          "integrable (restr_to_subalg M F) f"
  shows "integrable M f"
proof (rule integrableI_bounded)
  have [measurable]: "f \<in> borel_measurable F" using assms by auto
  then show "f \<in> borel_measurable M" using assms(1) measurable_from_subalg by blast

  have "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) = (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>(restr_to_subalg M F))"
    by (rule nn_integral_subalgebra2[symmetric], auto simp add: assms)
  also have "... < \<infinity>" using  integrable_iff_bounded assms by auto
  finally show "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M) < \<infinity>" by simp
qed

lemma integrable_in_subalg:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "subalgebra M F"
          "f \<in> borel_measurable F"
          "integrable M f"
  shows "integrable (restr_to_subalg M F) f"
proof (rule integrableI_bounded)
  show "f \<in> borel_measurable (restr_to_subalg M F)" using assms(2) assms(1) by auto
  have "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>(restr_to_subalg M F)) = (\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>M)"
    by (rule nn_integral_subalgebra2, auto simp add: assms)
  also have "... < \<infinity>" using  integrable_iff_bounded assms by auto
  finally show "(\<integral>\<^sup>+ x. ereal (norm (f x)) \<partial>(restr_to_subalg M F)) < \<infinity>" by simp
qed

subsection {*Nonnegative conditional expectation*}

text {* The conditional expectation of a function $f$, on a measure space $M$, with respect to a
sub sigma algebra $F$, should be a function $g$ which is $F$-measurable whose integral on any
$F$-set coincides with the integral of $f$.
Such a function is uniquely defined almost everywhere.
The most direct construction is to use the measure $f dM$, restrict it to the sigma-algebra $F$,
and apply the Radon-Nikodym theorem to write it as $g dM_{|F}$ for some $F$-measurable function $g$.
Another classical construction for $L^2$ functions is done by orthogonal projection on $F$-measurable
functions, and then extending by density to $L^1$. The Radon-Nikodym point of view avoids the $L^2$
machinery, and works for all positive functions.

In this paragraph, we develop the definition and basic properties for nonnegative functions,
as the basics of the general case. As in the definition of integrals, the nonnegative case is done
with ereal-valued functions, without any integrability assumption.
*}

definition nn_cond_exp :: "'a measure => 'a measure => ('a => ereal) \<Rightarrow> ('a \<Rightarrow> ereal)" where
  "nn_cond_exp M F f =
    (if f \<in> borel_measurable M \<and> (AE x in M. 0 \<le> f x) \<and> subalgebra M F
       then RN_deriv (restr_to_subalg M F) (restr_to_subalg (density M f) F)
       else (\<lambda>_. 0))"

lemma
  shows borel_measurable_nn_cond_exp [measurable]:  "nn_cond_exp M F f \<in> borel_measurable F"
  and   borel_measurable_nn_cond_exp2 [measurable]: "nn_cond_exp M F f \<in> borel_measurable M"
  and nn_cond_exp_nonneg: "\<And>x. nn_cond_exp M F f x \<ge> 0"
by (simp_all add: nn_cond_exp_def RN_deriv_nonneg)
  (metis borel_measurable_RN_deriv borel_measurable_subalgebra sets_restr_to_subalg space_restr_to_subalg subalgebra_def)

text {* The good setting for conditional expectations is the situation where the subalgebra $F$
gives rise to a sigma-finite measure space. To see what goes wrong if it is not sigma-finite,
think of $\mathbb{R}$ with the trivial sigma-algebra $\{\emptyset, \mathbb{R}\}$. In this case,
conditional expectations have to be constant functions, so they have integral $0$ or $\infty$.
This means that a positive integrable function can have no meaningful conditional expectation.*}

locale sigma_finite_subalgebra =
  fixes M F::"'a measure"
  assumes subalg: "subalgebra M F"
      and sigm_fin_subalg: "sigma_finite_measure (restr_to_subalg M F)"

sublocale sigma_finite_subalgebra \<subseteq> sigma_finite_measure
proof
  obtain A where Ap: "countable A \<and> A \<subseteq> sets (restr_to_subalg M F)  \<and> \<Union>A = space (restr_to_subalg M F) \<and> (\<forall>a\<in>A. emeasure (restr_to_subalg M F) a \<noteq> \<infinity>)"
    using sigma_finite_measure.sigma_finite_countable[OF sigm_fin_subalg] by auto
  have "A \<subseteq> sets F"  using Ap sets_restr_to_subalg[OF subalg] by fastforce
  then have "A \<subseteq> sets M" using subalg subalgebra_def by fastforce
  moreover have "\<Union>A = space M" using Ap space_restr_to_subalg by simp
  moreover have "\<forall>a\<in>A. emeasure M a \<noteq> \<infinity>" by (metis subsetD emeasure_restr_to_subalg[OF subalg] `A \<subseteq> sets F` Ap)
  ultimately show "\<exists>A. countable A \<and> A \<subseteq> sets M \<and> \<Union>A = space M \<and> (\<forall>a\<in>A. emeasure M a \<noteq> \<infinity>)" using Ap by auto
qed

text {* Conditional expectations are very often used in probability spaces. This is a special case
of the previous one, as we prove now. *}

locale finite_measure_subalgebra = finite_measure +
  fixes F::"'a measure"
  assumes subalg: "subalgebra M F"

lemma finite_measure_subalgebra_is_sigma_finite:
  assumes "finite_measure_subalgebra M F"
  shows "sigma_finite_subalgebra M F"
proof -
  interpret finite_measure_subalgebra M F using assms by simp
  have "finite_measure (restr_to_subalg M F)"
    using finite_measure_restr_to_subalg subalg finite_emeasure_space finite_measureI by blast
  then have "sigma_finite_measure (restr_to_subalg M F)"
    unfolding finite_measure_def by simp
  then show "sigma_finite_subalgebra M F" unfolding sigma_finite_subalgebra_def using subalg by simp
qed

sublocale finite_measure_subalgebra \<subseteq> sigma_finite_subalgebra
proof -
  have "finite_measure (restr_to_subalg M F)"
    using finite_measure_restr_to_subalg subalg finite_emeasure_space finite_measureI by blast
  then have "sigma_finite_measure (restr_to_subalg M F)"
    unfolding finite_measure_def by simp
  then show "sigma_finite_subalgebra M F" unfolding sigma_finite_subalgebra_def using subalg by simp
qed

context sigma_finite_subalgebra
begin

text{* The next lemma is arguably the most fundamental property of conditional expectation:
when computing an expectation against an $F$-measurable function, it is equivalent to work
with a function or with its $F$-conditional expectation.

This property (even for bounded test functions) characterizes conditional expectations, as the second lemma below shows.
From this point on, we will only work with it, and forget completely about
the definition using Radon-Nikodym derivatives.
*}

lemma nn_cond_exp_intg:
  assumes "AE x in M. g x \<ge> 0" and
          [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. f x * nn_cond_exp M F g x \<partial>M) = (\<integral>\<^sup>+ x. f x * g x \<partial>M)"
proof -
  have [measurable]: "f \<in> borel_measurable M"
    by (meson assms subalg borel_measurable_subalgebra subalgebra_def)
  have ac: "absolutely_continuous (restr_to_subalg M F) (restr_to_subalg (density M g) F)"
    unfolding absolutely_continuous_def
  proof -
    have "null_sets (restr_to_subalg M F) = null_sets M \<inter> sets F" by (rule null_sets_restr_to_subalg[OF subalg])
    moreover have "null_sets M \<subseteq> null_sets (density M g)" using absolutely_continuousI_density absolutely_continuous_def assms(3) by blast
    ultimately have "null_sets (restr_to_subalg M F) \<subseteq> null_sets (density M g) \<inter> sets F" by auto
    moreover have "null_sets (density M g) \<inter> sets F = null_sets (restr_to_subalg (density M g) F)"
     by (rule null_sets_restr_to_subalg[symmetric]) (metis subalg sets_density space_density subalgebra_def)
    ultimately show "null_sets (restr_to_subalg M F) \<subseteq> null_sets (restr_to_subalg (density M g) F)" by auto
  qed

  have "(\<integral>\<^sup>+ x. f x * nn_cond_exp M F g x \<partial>M) = (\<integral>\<^sup>+ x. f x * nn_cond_exp M F g x \<partial>(restr_to_subalg M F))"
    by (rule nn_integral_subalgebra2[symmetric]) (simp_all add: assms subalg nn_cond_exp_nonneg)
  also have "... = (\<integral>\<^sup>+ x. f x * RN_deriv (restr_to_subalg M F) (restr_to_subalg (density M g) F) x \<partial>(restr_to_subalg M F))"
    unfolding nn_cond_exp_def using assms subalg by simp
  also have "... = (\<integral>\<^sup>+ x. RN_deriv (restr_to_subalg M F) (restr_to_subalg (density M g) F) x * f x \<partial>(restr_to_subalg M F))"
    by (simp add: mult.commute)
  also have "... = (\<integral>\<^sup>+ x. f x \<partial>(restr_to_subalg (density M g) F))"
  proof (rule sigma_finite_measure.RN_deriv_nn_integral[symmetric])
    show "sets (restr_to_subalg (density M g) F) = sets (restr_to_subalg M F)"
      by (metis subalg restr_to_subalg_def sets.sets_measure_of_eq space_density subalgebra_def)
  qed (auto simp add: assms measurable_restrict ac measurable_in_subalg subalg  sigm_fin_subalg)
  also have "... = (\<integral>\<^sup>+ x. f x \<partial>(density M g))"
    by (metis nn_integral_subalgebra2 subalg assms(2) sets_density space_density subalgebra_def)
  also have "... = (\<integral>\<^sup>+ x. g x * f x \<partial>M)"
    by (rule nn_integral_density) (simp_all add: assms)
  also have "... =   (\<integral>\<^sup>+ x. f x * g x \<partial>M)"
    by (simp add: mult.commute)
  finally show ?thesis by simp
qed

lemma nn_cond_exp_charact:
  assumes "AE x in M. f x \<ge> 0" "AE x in M. g x \<ge> 0"
          "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. g x \<partial>M)" and
          [measurable]:  "f \<in> borel_measurable M" "g \<in> borel_measurable F"
  shows "AE x in M. g x = nn_cond_exp M F f x"
proof -
  let ?MF = "restr_to_subalg M F"
  {
    fix A assume "A \<in> sets ?MF"
    then have [measurable]: "A \<in> sets F" using sets_restr_to_subalg[OF subalg] by simp
    have "(\<integral>\<^sup>+ x \<in> A. g x \<partial> ?MF) = (\<integral>\<^sup>+ x \<in> A. g x \<partial>M)"
      by (simp add: nn_integral_subalgebra2 subalg)
    also have "... = (\<integral>\<^sup>+ x \<in> A. f x \<partial>M)" using assms(3) by simp
    also have "... = (\<integral>\<^sup>+ x. indicator A x * f x \<partial>M)" by (simp add: mult.commute)
    also have "... = (\<integral>\<^sup>+ x. indicator A x * nn_cond_exp M F f x \<partial>M)"
      by (rule nn_cond_exp_intg[symmetric]) (auto simp add: assms)
    also have "... = (\<integral>\<^sup>+ x \<in> A. nn_cond_exp M F f x \<partial>M)" by (simp add: mult.commute)
    also have "... = (\<integral>\<^sup>+ x \<in> A. nn_cond_exp M F f x \<partial> ?MF)"
      by (simp add: nn_integral_subalgebra2 subalg)
    finally have "(\<integral>\<^sup>+ x \<in> A. g x \<partial> ?MF) = (\<integral>\<^sup>+ x \<in> A. nn_cond_exp M F f x \<partial> ?MF)" by simp
  } note * = this
  have "AE x in ?MF. g x =  nn_cond_exp M F f x"
   by (rule sigma_finite_measure.density_unique2)
      (auto simp add: assms subalg  sigm_fin_subalg AE_restr_to_subalg2 * nn_cond_exp_nonneg)
  then show ?thesis using AE_restr_to_subalg[OF subalg] by simp
qed

lemma nn_cond_exp_F_meas:
   assumes "AE x in M. f x \<ge> 0"
           "f \<in> borel_measurable F"
   shows "AE x in M. f x = nn_cond_exp M F f x"
by (rule nn_cond_exp_charact) (auto simp add: assms measurable_from_subalg[OF subalg])

lemma nn_cond_exp_prod:
   assumes "AE x in M. f x \<ge> 0" "AE x in M. g x \<ge> 0" and
           [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable M"
   shows "AE x in M. f x * nn_cond_exp M F g x = nn_cond_exp M F (\<lambda>x. f x * g x) x"
proof (rule nn_cond_exp_charact)
  have [measurable]: "f \<in> borel_measurable M" by (rule measurable_from_subalg[OF subalg assms(3)])
  show "AE x in M. 0 \<le> f x * g x" using assms(1) assms(2) by auto
  show "AE x in M. 0 \<le> f x * nn_cond_exp M F g x"
    by (metis (mono_tags, lifting) assms(1) ereal_0_le_mult eventually_mono nn_cond_exp_nonneg)
  show "(\<lambda>x. f x * g x) \<in> borel_measurable M" by measurable

  fix A assume "A \<in> sets F"
  then have [measurable]: "(\<lambda>x. f x * indicator A x) \<in> borel_measurable F" by measurable
  have "\<integral>\<^sup>+x\<in>A. (f x * g x) \<partial>M = \<integral>\<^sup>+x. (f x * indicator A x) * g x \<partial>M"
    by (simp add: mult.commute mult.left_commute)
  also have "... =  \<integral>\<^sup>+x. (f x * indicator A x) * nn_cond_exp M F g x \<partial>M"
    by (rule nn_cond_exp_intg[symmetric]) (auto simp add: assms)
  also have "... = \<integral>\<^sup>+x\<in>A. (f x * nn_cond_exp M F g x)\<partial>M"
    by (simp add: mult.commute mult.left_commute)
  finally show "\<integral>\<^sup>+x\<in>A. (f x * g x) \<partial>M = \<integral>\<^sup>+x\<in>A. (f x *  nn_cond_exp M F g x)\<partial>M" by simp
qed (auto simp add: assms)

lemma nn_cond_exp_sum:
   assumes "AE x in M. f x \<ge> 0" "AE x in M. g x \<ge> 0" and
           [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
   shows "AE x in M. nn_cond_exp M F f x + nn_cond_exp M F g x = nn_cond_exp M F (\<lambda>x. f x + g x) x"
proof (rule nn_cond_exp_charact)
  show "AE x in M. 0 \<le> f x + g x" using assms(1) assms(2) by auto
  fix A assume [measurable]: "A \<in> sets F"
  then have "A \<in> sets M" by (meson subalg subalgebra_def subsetD)
  have "\<integral>\<^sup>+x\<in>A. (nn_cond_exp M F f x + nn_cond_exp M F g x)\<partial>M =  (\<integral>\<^sup>+x\<in>A. nn_cond_exp M F f x \<partial>M) +  (\<integral>\<^sup>+x\<in>A. nn_cond_exp M F g x \<partial>M)"
    by (rule nn_set_integral_add) (auto simp add: assms `A \<in> sets M` nn_cond_exp_nonneg)
  also have "... =  (\<integral>\<^sup>+x. indicator A x * nn_cond_exp M F f x \<partial>M) +  (\<integral>\<^sup>+x. indicator A x * nn_cond_exp M F g x \<partial>M)"
    by (metis (no_types, lifting) mult.commute nn_integral_cong)
  also have "... =  (\<integral>\<^sup>+x. indicator A x * f x \<partial>M) +  (\<integral>\<^sup>+x. indicator A x * g x \<partial>M)"
    by (simp add: nn_cond_exp_intg assms(1) assms(2) assms(3) assms(4))
  also have "... =  (\<integral>\<^sup>+x\<in>A. f x \<partial>M) +  (\<integral>\<^sup>+x\<in>A. g x \<partial>M)"
    by (metis (no_types, lifting) mult.commute nn_integral_cong)
  also have "... = \<integral>\<^sup>+x\<in>A. (f x + g x)\<partial>M"
    by (rule nn_set_integral_add[symmetric]) (auto simp add: assms `A \<in> sets M`)
  finally show "\<integral>\<^sup>+x\<in>A. (f x + g x)\<partial>M = \<integral>\<^sup>+x\<in>A. (nn_cond_exp M F f x + nn_cond_exp M F g x)\<partial>M"
    by simp
qed (auto simp add: assms nn_cond_exp_nonneg)

lemma nn_cond_exp_cong:
   assumes "AE x in M. f x = g x" and
           [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
   shows "AE x in M. nn_cond_exp M F f x = nn_cond_exp M F g x"
proof (cases)
  assume i: "AE x in M. 0 \<le> f x"
  then have *: "AE x in M. 0 \<le> g x" using assms(1) by auto
  show ?thesis
  proof (rule nn_cond_exp_charact)
  {
    fix A assume [measurable]: "A \<in> sets F"
    have " \<integral>\<^sup>+x\<in>A. nn_cond_exp M F f x \<partial>M = \<integral>\<^sup>+x. indicator A x * nn_cond_exp M F f x \<partial>M"
      by (simp add: mult.commute)
    also have "... = \<integral>\<^sup>+x. indicator A x * f x \<partial>M" by (simp add: nn_cond_exp_intg assms i)
    also have "... = \<integral>\<^sup>+x\<in>A. f x \<partial>M" by (simp add: mult.commute)
    also have "... = \<integral>\<^sup>+x\<in>A. g x \<partial>M" by (rule nn_set_integral_cong[OF assms(1)])
    finally show "\<integral>\<^sup>+x\<in>A. g x \<partial>M = \<integral>\<^sup>+x\<in>A. nn_cond_exp M F f x \<partial>M" by simp
  }
  qed (auto simp add: assms * nn_cond_exp_nonneg)
next
  assume *: "\<not>(AE x in M. 0 \<le> f x)"
  then have a: "nn_cond_exp M F f = (\<lambda>x. 0)" unfolding nn_cond_exp_def by simp
  have "\<not>(AE x in M. 0 \<le> g x)"
  proof (rule ccontr)
    assume " \<not> \<not> (AE x in M. 0 \<le> g x)"
    then have "AE x in M. 0 \<le> g x" by simp
    then have "AE x in M. 0 \<le> f x" using assms(1) by auto
    then show False using * by auto
  qed
  then have b: "nn_cond_exp M F g = (\<lambda>x. 0)" unfolding nn_cond_exp_def by simp
  show ?thesis using a b by simp
qed

lemma nn_cond_exp_mono:
   assumes "AE x in M. f x \<ge> 0" "AE x in M. f x \<le> g x" and
           [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
   shows "AE x in M. nn_cond_exp M F f x \<le> nn_cond_exp M F g x"
proof -
  def h \<equiv> "\<lambda>x. g x - f x"
  have [measurable]: "h \<in> borel_measurable M" unfolding h_def by simp
  have pos: "AE x in M. h x \<ge> 0" using assms(2) ereal_diff_positive h_def by auto
  have "AE x in M. f x \<noteq> (-\<infinity>)" using assms(1) by auto
  then have *: "AE x in M. g x = f x + h x" unfolding h_def using ereal_ineq_diff_add assms(2) by auto
  have "AE x in M. nn_cond_exp M F g x = nn_cond_exp M F (\<lambda>x. f x + h x) x"
    by (rule nn_cond_exp_cong) (auto simp add: * assms)
  moreover have "AE x in M. nn_cond_exp M F f x + nn_cond_exp M F h x = nn_cond_exp M F (\<lambda>x. f x + h x) x"
    by (rule nn_cond_exp_sum) (auto simp add: assms pos)
  ultimately have "AE x in M. nn_cond_exp M F g x =  nn_cond_exp M F f x + nn_cond_exp M F h x" by auto
  moreover have "AE x in M. nn_cond_exp M F h x \<ge> 0" using nn_cond_exp_nonneg by fastforce
  moreover have "\<And>a b c::ereal. a = b + c \<Longrightarrow> c \<ge> 0 \<Longrightarrow> b \<le> a"
    by (metis add.commute add.left_neutral ereal_add_le_add_iff2)
  ultimately show ?thesis by force
qed

lemma nested_subalg_is_sigma_finite:
  assumes "subalgebra M G" "subalgebra G F"
  shows "sigma_finite_subalgebra M G"
unfolding sigma_finite_subalgebra_def
proof (auto simp add: assms)
  have "\<exists>A. countable A \<and> A \<subseteq> sets (restr_to_subalg M F) \<and> \<Union>A = space (restr_to_subalg M F) \<and> (\<forall>a\<in>A. emeasure (restr_to_subalg M F) a \<noteq> \<infinity>)"
    using sigm_fin_subalg sigma_finite_measure_def by auto
  then obtain A where A:"countable A \<and> A \<subseteq> sets (restr_to_subalg M F) \<and> \<Union>A = space (restr_to_subalg M F) \<and> (\<forall>a\<in>A. emeasure (restr_to_subalg M F) a \<noteq> \<infinity>)"
    by auto
   have "sets F \<subseteq> sets M"
    by (meson assms order_trans subalgebra_def)
  then have "countable A \<and> A \<subseteq> sets (restr_to_subalg M G) \<and> \<Union>A = space (restr_to_subalg M F) \<and> (\<forall>a\<in>A. emeasure (restr_to_subalg M G) a \<noteq> \<infinity>)"
    by (metis (no_types) A assms basic_trans_rules(31) emeasure_restr_to_subalg order_trans sets_restr_to_subalg subalgebra_def)
  then show "sigma_finite_measure (restr_to_subalg M G)"
    by (metis sigma_finite_measure.intro space_restr_to_subalg)
qed

lemma nn_cond_exp_nested_subalg:
  assumes "subalgebra M G" "subalgebra G F"
    "AE x in M. f x \<ge> 0" and [measurable]:  "f \<in> borel_measurable M"
  shows "AE x in M. nn_cond_exp M F f x = nn_cond_exp M F (nn_cond_exp M G f) x"
proof (rule nn_cond_exp_charact, auto simp add: nn_cond_exp_nonneg)
  interpret G: sigma_finite_subalgebra M G by (rule nested_subalg_is_sigma_finite[OF assms(1) assms(2)])
  fix A assume [measurable]: "A \<in> sets F"
  then have [measurable]: "A \<in> sets G" using assms(2) by (meson set_mp subalgebra_def)

  have "set_nn_integral M A (nn_cond_exp M G f) = (\<integral>\<^sup>+ x. indicator A x * nn_cond_exp M G f x\<partial>M)"
    by (metis (no_types) mult.commute)
  also have "... = (\<integral>\<^sup>+ x. indicator A x * f x \<partial>M)" by (rule G.nn_cond_exp_intg, auto simp add: assms)
  also have "... = (\<integral>\<^sup>+ x. indicator A x * nn_cond_exp M F f x \<partial>M)" by (rule nn_cond_exp_intg[symmetric], auto simp add: assms)
  also have "... = set_nn_integral M A (nn_cond_exp M F f)" by (metis (no_types) mult.commute)
  finally show "set_nn_integral M A (nn_cond_exp M G f) = set_nn_integral M A (nn_cond_exp M F f)".
qed

end

subsection {*Real conditional expectation*}

text {*Once conditional expectations of positive functions are defined, the definition for real-valued functions
follows readily, by taking the difference of positive and negative parts.
One could also define a conditional expectation of vector-space valued functions, as in
\verb+Bochner_Integral+, but since the real-valued case is the most important, and quicker to formalize, I
concentrate on it. (It is also essential for the case of the most general Pettis integral.)
 *}

definition real_cond_exp :: "'a measure => 'a measure => ('a => real) \<Rightarrow> ('a \<Rightarrow> real)" where
  "real_cond_exp M F f = (\<lambda>x. real_of_ereal(nn_cond_exp M F (\<lambda>x. max (f x) (0::ereal)) x)
                            - real_of_ereal(nn_cond_exp M F (\<lambda>x. max (ereal(-f x)) (0::ereal)) x))"

lemma
  shows borel_measurable_cond_exp [measurable]:  "real_cond_exp M F f \<in> borel_measurable F"
  and   borel_measurable_cond_exp2 [measurable]: "real_cond_exp M F f \<in> borel_measurable M"
unfolding real_cond_exp_def by auto

context sigma_finite_subalgebra
begin

lemma real_cond_exp_abs:
  assumes [measurable]: "f \<in> borel_measurable M"
   shows "AE x in M. abs(real_cond_exp M F f x) \<le> nn_cond_exp M F (\<lambda>x. abs(f x)) x"
proof -
  def fp \<equiv> "\<lambda>x. max (f x) (0::ereal)"
  def fm \<equiv> "\<lambda>x. max (-f x) (0::ereal)"
  have [measurable]: "fp \<in> borel_measurable M" "fm \<in> borel_measurable M" unfolding fp_def fm_def by auto
  have eq: "\<And>x. abs(ereal(f x)) = fp x + fm x" unfolding fp_def fm_def by (simp add: max_def)

  {
    fix x assume H: "nn_cond_exp M F fp x + nn_cond_exp M F fm x = nn_cond_exp M F (\<lambda>x. fp x + fm x) x"
    have "real_cond_exp M F f x = real_of_ereal(nn_cond_exp M F fp x) - real_of_ereal(nn_cond_exp M F fm x)"
      unfolding real_cond_exp_def fp_def fm_def by auto
    then have "abs(real_cond_exp M F f x) \<le> abs(nn_cond_exp M F fp x) + abs(nn_cond_exp M F fm x)"
      by (metis ereal_abs_diff abs_ereal.simps(1) ereal_less_eq(1) ereal_minus(1) ereal_plus_eq_PInfty ereal_real)
    also have "... \<le> nn_cond_exp M F fp x + nn_cond_exp M F fm x"
      by (simp add: nn_cond_exp_nonneg)
    also have "... = nn_cond_exp M F (\<lambda>x. fp x + fm x) x" using H by simp
    finally have "abs(real_cond_exp M F f x) \<le> nn_cond_exp M F (\<lambda>x. fp x + fm x) x" by simp
  }
  moreover have "AE x in M. nn_cond_exp M F fp x + nn_cond_exp M F fm x = nn_cond_exp M F (\<lambda>x. fp x + fm x) x"
    by (rule nn_cond_exp_sum) (auto simp add: fp_def fm_def)
  ultimately have "AE x in M. abs(real_cond_exp M F f x) \<le> nn_cond_exp M F (\<lambda>x. fp x + fm x) x"
    by auto
  then show ?thesis using eq by simp
qed

text{* The next lemma shows that the conditional expectation
is an $F$-measurable function whose average against an $F$-measurable
function $f$ coincides with the average of the original function against $f$.
It is obtained as a consequence of the same property for the positive conditional
expectation, taking the difference of the positive and the negative part. The proof
is given first assuming $f \geq 0$ for simplicity, and then extended to the general case in
the subsequent lemma. The idea of the proof is essentially trivial, but the implementation
is slightly tedious as one should check all the integrability properties of the different parts, and go
back and forth between positive integral and signed integrals, and between real-valued
functions and ereal-valued functions.

Once this lemma is available, we will use it to characterize the conditional expectation,
and never come back to the original technical definition, as we did in the case of the
nonnegative conditional expectation.
*}

lemma real_cond_exp_intg_fpos:
  assumes "integrable M (\<lambda>x. f x * g x)" and
          f_pos: "\<And>x. f x \<ge> 0" and
          [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable M"
  shows  "integrable M (\<lambda>x. f x * real_cond_exp M F g x)"
         "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) = (\<integral> x. f x * g x \<partial>M)"
proof -
  have [measurable]: "f \<in> borel_measurable M" by (rule measurable_from_subalg[OF subalg assms(3)])
  def gp \<equiv> "\<lambda>x. max (g x) (0::ereal)"
  def gm \<equiv> "\<lambda>x. max (-g x) (0::ereal)"
  have [measurable]: "gp \<in> borel_measurable M" "gm \<in> borel_measurable M" unfolding gp_def gm_def by auto
  def h \<equiv> "\<lambda>x. ereal(abs(g x))"
  have hgpgm: "\<And>x. h x = gp x + gm x" unfolding gp_def gm_def h_def  by (simp add: max_def)
  have [measurable]: "h \<in> borel_measurable M" unfolding h_def by simp
  have pos: "\<And>x. h x \<ge> 0" "\<And>x. gp x \<ge> 0" "\<And>x. gm x \<ge> 0" unfolding h_def gp_def gm_def by simp_all
  have gp_real: "\<And>x. real_of_ereal(gp x) = max (g x) 0"
    unfolding gp_def by (metis ereal_max real_of_ereal.simps(1) zero_ereal_def)
  have gm_real: "\<And>x. real_of_ereal(gm x) = max (-g x) 0"
    unfolding gm_def by (metis ereal_max real_of_ereal.simps(1) zero_ereal_def)

  have "(\<integral>\<^sup>+ x. norm(f x * max (g x) 0) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x * g x) \<partial>M)"
    by (simp add: nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(f x * max (g x) 0) \<partial>M) < \<infinity>" by simp
  then have int1: "integrable M (\<lambda>x. f x * max (g x) 0)" by (simp add: integrableI_bounded)

  have "(\<integral>\<^sup>+ x. norm(f x * max (-g x) 0) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x * g x) \<partial>M)"
    by (simp add: nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(f x * max (-g x) 0) \<partial>M) < \<infinity>" by simp
  then have int2: "integrable M (\<lambda>x. f x * max (-g x) 0)" by (simp add: integrableI_bounded)

  have " (\<integral>\<^sup>+x. f x * nn_cond_exp M F h x \<partial>M) =  (\<integral>\<^sup>+x. f x * h x \<partial>M)"
    by (rule nn_cond_exp_intg) (auto simp add: pos)
  also have "... = (\<integral>\<^sup>+x. abs(f x * g x) \<partial>M)"
    unfolding h_def by (simp add: abs_mult f_pos)
  also have "... < \<infinity>" by (auto simp add: assms(1) integrableD(2))
  finally have *: "(\<integral>\<^sup>+x. f x * nn_cond_exp M F h x \<partial>M) < \<infinity>" by simp

  have "(\<integral>\<^sup>+x. norm(f x * real_cond_exp M F g x) \<partial>M) = (\<integral>\<^sup>+x. f x * abs(real_cond_exp M F g x) \<partial>M)"
    by (simp add: abs_mult f_pos)
  also have "... \<le>  (\<integral>\<^sup>+x. f x * nn_cond_exp M F h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    {
      fix x assume *: "abs(real_cond_exp M F g x) \<le> nn_cond_exp M F h x"
      have "ereal (f x * \<bar>real_cond_exp M F g x\<bar>) = f x * ereal(\<bar>real_cond_exp M F g x\<bar>)"
        by simp
      also have "... \<le> f x * nn_cond_exp M F h x"
        using * ereal_mult_left_mono f_pos by (metis ereal_less_eq(5))
      finally have "ereal (f x * \<bar>real_cond_exp M F g x\<bar>) \<le> f x * nn_cond_exp M F h x"
        by simp
    }
    then show "AE x in M. ereal (f x * \<bar>real_cond_exp M F g x\<bar>) \<le> f x * nn_cond_exp M F h x"
      using real_cond_exp_abs[OF assms(4)] h_def by auto
  qed
  finally have **: "(\<integral>\<^sup>+x. norm(f x * real_cond_exp M F g x) \<partial>M) < \<infinity>" using * by auto
  show "integrable M  (\<lambda>x. f x * real_cond_exp M F g x)"
    apply (rule integrableI_bounded) using ** by auto


  have "(\<integral>\<^sup>+x. f x * nn_cond_exp M F gp x \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_cond_exp M F h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    have "AE x in M. nn_cond_exp M F gp x \<le> nn_cond_exp M F h x"
      apply (rule nn_cond_exp_mono) apply (auto simp add: pos hgpgm)  using add_left_mono pos(3) by fastforce
    then show "AE x in M. f x * nn_cond_exp M F gp x \<le> f x * nn_cond_exp M F h x"
      using f_pos ereal_mult_left_mono by auto
  qed
  then have a: "(\<integral>\<^sup>+x. f x * nn_cond_exp M F gp x \<partial>M) < \<infinity>"
    using * by auto
  have "\<And>x. ereal(norm(f x * real_of_ereal(nn_cond_exp M F gp x))) \<le> f x * nn_cond_exp M F gp x"
    by (metis abs_ereal.simps(1) abs_ereal_ge0 ereal_0_le_mult ereal_less_eq(5)
        ereal_mult_zero ereal_real order_refl real_norm_def times_ereal.simps(1) f_pos nn_cond_exp_nonneg)
  then have "(\<integral>\<^sup>+x. norm(f x * real_of_ereal(nn_cond_exp M F gp x)) \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_cond_exp M F gp x \<partial>M)"
    by (simp add: nn_integral_mono)
  then have "(\<integral>\<^sup>+x. norm(f x * real_of_ereal(nn_cond_exp M F gp x)) \<partial>M) < \<infinity>" using a by auto
  then have gp_int: "integrable M (\<lambda>x. f x * real_of_ereal(nn_cond_exp M F gp x))" by (simp add: integrableI_bounded)
  have gp_fin: "AE x in M. f x * nn_cond_exp M F gp x \<noteq> \<infinity>"
    apply (rule nn_integral_PInf_AE) using a by auto

  have "(\<integral> x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M) = real_of_ereal (\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M)"
    by (rule integral_eq_nn_integral) (auto simp add: f_pos nn_cond_exp_nonneg real_of_ereal_pos)
  also have "... = real_of_ereal(\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gp x)) \<partial>M)"
  proof -
    {
      fix x assume "f x * nn_cond_exp M F gp x \<noteq> \<infinity>"
      then have "ereal (f x * real_of_ereal (nn_cond_exp M F gp x)) = ereal (f x) * nn_cond_exp M F gp x"
        by (metis abs_ereal_ge0 ereal_0_le_mult ereal_less_eq(5) ereal_real' f_pos
            nn_cond_exp_nonneg real_of_ereal.simps(1) real_of_ereal_mult)
    }
    then have "AE x in M. ereal (f x * real_of_ereal (nn_cond_exp M F gp x)) = ereal (f x) * nn_cond_exp M F gp x"
      using gp_fin by auto
    then have "(\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M) = (\<integral>\<^sup>+ x. f x * nn_cond_exp M F gp x \<partial>M)"
      by (rule nn_integral_cong_AE)
    also have "... = (\<integral>\<^sup>+ x. f x * gp x \<partial>M)"
      by (rule nn_cond_exp_intg) (auto simp add: gp_def)
    also have "... =  (\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gp x)) \<partial>M)"
      by (rule nn_integral_cong_AE, metis (mono_tags, lifting) ereal_max gp_def gp_real not_eventuallyD times_ereal.simps(1) zero_ereal_def)
    finally have "(\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M) = (\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gp x)) \<partial>M)" by simp
    then show ?thesis by simp
  qed
  also have "... = (\<integral> x. f x * real_of_ereal(gp x) \<partial>M)"
    by (rule integral_eq_nn_integral[symmetric]) (auto simp add: f_pos gp_def real_of_ereal_pos)
  finally have gp_expr: "(\<integral> x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M) =  (\<integral> x. f x * real_of_ereal(gp x) \<partial>M)" by simp


  have "(\<integral>\<^sup>+x. f x * nn_cond_exp M F gm x \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_cond_exp M F h x \<partial>M)"
  proof (rule nn_integral_mono_AE)
    have "AE x in M. nn_cond_exp M F gm x \<le> nn_cond_exp M F h x"
      apply (rule nn_cond_exp_mono) apply (auto simp add: pos hgpgm)  using add_right_mono pos(2) by fastforce
    then show "AE x in M. f x * nn_cond_exp M F gm x \<le> f x * nn_cond_exp M F h x"
      using f_pos ereal_mult_left_mono by auto
  qed
  then have a: "(\<integral>\<^sup>+x. f x * nn_cond_exp M F gm x \<partial>M) < \<infinity>"
    using * by auto
  have "\<And>x. ereal(norm(f x * real_of_ereal(nn_cond_exp M F gm x))) \<le> f x * nn_cond_exp M F gm x"
    by (metis abs_ereal.simps(1) abs_ereal_ge0 ereal_0_le_mult ereal_less_eq(5)
        ereal_mult_zero ereal_real order_refl real_norm_def times_ereal.simps(1) f_pos nn_cond_exp_nonneg)
  then have "(\<integral>\<^sup>+x. norm(f x * real_of_ereal(nn_cond_exp M F gm x)) \<partial>M) \<le> (\<integral>\<^sup>+x. f x * nn_cond_exp M F gm x \<partial>M)"
    by (simp add: nn_integral_mono)
  then have "(\<integral>\<^sup>+x. norm(f x * real_of_ereal(nn_cond_exp M F gm x)) \<partial>M) < \<infinity>" using a by auto
  then have gm_int: "integrable M (\<lambda>x. f x * real_of_ereal(nn_cond_exp M F gm x))" by (simp add: integrableI_bounded)
  have gm_fin: "AE x in M. f x * nn_cond_exp M F gm x \<noteq> \<infinity>"
    apply (rule nn_integral_PInf_AE) using a by auto

  have "(\<integral> x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M) = real_of_ereal (\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M)"
    by (rule integral_eq_nn_integral) (auto simp add: f_pos nn_cond_exp_nonneg real_of_ereal_pos)
  also have "... = real_of_ereal(\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gm x)) \<partial>M)"
  proof -
    {
      fix x assume "f x * nn_cond_exp M F gm x \<noteq> \<infinity>"
      then have "ereal (f x * real_of_ereal (nn_cond_exp M F gm x)) = ereal (f x) * nn_cond_exp M F gm x"
        by (metis abs_ereal_ge0 ereal_0_le_mult ereal_less_eq(5) ereal_real' f_pos
            nn_cond_exp_nonneg real_of_ereal.simps(1) real_of_ereal_mult)
    }
    then have "AE x in M. ereal (f x * real_of_ereal (nn_cond_exp M F gm x)) = ereal (f x) * nn_cond_exp M F gm x"
      using gm_fin by auto
    then have "(\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M) = (\<integral>\<^sup>+ x. f x * nn_cond_exp M F gm x \<partial>M)"
      by (rule nn_integral_cong_AE)
    also have "... =  (\<integral>\<^sup>+ x. f x * gm x \<partial>M)"
      by (rule nn_cond_exp_intg) (auto simp add: gm_def)
    also have "... =  (\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gm x)) \<partial>M)"
      by (rule nn_integral_cong_AE, metis (mono_tags, lifting) ereal_max gm_def gm_real not_eventuallyD times_ereal.simps(1) zero_ereal_def)
    finally have "(\<integral>\<^sup>+ x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M) = (\<integral>\<^sup>+ x. ereal(f x * real_of_ereal(gm x)) \<partial>M)" by simp
    then show ?thesis by simp
  qed
  also have "... = (\<integral> x. f x * real_of_ereal(gm x) \<partial>M)"
    by (rule integral_eq_nn_integral[symmetric]) (auto simp add: f_pos gm_def real_of_ereal_pos)
  finally have gm_expr: "(\<integral> x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M) =  (\<integral> x. f x * real_of_ereal(gm x) \<partial>M)" by simp


  have "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) =  (\<integral> x. f x * real_of_ereal(nn_cond_exp M F gp x) - f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M)"
    unfolding real_cond_exp_def gp_def gm_def by (simp add: right_diff_distrib)
  also have "... =  (\<integral> x. f x * real_of_ereal(nn_cond_exp M F gp x) \<partial>M) -  (\<integral> x. f x * real_of_ereal(nn_cond_exp M F gm x) \<partial>M)"
    by (rule integral_diff) (simp_all add: gp_int gm_int)
  also have "... = (\<integral> x. f x * real_of_ereal(gp x) \<partial>M) - (\<integral> x. f x * real_of_ereal(gm x) \<partial>M)"
    using gp_expr gm_expr by simp
  also have "... = (\<integral> x. f x * max (g x) 0 \<partial>M) - (\<integral> x. f x * max (-g x) 0 \<partial>M)"
    using gp_real gm_real by simp
  also have "... = (\<integral> x. f x * max (g x) 0 - f x * max (-g x) 0 \<partial>M)"
    by (rule integral_diff[symmetric]) (simp_all add: int1 int2)
  also have "... = (\<integral>x. f x * g x \<partial>M)"
    by (metis (mono_tags, hide_lams) diff_0 diff_zero eq_iff max.cobounded2 max_def minus_minus neg_le_0_iff_le right_diff_distrib)
  finally show "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) = (\<integral>x. f x * g x \<partial>M)"
    by simp
qed

lemma real_cond_exp_intg:
  assumes "integrable M (\<lambda>x. f x * g x)" and
          [measurable]: "f \<in> borel_measurable F" "g \<in> borel_measurable M"
  shows  "integrable M (\<lambda>x. f x * real_cond_exp M F g x)"
         "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) = (\<integral> x. f x * g x \<partial>M)"
proof -
  have [measurable]: "f \<in> borel_measurable M" by (rule measurable_from_subalg[OF subalg assms(2)])
  def fp \<equiv> "\<lambda>x. max (f x) 0"
  def fm \<equiv> "\<lambda>x. max (-f x) 0"
  have [measurable]: "fp \<in> borel_measurable M" "fm \<in> borel_measurable M"
    unfolding fp_def fm_def by simp_all
  have [measurable]: "fp \<in> borel_measurable F" "fm \<in> borel_measurable F"
    unfolding fp_def fm_def by simp_all

  have "(\<integral>\<^sup>+ x. norm(fp x * g x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x * g x) \<partial>M)"
    by (simp add: fp_def nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(fp x * g x) \<partial>M) < \<infinity>" by simp
  then have intp: "integrable M (\<lambda>x. fp x * g x)" by (simp add: integrableI_bounded)
  moreover have "\<And>x. fp x \<ge> 0" unfolding fp_def by simp
  ultimately have Rp: "integrable M (\<lambda>x. fp x * real_cond_exp M F g x)"
    "(\<integral> x. fp x * real_cond_exp M F g x \<partial>M) = (\<integral> x. fp x * g x \<partial>M)"
  using real_cond_exp_intg_fpos by auto

  have "(\<integral>\<^sup>+ x. norm(fm x * g x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x * g x) \<partial>M)"
    by (simp add: fm_def nn_integral_mono)
  also have "... < \<infinity>" using assms(1) by (simp add: integrable_iff_bounded)
  finally have "(\<integral>\<^sup>+ x. norm(fm x * g x) \<partial>M) < \<infinity>" by simp
  then have intm: "integrable M (\<lambda>x. fm x * g x)" by (simp add: integrableI_bounded)
  moreover have "\<And>x. fm x \<ge> 0" unfolding fm_def by simp
  ultimately have Rm: "integrable M (\<lambda>x. fm x * real_cond_exp M F g x)"
    "(\<integral> x. fm x * real_cond_exp M F g x \<partial>M) = (\<integral> x. fm x * g x \<partial>M)"
  using real_cond_exp_intg_fpos by auto

  have "integrable M (\<lambda>x. fp x * real_cond_exp M F g x - fm x * real_cond_exp M F g x)"
    using Rp(1) Rm(1) integrable_diff by simp
  moreover have *: "\<And>x. f x * real_cond_exp M F g x =  fp x * real_cond_exp M F g x - fm x * real_cond_exp M F g x"
    unfolding fp_def fm_def by (simp add: max_def)
  ultimately show "integrable M (\<lambda>x. f x * real_cond_exp M F g x)"
    by simp

  have "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) = (\<integral> x. fp x * real_cond_exp M F g x - fm x * real_cond_exp M F g x \<partial>M)"
    using * by simp
  also have "... =  (\<integral> x. fp x * real_cond_exp M F g x \<partial>M)  -  (\<integral> x. fm x * real_cond_exp M F g x \<partial>M)"
    using Rp(1) Rm(1) by simp
  also have "... = (\<integral> x. fp x * g x \<partial>M)  -  (\<integral> x. fm x * g x \<partial>M)"
    using Rp(2) Rm(2) by simp
  also have "... = (\<integral> x. fp x * g x - fm x * g x \<partial>M)"
    using intm intp by simp
  also have "... = (\<integral> x. f x * g x \<partial>M)"
    unfolding fp_def fm_def by (metis (no_types, hide_lams) diff_0 diff_zero max.commute
    max_def minus_minus mult.commute neg_le_iff_le right_diff_distrib)
  finally show "(\<integral> x. f x * real_cond_exp M F g x \<partial>M) = (\<integral> x. f x * g x \<partial>M)" by simp
qed

lemma real_cond_exp_intA:
  assumes [measurable]: "integrable M f" "A \<in> sets F"
  shows "(\<integral> x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. real_cond_exp M F f x \<partial>M)"
proof -
  have "A \<in> sets M" by (meson assms(2) subalg subalgebra_def subsetD)
  have "integrable M (\<lambda>x. indicator A x * f x)" using integrable_mult_indicator[OF `A \<in> sets M` assms(1)] by auto
  then show ?thesis using real_cond_exp_intg(2)[where ?f = "indicator A" and ?g = f, symmetric] by auto
qed

lemma real_cond_exp_int:
 assumes "integrable M f"
  shows  "integrable M (real_cond_exp M F f)" "(\<integral>x. real_cond_exp M F f x \<partial>M) = (\<integral>x. f x \<partial>M)"
using real_cond_exp_intg[where ?f = "\<lambda>x. 1" and ?g = f] assms by auto

lemma real_cond_exp_charact:
  assumes "\<And>A. A \<in> sets F \<Longrightarrow> (\<integral> x \<in> A. f x \<partial>M) = (\<integral> x \<in> A. g x \<partial>M)" and
          [measurable]:  "integrable M f" "integrable M g"
             "g \<in> borel_measurable F"
  shows "AE x in M. g x = real_cond_exp M F f x"
proof -
  let ?MF = "restr_to_subalg M F"
  have "AE x in ?MF. g x =  real_cond_exp M F f x"
  proof (rule density_unique_real)
    fix A assume "A \<in> sets ?MF"
    then have [measurable]: "A \<in> sets F" using sets_restr_to_subalg[OF subalg] by simp
    then have a [measurable]: "A \<in> sets M" by (meson subalg subalgebra_def subsetD)
    have "(\<integral>x \<in> A. g x \<partial> ?MF) = (\<integral>x \<in> A. g x \<partial>M)"
      by (simp add: integral_subalgebra2 subalg)
    also have "... = (\<integral>x \<in> A. f x \<partial>M)" using assms(1) by simp
    also have "... = (\<integral>x. indicator A x * f x \<partial>M)" by (simp add: mult.commute)
    also have "... = (\<integral>x. indicator A x * real_cond_exp M F f x \<partial>M)"
      apply (rule real_cond_exp_intg(2)[symmetric]) using integrable_mult_indicator[OF a assms(2)]  by (auto simp add: assms)
    also have "... = (\<integral>x \<in> A. real_cond_exp M F f x \<partial>M)" by (simp add: mult.commute)
    also have "... = (\<integral>x \<in> A. real_cond_exp M F f x \<partial> ?MF)"
      by (simp add: integral_subalgebra2 subalg)
    finally show "(\<integral>x \<in> A. g x \<partial> ?MF) = (\<integral>x \<in> A. real_cond_exp M F f x \<partial> ?MF)" by simp
  next
    have "integrable M (real_cond_exp M F f)" by (rule real_cond_exp_int(1)[OF assms(2)])
    then show "integrable ?MF (real_cond_exp M F f)" by (metis borel_measurable_cond_exp integrable_in_subalg[OF subalg])
    show "integrable (restr_to_subalg M F) g" by (simp add: assms(3) integrable_in_subalg[OF subalg])
  qed
  then show ?thesis using AE_restr_to_subalg[OF subalg] by simp
qed

lemma real_cond_exp_F_meas:
   assumes "integrable M f"
           "f \<in> borel_measurable F"
   shows "AE x in M. f x = real_cond_exp M F f x"
by (rule real_cond_exp_charact, auto simp add: assms measurable_from_subalg[OF subalg])

lemma real_cond_exp_mult:
   assumes [measurable]:"f \<in> borel_measurable F" "g \<in> borel_measurable M" "integrable M (\<lambda>x. f x * g x)"
   shows "AE x in M. f x * real_cond_exp M F g x = real_cond_exp M F (\<lambda>x. f x * g x) x"
proof (rule real_cond_exp_charact)
  fix A assume "A \<in> sets F"
  then have [measurable]: "(\<lambda>x. f x * indicator A x) \<in> borel_measurable F" by measurable
  have [measurable]: "A \<in> sets M" using subalg by (meson `A \<in> sets F` subalgebra_def subsetD)
  have "\<integral>x\<in>A. (f x * g x) \<partial>M = \<integral>x. (f x * indicator A x) * g x \<partial>M"
    by (simp add: mult.commute mult.left_commute)
  also have "... =  \<integral>x. (f x * indicator A x) * real_cond_exp M F g x \<partial>M"
    apply (rule real_cond_exp_intg(2)[symmetric], auto simp add: assms)
    using integrable_mult_indicator[OF `A \<in> sets M` assms(3)] by (simp add: mult.commute mult.left_commute)
  also have "... = \<integral>x\<in>A. (f x * real_cond_exp M F g x)\<partial>M"
    by (simp add: mult.commute mult.left_commute)
  finally show "\<integral>x\<in>A. (f x * g x) \<partial>M = \<integral>x\<in>A. (f x * real_cond_exp M F g x)\<partial>M" by simp
qed (auto simp add: real_cond_exp_intg(1) assms)

lemma real_cond_exp_add:
   assumes [measurable]: "integrable M f" "integrable M g"
   shows "AE x in M. real_cond_exp M F f x + real_cond_exp M F g x = real_cond_exp M F (\<lambda>x. f x + g x) x"
proof (rule real_cond_exp_charact)
  have "integrable M (real_cond_exp M F f)" "integrable M (real_cond_exp M F g)"
    using real_cond_exp_int(1) assms by auto
  then show "integrable M (\<lambda>x. real_cond_exp M F f x + real_cond_exp M F g x)"
    by auto

  fix A assume [measurable]: "A \<in> sets F"
  then have "A \<in> sets M" by (meson subalg subalgebra_def subsetD)
  have intAf: "integrable M (\<lambda>x. indicator A x * f x)"
    using integrable_mult_indicator[OF `A \<in> sets M` assms(1)] by auto
  have intAg: "integrable M (\<lambda>x. indicator A x * g x)"
    using integrable_mult_indicator[OF `A \<in> sets M` assms(2)] by auto

  have "\<integral>x\<in>A. (real_cond_exp M F f x + real_cond_exp M F g x)\<partial>M =  (\<integral>x\<in>A. real_cond_exp M F f x \<partial>M) +  (\<integral>x\<in>A. real_cond_exp M F g x \<partial>M)"
    apply (rule set_integral_add, auto simp add: assms)
    using  integrable_mult_indicator[OF `A \<in> sets M` real_cond_exp_int(1)[OF assms(1)]]
           integrable_mult_indicator[OF `A \<in> sets M` real_cond_exp_int(1)[OF assms(2)]] by simp_all
  also have "... =  (\<integral>x. indicator A x * real_cond_exp M F f x \<partial>M) +  (\<integral>x. indicator A x * real_cond_exp M F g x \<partial>M)"
    by auto
  also have "... =  (\<integral>x. indicator A x * f x \<partial>M) +  (\<integral>x. indicator A x * g x \<partial>M)"
    using real_cond_exp_intg(2) assms `A \<in> sets F` intAf intAg by auto
  also have "... =  (\<integral>x\<in>A. f x \<partial>M) +  (\<integral>x\<in>A. g x \<partial>M)"
    by auto
  also have "... = \<integral>x\<in>A. (f x + g x)\<partial>M"
    by (rule set_integral_add(2)[symmetric]) (auto simp add: assms `A \<in> sets M` intAf intAg)
  finally show "\<integral>x\<in>A. (f x + g x)\<partial>M = \<integral>x\<in>A. (real_cond_exp M F f x + real_cond_exp M F g x)\<partial>M"
    by simp
qed (auto simp add: assms)

lemma real_cond_exp_cong:
   assumes "AE x in M. f x = g x" and
           [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
   shows "AE x in M. real_cond_exp M F f x = real_cond_exp M F g x"
proof -
  have "AE x in M. nn_cond_exp M F (\<lambda>x. max (f x) (0::ereal)) x = nn_cond_exp M F (\<lambda>x. max (g x) (0::ereal)) x"
    apply (rule nn_cond_exp_cong) using assms by auto
  moreover have "AE x in M. nn_cond_exp M F (\<lambda>x. max (ereal(-f x)) (0::ereal)) x = nn_cond_exp M F (\<lambda>x. max (ereal(-g x)) (0::ereal)) x"
    apply (rule nn_cond_exp_cong) using assms by auto
  ultimately show "AE x in M. real_cond_exp M F f x = real_cond_exp M F g x"
    unfolding real_cond_exp_def by auto
qed

lemma real_cond_exp_cmult:
  fixes c::real
  assumes "integrable M f"
  shows "AE x in M. c * real_cond_exp M F f x = real_cond_exp M F (\<lambda>x. c * f x) x"
by (rule real_cond_exp_mult[where ?f = "\<lambda>x. c" and ?g = f], auto simp add: assms borel_measurable_integrable)

lemma real_cond_exp_diff:
   assumes [measurable]: "integrable M f" "integrable M g"
   shows "AE x in M. real_cond_exp M F f x - real_cond_exp M F g x = real_cond_exp M F (\<lambda>x. f x - g x) x"
proof -
  have "AE x in M. real_cond_exp M F (\<lambda>x. f x + (- g x)) x = real_cond_exp M F f x + real_cond_exp M F (\<lambda>x. -g x) x"
    using real_cond_exp_add[where ?f = f and ?g = "\<lambda>x. - g x"] assms by auto
  moreover have "AE x in M. real_cond_exp M F (\<lambda>x. -g x) x = - real_cond_exp M F g x"
    using real_cond_exp_cmult[where ?f = g and ?c = "-1"] assms(2) by auto
  ultimately show ?thesis by auto
qed

lemma real_cond_exp_pos:
  assumes "AE x in M. f x \<ge> 0" and [measurable]: "f \<in> borel_measurable M"
  shows "AE x in M. real_cond_exp M F f x \<ge> 0"
proof -
  def g \<equiv> "\<lambda>x. max (f x) 0"
  have "AE x in M. f x = g x" using assms g_def by auto
  then have *: "AE x in M. real_cond_exp M F f x = real_cond_exp M F g x" using real_cond_exp_cong g_def by auto

  have "\<And>x. g x \<ge> 0" unfolding g_def by simp
  then have " (\<lambda>x. max (ereal(-g x)) (0::ereal)) =  (\<lambda>x. 0)"
    by (simp add: max_def)
  moreover have "AE x in M. 0 = nn_cond_exp M F (\<lambda>x. 0) x"
    by (rule nn_cond_exp_F_meas, auto)
  ultimately have "AE x in M. nn_cond_exp M F (\<lambda>x. max (ereal(-g x)) (0::ereal)) x = 0"
    by simp
  then have "AE x in M. real_cond_exp M F g x = real_of_ereal(nn_cond_exp M F (\<lambda>x. max (g x) (0::ereal)) x)"
    unfolding real_cond_exp_def by auto
  then have "AE x in M. real_cond_exp M F g x \<ge> 0" by (auto simp add: nn_cond_exp_nonneg real_of_ereal_pos)
  then show ?thesis using * by auto
qed

lemma real_cond_exp_mono:
  assumes "AE x in M. f x \<le> g x" and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F f x \<le> real_cond_exp M F g x"
proof -
  have "AE x in M. real_cond_exp M F g x - real_cond_exp M F f x = real_cond_exp M F (\<lambda>x. g x - f x) x"
    by (rule real_cond_exp_diff, auto simp add: assms)
  moreover have "AE x in M. real_cond_exp M F (\<lambda>x. g x - f x) x \<ge> 0"
    by (rule real_cond_exp_pos, auto simp add: assms(1))
  ultimately have "AE x in M. real_cond_exp M F g x - real_cond_exp M F f x \<ge> 0" by auto
  then show ?thesis by auto
qed

lemma real_cond_exp_pos_strict:
  assumes "AE x in M. f x > 0" and [measurable]: "integrable M f"
  shows "AE x in M. real_cond_exp M F f x > 0"
proof -
  have pos: "AE x in M. f x \<ge> 0" using assms(1) by auto
  then have a: "AE x in M. real_cond_exp M F f x \<ge> 0" using real_cond_exp_pos by simp

  def A \<equiv> "{x \<in> space M. real_cond_exp M F f x = 0}"
  have *: "\<And>x. indicator A x * real_cond_exp M F f x = 0" unfolding A_def by auto
  have "A \<in> sets M" unfolding A_def using borel_measurable_cond_exp by auto
  have "A = {x \<in> space F. real_cond_exp M F f x = 0}" using subalg A_def unfolding subalgebra_def by auto
  then have "A \<in> sets F" using borel_measurable_cond_exp by auto
  then have "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. real_cond_exp M F f x \<partial>M)"
    using real_cond_exp_intA assms(2) by auto
  also have "... = 0" by (simp add: *)
  finally have *: "(\<integral>x \<in> A. f x \<partial>M) = 0" by simp
  have "A \<in> null_sets M"
    apply (rule null_if_pos_func_has_zero_int[OF assms(2) `A \<in> sets M`]) using assms(1) * by auto
  then have "AE x in M. real_cond_exp M F f x \<noteq> 0" unfolding A_def
    by (metis (no_types, lifting) eventually_ae_filter mem_Collect_eq subsetI)
  then show ?thesis using a by auto
qed

lemma real_cond_exp_mono_strict:
  assumes "AE x in M. f x < g x" and [measurable]: "integrable M f" "integrable M g"
  shows "AE x in M. real_cond_exp M F f x < real_cond_exp M F g x"
proof -
  have "AE x in M. real_cond_exp M F g x - real_cond_exp M F f x = real_cond_exp M F (\<lambda>x. g x - f x) x"
    by (rule real_cond_exp_diff, auto simp add: assms)
  moreover have "AE x in M. real_cond_exp M F (\<lambda>x. g x - f x) x > 0"
    by (rule real_cond_exp_pos_strict, auto simp add: assms)
  ultimately have "AE x in M. real_cond_exp M F g x - real_cond_exp M F f x > 0" by auto
  then show ?thesis by auto
qed

lemma real_cond_exp_nested_subalg:
  assumes "subalgebra M G" "subalgebra G F"
     and [measurable]:  "integrable M f"
  shows "AE x in M. real_cond_exp M F f x = real_cond_exp M F (real_cond_exp M G f) x"
proof (rule real_cond_exp_charact)
  interpret G: sigma_finite_subalgebra M G by (rule nested_subalg_is_sigma_finite[OF assms(1) assms(2)])
  show "integrable M (real_cond_exp M G f)" by (auto simp add: assms  G.real_cond_exp_int(1))

  fix A assume [measurable]: "A \<in> sets F"
  then have [measurable]: "A \<in> sets G" using assms(2) by (meson set_mp subalgebra_def)
  have "set_lebesgue_integral M A (real_cond_exp M G f) = set_lebesgue_integral M A f"
    by (rule G.real_cond_exp_intA[symmetric], auto simp add: assms(3))
  also have "... = set_lebesgue_integral M A (real_cond_exp M F f)"
    by (rule real_cond_exp_intA, auto simp add: assms(3))
  finally show "set_lebesgue_integral M A (real_cond_exp M G f) = set_lebesgue_integral M A (real_cond_exp M F f)" by auto
qed (auto simp add: assms real_cond_exp_int(1))

lemma real_cond_exp_setsum:
  fixes f::"'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>i. integrable M (f i)"
  shows "AE x in M. (\<Sum>i\<in>I. real_cond_exp M F (f i) x) = real_cond_exp M F (\<lambda>x. \<Sum>i\<in>I. f i x) x"
proof (rule real_cond_exp_charact)
  fix A assume [measurable]: "A \<in> sets F"
  then have A_meas [measurable]: "A \<in> sets M" by (meson set_mp subalg subalgebra_def)
  have *: "integrable M (\<lambda>x. indicator A x * f i x)" for i
    using integrable_mult_indicator[OF `A \<in> sets M` assms(1)] by auto
  have **: "integrable M (\<lambda>x. indicator A x * real_cond_exp M F (f i) x)" for i
    using integrable_mult_indicator[OF `A \<in> sets M` real_cond_exp_int(1)[OF assms(1)]] by auto
  have inti: "(\<integral>x. indicator A x * f i x \<partial>M) =  (\<integral>x. indicator A x * real_cond_exp M F (f i) x \<partial>M)" for i
    by (rule real_cond_exp_intg(2)[symmetric], auto simp add: *)

  have "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x. (\<Sum>i\<in>I. indicator A x * f i x)\<partial>M)"
    by (simp add: setsum_right_distrib)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x * f i x \<partial>M))"
    by (rule integral_setsum, simp add: *)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x * real_cond_exp M F (f i) x \<partial>M))"
    using inti by auto
  also have "... = (\<integral>x. (\<Sum>i\<in>I. indicator A x * real_cond_exp M F (f i) x)\<partial>M)"
    by (rule integral_setsum[symmetric], simp add: **)
  also have "... = (\<integral>x\<in>A. (\<Sum>i\<in>I. real_cond_exp M F (f i) x)\<partial>M)"
    by (simp add: setsum_right_distrib)
  finally show "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x\<in>A. (\<Sum>i\<in>I. real_cond_exp M F (f i) x)\<partial>M)" by auto
qed (auto simp add: assms real_cond_exp_int(1)[OF assms(1)])

end

end
