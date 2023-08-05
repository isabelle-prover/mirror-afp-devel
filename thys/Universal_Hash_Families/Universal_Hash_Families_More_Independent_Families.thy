section \<open>Preliminary Results\<close>

theory Universal_Hash_Families_More_Independent_Families
  imports
    Universal_Hash_Families
    "HOL-Probability.Stream_Space"
    "HOL-Probability.Probability_Mass_Function"
begin

lemma set_comp_image_cong:
  assumes "\<And>x. P x \<Longrightarrow> f x = h (g x)"
  shows "{f x| x. P x} = h ` {g x| x. P x}"
  using assms by (auto simp: setcompr_eq_image)

lemma (in prob_space) k_wise_indep_vars_compose:
  assumes "k_wise_indep_vars k M' X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "k_wise_indep_vars k N (\<lambda>i x. Y i (X i x)) I"
  using indep_vars_compose2[where N="N" and X="X" and Y="Y" and M'="M'"] assms
  by (simp add: k_wise_indep_vars_def subsetD)

text \<open>The following two lemmas are of independent interest, they help infer independence of events
and random variables on distributions. (Candidates for
@{theory "HOL-Probability.Independent_Family"}).\<close>

lemma (in prob_space) indep_sets_distr:
  fixes A
  assumes "random_variable N f"
  defines "F \<equiv> (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i)"
  assumes indep_F: "indep_sets F I"
  assumes sets_A: "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
  shows "prob_space.indep_sets (distr M N f) A I"
proof (rule prob_space.indep_setsI)
  show "\<And>A' J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> \<forall>j\<in>J. A' j \<in> A j \<Longrightarrow>
      measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
  proof -
    fix A' J
    assume a:"J \<subseteq> I" "finite J" "J \<noteq> {}" "\<forall>j \<in> J. A' j \<in> A j"

    define F' where "F' = (\<lambda>i. f -` A' i \<inter> space M)"

    have "\<Inter> (F' ` J) = f -` (\<Inter> (A' ` J)) \<inter> space M"
      unfolding  set_eq_iff F'_def using a(3) by simp
    moreover have "\<Inter> (A' ` J) \<in> sets N"
      by (metis a sets_A sets.finite_INT subset_iff)
    ultimately have b:
      "measure (distr M N f) (\<Inter> (A' ` J)) = measure M (\<Inter> (F' ` J))"
      by (metis assms(1) measure_distr)

    have "\<And>j. j \<in> J \<Longrightarrow> F' j \<in> F j"
      using a(4) F'_def F_def by blast
    hence c:"measure M (\<Inter> (F' ` J)) = (\<Prod>j\<in> J. measure M (F' j))"
      by (metis indep_F indep_setsD a(1,2,3))

    have "\<And>j. j \<in> J \<Longrightarrow> F' j =  f -` A' j  \<inter> space M"
      by (simp add:F'_def)
    moreover have "\<And>j. j \<in> J \<Longrightarrow> A' j \<in> sets N"
      using a(1,4) sets_A by blast
    ultimately have d:
      "\<And>j. j \<in> J \<Longrightarrow> measure M (F' j) = measure (distr M N f) (A' j)"
      using assms(1) measure_distr by metis

    show
      "measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
      using b c d by auto
  qed
  show "prob_space (distr M N f)" using prob_space_distr assms by blast
  show "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets (distr M N f)" using sets_A sets_distr by blast
qed

lemma (in prob_space) indep_vars_distr:
  assumes "f \<in> measurable M N"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X' i \<in> measurable N (M' i)"
  assumes "indep_vars M' (\<lambda>i. (X' i) \<circ> f) I"
  shows "prob_space.indep_vars (distr M N f) M' X' I"
proof -
  interpret D: prob_space "(distr M N f)"
    using prob_space_distr[OF assms(1)] by simp

  have a: "f \<in> space M \<rightarrow> space N" using assms(1) by (simp add:measurable_def)

  have "D.indep_sets (\<lambda>i. {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}) I"
  proof (rule indep_sets_distr[OF assms(1)])
    have "\<And>i. i \<in> I \<Longrightarrow> {(X' i \<circ> f) -` A \<inter> space M |A. A \<in> sets (M' i)} =
      (\<lambda>a. f -` a \<inter> space M) ` {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}"
      by (rule set_comp_image_cong, simp add:set_eq_iff, use a in blast)
    thus "indep_sets (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) `
        {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}) I"
      using assms(3) by (simp add:indep_vars_def2 cong:indep_sets_cong)
  next
    fix i
    assume "i \<in> I"
    thus "{X' i -` A \<inter> space N |A. A \<in> sets (M' i)} \<subseteq> sets N"
      using assms(2) measurable_sets by blast
  qed
  thus ?thesis
    using assms by (simp add:D.indep_vars_def2)
qed

lemma range_inter: "range ((\<inter>) F) = Pow F"
  unfolding image_def by auto

text \<open>The singletons and the empty set form an intersection stable generator of a countable
discrete $\sigma$-algebra:\<close>

lemma sigma_sets_singletons_and_empty:
  assumes "countable M"
  shows "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) = Pow M"
proof -
  have "sigma_sets M ((\<lambda>k. {k}) ` M) = Pow M"
    using assms sigma_sets_singletons by auto
  hence "Pow M \<subseteq> sigma_sets M (insert {} ((\<lambda>k. {k}) ` M))"
    by (metis sigma_sets_subseteq subset_insertI)
  moreover have "(insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M" by blast
  hence "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M"
    by (meson sigma_algebra.sigma_sets_subset sigma_algebra_Pow)
  ultimately show ?thesis by force
qed

text \<open>In some of the following theorems, the premise @{term "M = measure_pmf p"} is used. This allows stating
theorems that hold for pmfs more concisely, for example, instead of
@{term "measure_pmf.prob p A \<le> measure_pmf.prob p B"} we can
just write @{term "M = measure_pmf p \<Longrightarrow> prob A \<le> prob B"} in the locale @{locale "prob_space"}.\<close>

lemma prob_space_restrict_space:
  assumes [simp]:"M = measure_pmf p"
  shows "prob_space (restrict_space M (set_pmf p))"
  by (rule prob_spaceI, auto simp:emeasure_restrict_space emeasure_pmf)

text \<open>The abbreviation below is used to specify the discrete $\sigma$-algebra on @{term "UNIV"}
as a measure space. It is used in places where the existing definitions, such as @{term "indep_vars"},
expect a measure space even though only a \emph{measurable} space is really needed, i.e., in cases
where the property is invariant with respect to the actual measure.\<close>

hide_const (open) discrete

abbreviation "discrete \<equiv> count_space UNIV"

lemma (in prob_space) indep_vars_restrict_space:
  assumes [simp]:"M = measure_pmf p"
  assumes
    "prob_space.indep_vars (restrict_space M (set_pmf p)) (\<lambda>_. discrete) X I"
  shows "indep_vars (\<lambda>_. discrete) X I"
proof -
  have a: "id \<in> restrict_space M (set_pmf p) \<rightarrow>\<^sub>M M"
    by (simp add:measurable_def range_inter sets_restrict_space)

  have "prob_space.indep_vars (distr (restrict_space M (set_pmf p)) M id) (\<lambda>_. discrete) X I"
    using assms a prob_space_restrict_space by (auto intro!:prob_space.indep_vars_distr)
  moreover have
    "\<And>A. emeasure (distr (restrict_space M (set_pmf p)) M id) A = emeasure M A"
    using emeasure_distr[OF a]
    by (auto simp add: emeasure_restrict_space emeasure_Int_set_pmf)
  hence "distr (restrict_space M p) M id = M"
    by (auto intro: measure_eqI)
  ultimately show ?thesis by simp
qed

lemma (in prob_space) measure_pmf_eq:
  assumes "M = measure_pmf p"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> (x \<in> P) = (x \<in> Q)"
  shows "prob P = prob Q"
  unfolding assms(1)
  by (rule measure_eq_AE, rule AE_pmfI[OF assms(2)], auto)

text \<open>The following lemma is an intro rule for the independence of random variables defined on pmfs.
In that case it is possible, to check the independence of random variables point-wise.

The proof relies on the fact that the support of a pmf is countable and the $\sigma$-algebra of
such a set can be generated by singletons.\<close>

lemma (in prob_space) indep_vars_pmf:
  assumes [simp]:"M = measure_pmf p"
  assumes "\<And>a J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow>
    prob {\<omega>. \<forall>i \<in> J. X i \<omega> = a i} = (\<Prod>i \<in> J. prob {\<omega>. X i \<omega> = a i})"
  shows "indep_vars (\<lambda>_. discrete) X I"
proof -
  interpret R:prob_space "(restrict_space M (set_pmf p))"
    using prob_space_restrict_space by auto

  have events_eq_pow: "R.events = Pow (set_pmf p)"
    by (simp add:sets_restrict_space range_inter)

  define G where "G = (\<lambda>i. {{}} \<union> (\<lambda>x. {x}) ` (X i ` set_pmf p))"
  define F where "F = (\<lambda>i. {X i -` a \<inter> set_pmf p|a. a \<in> G i})"

  have sigma_sets_pow:
    "\<And>i. i \<in> I \<Longrightarrow> sigma_sets (X i ` set_pmf p) (G i) = Pow (X i ` set_pmf p)"
    by (simp add:G_def, metis countable_image countable_set_pmf sigma_sets_singletons_and_empty)

  have F_in_events: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> Pow (set_pmf p)"
    unfolding F_def by blast

  have as_sigma_sets:
    "\<And>i. i \<in> I \<Longrightarrow> {u. \<exists>A. u = X i -` A \<inter> set_pmf p} = sigma_sets (set_pmf p) (F i)"
  proof -
    fix i
    assume a:"i \<in> I"
    have "\<And>A. X i -` A \<inter> set_pmf p = X i -` (A \<inter> X i ` set_pmf p) \<inter> set_pmf p"
      by auto
    hence "{u. \<exists>A. u = X i -` A \<inter> set_pmf p} =
          {X i -` A \<inter> set_pmf p |A. A \<subseteq> X i ` set_pmf p}"
      by (metis (no_types, opaque_lifting) inf_le2)
    also have
      "... = {X i -` A \<inter> set_pmf p |A. A \<in> sigma_sets (X i ` set_pmf p) (G i)}"
      using a by (simp add:sigma_sets_pow)
    also have "... = sigma_sets (set_pmf p) {X i -` a \<inter> set_pmf p |a. a \<in> G i}"
      by (subst sigma_sets_vimage_commute[symmetric], auto)
    also have "... = sigma_sets (set_pmf p) (F i)"
      by (simp add:F_def)
    finally show
      "{u. \<exists>A. u = X i -` A \<inter> set_pmf p} = sigma_sets (set_pmf p) (F i)"
      by simp
  qed

  have F_Int_stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  proof (rule Int_stableI)
    fix i a b
    assume "i \<in> I"  "a \<in> F i"  "b \<in> F i"
    thus "a \<inter> b \<in> (F i)"
      unfolding F_def G_def by (cases "a \<inter> b = {}", auto)
  qed

  have F_indep_sets:"R.indep_sets F I"
  proof (rule R.indep_setsI)
    fix i
    assume "i \<in> I"
    show "F i \<subseteq> R.events"
      unfolding F_def events_eq_pow by blast
  next
    fix A
    fix J
    assume a:"J \<subseteq> I" "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> F j"
    have b: "\<And>j. j \<in> J \<Longrightarrow> A j \<subseteq> set_pmf p"
      by (metis PowD a(1,4) subsetD F_in_events)
    obtain x where x_def:"\<And>j. j \<in> J  \<Longrightarrow> A j = X j -` x j \<inter> set_pmf p \<and> x j \<in> G j"
      using a by (simp add:Pi_def F_def, metis)

    show "R.prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. R.prob (A j))"
    proof (cases "\<exists>j \<in> J. A j = {}")
      case True
      hence "\<Inter> (A ` J) = {}" by blast
      then show ?thesis
        using a True by (simp, metis measure_empty)
    next
      case False
      then have "\<And>j. j \<in> J \<Longrightarrow> x j \<noteq> {}" using x_def by auto
      hence "\<And>j. j \<in> J \<Longrightarrow> x j \<in> (\<lambda>x. {x}) ` X j ` set_pmf p"
        using x_def by (simp add:G_def)
      then obtain y where y_def: "\<And>j. j \<in> J \<Longrightarrow> x j = {y j}"
        by (simp add:image_def, metis)

      have "\<Inter> (A ` J) \<subseteq> set_pmf p" using b a(2) by blast
      hence "R.prob (\<Inter> (A ` J)) = prob (\<Inter> j \<in> J. A j)"
        by (simp add: measure_restrict_space)
      also have "... = prob ({\<omega>. \<forall>j \<in> J. X j \<omega> = y j})"
        using a x_def y_def apply (simp add:vimage_def measure_Int_set_pmf)
        by (rule arg_cong2 [where f="measure"], auto)
      also have "... = (\<Prod> j\<in> J. prob (A j))"
        using x_def y_def a assms(2)
        by (simp add:vimage_def measure_Int_set_pmf)
      also have "... = (\<Prod>j\<in>J. R.prob (A j))"
        using b by (simp add: measure_restrict_space cong:prod.cong)
      finally show ?thesis by blast
    qed
  qed

  have "R.indep_sets (\<lambda>i. sigma_sets (set_pmf p) (F i)) I"
    using R.indep_sets_sigma[simplified] F_Int_stable F_indep_sets
    by (auto simp:space_restrict_space)

  hence "R.indep_sets (\<lambda>i. {u. \<exists>A. u = X i -` A \<inter> set_pmf p}) I"
    by (simp add: as_sigma_sets cong:R.indep_sets_cong)

  hence "R.indep_vars (\<lambda>_. discrete) X I"
    unfolding  R.indep_vars_def2
    by (simp add:measurable_def sets_restrict_space range_inter)

  thus ?thesis
    using indep_vars_restrict_space[OF assms(1)] by simp
qed

lemma (in prob_space) split_indep_events:
  assumes "M = measure_pmf p"
  assumes "indep_vars (\<lambda>i. discrete) X' I"
  assumes "K \<subseteq> I" "finite K"
  shows "prob {\<omega>. \<forall>x \<in> K. P x (X' x \<omega>)} = (\<Prod>x \<in> K. prob {\<omega>. P x (X' x \<omega>)})"
proof -
  have [simp]: "space M = UNIV"  "events = UNIV"  "prob UNIV = 1"
    by (simp add:assms(1))+

  have "indep_vars (\<lambda>_. discrete) X' K"
    using assms(2,3) indep_vars_subset by blast
  hence "indep_events (\<lambda>x. {\<omega> \<in> space M. P x (X' x \<omega>)}) K"
    using indep_eventsI_indep_vars by force
  hence a:"indep_events (\<lambda>x. {\<omega>. P x (X' x \<omega>)}) K"
    by simp

  have "prob  {\<omega>. \<forall>x \<in> K. P x (X' x \<omega>)} = prob (\<Inter>x \<in> K. {\<omega>. P x (X' x \<omega>)})"
    by (simp add: measure_pmf_eq[OF assms(1)])
  also have "... =  (\<Prod> x \<in> K. prob {\<omega>. P x (X' x \<omega>)})"
    using a assms(4) by (cases "K = {}", auto simp: indep_events_def)
  finally show ?thesis by simp
qed

lemma pmf_of_set_eq_uniform:
  assumes "finite A" "A \<noteq> {}"
  shows "measure_pmf (pmf_of_set A) = uniform_measure discrete A"
proof -
  have a:"real (card A) > 0" using assms
    by (simp add: card_gt_0_iff)

  have b:
    "\<And>Y. emeasure (pmf_of_set A) Y = emeasure (uniform_measure discrete A) Y"
    using assms a
    by (simp add: emeasure_pmf_of_set divide_ennreal ennreal_of_nat_eq_real_of_nat)

  show ?thesis
    by (rule measure_eqI, auto simp add: b)
qed

lemma (in prob_space) uniform_onI:
  assumes "M = measure_pmf p"
  assumes "finite A" "A \<noteq> {}"
  assumes "\<And>a. prob {\<omega>. X \<omega> = a} = indicator A a / card A"
  shows "uniform_on X A"
proof -
  have a:"\<And>a. measure_pmf.prob p {x. X x = a} = indicator A a / card A"
    using assms(1,4) by simp

  have b:"map_pmf X p = pmf_of_set A"
    by (rule pmf_eqI, simp add:assms pmf_map vimage_def a)

  have "distr M discrete X = map_pmf X p"
    by (simp add: map_pmf_rep_eq assms(1))
  also have "... = measure_pmf (pmf_of_set A)"
    using b by simp
  also have "... =  uniform_measure discrete A"
    by (rule pmf_of_set_eq_uniform[OF assms(2,3)])
  finally have "distr M discrete X = uniform_measure discrete A"
    by simp
  moreover have "random_variable discrete X"
    by (simp add: assms(1))
  ultimately show  ?thesis using assms(2,3)
    by (simp add: uniform_on_def)
qed

end
