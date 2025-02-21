
(*
 Title:Comparable_Probability_Measures.thy
 Author: Tetsuya Sato
 Author: Yasuhiko Minamide
*)

theory Comparable_Probability_Measures
  imports"HOL-Probability.Probability"
    "Additional_Lemmas_for_Integrals"
begin

section \<open>Comparable Pairs of Probability Measures\<close>

text\<open>To compare two probability measures M and N on the same space, we introduce their Radon-Nikodym derivatives (i.e. density functions) with respect to the sum measure M + N. We could consider various base measures, but we choose the sum measure, because it is finite; it is easy to check the absolute continuity M, N << M + N; the Radon-Nikodym derivatives dM and dN are bounded and are essentially partition of unity(i.e. dM + dN = 1 a.e.). \<close>

subsection \<open>Sum of two measures\<close>

definition sum_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure" where
  "sum_measure M N = measure_of (space M) (sets M) (\<lambda> A. emeasure M A + emeasure N A)"

lemma sum_measure_space[simp, measurable]:
  shows "space (sum_measure M N) = space M"
    and "sets (sum_measure M N) = sets M"
  by (auto simp: sum_measure_def)

lemma sum_measure_commutativitiy:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "sum_measure N M = sum_measure M N"
  by (auto simp: sum_measure_def ac_simps realrel_def assms)

lemma sum_measure_space2:
  assumes "space M = space N"
    and "sets M = sets N"
  shows "space (sum_measure M N) = space N"
    and "sets (sum_measure M N) = sets N"
  by (auto simp: assms)

text \<open> This lemma is inspired from @{thm Radon_Nikodym.emeasure_diff_measure} in the standard library. \<close>

lemma emeasure_sum_measure [simp]:
  assumes fin: "finite_measure M"
    and "finite_measure N"
    and sets_eq: "sets M = sets N"
    and A: "A \<in> sets M"
  shows "emeasure (sum_measure M N) A = emeasure M A + emeasure N A"
    (is"_ = ?\<mu> A")
proof(unfold sum_measure_def, rule emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)"
    by (auto simp: sets.sigma_algebra_axioms)
  show "positive (sets M) ?\<mu>"
    by (auto simp: positive_def)
  show "countably_additive (sets M) ?\<mu>"
  proof(rule countably_additiveI)
    fix A :: "nat \<Rightarrow> _"
    assume A: "range A \<subseteq> sets M" and "disjoint_family A"
    hence suminf:
      "(\<Sum>i. emeasure M (A i)) = emeasure M (\<Union>i. A i)"
      "(\<Sum>i. emeasure N (A i)) = emeasure N (\<Union>i. A i)"
      by (simp_all add: suminf_emeasure sets_eq)
    with A have "(\<Sum>i. emeasure M (A i) + emeasure N (A i)) = (\<Sum>i. emeasure M (A i)) + (\<Sum>i. emeasure N (A i))"
      using fin suminf_add summableI by(metis (full_types))
    thus"(\<Sum>i :: nat. emeasure M (A i) + emeasure N (A i)) = emeasure M (\<Union> (range A)) + emeasure N (\<Union> (range A))"
      by (auto simp: suminf(1) suminf(2))
  qed
  show "A \<in> sets M"by (auto simp: A)
qed

lemma sum_measure_finiteness [simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "finite_measure (sum_measure M N)"
proof(rule finite_measureI)
  have "emeasure (sum_measure M N) (space (sum_measure M N)) = emeasure M (space M) + emeasure N (space N)"
    by (auto simp: assms)
  thus "emeasure (sum_measure M N) (space (sum_measure M N)) \<noteq> \<infinity>"
    using assms(1,2) finite_measure.finite_emeasure_space by auto
qed

lemma absolute_continuity_sum_measure [simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "absolutely_continuous (sum_measure M N) M"
  unfolding absolutely_continuous_def null_sets_def
proof(intro subsetI allI impI CollectI)
  fix x assume "x \<in> {x2 \<in> sets (sum_measure M N). emeasure (sum_measure M N) x2 = 0}"
  hence A: "x \<in> sets M \<and> emeasure (sum_measure M N) x = 0"by auto
  have A1: "(sum_measure M N) x = emeasure M x + emeasure N x"
    using A assms(1) assms(2) assms(4) emeasure_sum_measure by blast
  have A2: "emeasure M x \<le> emeasure M x + emeasure N x"by auto
  with A A1 have A3: "emeasure M x + emeasure N x = 0"by auto
  thus"x \<in> sets M \<and> emeasure M x = 0"using A by auto
qed

lemma absolute_continuity_sum_measure2[simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "absolutely_continuous (sum_measure N M) M"
  by (auto simp: assms sum_measure_commutativitiy)

lemma density_sum_measure:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "density (sum_measure M N) (RN_deriv (sum_measure M N) M) = M"
proof-
  have P1: "finite_measure (sum_measure M N)"
    by (auto simp: assms)
  have "absolutely_continuous (sum_measure M N) M"
    by (auto simp: assms)
  thus ?thesis
    by (auto simp: P1 finite_measure.sigma_finite_measure sigma_finite_measure.density_RN_deriv sum_measure_space(2)[of M N])
qed

lemma density_sum_measure2:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "density (sum_measure N M) (RN_deriv (sum_measure N M) M) = M"
  by (auto simp: density_sum_measure assms sum_measure_space(2)[of M N] sum_measure_commutativitiy[of M N])

lemma absolutely_continuous_emeasure_less[simp]:
  assumes "sets M = sets N"
    and "\<forall> A \<in> sets M. emeasure M A \<le> emeasure N A"
  shows "absolutely_continuous N M"
  unfolding absolutely_continuous_def null_sets_def
proof(rule subsetI)
  fix A assume "A \<in> {A \<in> sets N. emeasure N A = 0}"
  hence "A \<in> sets N" and "emeasure N A = 0" and  "A \<in> sets M" and "emeasure M A \<le> emeasure N A"
    using assms by auto
  moreover hence "emeasure M A = 0"
    by auto
  ultimately show "A \<in> {A \<in> sets M. emeasure M A = 0}"
    by auto
qed

lemma emeasure_less_RN_deriv_bound_1[simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
    and "\<forall> A \<in> sets M. emeasure M A \<le> emeasure N A"
  shows "AE x in N . RN_deriv N M x \<le> 1"
proof(rule AE_upper_bound_inf_ennreal)
  fix e :: real assume pose: "0 < e"
  have abs: "absolutely_continuous N M"
    using absolutely_continuous_emeasure_less assms by blast
  show "AE x in N. RN_deriv N M x \<le> 1 + ennreal e"
  proof(rule AE_I)
    let ?C = "{x \<in> space N. \<not> RN_deriv N M x \<le> 1 + ennreal e}"
    show measurableA: "?C \<in> N"
      by measurable
    show "?C \<subseteq> ?C"
      by auto
    have "(1 + ennreal e) * emeasure N ?C = (1 + ennreal e) * \<integral>\<^sup>+ x. indicator ?C x \<partial>N"
      by auto
    also have "... = \<integral>\<^sup>+ x. (1 + ennreal e)* indicator ?C x \<partial>N"
      by (metis (mono_tags, lifting) calculation measurableA nn_integral_cmult_indicator nn_integral_cong)
    also have "... \<le> \<integral>\<^sup>+ x. RN_deriv N M x * indicator ?C x \<partial>N"
    proof(rule nn_integral_mono,cases)
      fix x assume "x \<in> space N" assume A: "x \<in> ?C"
      thus"(1 + ennreal e) * indicator ?C x \<le> RN_deriv N M x * indicator ?C x"
        using A by force
    next
      fix x assume "x \<in> space N" assume A: "x \<notin> ?C"
      thus"(1 + ennreal e) * indicator ?C x \<le> RN_deriv N M x * indicator ?C x"
        using A by force
    qed
    also have "... = \<integral>\<^sup>+ x. indicator ?C x \<partial>M"
    proof(rule sigma_finite_measure.RN_deriv_nn_integral[THEN sym])
      show "sigma_finite_measure N"
        using assms(2) finite_measure_def by auto
      show "absolutely_continuous N M"
        by(intro abs)
      show "sets M = sets N"
        by(intro assms)
      show "indicator {x \<in> space N. \<not> RN_deriv N M x \<le> 1 + ennreal e} \<in> borel_measurable N"
        by measurable
    qed
    also have "... = emeasure M ?C"
      by (auto simp: assms(4))
    also have "... \<le> emeasure N ?C"
      by (auto simp: assms(4) assms(5))
    finally have "(1 + ennreal e)*emeasure N ?C \<le> emeasure N ?C".
    hence "emeasure N ?C + ennreal e * emeasure N ?C \<le> emeasure N ?C"
      by (auto simp: comm_semiring_class.distrib)
    hence "emeasure N ?C - emeasure N ?C + ennreal e * emeasure N ?C \<le> emeasure N ?C - emeasure N ?C"
      by (auto simp: ennreal_minus_mono)
    hence ineq2: "(emeasure N ?C - emeasure N ?C) + ennreal e * emeasure N ?C \<le> (emeasure N ?C - emeasure N ?C)"
      by auto
    have "(emeasure N ?C - emeasure N ?C) = 0"
    proof(rule ennreal_diff_self)
      from assms(2) finite_measure.emeasure_real[of N]
      obtain r :: real where "emeasure N ?C = ennreal r"by auto
      also have "... \<noteq> \<top>"
        using top_neq_ennreal by auto
      finally show "emeasure N ?C \<noteq> \<top>".
    qed
    from this ineq2 have "ennreal e * emeasure N ?C = 0"
      by auto
    thus"emeasure N ?C = 0"
      using pose by auto
  qed
qed

lemma functions_less_upto_AE[simp]:
  assumes "(f :: _\<Rightarrow> 'b :: {linorder_topology, second_countable_topology}) \<in> borel_measurable M"
    and "(g :: _\<Rightarrow>'b) \<in> borel_measurable M"
    and "(h :: _\<Rightarrow> 'b) \<in> borel_measurable M"
    and fgequal: "AE x in M. f x = g x"
    and "AE x in M. g x \<le> h x"
  shows "AE x in M. f x \<le> h x"
proof(rule AE_mp[OF fgequal],rule AE_I')
  let ?C = "{x \<in> space M. g x > h x}"
  let ?B = "{x \<in> space M. f x \<noteq> g x}"
  have Anull: "?C \<in> null_sets M"
    using assms by (subst AE_iff_null_sets, auto)
  have Bnull: "?B \<in> null_sets M"
    using assms by (subst AE_iff_null_sets, auto)
  show "?C \<union> ?B \<in> null_sets M"
    using Anull Bnull by auto
qed(auto)

lemma density_sum_measure_bounded[simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "AE x in (sum_measure M N) .(RN_deriv (sum_measure M N) M) x \<le> 1"
  by(rule emeasure_less_RN_deriv_bound_1,simp_all add: assms)

lemma density_sum_measure_bounded2[simp]:
  assumes "finite_measure M"
    and "finite_measure N"
    and "space M = space N"
    and "sets M = sets N"
  shows "AE x in (sum_measure M N) .(RN_deriv (sum_measure M N) N) x \<le> 1"
  by(rule emeasure_less_RN_deriv_bound_1,simp_all add: assms)

subsection\<open> Miscellaneous additional lemmas on probability measures \<close>

lemma measurable_bind_prob_space_simple:
  assumes[measurable]: "f \<in> L \<rightarrow>\<^sub>M (prob_algebra K)"
  shows "(\<lambda>M. (M \<bind> f)) \<in> (prob_algebra L)\<rightarrow>\<^sub>M (prob_algebra K)"
  by(rule measurable_bind_prob_space[where N = L],auto)

lemma
  assumes "M \<in> space (prob_algebra L)"
  shows actual_prob_space: "prob_space M"
    and space_prob_algebra_sets: "sets M = sets L"
    and space_prob_algebra_space: "space M = space L"
proof-
  show "prob_space M" and 1: "sets M = sets L"
    using assms space_prob_algebra by auto
  show "space M = space L"
    using sets_eq_imp_space_eq[OF 1] by auto
qed

lemma evaluations_probabilistic_process [simp,intro]:
  assumes f: "f \<in> measurable L (prob_algebra K)"
    and "A \<in> sets K"
  shows "(\<lambda> x. measure (f x) A) \<in> borel_measurable L"
    and "(\<lambda> x. emeasure (f x) A) \<in> borel_measurable L"
    and "\<forall> x \<in> space L. measure (f x) A \<le> 1"
    and "\<forall> x \<in> space L. measure (f x) A \<ge> 0"
    and "\<forall> x \<in> space L. norm(measure (f x) A) \<le> 1"
    and "\<forall> x \<in> space L. emeasure (f x) A \<le> 1"
    and "(sets N = sets L) \<Longrightarrow> (finite_measure N)\<Longrightarrow> integrable N (\<lambda> x. measure (f x) A)"
proof-
  show p0: "(\<lambda>x. measure (f x) A) \<in> borel_measurable L"
    using assms by measurable
  show "(\<lambda>x. emeasure (f x) A) \<in> borel_measurable L"
    by (metis assms(1) assms(2) measurable_emeasure_kernel measurable_prob_algebraD)
  show "\<forall> x \<in> space L. emeasure (f x) A \<le> 1"
  proof
    fix x assume xinL: "x \<in> space L"
    show "emeasure (f x) A \<le> 1"
      using assms subprob_space.subprob_emeasure_le_1 subprob_space_kernel[of f ,OF measurable_prob_algebraD[of f L K]] xinL
      by blast
  qed
  thus p1: "\<forall> x \<in> space L. measure (f x) A \<le> 1"
    by (auto intro: f measurable_prob_algebraD subprob_space.subprob_measure_le_1 subprob_space_kernel)
  show p2: "\<forall> x \<in> space L. measure (f x) A \<ge> 0"
    by auto
  show p3: "\<forall> x \<in> space L. norm(measure (f x) A) \<le> 1"
    using p1 p2 by auto
  show "(sets N = sets L) \<Longrightarrow> (finite_measure N)\<Longrightarrow>integrable N (\<lambda> x. measure (f x) A)"
  proof-
    assume a2: "(sets N = sets L)" and a3: "(finite_measure N)"
    show "integrable N (\<lambda>x. measure (f x) A)"
    proof(rule integrableI_bounded)
      show "(\<lambda>x. measure (f x) A) \<in> borel_measurable N"
        using p0 a2 by measurable
      have "(\<integral>\<^sup>+ x. ennreal (norm (measure (f x) A)) \<partial>N) \<le> (\<integral>\<^sup>+ x. ennreal 1 \<partial>N)"
      proof(intro nn_integral_mono)
        fix x assume "x \<in> space N"hence *: "x \<in> space L"
          using a2 sets_eq_imp_space_eq by auto
        thus"ennreal (norm (Sigma_Algebra.measure (f x) A)) \<le> ennreal 1"
          using p3 by auto
      qed
      also have "... = emeasure N (space N)"
        by auto
      also have "... < \<infinity>"
        using a3 finite_measure.finite_emeasure_space top.not_eq_extremum by auto
      finally show "(\<integral>\<^sup>+ x. ennreal (norm (measure (f x) A)) \<partial>N) < \<infinity>".
    qed
  qed
qed

lemma Giry_strength_bind_return:
  assumes "N \<in> space (prob_algebra L)"
    and "x \<in> space K"
  shows "return K x \<Otimes>\<^sub>M N = N \<bind> (\<lambda>y. return (return K x \<Otimes>\<^sub>M N) (x, y))"
proof-
  have 1: "sigma_finite_measure (return K x)"
    by (auto simp: assms(2) prob_space_imp_sigma_finite prob_space_return)
  have 2: "prob_space N"
    using actual_prob_space assms(1) by auto
  hence 3: "sigma_finite_measure N"
    by (auto simp: prob_space_imp_sigma_finite)
  have 4: "prob_space (return K x)"
    by (auto simp: assms(2) prob_space_imp_sigma_finite prob_space_return)
  have "return K x \<Otimes>\<^sub>M N = return K x \<bind> (\<lambda>xa. N \<bind> (\<lambda>y. return (return K x \<Otimes>\<^sub>M N) (xa, y)))"
    by(rule pair_prob_space.pair_measure_eq_bind[of"(return K x)"N ])(auto simp: pair_prob_space_def pair_sigma_finite_def 1 2 3 4)
  also have "... =  N \<bind> (\<lambda>y. return K x \<bind> (\<lambda>xa. return (return K x \<Otimes>\<^sub>M N) (xa, y)))"
    by(rule pair_prob_space.bind_rotate[of _ _ _ "(return K x \<Otimes>\<^sub>M N)"])(auto simp: pair_prob_space_def pair_sigma_finite_def 1 2 3 4)
  also have "... = N \<bind> (\<lambda>y. return (return K x \<Otimes>\<^sub>M N) (x, y))"
    by(intro bind_cong_All ballI bind_return[where N = "K \<Otimes>\<^sub>M N"],subst return_sets_cong[where N = "K \<Otimes>\<^sub>M N"])(auto simp: assms(2))
  finally show "(return K x) \<Otimes>\<^sub>M N = (N \<bind> (\<lambda>y. return ((return K x) \<Otimes>\<^sub>M N) (x, y)))".
qed

subsection \<open> intgrability for pointwise multiplication of funcitons \<close>

definition ess_bounded :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b :: {banach, second_countable_topology}) \<Rightarrow> bool" where
  "ess_bounded M f \<equiv> ((f \<in> borel_measurable M)\<and>(\<exists>r :: real. AE x in M. norm(f x) \<le> r))"

lemma integrable_mult_ess_bounded_integrable[simp]:
  fixes f :: "_\<Rightarrow> 'b :: {banach, second_countable_topology,real_normed_algebra}"
  assumes "ess_bounded M f"
    and "integrable M g"
  shows "integrable M (\<lambda> x. g x * f x)"
proof-
  obtain r where normed: "AE x in M. norm(f x) \<le> r"
    using assms ess_bounded_def by auto
  have [measurable]: "f \<in> borel_measurable M"
    using assms(1) ess_bounded_def by auto
  have [measurable]: "g \<in> borel_measurable M"
    using assms(2) by auto
  show "integrable M (\<lambda> x. g x * f x)"
  proof(rule Bochner_Integration.integrable_bound[of M"\<lambda> x. r *\<^sub>R g x" "(\<lambda> x. g x * f x)"])
    show "integrable M (\<lambda>x. r *\<^sub>R g x)"
      using assms(2) by auto
    show "(\<lambda>x. g x * f x) \<in> borel_measurable M"
      using borel_measurable_times by auto
    show "AE x in M. norm (g x * f x) \<le> norm (r *\<^sub>R g x)"
    proof(rule AE_mp[OF normed],intro AE_I2 impI)
      fix x assume "x \<in> space M" and normed2: "norm (f x) \<le> r"
      show "norm (g x * f x) \<le> norm (r *\<^sub>R g x)"
        by (metis abs_of_nonneg dual_order.trans mult.commute mult_right_mono norm_ge_zero norm_mult_ineq norm_scaleR normed2)
    qed
  qed
qed

lemma integrable_mult_integrable_ess_bounded[simp]:
  fixes f :: "_\<Rightarrow> 'b :: {banach, second_countable_topology,real_normed_algebra}"
  assumes "ess_bounded M f" and "integrable M g"
  shows "integrable M (\<lambda> x. f x * g x)"
proof-
  obtain r where normed: "AE x in M. norm(f x) \<le> r"
    using assms ess_bounded_def by auto
  have [measurable]: "f \<in> borel_measurable M"
    using assms(1) ess_bounded_def by auto
  have [measurable]: "g \<in> borel_measurable M"
    using assms(2) by auto
  show "integrable M (\<lambda> x. f x * g x)"
  proof(rule Bochner_Integration.integrable_bound[of M"\<lambda> x. r *\<^sub>R g x" "(\<lambda> x. (f x) * (g x))"])
    show "integrable M (\<lambda>x. r *\<^sub>R g x)"
      using assms(2) by auto
    show "(\<lambda> x. f x * g x) \<in> borel_measurable M"
      using borel_measurable_times by auto
    show "AE x in M. norm ((f x) * (g x)) \<le> norm (r *\<^sub>R g x)"
    proof(rule AE_mp[OF normed],intro AE_I2 impI)
      fix x assume "x \<in> space M" and normed2: "norm (f x) \<le> r"
      show "norm (f x * g x) \<le> norm (r *\<^sub>R g x)"
        by (metis abs_of_nonneg dual_order.trans mult_right_mono norm_ge_zero norm_mult_ineq norm_scaleR normed2)
    qed
  qed
qed


lemma ess_bounded_const_real[simp,intro]:
  shows "ess_bounded M (\<lambda> x. r :: real)"
  unfolding ess_bounded_def by auto

lemma
  fixes f g :: "_ \<Rightarrow> 'b :: {banach, second_countable_topology, linorder_topology}"
  assumes "ess_bounded M f" and "ess_bounded M g"
  shows ess_bounded_max_real[simp,intro]: "ess_bounded M (\<lambda> x. (max (f x) (g x)))"
    and ess_bounded_min_real[simp,intro]: "ess_bounded M (\<lambda> x. (min (f x) (g x)))"
proof-
  have f[measurable]: "f \<in> borel_measurable M"
    using assms(1) ess_bounded_def by auto
  have g[measurable]: "g \<in> borel_measurable M"
    using assms(2) ess_bounded_def by auto
  obtain r1 :: real where r1: "AE x in M. norm (f x) \<le> r1"
    using assms(1) ess_bounded_def by blast
  obtain r2 :: real where r2: "AE x in M. norm (g x) \<le> r2"
    using assms(2) ess_bounded_def by blast
  let ?A = "{x \<in> space M. norm (f x) > r1}"
  let ?B = "{x \<in> space M. norm (g x) > r2}"
  have NA: "?A \<in> null_sets M"
  proof(subst AE_iff_null_sets)
    show "?A\<in> sets M"using f by measurable
    show "AE x in M. x \<notin> ?A"using r1 by auto
  qed
  have NB: "?B \<in> null_sets M"
  proof(subst AE_iff_null_sets)
    show "?B\<in> sets M"
      by measurable
    show "AE x in M. x \<notin> ?B"using r2
      by auto
  qed
  show "ess_bounded M (\<lambda>x. max (f x) (g x))"
  proof(unfold ess_bounded_def,intro conjI)
    show "(\<lambda>x. max (f x) (g x)) \<in> borel_measurable M"
      by measurable
    show "\<exists>r. AE x in M. norm (max (f x) (g x)) \<le> r"
    proof
      show "AE x in M. norm (max (f x) (g x)) \<le> (max r1 r2)"
      proof(rule AE_I')
        show "?A \<union> ?B \<in> null_sets M"
          by (auto simp: NA NB null_sets.Un)
        show "{x \<in> space M. \<not> norm (max (f x) (g x)) \<le> max r1 r2} \<subseteq> {x \<in> space M. r1 < norm (f x)} \<union> {x \<in> space M. r2 < norm (g x)}"
          by auto
      qed
    qed
  qed

  show "ess_bounded M (\<lambda>x. min (f x) (g x))"
  proof(unfold ess_bounded_def,intro conjI)
    show "(\<lambda>x. min (f x) (g x)) \<in> borel_measurable M"
      by measurable
    show "\<exists>r. AE x in M. norm (min (f x) (g x)) \<le> r"
    proof
      show "AE x in M. norm (min (f x) (g x)) \<le> (max r1 r2)"
      proof(rule AE_I')
        show "?A \<union> ?B \<in> null_sets M"
          by (auto simp: NA NB null_sets.Un)
        show "{x \<in> space M. \<not> norm (min (f x) (g x)) \<le> max r1 r2} \<subseteq> {x \<in> space M. r1 < norm (f x)} \<union> {x \<in> space M. r2 < norm (g x)}"
          by auto
      qed
    qed
  qed
qed

lemma
  fixes f g :: "_\<Rightarrow> 'b :: {banach, second_countable_topology,real_normed_algebra}"
  assumes "ess_bounded M f"
    and "ess_bounded M g"
  shows ess_bounded_add[simp,intro]: "ess_bounded M (\<lambda> x. f x + g x)"
    and ess_bounded_diff[simp,intro]: "ess_bounded M (\<lambda> x. f x - g x)"
    and ess_bounded_mult[simp,intro]: "ess_bounded M (\<lambda> x. f x * g x)"
proof(unfold ess_bounded_def)
  have f[measurable]: "f \<in> borel_measurable M"
    using assms(1) ess_bounded_def by auto
  have g[measurable]: "g \<in> borel_measurable M"
    using assms(2) ess_bounded_def by auto
  obtain r1 :: real where r1: "AE x in M. norm (f x) \<le> r1"
    using assms(1) ess_bounded_def by auto
  obtain r2 :: real where r2: "AE x in M. norm (g x) \<le> r2"
    using assms(2) ess_bounded_def by auto
  let ?A = "{x \<in> space M. norm (f x) > r1}"
  let ?B = "{x \<in> space M. norm (g x) > r2}"
  have NA: "?A \<in> null_sets M"
  proof(subst AE_iff_null_sets)
    show "?A\<in> sets M"using f by measurable
    show "AE x in M. x \<notin> ?A"using r1 by auto
  qed
  have NB: "?B \<in> null_sets M"
  proof(subst AE_iff_null_sets)
    show "?B\<in> sets M"using g by measurable
    show "AE x in M. x \<notin> ?B"using r2 by auto
  qed

  show "(\<lambda>x. f x + g x) \<in> borel_measurable M \<and> (\<exists>r. AE x in M. norm (f x + g x) \<le> r)"
  proof
    show "(\<lambda>x. f x + g x) \<in> borel_measurable M"
      by measurable
    show "\<exists>r. AE x in M. norm (f x + g x) \<le> r"
    proof(intro exI[of _ "r1 + r2"] AE_I')
      show "?A \<union> ?B \<in> null_sets M"
        by (auto simp: NA NB null_sets.Un)
      show "{x \<in> space M. \<not> norm (f x + g x) \<le> r1 + r2} \<subseteq> ?A \<union> ?B"
      proof(safe)
        fix x assume "x \<in> space M" assume "\<not> norm (f x + g x) \<le> r1 + r2"
        hence *: "\<not> (r2 \<ge> norm (g x) \<and> r1 \<ge> norm (f x))"
          by (metis add_mono_thms_linordered_semiring(1) dual_order.trans norm_triangle_ineq)
        assume "\<not> r2 < norm (g x)"
        thus"r1 < norm (f x)"using * by auto
      qed
    qed
  qed


  show "(\<lambda>x. f x - g x) \<in> borel_measurable M \<and> (\<exists>r. AE x in M. norm (f x - g x) \<le> r)"
  proof
    show "(\<lambda>x. f x - g x) \<in> borel_measurable M"
      by measurable
    show "\<exists>r. AE x in M. norm (f x - g x) \<le> r"
    proof(intro exI[of _ "r1 + r2"] AE_I')
      show "?A \<union> ?B \<in> null_sets M"
        by (auto simp: NA NB null_sets.Un)
      show "{x \<in> space M. \<not> norm (f x - g x) \<le> r1 + r2} \<subseteq> ?A \<union> ?B"
      proof(safe)
        fix x assume "x \<in> space M" assume A0: "\<not> norm (f x - g x) \<le> r1 + r2"
        hence *: "\<not> (r2 \<ge> norm (g x) \<and> r1 \<ge> norm (f x))"
        proof -
          have "norm (f x - g x) \<le> norm (f x) + norm (g x)"
            using norm_triangle_ineq4 by blast
          thus ?thesis
            using A0 by force
        qed
        thus "\<not> r2 < norm (g x) \<Longrightarrow> r1 < norm (f x)"
          using * A0 by auto
      qed
    qed
  qed

  show "(\<lambda>x. f x * g x) \<in> borel_measurable M \<and> (\<exists>r. AE x in M. norm (f x * g x) \<le> r)"
  proof
    show "(\<lambda>x. f x * g x) \<in> borel_measurable M"
      using f g borel_measurable_times by blast
    show "\<exists>r. AE x in M. norm (f x * g x) \<le> r"
    proof(intro exI[of _ "r1 * r2"] AE_I')
      show "?A \<union> ?B \<in> null_sets M"
        by (auto simp: NA NB null_sets.Un)
      show "{x \<in> space M. \<not> norm (f x * g x) \<le> r1 * r2} \<subseteq> ?A \<union> ?B"
      proof(safe)
        fix x assume A1: "\<not> norm (f x * g x) \<le> r1 * r2"
        hence A11: "\<not> (norm (f x) \<le> r1 \<and> norm (g x)\<le> r2)"
          using norm_mult_ineq mult_mono'
          by (metis dual_order.trans norm_ge_zero)
        assume A2: "\<not> r2 < norm (g x)"show "r1 < norm (f x)"
          using A11 A2 by auto
      qed
    qed
  qed
qed

lemma integrable_ess_bounded_finite_measure[simp]:
  assumes "finite_measure M"
    and "ess_bounded M f"
  shows "integrable M f"
proof(subst integrable_iff_bounded,rule conjI)
  show "f \<in> borel_measurable M"
    using assms(2) ess_bounded_def by auto
  obtain r where normed: "AE x in M. norm(f x) \<le> r"
    using assms ess_bounded_def by auto
  have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>M) \<le>(\<integral>\<^sup>+ x. ennreal r \<partial>M)"
  proof(rule nn_integral_mono_AE)
    show "AE x in M. ennreal (norm (f x)) \<le> ennreal r"
      using normed ennreal_leI by force
  qed
  also have "... = ennreal r * emeasure M (space M)"
    by auto
  also have "... < \<infinity>"
    using assms
    by (auto simp: ennreal_mult_less_top finite_measure.emeasure_eq_measure)
  finally show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>M) < \<infinity>".
qed

lemma indicat_real_ess_bounded[simp,intro]:
  assumes "A \<in> sets M"
  shows "ess_bounded M (indicat_real A)"
  unfolding ess_bounded_def
proof
  show "indicat_real A \<in> borel_measurable M"
    using assms by measurable
  have "AE x in M. norm (indicat_real A x) \<le> 1"
  proof(rule AE_I2,cases)
    fix x assume "x \<in> space M"
    assume "x \<in> A"
    hence "indicat_real A x = 1"by auto
    thus"norm (indicat_real A x) \<le> 1" by auto
  next fix x assume "x \<in> space M"
    assume "x \<notin> A"
    hence "indicat_real A x = 0"by auto
    thus"norm (indicat_real A x) \<le> 1" by auto
  qed
  thus"\<exists>r. AE x in M. norm (indicat_real A x) \<le> r"by auto
qed

lemma indicat_real_integrable_finite_measure[simp,intro]:
  assumes "finite_measure M" and "A \<in> sets M"
  shows "integrable M (indicat_real A)"
  by (auto simp: assms)

lemma probability_kernel_evaluation_ess_bounded:
  assumes "f \<in> measurable L (prob_algebra M)" and "A \<in> sets M"
  shows "ess_bounded L (\<lambda> x. measure (f x) A)"
  unfolding ess_bounded_def
proof
  show "(\<lambda>x. measure (f x) A) \<in> borel_measurable L"
    using assms by measurable
  have "\<forall> x \<in> space L. (measure (f x) A) \<le> 1"
  proof
    fix x assume P: "x \<in> space L"
    hence "(emeasure (f x) A) \<le> 1"
      by (meson actual_prob_space assms(1) measurable_space prob_space.measure_le_1)
    thus"(measure (f x) A) \<le> 1"
      by (metis P assms(1) assms(2) evaluations_probabilistic_process(3))
  qed
  thus "\<exists>r. AE x in L. norm (measure (f x) A) \<le> r"by auto
qed

lemma probability_kernel_evaluation_integrable[simp,intro]:
  assumes "finite_measure L"
    and "f \<in> measurable L (prob_algebra M)"
    and "A \<in> sets M"
  shows "integrable L (\<lambda> x. measure (f x) A)"
  using assms probability_kernel_evaluation_ess_bounded integrable_ess_bounded_finite_measure by auto

subsection \<open> real-valued bounded density functions of finite measures \<close>

definition real_RN_deriv :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a \<Rightarrow> real" where
  "real_RN_deriv L K =
    (if \<exists>k. (k \<in> borel_measurable L)
     \<and> (density L (ennreal o k) = K)
     \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)
    then SOME k. ((k \<in> borel_measurable L)
    \<and> (density L (ennreal o k) = K)
    \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x))
    else (\<lambda>_. 0))"

lemma real_RN_deriv_I[intro]:
  assumes " k \<in> borel_measurable L \<and> density L (ennreal \<circ> k) = K \<and> (AE x in K. 0 < k x) \<and> (\<forall>x. 0 \<le> k x)"
  shows "density L (ennreal o (real_RN_deriv L K)) = K"
    and "(AE x in K. 0 < real_RN_deriv L K x)"
proof-
  have *: "\<exists>k. (k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)"
    using assms by auto
  hence "(density L (ennreal o (SOME k. ((k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x))))) = K"
    by (rule someI2_ex, blast)
  thus "density L (ennreal o real_RN_deriv L K) = K"
    using * by (auto simp: real_RN_deriv_def)
  from * have "AE x in K. 0 < (SOME k. ((k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x))) x"
    by (rule someI2_ex, blast)
  thus"AE x in K. 0 < real_RN_deriv L K x"
    using * by (auto simp: real_RN_deriv_def)
qed

lemma real_RN_deriv_density[simp]:
  assumes "sigma_finite_measure L"
    and "absolutely_continuous L K"
    and "finite_measure K"
    and "sets K = sets L"
  shows "density L (ennreal o real_RN_deriv L K) = K"
proof-
  obtain k where kborel: "k \<in> borel_measurable L"
    and AEkdensity: "AE x in L. RN_deriv L K x = ennreal (k x)"
    and AEkpos: "AE x in K. 0 < k x"
    and kpos: "\<forall> x. 0 \<le> k x"
    by(rule sigma_finite_measure.real_RN_deriv[of L K],simp_all add: assms)

  have kdensity: "density L (ennreal o k) = density L (RN_deriv L K)"
  proof(rule density_cong,unfold comp_def)
    show "(\<lambda>x. ennreal (k x)) \<in> borel_measurable L"
      using kborel by measurable
    show "AE x in L. ennreal (k x) = RN_deriv L K x"
      using AEkdensity by auto
    show "RN_deriv L K \<in> borel_measurable L"
      by auto
  qed
  also have "... = K"
    using sigma_finite_measure.density_RN_deriv assms(1,2,4) by auto

  hence P: "(k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)"
    by (auto simp: AEkpos kborel kdensity kpos)
  show "density L (ennreal o real_RN_deriv L K) = K"
    by(rule real_RN_deriv_I[OF P])
qed

lemma real_RN_deriv_positive_AE[simp,intro]:
  assumes "sigma_finite_measure L"
    and "absolutely_continuous L K"
    and "finite_measure K"
    and "sets K = sets L"
  shows "AE x in K. 0 < real_RN_deriv L K x"
proof-
  obtain k where kborel[measurable]: "k \<in> borel_measurable L"
    and AEkdensity: "AE x in L. RN_deriv L K x = ennreal (k x)"
    and AEkpos: "AE x in K. 0 < k x"
    and kpos: "\<forall> x. 0 \<le> k x"
    by(rule sigma_finite_measure.real_RN_deriv[of L K],simp_all add: assms)
  hence "density L (ennreal o k) = density L (RN_deriv L K)"
    by(intro density_cong,unfold comp_def,auto)
  also have "... = K"
    using sigma_finite_measure.density_RN_deriv assms(1) assms(2) assms(4) by auto
  hence P: "(k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)"
    by (auto simp: calculation AEkpos kborel kpos)
  show "AE x in K. 0 < real_RN_deriv L K x"
    by(rule real_RN_deriv_I[OF P])
qed

lemma borel_measurable_real_RN_deriv[measurable]:
  shows "real_RN_deriv L K \<in> borel_measurable L"
proof-
  {assume "\<exists>k. ((k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x))"
    hence "(SOME k. (k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)) \<in> borel_measurable L"
      by (rule someI2_ex) auto}
  thus ?thesis by (auto simp: real_RN_deriv_def)
qed

lemma real_RN_deriv_nonegative[simp,intro]:
  shows "\<forall>x. 0 \<le> real_RN_deriv L K x"
proof-
  {
    assume "\<exists>k. k \<in> borel_measurable L \<and> density L (ennreal \<circ> k) = K \<and> (AE x in K. 0 < k x) \<and> (\<forall>x. 0 \<le> k x)"
    hence "\<forall> x. 0 \<le> (SOME k. (k \<in> borel_measurable L) \<and> (density L (ennreal o k) = K) \<and> (AE x in K. 0 < k x) \<and> (\<forall> x. 0 \<le> k x)) x"
      by (rule someI2_ex) auto
  }
  thus ?thesis
    by (auto simp: real_RN_deriv_def)
qed

lemma real_RN_deriv_equals_RN_deriv_AE:
  assumes "sigma_finite_measure L"
    and "absolutely_continuous L K"
    and "finite_measure K"
    and "sets K = sets L"
  shows "AE x in L. (ennreal o real_RN_deriv L K) x = (RN_deriv L K) x"
proof-
  have P: "density L (ennreal o real_RN_deriv L K) = K"
    using assms real_RN_deriv_density by auto
  show "AE x in L. (ennreal o real_RN_deriv L K) x = (RN_deriv L K x)"
  proof(rule sigma_finite_measure.RN_deriv_unique)
    show "density L (ennreal \<circ> real_RN_deriv L K) = K"
      using real_RN_deriv_density[OF assms] by auto
    show "ennreal \<circ> real_RN_deriv L K \<in> borel_measurable L"
      by auto
    show "sigma_finite_measure L"
      using assms by auto
  qed
qed

lemma real_RN_deriv_equals_RN_deriv_AE2:
  assumes "sigma_finite_measure L"
    and "absolutely_continuous L K"
    and "finite_measure K"
    and "sets K = sets L"
  shows "AE x in L. real_RN_deriv L K x = enn2real((RN_deriv L K) x)"
proof-
  have "AE x in L. (ennreal((real_RN_deriv L K) x)) = (RN_deriv L K) x"
    using real_RN_deriv_equals_RN_deriv_AE[OF assms] by auto
  hence "AE x in L. enn2real (ennreal((real_RN_deriv L K) x)) = enn2real ((RN_deriv L K) x)"
    by fastforce
  thus"AE x in L. real_RN_deriv L K x = enn2real (RN_deriv L K x)"
    by auto
qed

lemma real_RN_deriv_bind[simp]:
  assumes "sigma_finite_measure L"
    and "absolutely_continuous L K"
    and "K \<in> space (prob_algebra L)"
    and "f \<in> measurable L (prob_algebra M)"
    and "A \<in> (sets M)"
  shows "measure (K \<bind> f) A = \<integral> x. (real_RN_deriv L K x) * (measure (f x) A) \<partial>L"
proof-
  have finK: "finite_measure K"
    using space_prob_algebra_sets assms prob_space.finite_measure[of K]
    by (metis in_space_prob_algebra prob_spaceI sets_eq_imp_space_eq)
  have setsK: "sets K = sets L"
    using space_prob_algebra_sets assms by auto

  have "measure (K \<bind> f) A = \<integral> x.(measure (f x) A) \<partial>K"
  proof(rule subprob_space.measure_bind[where N = M])
    show "subprob_space K"
      using assms(3) prob_space_imp_subprob_space[of K]
      by (metis in_space_prob_algebra prob_spaceI setsK sets_eq_imp_space_eq)
    show "f \<in> K \<rightarrow>\<^sub>M subprob_algebra M"
      using assms(4) assms(3)
      by (metis measurable_cong_sets measurable_prob_algebraD space_prob_algebra_sets)
    show "A \<in> sets M"
      by (intro assms(5))
  qed
  also have "... = \<integral> x. (measure (f x) A) \<partial>(density L (ennreal o (real_RN_deriv L K)))"
    using real_RN_deriv_density[OF assms(1) assms(2) finK setsK,THEN sym]
    by auto
  also have "... = \<integral> x. (measure (f x) A) \<partial>(density L (real_RN_deriv L K))"
    by (unfold comp_def,auto)
  also have "... = \<integral> x. (real_RN_deriv L K x) * (measure (f x) A) \<partial>L"
    using integral_density[of"\<lambda> x. (measure (f x) A)"L"real_RN_deriv L K"] real_RN_deriv_nonegative assms(4) assms(5)
    by force
  finally show "measure (K \<bind> f) A = \<integral> x. (real_RN_deriv L K x) * (measure (f x) A) \<partial>L".
qed


subsection \<open>Locale for pairs of probability measures to compare.\<close>

locale comparable_probability_measures =
  fixes L M N :: "'a measure"
  assumes M: "M \<in> space (prob_algebra L)"
    and N: "N \<in> space (prob_algebra L)"
begin

(* basic simps *)

lemma prob_spaceM[simp,intro]: "prob_space M"
  using M space_prob_algebra by auto
lemma prob_spaceN[simp,intro]: "prob_space N"
  using N space_prob_algebra by auto
lemma spaceM[simp]: "sets M = sets L"
  using M space_prob_algebra by auto
lemma spaceN[simp]: "sets N = sets L"
  using N space_prob_algebra by auto
lemma finM[simp,intro]: "finite_measure M"
  by(rule prob_space.finite_measure,auto)
lemma finN[simp,intro]: "finite_measure N"
  by(rule prob_space.finite_measure,auto)
lemma spaceML[simp]: "space M = space L"
  using spaceM sets_eq_imp_space_eq by blast
lemma spaceNL[simp]: "space N = space L"
  using spaceN sets_eq_imp_space_eq by blast
lemma McontMN[simp,intro]: "absolutely_continuous (sum_measure M N) M"
  by auto
lemma NcontMN[simp,intro]: "absolutely_continuous (sum_measure M N) N"
  by auto
lemma MNfinite[simp,intro]: "finite_measure (sum_measure M N)"
  by auto
lemma MNsfinite[simp,intro]: "sigma_finite_measure (sum_measure M N)"
  using finite_measure.sigma_finite_measure MNfinite by blast
lemma setMN_L[simp]: "sets (sum_measure M N) = sets L"
  by auto
lemma spaceMN_L[simp]: "space (sum_measure M N) = space L"
  by auto
lemma spaceMN_M: "space (sum_measure M N) = space M"
  by auto
lemma setMN_M: "sets (sum_measure M N) = sets M"
  by auto
lemma spaceMN_N: "space (sum_measure M N) = space N"
  by auto
lemma setMN_N: "sets (sum_measure M N) = sets N"
  by auto
lemma space_sumM[simp]: "M \<in> space (prob_algebra (sum_measure M N))"
  using subprob_algebra_cong space_prob_algebra by fastforce
lemma space_sumN[simp]: "N \<in> space (prob_algebra (sum_measure M N))"
  using subprob_algebra_cong space_prob_algebra by fastforce

(* bounded density functions *)

definition "dM = real_RN_deriv (sum_measure M N) M"

lemma
  shows borel_measurable_dM[measurable]: "dM \<in> borel_measurable (sum_measure M N)"
    and dM_positive_AE[simp]: "AE x in M. 0 < dM x"
    and dM_density [simp]: "density (sum_measure M N) (ennreal o dM) = M"
    and dM_nonnegative[simp]: "(\<forall> x. 0 \<le> dM x)"
  by (simp_all add: dM_def)

lemma dM_RN_deriv_AE:
  shows "AE x in sum_measure M N. dM x = enn2real (RN_deriv (sum_measure M N) M x)"
proof-
  have "AE x in (sum_measure M N). (ennreal \<circ> real_RN_deriv (sum_measure M N) M) x = RN_deriv (sum_measure M N) M x"
    by(rule real_RN_deriv_equals_RN_deriv_AE,simp_all)
  hence "AE x in (sum_measure M N). RN_deriv (sum_measure M N) M x = dM x"
    using dM_def by fastforce
  thus"AE x in sum_measure M N. dM x = enn2real (RN_deriv (sum_measure M N) M x)"
    by auto
qed

lemma dM_less_1_AE:
  shows "AE x in (sum_measure M N). dM x \<le> 1"
proof(rule functions_less_upto_AE[where g = "real_of_ereal o enn2ereal o (RN_deriv (sum_measure M N) M)"])
  show "AE x in sum_measure M N. dM x = (real_of_ereal \<circ> enn2ereal \<circ> RN_deriv (sum_measure M N) M) x"
    using real_RN_deriv_equals_RN_deriv_AE2 by (auto simp: dM_RN_deriv_AE)
  have "AE x in sum_measure M N. (RN_deriv (sum_measure M N) M x) \<le> 1"
    by auto
  thus"AE x in sum_measure M N. (real_of_ereal \<circ> enn2ereal \<circ> RN_deriv (sum_measure M N) M) x \<le> 1"
    using enn2real_leI by fastforce
qed(auto)

lemma dM_bounded:
  shows "AE x in (sum_measure M N). \<bar>dM x\<bar> \<le> 1"
  using dM_less_1_AE dM_nonnegative by auto

lemma dM_boundes2[simp,intro]:
  shows "ess_bounded (sum_measure M N) dM"
  unfolding ess_bounded_def using dM_bounded borel_measurable_dM by fastforce

lemma dM_integrable[simp,intro]:
  shows "integrable(sum_measure M N) dM"
  using dM_boundes2 by auto

lemma dM_bind_integral[simp]:
  assumes "f \<in> measurable (sum_measure M N) (prob_algebra K)" "A \<in> (sets K)"
  shows "measure (M \<bind> f) A = \<integral> x. (dM x) * (measure (f x) A) \<partial> (sum_measure M N)"
  using assms(1) assms(2) dM_def by auto

definition "dN = real_RN_deriv (sum_measure M N) N"

lemma
  shows borel_measurable_dN[measurable]: "dN \<in> borel_measurable (sum_measure M N)"
    and dN_positive_AE[simp]: "AE x in N. 0 < dN x"
    and dN_density[simp]: "density (sum_measure M N) (ennreal o dN) = N"
    and dN_nonnegative[simp]: "(\<forall> x. 0 \<le> dN x)"
  by (simp_all add: dN_def)

lemma dN_less_1_AE:
  shows "AE x in (sum_measure M N). dN x \<le> 1"
proof(rule functions_less_upto_AE[where g = "real_of_ereal o enn2ereal o (RN_deriv (sum_measure M N) N)"])
  have "AE x in (sum_measure M N). (ennreal \<circ> real_RN_deriv (sum_measure M N) N) x = RN_deriv (sum_measure M N) N x"
    by(rule real_RN_deriv_equals_RN_deriv_AE,simp_all)
  thus"AE x in sum_measure M N. dN x = (real_of_ereal \<circ> enn2ereal \<circ> RN_deriv (sum_measure M N) N) x"
    by (auto simp: dN_def real_RN_deriv_equals_RN_deriv_AE2)
  have "AE x in sum_measure M N. (RN_deriv (sum_measure M N) N x) \<le> 1"
    using spaceMN_N by auto
  thus"AE x in sum_measure M N. (real_of_ereal \<circ> enn2ereal \<circ> RN_deriv (sum_measure M N) N) x \<le> 1"
    using enn2real_leI by fastforce
qed(auto)

lemma dN_bounded:
  shows "AE x in (sum_measure M N). \<bar>dN x\<bar> \<le> 1"
  using dN_less_1_AE dN_nonnegative by auto

lemma dN_boundes2[simp,intro]:
  shows "ess_bounded (sum_measure M N) dN"
  unfolding ess_bounded_def using dN_bounded borel_measurable_dN by fastforce

lemma dN_integrable[simp,intro]:
  shows "integrable(sum_measure M N) dN"
  using dN_boundes2 by auto

lemma dN_bind_integral[simp]:
  assumes "f \<in> measurable (sum_measure M N) (prob_algebra K)" and "A \<in> (sets K)"
  shows "measure (N \<bind> f) A = \<integral> x. (dN x) * (measure (f x) A) \<partial> (sum_measure M N)"
  using assms(1) assms(2) dN_def by auto

lemma dM_dN_partition_1_AE:
  shows "AE x in sum_measure M N. dM x + dN x = 1"
proof-
  have F: "\<forall> A \<in> sets(sum_measure M N). emeasure (density (sum_measure M N) (\<lambda> x. ennreal (dM x + dN x))) A = emeasure (sum_measure M N) A"
  proof
    fix A assume A: "A \<in> sets (sum_measure M N)"
    hence "emeasure (density (sum_measure M N) (\<lambda>x. ennreal (dM x + dN x))) A = emeasure (density (sum_measure M N) (\<lambda>x. ennreal (dM x))) A + emeasure (density (sum_measure M N) (\<lambda>x. ennreal (dN x))) A"
      by(auto simp : A intro!: Nonnegative_Lebesgue_Integration.emeasure_density_add[symmetric])
    also have "... = emeasure M A + emeasure N A"
      by(metis dN_density dM_density comp_def[THEN sym])
    also have "... = emeasure (sum_measure M N) A"
      using A by auto
    finally show "emeasure (density (sum_measure M N) (\<lambda>x. ennreal (dM x + dN x))) A = emeasure (sum_measure M N) A".
  qed
  hence "(density (sum_measure M N) (\<lambda> x. ennreal (dM x + dN x))) = (sum_measure M N)"
    by(auto intro!: measure_eqI)
  hence P1: "AE x in sum_measure M N. ennreal(dM x + dN x) = (RN_deriv (sum_measure M N) (sum_measure M N) x)"
    by(auto intro!: sigma_finite_measure.RN_deriv_unique)
  have P3: "(density (sum_measure M N) (\<lambda> x. 1 :: ennreal)) = (sum_measure M N)"
    by (auto simp: density_1)
  have P2: "AE x in sum_measure M N. (\<lambda> y. 1 :: ennreal) x = (RN_deriv (sum_measure M N) (sum_measure M N) x)"
    by(rule sigma_finite_measure.RN_deriv_unique,auto simp add: P3)
  have "AE x in sum_measure M N. ennreal(dM x + dN x) = (1 :: ennreal)"
    using P1 P2 by auto
  thus"AE x in sum_measure M N. (dM x + dN x) = (1 :: real)"
  proof
    show "AE x in sum_measure M N. ennreal (dM x + dN x) = 1 \<longrightarrow> dM x + dN x = 1"
      by (metis (mono_tags, lifting) AE_I2 ennreal_eq_1)
  qed
qed

end (* end of locale *)

end