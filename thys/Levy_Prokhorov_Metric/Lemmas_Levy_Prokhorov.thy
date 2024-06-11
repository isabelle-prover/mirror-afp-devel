(*  Title:   Lemmas_Levy_Prokhorov.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Preliminaries\<close>
theory Lemmas_Levy_Prokhorov
  imports "Standard_Borel_Spaces.StandardBorel"
begin

(* TODO: move the following *)
lemma(in Metric_space) [measurable]:
  shows mball_sets: "mball x e \<in> sets (borel_of mtopology)"
  and mcball_sets: "mcball x e \<in> sets (borel_of mtopology)"
  by(auto simp: borel_of_open borel_of_closed)

lemma Metric_space_eq_MCauchy:
  assumes "Metric_space M d" "\<And>x y. x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> d x y = d' x y"
      and "\<And>x y. d' x y = d' y x" "\<And>x y. d' x y \<ge> 0"
    shows "Metric_space.MCauchy M d xn \<longleftrightarrow> Metric_space.MCauchy M d' xn"
proof -
  interpret d: Metric_space M d by fact
  interpret d': Metric_space M d'
    using Metric_space_eq assms d.Metric_space_axioms by blast
  show ?thesis
    using assms(2) by(auto simp: d.MCauchy_def d'.MCauchy_def subsetD)
qed

lemma borel_of_compact: "Hausdorff_space X \<Longrightarrow> compactin X K \<Longrightarrow> K \<in> sets (borel_of X)"
  by(auto intro!: borel_of_closed compactin_imp_closedin)

(* Want the following to be in HOL-Probability *)
lemma prob_algebra_cong: "sets M = sets N \<Longrightarrow> prob_algebra M = prob_algebra N"
  by(simp add: prob_algebra_def cong: subprob_algebra_cong)

(* Want the following to be in Abstract_Topology *)
lemma topology_eq_closedin: "X = Y \<longleftrightarrow> (\<forall>C. closedin X C \<longleftrightarrow> closedin Y C)"
  unfolding topology_eq
  by (metis closedin_def closedin_topspace openin_closedin_eq openin_topspace subset_antisym) 

text \<open> Another version of @{thm finite_measure.countable_support}\<close>
lemma(in finite_measure) countable_support_sets:
  assumes "disjoint_family_on Ai D"
  shows "countable {i\<in>D. measure M (Ai i) \<noteq> 0}"
proof cases
  assume "measure M (space M) = 0"
  with bounded_measure measure_le_0_iff have [simp]:"{i\<in>D. measure M (Ai i) \<noteq> 0} = {}"
    by auto
  show ?thesis
    by simp
next
  let ?M = "measure M (space M)" and ?m = "\<lambda>i. measure M (Ai i)"
  assume "?M \<noteq> 0"
  then have *: "{i\<in>D. ?m i \<noteq> 0} = (\<Union>n. {i\<in>D. ?M / Suc n < ?m i})"
    using reals_Archimedean[of "?m x / ?M" for x]
    by (auto simp: field_simps not_le[symmetric] divide_le_0_iff measure_le_0_iff)
  have **: "\<And>n. finite {i\<in>D. ?M / Suc n < ?m i}"
  proof (rule ccontr)
    fix n assume "infinite {i\<in>D. ?M / Suc n < ?m i}" (is "infinite ?X")
    then obtain X where "finite X" "card X = Suc (Suc n)" "X \<subseteq> ?X"
      by (meson infinite_arbitrarily_large)
    from this(3) have *: "\<And>x. x \<in> X \<Longrightarrow> ?M / Suc n \<le> ?m x"
      by auto
    { fix i assume "i \<in> X"
      from \<open>?M \<noteq> 0\<close> *[OF this] have "?m i \<noteq> 0" by (auto simp: field_simps measure_le_0_iff)
      then have "Ai i \<in> sets M" by (auto dest: measure_notin_sets) }
    note sets_Ai = this
    have disj: "disjoint_family_on Ai X"
      using \<open>X \<subseteq> ?X\<close> assms by(auto simp: disjoint_family_on_def)
    have "?M < (\<Sum>x\<in>X. ?M / Suc n)"
      using \<open>?M \<noteq> 0\<close>
      by (simp add: \<open>card X = Suc (Suc n)\<close> field_simps less_le)
    also have "\<dots> \<le> (\<Sum>x\<in>X. ?m x)"
      by (rule sum_mono) fact
    also have "\<dots> = measure M (\<Union>i\<in>X. Ai i)"
      using sets_Ai \<open>finite X\<close>  by (intro  finite_measure_finite_Union[symmetric,OF _ _ disj])
        (auto simp: disjoint_family_on_def)
    finally have "?M < measure M (\<Union>i\<in>X. Ai i)" .
    moreover have "measure M (\<Union>i\<in>X. Ai i) \<le> ?M"
      using sets_Ai[THEN sets.sets_into_space] by (intro finite_measure_mono) auto
    ultimately show False by simp
  qed
  show ?thesis
    unfolding * by (intro countable_UN countableI_type countable_finite[OF **])
qed

subsection \<open> Finite Sum of Measures \<close>
definition sum_measure :: "'b measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> 'b measure" where
"sum_measure M I Mi \<equiv> measure_of (space M) (sets M) (\<lambda>A. \<Sum>i\<in>I. emeasure (Mi i) A)"

lemma sum_measure_cong:
  assumes "sets M = sets M'" "\<And>i. i \<in> I \<Longrightarrow> N i = N' i"
  shows "sum_measure M I N = sum_measure M' I N'"
  by(simp add: sum_measure_def assms cong: sets_eq_imp_space_eq)

lemma [simp]:
  shows space_sum_measure: "space (sum_measure M I Mi) = space M"
    and sets_sum_measure[measurable_cong]: "sets (sum_measure M I Mi) = sets M"
  by(auto simp: sum_measure_def)

lemma emeasure_sum_measure:
  assumes [measurable]:"A \<in> sets M" and "\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets M"
  shows "emeasure (sum_measure M I Mi) A = (\<Sum>i\<in>I. Mi i A)"

proof(rule emeasure_measure_of[of _ "space M" "sets M"])
  show "countably_additive (sets (sum_measure M I Mi)) (\<lambda>A. \<Sum>i\<in>I. emeasure (Mi i) A)"
    unfolding sum_measure_def sets.sets_measure_of_eq countably_additive_def
  proof safe
    fix Ai :: "nat \<Rightarrow> _"
    assume h:"range Ai \<subseteq> sets M" "disjoint_family Ai"
    then have [measurable]: "\<And>i j. j \<in> I \<Longrightarrow> Ai i \<in> sets (Mi j)"
      by(auto simp: assms)
    show "(\<Sum>i. \<Sum>j\<in>I. emeasure (Mi j) (Ai i)) = (\<Sum>i\<in>I. emeasure (Mi i) (\<Union> (range Ai)))"
      by(auto simp: suminf_sum intro!: Finite_Cartesian_Product.sum_cong_aux suminf_emeasure h)
  qed
qed(auto simp: positive_def sum_measure_def intro!: sets.sets_into_space)

lemma sum_measure_infinite: "infinite I \<Longrightarrow> sum_measure M I Mi = null_measure M"
  by(auto simp: sum_measure_def null_measure_def)

lemma nn_integral_sum_measure:
  assumes "f \<in> borel_measurable M" and [measurable_cong]: "\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets M"
  shows "(\<integral>\<^sup>+x. f x \<partial>sum_measure M I Mi) = (\<Sum>i\<in>I. (\<integral>\<^sup>+x. f x \<partial>(Mi i)))"
  using assms(1)
proof induction
  case h:(cong f g)
  then show ?case (is "?lhs = ?rhs")
    by(auto cong: nn_integral_cong[of "sum_measure M I Mi",simplified] intro!: Finite_Cartesian_Product.sum_cong_aux)
      (auto cong: nn_integral_cong simp: sets_eq_imp_space_eq[OF assms(2)[symmetric]])
next
  case (set A)
  then show ?case
    by(auto simp: emeasure_sum_measure assms)
next
  case (mult u c)
  then show ?case
    by(auto simp add: nn_integral_cmult sum_distrib_left intro!: Finite_Cartesian_Product.sum_cong_aux)
next
  case (add u v)
  then show ?case
    by(auto simp: nn_integral_add sum.distrib)
next
  case ih[measurable]:(seq U)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+ x. (\<Squnion>i. U i x) \<partial>sum_measure M I Mi)"
      by(auto intro!: nn_integral_cong) (use SUP_apply in auto)
    also have "... = (\<Squnion>i. (\<integral>\<^sup>+x. U i x \<partial>sum_measure M I Mi))"
      by(rule nn_integral_monotone_convergence_SUP) (use ih in auto)
    also have "... = (\<Squnion>i. \<Sum>j\<in>I. (\<integral>\<^sup>+x. U i x \<partial>(Mi j)))"
      by(simp add: ih)
    also have "... = (\<Sum>j\<in>I. \<Squnion>i. \<integral>\<^sup>+x. U i x \<partial>(Mi j))"
      by(auto intro!: incseq_nn_integral ih ennreal_SUP_sum)
    also have "... = (\<Sum>j\<in>I. \<integral>\<^sup>+x. (\<Squnion>i. U i x) \<partial>(Mi j))"
      by(auto intro!: Finite_Cartesian_Product.sum_cong_aux nn_integral_monotone_convergence_SUP[symmetric] ih)
    also have "... = ?rhs"
      by(auto intro!: Finite_Cartesian_Product.sum_cong_aux nn_integral_cong) (metis SUP_apply Sup_apply)
    finally show ?thesis .
  qed
qed

corollary integrable_sum_measure_iff_ne:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable_cong]: "\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets M" and "finite I" and "I \<noteq> {}"
  shows "integrable (sum_measure M I Mi) f \<longleftrightarrow> (\<forall>i\<in>I. integrable (Mi i) f)"
proof safe
  fix i
  assume [measurable]: "integrable (sum_measure M I Mi) f" and i:"i \<in> I"
  then have [measurable]:"\<And>i. i \<in> I \<Longrightarrow> f \<in> borel_measurable (Mi i)"
    "f \<in> borel_measurable M" "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>sum_measure M I Mi) < \<infinity>"
    by(auto simp: integrable_iff_bounded)
  hence "(\<Sum>i\<in>I. \<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>Mi i) < \<infinity>"
    by(simp add: nn_integral_sum_measure assms)
  thus "integrable (Mi i) f"
    by(auto simp: assms integrable_iff_bounded i)
next
  assume h:"\<forall>i\<in>I. integrable (Mi i) f"
  obtain i where i:"i \<in> I"
    using assms by auto
  have [measurable]: "f \<in> borel_measurable M"
    using h[rule_format,OF i] i by auto
  show "integrable (sum_measure M I Mi) f"
    using h by(auto simp: integrable_iff_bounded nn_integral_sum_measure assms)
qed

corollary integrable_sum_measure_iff:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable_cong]: "\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets M" and "finite I"
      and [measurable]: "f \<in> borel_measurable M"
    shows "integrable (sum_measure M I Mi) f \<longleftrightarrow> (\<forall>i\<in>I. integrable (Mi i) f)"
proof safe
  fix i
  assume "integrable (sum_measure M I Mi) f" "i \<in> I"
  thus "integrable (Mi i) f"
    using integrable_sum_measure_iff_ne[of I Mi,OF assms(1-2)] by auto
qed(auto simp: integrable_iff_bounded nn_integral_sum_measure assms)

lemma integral_sum_measure:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable_cong]:"\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets M" "\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) f"
  shows "(\<integral>x. f x \<partial>sum_measure M I Mi) = (\<Sum>i\<in>I. (\<integral>x. f x \<partial>(Mi i)))"
proof -
  consider "I = {}" | "finite I" "I \<noteq> {}" | "infinite I" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto simp: sum_measure_def integral_null_measure[simplified null_measure_def])
  next
    case 2
    have "integrable (sum_measure M I Mi) f"
      by(auto simp: assms(2)  integrable_sum_measure_iff_ne[of I Mi,OF assms(1) 2,simplified])
    thus ?thesis
    proof induction
      case h:(base A c)
      then have h':"\<And>i. i \<in> I \<Longrightarrow> emeasure (Mi i) A < \<top>"
        by(auto simp: emeasure_sum_measure assms 2)
      show ?case
        using h
        by(auto simp: measure_def h' emeasure_sum_measure assms enn2real_sum[of I "\<lambda>i. emeasure (Mi i) A",OF h'] scaleR_left.sum
              intro!: Finite_Cartesian_Product.sum_cong_aux)
    next
      case ih:(add f g)
      then have "\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) g" "\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) f"
        by(auto simp: integrable_sum_measure_iff_ne assms 2)
      with ih show ?case
        by(auto simp: sum.distrib)
    next
      case ih:(lim f s)
      then have [measurable]:"f \<in> borel_measurable M" "\<And>i. s i \<in> borel_measurable M"
        by auto
      have int[measurable]:"integrable (Mi i) f" "\<And>j. integrable (Mi i) (s j)" if "i \<in> I" for i
        using that ih 2 by(auto simp add: integrable_sum_measure_iff assms)
      show ?case
      proof(rule LIMSEQ_unique[where X="\<lambda>i. \<Sum>j\<in>I. \<integral>x. s i x \<partial>(Mi j)"])
        show "(\<lambda>i. \<Sum>j\<in>I. \<integral>x. s i x \<partial>(Mi j)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>sum_measure M I Mi)"
          using ih by(auto simp: ih(5)[symmetric] intro!: integral_dominated_convergence[where w="\<lambda>x. 2*norm (f x)"])
        show "(\<lambda>i. \<Sum>j\<in>I. \<integral>x. s i x \<partial>(Mi j)) \<longlonglongrightarrow> (\<Sum>j\<in>I. (\<integral>x. f x \<partial>(Mi j)))"
        proof(rule tendsto_sum)
          fix j
          assume j: "j \<in> I"
          show "(\<lambda>i. \<integral>x. s i x \<partial>(Mi j)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>(Mi j))"
            using integral_dominated_convergence[of f "Mi j" s "\<lambda>x. 2 * norm (f x)",OF _ _ _ AE_I2 AE_I2] ih int[OF j]
            by(auto simp: sets_eq_imp_space_eq[OF assms(1)[OF j]])
        qed
      qed
    qed
  next
    case 3
    then show ?thesis
      by(simp add: sum_measure_infinite)
  qed
qed

text \<open> Lemmas related to scale measure \<close>
lemma integrable_scale_measure:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable (scale_measure (ennreal r) M) f"
  using assms ennreal_less_top
  by(auto simp: integrable_iff_bounded nn_integral_scale_measure ennreal_mult_less_top)

lemma integral_scale_measure:
  assumes "r \<ge> 0" "integrable M f"
  shows "(\<integral>x. f x \<partial>scale_measure (ennreal r) M) = r * (\<integral>x. f x \<partial>M)"
  using assms(2)
proof induction
  case ih:(lim f s)
  show ?case
  proof(rule LIMSEQ_unique[where X="\<lambda>i. \<integral>x. s i x \<partial>scale_measure (ennreal r) M"])
    from ih(1-4) show "(\<lambda>i. \<integral>x. s i x \<partial>scale_measure (ennreal r) M) \<longlonglongrightarrow> (\<integral>x. f x \<partial>scale_measure (ennreal r) M)"
      by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"] integrable_scale_measure
          simp: space_scale_measure)
    show "(\<lambda>i. \<integral>x. s i x \<partial>scale_measure (ennreal r) M) \<longlonglongrightarrow>  r * (\<integral>x. f x \<partial>M)"
      unfolding ih(5) using ih(1-4) by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"] tendsto_mult_left)
  qed
qed(auto simp: measure_scale_measure[OF assms(1)] ring_class.ring_distribs(1) integrable_scale_measure)

lemma
  fixes c :: ereal
  assumes c: "c \<noteq> - \<infinity>" and a: "\<And>n. 0 \<le> a n"
  shows liminf_cadd: "liminf  (\<lambda>n. c + a n) = c + liminf a"
    and limsup_cadd: "limsup  (\<lambda>n. c + a n) = c + limsup a"
  by(auto simp add: liminf_SUP_INF limsup_INF_SUP INF_ereal_add_right[OF _ c a] SUP_ereal_add_right[OF _ c]
      intro!: INF_ereal_add_right c SUP_upper2 a)

lemma(in Metric_space) frontier_measure_zero_balls:
  assumes "sets N = sets (borel_of mtopology)" "finite_measure N" "M \<noteq> {}"
    and "e > 0" and "separable_space mtopology"
  obtains ai ri where
    "(\<Union>i::nat. mball (ai i) (ri i)) = M" "(\<Union>i::nat. mcball (ai i) (ri i)) = M"
    "\<And>i. ai i \<in> M" "\<And>i. ri i > 0" "\<And>i. ri i < e"
    "\<And>i. measure N (mtopology frontier_of (mball (ai i) (ri i))) = 0"
    "\<And>i. measure N (mtopology frontier_of (mcball (ai i) (ri i))) = 0"
proof -
  interpret N: finite_measure N by fact
  have [measurable]: "\<And>a r. mball a r \<in> sets N" "\<And>a r. mcball a r \<in> sets N"
    "\<And>a r. mtopology frontier_of (mball a r) \<in> sets N" "\<And>a r. mtopology frontier_of (mcball a r) \<in> sets N"
    by(auto simp: assms(1) borel_of_closed borel_of_open[OF openin_mball] closedin_frontier_of)
  have mono:"mtopology frontier_of (mball a r) \<subseteq> {y\<in>M. d a y = r}"
    "mtopology frontier_of (mcball a r) \<subseteq> {y\<in>M. d a y = r}" for a r
  proof -
    have "mtopology frontier_of (mball a r) \<subseteq> mcball a r - mball a r"
      using closure_of_mball by(auto simp: frontier_of_def interior_of_openin[OF openin_mball])
    also have "... \<subseteq> {y\<in>M. d a y = r}"
      by auto
    finally show "mtopology frontier_of (mball a r) \<subseteq> {y\<in>M. d a y = r}" .
    have "mtopology frontier_of (mcball a r) \<subseteq> mcball a r - mball a r"
      using interior_of_mcball by(auto simp: frontier_of_def closure_of_closedin[OF closedin_mcball])
    also have "... \<subseteq> {y\<in>M. d a y = r}"
      by(auto simp: mcball_def mball_def)
    finally show "mtopology frontier_of (mcball a r) \<subseteq> {y\<in>M. d a y = r}" .
  qed
  have sets[measurable]: "{y\<in>M. d a y = r} \<in> sets N" if "a \<in> M" for a r
  proof -
    have [simp]: "d a -` {r} \<inter> M = {y\<in>M. d a y = r}" by blast
    show ?thesis
      using measurable_sets[OF continuous_map_measurable[OF uniformly_continuous_imp_continuous_map[OF mdist_set_uniformly_continuous[of Self "{a}"]]],of "{r}"]
      by(simp add: borel_of_euclidean mtopology_of_def space_borel_of assms(1) mdist_set_Self)
        (metis (no_types, lifting) \<open>d a -` {r} \<inter> M = {y \<in> M. d a y = r}\<close> commute d_set_singleton that vimage_inter_cong)
  qed
  from assms(5) obtain U where U: "countable U" "mdense U" by(auto simp: separable_space_def2)
  with assms(3) have U_ne: "U \<noteq> {}"
    by(auto simp: mdense_empty_iff)
  { fix i :: nat
    have "countable {r \<in> {e/2<..<e}. measure N {y \<in> M. d (from_nat_into U i) y = r} \<noteq> 0}"
      by(rule N.countable_support_sets) (auto simp: disjoint_family_on_def)
    from real_interval_avoid_countable_set[of "e / 2" e,OF _ this] assms(4)
    have "\<exists>r. measure N {y\<in>M. d (from_nat_into U i) y = r} = 0 \<and> r > e / 2 \<and> r < e"
      by auto
  }
  then obtain ri where ri: "\<And>i. measure N {y\<in>M. d (from_nat_into U i) y = ri i} = 0"
    "\<And>i. ri i > e / 2" "\<And>i. ri i < e"
    by metis
  have 1: "(\<Union>i. mball (from_nat_into U i) (ri i)) = M" "(\<Union>i. mcball (from_nat_into U i) (ri i)) = M"
  proof -
    have "M = (\<Union>u\<in>U. mball u (e / 2))"
      by(rule mdense_balls_cover[OF U(2),symmetric]) (simp add: assms(4))
    also have "... = (\<Union>i. mball (from_nat_into U i) (e / 2))"
      by(rule UN_from_nat_into[OF U(1) U_ne])
    also have "... \<subseteq> (\<Union>i. mball (from_nat_into U i) (ri i))"
      using mball_subset_concentric[OF order.strict_implies_order[OF ri(2)]] by auto
    finally have 1:"M \<subseteq> (\<Union>i. mball (from_nat_into U i) (ri i))" .
    moreover have "M \<subseteq> (\<Union>i. mcball (from_nat_into U i) (ri i))"
      by(rule order.trans[OF 1]) fastforce
    ultimately show "(\<Union>i. mball (from_nat_into U i) (ri i)) = M" "(\<Union>i. mcball (from_nat_into U i) (ri i)) = M"
      by fastforce+
  qed
  have 2: "\<And>i. from_nat_into U i \<in> M" "\<And>i. ri i > 0" "\<And>i. ri i < e"
    using from_nat_into[OF U_ne] dense_in_subset[OF U(2)] ri(3) assms(4)
    by(auto intro!: order.strict_trans[OF _ ri(2),of 0])
  have 3: "measure N (mtopology frontier_of (mball (from_nat_into U i) (ri i))) = 0"
    "measure N (mtopology frontier_of (mcball (from_nat_into U i) (ri i))) = 0" for i
    using N.finite_measure_mono[OF mono(1) sets[of "from_nat_into U i" "ri i"]]
          N.finite_measure_mono[OF mono(2) sets[of "from_nat_into U i" "ri i"]]
    by (auto simp add: 2 measure_le_0_iff ri(1))
  show ?thesis
    using 1 2 3 that by blast
qed

lemma finite_measure_integral_eq_dense:
  assumes finite: "finite_measure N" "finite_measure M"
    and sets_N:"sets N = sets (borel_of X)" and sets_M: "sets M = sets (borel_of X)"
    and dense:"dense_in (mtopology_of (cfunspace X euclidean_metric)) F"
    and integ_eq:"\<And>f::_ \<Rightarrow> real. f \<in> F \<Longrightarrow> (\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
    and f:"continuous_map X euclideanreal f" "bounded (f ` topspace X)"
  shows "(\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
proof -
  interpret N: finite_measure N
    by fact
  interpret M: finite_measure M
    by fact
  have integ_N: "\<And>A. A \<in> sets N \<Longrightarrow> integrable N (indicat_real A)"
   and integ_M: "\<And>A. A \<in> sets M \<Longrightarrow> integrable M (indicat_real A)"
    by (auto simp add: N.emeasure_eq_measure M.emeasure_eq_measure)
  have space_N: "space N = topspace X" and space_M: "space M = topspace X"
    using sets_N sets_M sets_eq_imp_space_eq[of _ "borel_of X"]
    by(auto simp: space_borel_of)
  from f obtain B where B: "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>f x\<bar> \<le> B"
    by (meson bounded_real imageI)
  show  "(\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
  proof -
    have in_mspace_measurable: "g \<in> borel_measurable N" "g \<in> borel_measurable M"
      if g:"g \<in> mspace (cfunspace X (euclidean_metric :: real metric))" for g
      using continuous_map_measurable[of X euclidean,simplified borel_of_euclidean] g
      by(auto simp: sets_M cong: measurable_cong_sets sets_N)
    have f':"(\<lambda>x\<in>topspace X. f x) \<in> mspace (cfunspace X euclidean_metric)"
      using f(1) f(2) by simp
    with mdense_of_def3[THEN iffD1,OF assms(5)] obtain fn where fn:
      "range fn \<subseteq> F" "limitin (mtopology_of (cfunspace X euclidean_metric)) fn (\<lambda>x\<in>topspace X. f x) sequentially"
      by blast
    hence fn_space: "\<And>n. fn n \<in> mspace (cfunspace X euclidean_metric)"
      using dense_in_subset[OF assms(5)] by auto
    hence [measurable]: "(\<lambda>x\<in>topspace X. f x) \<in> borel_measurable N" "(\<lambda>x\<in>topspace X. f x) \<in> borel_measurable M"
      "\<And>n. fn n \<in> borel_measurable N" "\<And>n. fn n \<in> borel_measurable M"
      using f' by (auto simp del: mspace_cfunspace intro!: in_mspace_measurable)
    interpret d: Metric_space "mspace (cfunspace X euclidean_metric)" "mdist (cfunspace X (euclidean_metric :: real metric))"
      by blast
    from fn have "limitin d.mtopology fn (\<lambda>x\<in>topspace X. f x) sequentially"
      by (simp add: mtopology_of_def)
    hence limit:"\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. fn n \<in> mspace (cfunspace X euclidean_metric) \<and>
                      mdist (cfunspace X euclidean_metric) (fn n) (restrict f (topspace X)) < \<epsilon>"
      unfolding d.limit_metric_sequentially by blast
    from this[of 1] obtain N0 where N0:
      "\<And>n. n \<ge> N0 \<Longrightarrow> mdist (cfunspace X euclidean_metric) (fn n) (\<lambda>x\<in>topspace X. f x) < 1"
      by auto
    have 1: "(\<lambda>i. fn (i + N0) x) \<longlonglongrightarrow> (\<lambda>x\<in>topspace X. f x) x" if x:"x \<in> topspace X" for x
    proof(rule LIMSEQ_I)
      fix r :: real
      assume r:"0 < r"
      from limit[OF half_gt_zero[OF r]] obtain N where N:
        "\<And>n. n \<ge> N \<Longrightarrow> mdist (cfunspace X euclidean_metric) (fn n) (restrict f (topspace X)) < r / 2"
        by blast
      show "\<exists>no. \<forall>n\<ge>no.  norm (fn (n + N0) x - restrict f (topspace X) x) < r"
      proof(safe intro!: exI[where x=N])
        fix n
        assume n:"N \<le> n"
        with N[OF trans_le_add1[OF this,of N0]]
        have "mdist (cfunspace X euclidean_metric) (fn (n + N0)) (restrict f (topspace X)) \<le> r / 2"
          by auto
        from order.strict_trans1[OF mdist_cfunspace_imp_mdist_le[OF fn_space f' this x],of r] x r
        show "norm (fn (n + N0) x - restrict f (topspace X) x) < r"
          by (auto simp: dist_real_def)
      qed
    qed
    have 2: "norm (fn (i + N0) x) \<le> 2 * B + 1" if x:"x \<in> topspace X" for i x
    proof-
      from N0[of "i + N0"]
      have "mdist (cfunspace X euclidean_metric) (fn (i + N0)) (restrict f (topspace X)) \<le> 1"
        by linarith
      from mdist_cfunspace_imp_mdist_le[OF fn_space f' this x]
      have "norm (fn (i + N0) x - f x) \<le> 1"
        using x by (auto simp: dist_real_def)
      thus ?thesis
        using B[OF x] by auto
    qed
    from 1 2 have "(\<lambda>i. integral\<^sup>L N (fn (i + N0))) \<longlonglongrightarrow> integral\<^sup>L N (restrict f (topspace X))"
      by(auto intro!: integral_dominated_convergence[where s="\<lambda>i. fn (i + N0)" and w="\<lambda>x. 2 * B + 1"]
                simp: space_N)
    moreover have "(\<lambda>i. integral\<^sup>L N (fn (i + N0))) \<longlonglongrightarrow> integral\<^sup>L M (restrict f (topspace X))"
    proof -
      have [simp]:"integral\<^sup>L N (fn (i + N0)) = integral\<^sup>L M (fn (i + N0))" for i
        using fn(1) by(auto intro!: assms(6))
      from 1 2 show ?thesis
        by(auto intro!: integral_dominated_convergence[where s="\<lambda>i. fn (i + N0)" and w="\<lambda>x. 2 * B + 1"]
                  simp: space_M)
    qed
    ultimately have "integral\<^sup>L N (restrict f (topspace X)) = integral\<^sup>L M (restrict f (topspace X))"
      by(rule tendsto_unique[OF sequentially_bot])
    moreover have "integral\<^sup>L N (restrict f (topspace X)) = integral\<^sup>L N f"
      by(auto cong: Bochner_Integration.integral_cong[OF refl] simp: space_N[symmetric])
    moreover have "integral\<^sup>L M (restrict f (topspace X)) = integral\<^sup>L M f"
      by(auto cong: Bochner_Integration.integral_cong[OF refl] simp: space_M[symmetric])
    ultimately show ?thesis
      by simp
  qed
qed

subsection \<open> Sequentially Continuous Maps\<close>
definition seq_continuous_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"seq_continuous_map X Y f \<equiv> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> limitin Y (\<lambda>n. f (xn n)) (f x) sequentially)"

lemma seq_continuous_map:
  "seq_continuous_map X Y f \<longleftrightarrow> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> limitin Y (\<lambda>n. f (xn n)) (f x) sequentially)"
  by(auto simp: seq_continuous_map_def)

lemma seq_continuous_map_funspace:
  assumes "seq_continuous_map X Y f"
  shows "f \<in> topspace X \<rightarrow> topspace Y"
proof
  fix x
  assume "x \<in> topspace X"
  then have "limitin X (\<lambda>n. x) x sequentially"
    by auto
  hence "limitin Y (\<lambda>n. f x) (f x) sequentially"
    using assms
    by (meson limitin_sequentially seq_continuous_map)
  thus "f x \<in> topspace Y"
    by auto
qed

lemma seq_continuous_iff_continuous_first_countable:
  assumes "first_countable X"
  shows "seq_continuous_map X Y = continuous_map X Y"
  by standard (simp add: continuous_map_iff_limit_seq assms seq_continuous_map_def)

subsection \<open> Sequential Compactness \<close>
definition seq_compactin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where
"seq_compactin X S
\<longleftrightarrow> S \<subseteq> topspace X \<and> (\<forall>xn. (\<forall>n::nat. xn n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>a::nat \<Rightarrow> nat. strict_mono a \<and> limitin X (xn \<circ> a) l sequentially))"

definition "seq_compact_space X \<equiv> seq_compactin X (topspace X)"

lemma seq_compactin_subset_topspace: "seq_compactin X S \<Longrightarrow> S \<subseteq> topspace X"
  by(auto simp: seq_compactin_def)

lemma seq_compactin_empty[simp]: "seq_compactin X {}"
  by(auto simp: seq_compactin_def)

lemma seq_compactin_seq_compact[simp]: "seq_compactin euclidean S \<longleftrightarrow> seq_compact S"
  by(auto simp: seq_compactin_def seq_compact_def)

lemma image_seq_compactin:
  assumes "seq_compactin X S" "seq_continuous_map X Y f" 
  shows "seq_compactin Y (f ` S)"
  unfolding seq_compactin_def
proof safe
  fix yn
  assume "\<forall>n::nat. yn n \<in> f ` S"
  then have "\<forall>n. \<exists>x\<in>S. yn n = f x"
    by blast
  then obtain xn where xn: "\<And>n::nat. xn n \<in> S" "\<And>n. yn n = f (xn n)"
    by metis
  then obtain lx a where la: "lx \<in> S" "strict_mono a" "limitin X (xn \<circ> a) lx sequentially"
    by (meson assms(1) seq_compactin_def)
  show "\<exists>l\<in>f ` S. \<exists>a. strict_mono a \<and> limitin Y (yn \<circ> a) l sequentially"
  proof(safe intro!: bexI[where x="f lx"] exI[where x=a])
    have [simp]:"yn \<circ> a = (\<lambda>n. f ((xn \<circ> a) n))"
      by(auto simp: xn(2) comp_def)
    show "limitin Y (yn \<circ> a) (f lx) sequentially"
      using la(3) assms(2) xn(1,2) by(fastforce simp: seq_continuous_map)
  qed(use la in auto)
qed(use seq_compactin_subset_topspace[OF assms(1)] seq_continuous_map_funspace[OF assms(2)] in auto)

lemma closed_seq_compactin:
  assumes "seq_compactin X K" "C \<subseteq> K" "closedin X C"
  shows "seq_compactin X C"
  unfolding seq_compactin_def
proof safe
  fix xn
  assume xn: "\<forall>n::nat. xn n \<in> C"
  then have "\<forall>n. xn n \<in> K"
    using assms(2) by blast
  with assms(1) obtain l a where l: "l \<in> K" "strict_mono a" "limitin X (xn \<circ> a) l sequentially"
    by (meson seq_compactin_def)
  have "l \<in> C"
    using xn by(auto intro!: limitin_closedin[OF l(3) assms(3)])
  with l(2,3) show "\<exists>l\<in>C. \<exists>a. strict_mono a \<and> limitin X (xn \<circ> a) l sequentially"
    by blast
qed(use closedin_subset[OF assms(3)] in auto)

corollary closedin_seq_compact_space:
 "seq_compact_space X \<Longrightarrow> closedin X C \<Longrightarrow> seq_compactin X C"
  by(auto intro!: closed_seq_compactin[where K="topspace X" and C=C] closedin_subset simp: seq_compact_space_def)

lemma seq_compactin_subtopology: "seq_compactin (subtopology X S) T \<longleftrightarrow> seq_compactin X T \<and> T \<subseteq> S"
  by(fastforce simp: seq_compactin_def limitin_subtopology subsetD)

corollary seq_compact_space_subtopology: "seq_compactin X S \<Longrightarrow> seq_compact_space (subtopology X S)"
  by(auto simp: seq_compact_space_def seq_compactin_subtopology inf_absorb2 seq_compactin_subset_topspace)

lemma seq_compactin_PiED:
  assumes "seq_compactin (product_topology X I) (Pi\<^sub>E I S)"
  shows "(Pi\<^sub>E I S = {} \<or> (\<forall>i\<in>I. seq_compactin (X i) (S i)))"
proof -
  consider "Pi\<^sub>E I S = {}" | "Pi\<^sub>E I S \<noteq> {}"
    by blast
  then show "(Pi\<^sub>E I S = {} \<or> (\<forall>i\<in>I. seq_compactin (X i) (S i)))"
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then have Si_ne:"\<And>i. i \<in> I \<Longrightarrow> S i \<noteq> {}"
      by blast
    then obtain ci where ci: "\<And>i. i \<in> I \<Longrightarrow> ci i \<in> S i"
      by (meson PiE_E ex_in_conv)      
    show ?thesis
    proof(safe intro!: disjI2)
      fix i
      assume i: "i \<in> I"
      show "seq_compactin (X i) (S i)"
        unfolding seq_compactin_def
      proof safe
        fix xn
        assume xn:"\<forall>n::nat. xn n \<in> S i"
        define Xn where "Xn \<equiv> (\<lambda>n. \<lambda>j\<in>I. if j = i then xn n else ci j)"
        have "\<And>n. Xn n \<in> Pi\<^sub>E I S"
          using i xn ci by(auto simp: Xn_def)
        then obtain L a where L: "L \<in> Pi\<^sub>E I S" "strict_mono a"
          "limitin (product_topology X I) (Xn \<circ> a) L sequentially"
          by (meson assms seq_compactin_def)
        thus "\<exists>l\<in>S i. \<exists>a. strict_mono a \<and> limitin (X i) (xn \<circ> a) l sequentially"
          using i by(auto simp: limitin_componentwise Xn_def comp_def intro!: bexI[where x="L i"] exI[where x=a])
      next
        show "\<And>x. x \<in> S i \<Longrightarrow> x \<in> topspace (X i)"
          using i  subset_PiE[THEN iffD1,OF seq_compactin_subset_topspace[OF assms,simplified]] 2 by auto
      qed
    qed
  qed
qed

lemma metrizable_seq_compactin_iff_compactin:
  assumes "metrizable_space X"
  shows "seq_compactin X S \<longleftrightarrow> compactin X S"
proof -
  obtain d where d: "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis Metric_space.topspace_mtopology assms metrizable_space_def)
  interpret Metric_space "topspace X" d
    by fact
  have "seq_compactin X S \<longleftrightarrow> seq_compactin mtopology S"
    by(simp add: d)
  also have "... \<longleftrightarrow> compactin mtopology S"
    by(fastforce simp: compactin_sequentially seq_compactin_def)
  also have "... \<longleftrightarrow> compactin X S"
    by(simp add: d)
  finally show ?thesis .
qed

corollary metrizable_seq_compact_space_iff_compact_space:
  shows "metrizable_space X \<Longrightarrow> seq_compact_space X \<longleftrightarrow> compact_space X"
  unfolding seq_compact_space_def compact_space_def by(rule metrizable_seq_compactin_iff_compactin)

subsection \<open> Lemmas for Limsup and Liminf\<close>
lemma real_less_add_ex_less_pair:
  fixes x w v :: real
  assumes "x < w + v"
  shows "\<exists>y z. x = y + z \<and> y < w \<and> z < v"
  apply(rule exI[where x="w - (w + v - x) / 2"])
  apply(rule exI[where x="v - (w + v - x) / 2"])
  using assms by auto

lemma ereal_less_add_ex_less_pair:
  fixes x w v :: ereal
  assumes "- \<infinity> < w" "- \<infinity> < v" "x < w + v"
  shows "\<exists>y z. x = y + z \<and> y < w \<and> z < v"
proof -
  consider "x = - \<infinity>" | "- \<infinity> < x" "x < \<infinity>" "w = \<infinity>" "v = \<infinity>"
    | "- \<infinity> < x" "x < \<infinity>" "w < \<infinity>" "v = \<infinity>" | "- \<infinity> < x" "x < \<infinity>" "v < \<infinity>" "w = \<infinity>"
    | "- \<infinity> < x" "x < \<infinity>" "w < \<infinity>" "v < \<infinity>"
    using assms(3) less_ereal.simps(2) by blast
  then show ?thesis
  proof cases
    assume "x = - \<infinity>"
    then show ?thesis
      using assms by(auto intro!: exI[where x="- \<infinity>"])
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "w = \<infinity>" "v = \<infinity>"
    show ?thesis
      apply(rule exI[where x=0])
      apply(rule exI[where x=x])
      using h assms by simp
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "w < \<infinity>" "v = \<infinity>"
    then obtain x' w' where eq: "w = ereal w'" "x = ereal x'"
      using assms by (metis less_irrefl sgn_ereal.cases)
    show ?thesis
      apply(rule exI[where x="w - 1"])
      apply(rule exI[where x="x - (w - 1)"])
      using h assms by(auto simp: eq one_ereal_def)
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "v < \<infinity>" "w = \<infinity>"
    then obtain x' v' where eq: "v = ereal v'" "x = ereal x'"
      using assms by (metis less_irrefl sgn_ereal.cases)
    show ?thesis
      apply(rule exI[where x="x - (v - 1)"])
      apply(rule exI[where x="v - 1"])
      using h assms by(auto simp: eq one_ereal_def)
  next
    assume  "- \<infinity> < x" "x < \<infinity>" "w < \<infinity>" "v < \<infinity>"
    then obtain x' v' w' where eq: "x = ereal x'" "w = ereal w'" "v = ereal v'"
      using assms by (metis less_irrefl sgn_ereal.cases)
    have "\<exists>y' z'. x' = y' + z' \<and> y' < w' \<and> z' < v'"
      using real_less_add_ex_less_pair assms by(simp add: eq)
    then obtain y' z' where yz':"x' = y' + z' \<and> y' < w' \<and> z' < v'"
      by blast
    show ?thesis
      apply(rule exI[where x="ereal y'"])
      apply(rule exI[where x="ereal z'"])
      using yz' by(simp add: eq)
  qed
qed

lemma real_add_less:
  fixes x w v :: real
  assumes "w + v < x"
  shows "\<exists>y z. x = y + z \<and> w < y \<and> v < z"
  apply(rule exI[where x="w + (x - (w + v)) / 2"])
  apply(rule exI[where x="v + (x - (w + v)) / 2"])
  using assms by auto

lemma ereal_add_less:
  fixes x w v :: ereal
  assumes "w + v < x"
  shows "\<exists>y z. x = y + z \<and> w < y \<and> v < z"
proof -
  have "- \<infinity> < x" "v < \<infinity>" "w < \<infinity>"
    using assms less_ereal.simps(2,3) by auto
  then consider "x = \<infinity>" "w < \<infinity>" "v < \<infinity>" | "- \<infinity> < x" "x < \<infinity>" "w = - \<infinity>" "v = - \<infinity>"
    | "- \<infinity> < x" "x < \<infinity>" "w = - \<infinity>" "v < \<infinity>" "- \<infinity> < v"
    | "- \<infinity> < x" "x < \<infinity>" "v = - \<infinity>" "w < \<infinity>" "- \<infinity> < w"
    | "- \<infinity> < x" "x < \<infinity>" "- \<infinity> < w" "w < \<infinity>" "v < \<infinity>" "- \<infinity> < v"
    by blast
  thus ?thesis
  proof cases
    assume "x = \<infinity>" "w < \<infinity>" "v < \<infinity>"
    then show ?thesis
      by(auto intro!: exI[where x=\<infinity>])
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "w = - \<infinity>" "v = - \<infinity>"
    show ?thesis
      apply(rule exI[where x=0])
      apply(rule exI[where x=x])
      using h assms by simp
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "w = - \<infinity>" "v < \<infinity>" "- \<infinity> < v"
    then obtain x' v' where xv': "x = ereal x'" "v = ereal v'"
      by (metis less_irrefl sgn_ereal.cases)
    show ?thesis
      apply(rule exI[where x="x - (v + 1)"])
      apply(rule exI[where x="v + 1"])
      using h by(auto simp: xv')
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "v = - \<infinity>" "w < \<infinity>" "- \<infinity> < w"
    then obtain x' w' where xw': "x = ereal x'" "w = ereal w'"
      by (metis less_irrefl sgn_ereal.cases)
    show ?thesis
      apply(rule exI[where x="w + 1"])
      apply(rule exI[where x="x - (w + 1)"])
      using h by(auto simp: xw')
  next
    assume h:"- \<infinity> < x" "x < \<infinity>" "- \<infinity> < w" "w < \<infinity>" "v < \<infinity>" "- \<infinity> < v"
    then obtain x' v' w' where eq: "x = ereal x'" "w = ereal w'" "v = ereal v'"
      using assms by (metis less_irrefl sgn_ereal.cases)
    have "\<exists>y' z'. x' = y' + z' \<and> y' > w' \<and> z' > v'"
      using assms real_add_less by(auto simp: eq)
    then obtain y' z' where yz':"x' = y' + z' \<and> y' > w' \<and> z' > v'"
      by blast
    show ?thesis
      apply(rule exI[where x="ereal y'"])
      apply(rule exI[where x="ereal z'"])
      using yz' by(simp add: eq)
  qed
qed

text \<open> A generalized version of @{thm ereal_liminf_add_mono}.\<close>
lemma ereal_Liminf_add_mono:
  fixes u v::"'a \<Rightarrow> ereal"
  assumes "\<not>((Liminf F u = \<infinity> \<and> Liminf F v = -\<infinity>) \<or> (Liminf F u = -\<infinity> \<and> Liminf F v = \<infinity>))"
  shows "Liminf F (\<lambda>n. u n + v n) \<ge> Liminf F u + Liminf F v"
proof (cases)
  assume "(Liminf F u = -\<infinity>) \<or> (Liminf F v = -\<infinity>)"
  then have *: "Liminf F u + Liminf F v = -\<infinity>" using assms by auto
  show ?thesis by (simp add: *)
next
  assume "\<not>((Liminf F u = -\<infinity>) \<or> (Liminf F v = -\<infinity>))"
  then have h:"Liminf F u > -\<infinity>" "Liminf F v > -\<infinity>" by auto
  show ?thesis
    unfolding le_Liminf_iff
  proof safe
    fix y
    assume y: "y < Liminf F u + Liminf F v"
    then obtain x z where xz: "y = x + z" "x < Liminf F u" " z < Liminf F v"
      using ereal_less_add_ex_less_pair h by blast
    show "\<forall>\<^sub>F x in F. y < u x + v x"
      by(rule eventually_mp[OF _ eventually_conj[OF less_LiminfD[OF xz(2)] less_LiminfD[OF xz(3)]]])
        (auto simp: xz intro!: eventuallyI ereal_add_strict_mono2)
  qed
qed

text \<open> A generalized version of @{thm ereal_limsup_add_mono}.\<close>
lemma ereal_Limsup_add_mono:
  fixes u v::"'a \<Rightarrow> ereal"
  shows "Limsup F (\<lambda>n. u n + v n) \<le> Limsup F u + Limsup F v"
  unfolding Limsup_le_iff
proof safe
  fix y
  assume "Limsup F u + Limsup F v < y"
  then obtain x z where xz: "y = x + z" "Limsup F u < x" "Limsup F v < z"
    using ereal_add_less by blast
  show "\<forall>\<^sub>F x in F. u x + v x < y"
    by(rule eventually_mp[OF _ eventually_conj[OF Limsup_lessD[OF xz(2)] Limsup_lessD[OF xz(3)]]])
      (auto simp: xz intro!: eventuallyI ereal_add_strict_mono2)
qed

subsection \<open> A Characterization of Closed Sets by Limit \<close>
text \<open> There is a net which charactrize closed sets in terms of convergence.
       Since Isabelle/HOL's convergent is defined through filters, we transform the net to
       a filter. We refer to the lecture notes by Shi~\cite{nets} for the conversion.\<close>

definition derived_filter :: "['i set, 'i \<Rightarrow> 'i \<Rightarrow> bool] \<Rightarrow> 'i filter" where
"derived_filter I op \<equiv> (\<Sqinter>i\<in>I. principal {j\<in>I. op i j})"

lemma eventually_derived_filter:
  assumes "A \<noteq> {}"
    and refl:"\<And>a. a \<in> A \<Longrightarrow> rel a a"
    and trans:"\<And>a b c. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> c \<in> A \<Longrightarrow> rel a b \<Longrightarrow> rel b c \<Longrightarrow> rel a c"
    and pair_bounded:"\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> \<exists>c\<in>A. rel a c \<and> rel b c"
  shows "eventually P (derived_filter A rel) \<longleftrightarrow> (\<exists>i\<in>A. \<forall>n\<in>A. rel i n \<longrightarrow> P n)"
proof -
  show ?thesis
    unfolding derived_filter_def
  proof(subst eventually_INF_base)
    fix a b
    assume h:"a \<in> A" "b \<in> A"
    then obtain z where "z \<in> A" "rel a z" "rel b z"
      using pair_bounded by metis
    thus "\<exists>x\<in>A. principal {j \<in> A. rel x j} \<le> principal {j \<in> A. rel a j} \<sqinter> principal {j \<in> A. rel b j}"
      using h by(auto intro!: bexI[where x=z] dest: trans)
  next
    show "(\<exists>b\<in>A. eventually P (principal {j \<in> A. rel b j})) \<longleftrightarrow> (\<exists>i\<in>A. \<forall>n\<in>A. rel i n \<longrightarrow> P n)"
      unfolding eventually_principal by blast
  qed fact
qed

definition nhdsin_sets :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a set filter" where
"nhdsin_sets X x \<equiv> derived_filter {U. openin X U \<and> x \<in> U} (\<supseteq>)"

lemma eventually_nhdsin_sets:
  assumes "x \<in> topspace X"
  shows "eventually P (nhdsin_sets X x) \<longleftrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>V. openin X V \<longrightarrow> x \<in> V \<longrightarrow> V \<subseteq> U \<longrightarrow> P V))"
proof -
  have h:"{U. openin X U \<and> x \<in> U} \<noteq> {}"
         "\<And>a. a \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> (\<supseteq>) a a"
         "\<And>a b c. a \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> b \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> c \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> (\<supseteq>) a b \<Longrightarrow> (\<supseteq>) b c \<Longrightarrow> (\<supseteq>) a c"
         "\<And>a b. a \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> b \<in> {U. openin X U \<and> x \<in> U} \<Longrightarrow> \<exists>c\<in>{U. openin X U \<and> x \<in> U}. (\<supseteq>) a c \<and> (\<supseteq>) b c"
  proof safe
    fix U V
    assume "x \<in> U" "x \<in> V" "openin X U" "openin X V"
    then show "\<exists>W\<in>{U. openin X U \<and> x \<in> U}. W \<subseteq> U \<and> W \<subseteq> V"
      using openin_Int[of X U V] by auto
  qed(use assms in fastforce)+
  show ?thesis
    unfolding nhdsin_sets_def
    apply(subst eventually_derived_filter[of "{U. openin X U \<and> x \<in> U}" "(\<supseteq>)"])
    using h apply blast
       apply simp
    using h
      apply blast
    using h
     apply blast
    apply fastforce
    done
qed

lemma eventually_nhdsin_setsI:
  assumes "x \<in> topspace X" "\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> P U"
  shows "eventually P (nhdsin_sets X x)"
  using assms by(auto simp: eventually_nhdsin_sets)

lemma nhdsin_sets_bot[simp, intro]:
  assumes "x \<in> topspace X"
  shows "nhdsin_sets X x \<noteq> \<bottom>"
  by(auto simp: trivial_limit_def eventually_nhdsin_sets[OF assms])

corollary limitin_nhdsin_sets: "limitin X xn x (nhdsin_sets X x) \<longleftrightarrow> x \<in> topspace X \<and> (\<forall>U. openin X U \<longrightarrow> x \<in> U \<longrightarrow> (\<exists>V. openin X V \<and> x \<in> V \<and> (\<forall>W. openin X W \<longrightarrow> x \<in> W \<longrightarrow> W \<subseteq> V \<longrightarrow> xn W \<in> U)))"
  using eventually_nhdsin_sets by(fastforce dest: limitin_topspace simp: limitin_def)

lemma closedin_limitin:
  assumes "T \<subseteq> topspace X" "\<And>xn x. x \<in> topspace X \<Longrightarrow> (\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> xn U \<noteq> x) \<Longrightarrow> (\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> xn U \<in> T) \<Longrightarrow> (\<And>U. xn U \<in> topspace X) \<Longrightarrow>  limitin X xn x (nhdsin_sets X x) \<Longrightarrow> x \<in> T"
  shows "closedin X T"
proof -
  have 1: "X derived_set_of T \<subseteq> T"
  proof
    fix x
    assume x:"x \<in> X derived_set_of T"
    hence x':"x \<in> topspace X"
      by (simp add: in_derived_set_of)
    define xn where "xn \<equiv> (\<lambda>U. if x \<in> U \<and> openin X U then (SOME y. y \<noteq> x \<and> y \<in> T \<and> y \<in> U) else x)"
    have xn: "xn U \<noteq> x" "xn U \<in> T" "xn U \<in> U" if U: "openin X U" "x \<in> U" for U
    proof -
      have "(SOME y. y \<noteq> x \<and> y \<in> T \<and> y \<in> U) \<noteq> x \<and> (SOME y. y \<noteq> x \<and> y \<in> T \<and> y \<in> U) \<in> T \<and> (SOME y. y \<noteq> x \<and> y \<in> T \<and> y \<in> U) \<in> U"
        by(rule someI_ex,insert x U) (auto simp: derived_set_of_def)
      thus "xn U \<noteq> x" "xn U \<in> T" "xn U \<in> U"
        by(auto simp: xn_def U)
    qed
    hence 1:"\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> xn U \<noteq> x" "\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> xn U \<in> T"
      by simp_all
    moreover have "xn U \<in> topspace X" for U
    proof(cases "x \<in> U \<and> openin X U")
      case True
      with assms 1 show ?thesis
        by fast
    next
      case False
      with x 1 derived_set_of_subset_topspace[of X T] show ?thesis
        by(auto simp: xn_def)
    qed
    moreover have "limitin X xn x (nhdsin_sets X x)"
      unfolding limitin_nhdsin_sets
    proof safe
      fix U
      assume U: "openin X U" "x \<in> U"
      then show "\<exists>V. openin X V \<and> x \<in> V \<and> (\<forall>W. openin X W \<longrightarrow> x \<in> W \<longrightarrow> W \<subseteq> V \<longrightarrow> xn W \<in> U)"
        using xn by(fastforce intro!: exI[where x=U])
    qed(use x derived_set_of_subset_topspace in fastforce)
    ultimately show "x \<in> T"
      by(rule assms(2)[OF x'])
  qed
  thus ?thesis
    using assms(1) by(auto intro!: closure_of_eq[THEN iffD1] simp: closure_of)
qed

corollary closedin_iff_limitin_eq:
  fixes X :: "'a topology"
  shows "closedin X C
    \<longleftrightarrow> C \<subseteq> topspace X \<and>
        (\<forall>xi x (F :: 'a set filter). (\<forall>i. xi i \<in> topspace X) \<longrightarrow> x \<in> topspace X
              \<longrightarrow> (\<forall>\<^sub>F i in F. xi i \<in> C) \<longrightarrow> F \<noteq> \<bottom> \<longrightarrow> limitin X xi x F \<longrightarrow> x \<in> C)"
proof
  assume "C \<subseteq> topspace X \<and>
          (\<forall>xi x (F ::  'a set filter). (\<forall>i. xi i \<in> topspace X) \<longrightarrow> x \<in> topspace X
                 \<longrightarrow> (\<forall>\<^sub>F i in F. xi i \<in> C)  \<longrightarrow> F \<noteq> \<bottom> \<longrightarrow> limitin X xi x F \<longrightarrow> x \<in> C)"
  then show "closedin X C"
  apply(intro closedin_limitin)
    apply blast
    by (metis (mono_tags, lifting) nhdsin_sets_bot eventually_nhdsin_setsI)
qed(auto dest: limitin_closedin closedin_subset)

lemma closedin_iff_limitin_sequentially:
  assumes "first_countable X"
  shows "closedin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> (\<forall>\<sigma> l. range \<sigma> \<subseteq> S \<and> limitin X \<sigma> l sequentially \<longrightarrow> l \<in> S)" (is "?lhs=?rhs")
proof safe
  assume h:"S \<subseteq> topspace X" "\<forall>\<sigma> l. range \<sigma> \<subseteq> S \<and> limitin X \<sigma> l sequentially \<longrightarrow> l \<in> S"
  show "closedin X S"
  proof(rule closedin_limitin)
    fix xu x
    assume xu: "\<And>U. x \<in> U \<Longrightarrow> openin X U \<Longrightarrow> xu U \<in> S" "\<And>U. xu U \<in> topspace X" "limitin X xu x (nhdsin_sets X x)"
    then have x:"x \<in> topspace X"
      by(auto simp: limitin_topspace)
    then obtain B where B: "countable B" "\<And>V. V \<in> B \<Longrightarrow> openin X V"
      "\<And>U. openin X U \<Longrightarrow> x \<in> U \<Longrightarrow> (\<exists>V\<in>B. x \<in> V \<and> V \<subseteq> U)"
      using assms first_countable_def by metis
    define B' where "B' \<equiv> B \<inter> {U. x \<in> U}"
    have B'_ne:"B' \<noteq> {}"
      using B'_def B(3) x by fastforce
    have cB':"countable B'"
      using B by(simp add: B'_def)
    have B': "\<And>V. V \<in> B' \<Longrightarrow> openin X V" "\<And>U. openin X U \<Longrightarrow> x \<in> U \<Longrightarrow> (\<exists>V\<in>B'. x \<in> V \<and> V \<subseteq> U)"
      using B B'_def by fastforce+
    define xn where "xn \<equiv> (\<lambda>n. xu (\<Inter>i\<le>n. (from_nat_into B' i)))"
    have xn_in_S: "range xn \<subseteq> S" and limitin_xn: "limitin X xn x sequentially"
    proof -
      have 1:"\<And>n. openin X (\<Inter>i\<le>n. (from_nat_into B' i))"
        by (auto simp: B'(1) B'_ne from_nat_into)
      have 2: "\<And>n. x \<in> (\<Inter>i\<le>n. (from_nat_into B' i))"
        by (metis B'_def B'_ne INT_I Int_iff from_nat_into mem_Collect_eq)
      thus "range xn \<subseteq> S"
        using 1 by(auto simp: xn_def intro!: xu)
      show "limitin X xn x sequentially"
        unfolding limitin_sequentially
      proof safe
        fix U
        assume U: "openin X U" "x \<in> U"
        then obtain V where V: "x \<in> V" "openin X V" "\<And>W. openin X W \<Longrightarrow> x \<in> W \<Longrightarrow> W \<subseteq> V \<Longrightarrow> xu W \<in> U"
          by (metis limitin_nhdsin_sets xu(3))
        then obtain V' where V': "V' \<in> B'" "x \<in> V'" "V' \<subseteq> V"
          using B' by meson
        then obtain N where N: "(\<Inter>i\<le>N. (from_nat_into B' i)) \<subseteq> V'"
          by (metis Inf_lower atMost_iff cB' from_nat_into_surj image_iff order.refl)
        show "\<exists>N. \<forall>n\<ge>N. xn n \<in> U"
        proof(safe intro!: exI[where x=N])
          fix n
          assume [arith]:"n \<ge> N"
          show "xn n \<in> U"
            unfolding xn_def
          proof(rule V(3))
            have "(\<Inter>i\<le>n. (from_nat_into B' i)) \<subseteq> (\<Inter>i\<le>N. (from_nat_into B' i))"
              by force
            also have "... \<subseteq> V"
              using N V' by simp
            finally show "\<Inter> (from_nat_into B' ` {..n}) \<subseteq> V" .
          qed(use 1 2 in auto)
        qed
      qed fact
    qed
    thus "x \<in> S"
      using h(2) by blast
  qed fact
qed(auto simp: limitin_closedin range_subsetD dest: closedin_subset)

subsection \<open> A Characterization of Topology by Limit \<close>
lemma topology_eq_filter:
  fixes X :: "'a topology"
  assumes "topspace X = topspace Y"
    and "\<And>(F :: 'a set filter) xi x. (\<And>i. xi i \<in> topspace X) \<Longrightarrow> x \<in> topspace X \<Longrightarrow> limitin X xi x F \<longleftrightarrow> limitin Y xi x F"
  shows "X = Y"
  unfolding topology_eq_closedin closedin_iff_limitin_eq using assms by simp

lemma topology_eq_limit_sequentially:
  assumes "topspace X = topspace Y"
    and "first_countable X" "first_countable Y"
    and "\<And>xn x. (\<And>n. xn i \<in> topspace X) \<Longrightarrow> x \<in> topspace X \<Longrightarrow> limitin X xn x sequentially \<longleftrightarrow> limitin Y xn x sequentially"
  shows "X = Y"
  unfolding topology_eq_closedin closedin_iff_limitin_sequentially[OF assms(2)] closedin_iff_limitin_sequentially[OF assms(3)]
  by (metis dual_order.trans limitin_topspace range_subsetD assms(1,4))

subsection \<open> A Characterization of Open Sets by Limit \<close>
corollary openin_limitin:
  assumes "U \<subseteq> topspace X" "\<And>xi x. x \<in> topspace X \<Longrightarrow> (\<And>i. xi i \<in> topspace X) \<Longrightarrow> limitin X xi x (nhdsin_sets X x) \<Longrightarrow> x \<in> U \<Longrightarrow> \<forall>\<^sub>F i in (nhdsin_sets X x). xi i \<in> U"
  shows "openin X U"
  unfolding openin_closedin_eq
proof(safe intro!: assms(1) closedin_limitin)
  fix xi x
  assume h:"x \<in> topspace X" "\<forall>V. x \<in> V \<longrightarrow> openin X V \<longrightarrow> xi V \<in> topspace X - U"
    "\<forall>V. xi V \<in> topspace X" "limitin X xi x (nhdsin_sets X x)" "x \<in> U"
  show False
    using assms(2)[OF h(1,3,4,5)[rule_format]] h(2)
    by(auto simp: eventually_nhdsin_sets[OF h(1)])
qed

corollary openin_iff_limitin_eq:
  fixes X :: "'a topology"
  shows "openin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> (\<forall>xi x (F :: 'a set filter). (\<forall>i. xi i \<in> topspace X) \<longrightarrow> x \<in> U \<longrightarrow> limitin X xi x F \<longrightarrow> (\<forall>\<^sub>F i in F. xi i \<in> U))"
    by(auto intro!: openin_limitin openin_subset simp: limitin_def)

corollary limitin_openin_sequentially:
  assumes "first_countable X"
  shows "openin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> (\<forall>xn x. x \<in> U \<longrightarrow> limitin X xn x sequentially \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. xn n \<in> U))"
  unfolding openin_closedin_eq closedin_iff_limitin_sequentially[OF assms] 
  apply safe
    apply (simp add: assms closedin_iff_limitin_sequentially limitin_sequentially openin_closedin)
   apply (simp add: limitin_sequentially)
  apply blast
  done

lemma upper_semicontinuous_map_limsup_iff:
  fixes f :: "'a \<Rightarrow> ('b :: {complete_linorder,linorder_topology})"
  assumes "first_countable X"
  shows "upper_semicontinuous_map X f \<longleftrightarrow> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> limsup (\<lambda>n. f (xn n)) \<le> f x)"
  unfolding upper_semicontinuous_map_def
proof safe
  fix xn x
  assume h:"\<forall>a. openin X {x \<in> topspace X. f x < a}" "limitin X xn x sequentially"
  show "limsup (\<lambda>n. f (xn n)) \<le> f x"
    unfolding Limsup_le_iff eventually_sequentially
  proof safe
    fix y
    assume y:"f x < y"
    show "\<exists>N. \<forall>n\<ge>N. f (xn n) < y"
    proof(rule ccontr)
      assume "\<nexists>N. \<forall>n\<ge>N. f (xn n) < y"
      then have hc:"\<And>N. \<exists>n\<ge>N. f (xn n) \<ge> y"
        using linorder_not_less by blast
      define a :: "nat \<Rightarrow> nat" where "a \<equiv> rec_nat (SOME n. f (xn n) \<ge> y) (\<lambda>n an. SOME m. m > an \<and> f (xn m) \<ge> y)"
      have "strict_mono a"
      proof(rule strict_monoI_Suc)
        fix n
        have [simp]:"a (Suc n) = (SOME m. m > a n \<and> f (xn m) \<ge> y)"
          by(auto simp: a_def)
        show "a n < a (Suc n)"
          by simp (metis (mono_tags, lifting) Suc_le_lessD hc someI)
      qed
      have *:"f (xn (a n)) \<ge> y" for n
      proof(cases n)
        case 0
        then show ?thesis
          using hc[of 0] by(auto simp: a_def intro!: someI_ex)
      next
        case (Suc n')
        then show ?thesis
          by(simp add: a_def) (metis (mono_tags, lifting) Suc_le_lessD hc someI_ex)
      qed
      have "\<exists>N. \<forall>n\<ge>N. (xn \<circ> a) n \<in> {x \<in> topspace X. f x < y}"
        using limitin_subsequence[OF \<open>strict_mono a\<close> h(2)] h(1)[rule_format,of y] y
        by(fastforce simp: limitin_sequentially)
      with * show False
        using leD by auto
    qed
  qed
next
  fix a
  assume h:" \<forall>xn x. limitin X xn x sequentially \<longrightarrow> limsup (\<lambda>n. f (xn n)) \<le> f x"
  show "openin X {x \<in> topspace X. f x < a}"
    unfolding limitin_openin_sequentially[OF assms]
  proof safe
    fix x xn
    assume h':"limitin X xn x sequentially" "x \<in> topspace X" "f x < a"
    with h have "limsup (\<lambda>n. f (xn n)) \<le> f x"
      by auto
    with h'(3) obtain N where N:"\<And>n. n\<ge>N \<Longrightarrow> f (xn n) < a"
      by(auto simp: Limsup_le_iff eventually_sequentially)
    obtain N' where N': "\<And>n. n\<ge>N' \<Longrightarrow> xn n \<in> topspace X"
      by (meson h'(1) limitin_sequentially openin_topspace)
    thus "\<exists>N. \<forall>n\<ge>N. xn n \<in> {x \<in> topspace X. f x < a}"
      using h'(3) N by(auto  intro!: exI[where x="max N N'"])
  qed
qed

subsection \<open> Lemmas for Upper/Lower-Semi Continuous Maps \<close>
(* TODO: Move *)
lemma upper_semicontinuous_map_limsup_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "first_countable X"
  shows "upper_semicontinuous_map X f \<longleftrightarrow> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> limsup (\<lambda>n. f (xn n)) \<le> f x)"
  unfolding upper_semicontinuous_map_real_iff upper_semicontinuous_map_limsup_iff[OF assms] by simp

lemma lower_semicontinuous_map_liminf_iff:
  fixes f :: "'a \<Rightarrow> ('b :: {complete_linorder,linorder_topology})"
  assumes "first_countable X"
  shows "lower_semicontinuous_map X f \<longleftrightarrow> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> f x \<le> liminf (\<lambda>n. f (xn n)))"
  unfolding lower_semicontinuous_map_def
proof safe
  fix xn x
  assume h:"\<forall>a. openin X {x \<in> topspace X. a < f x}" "limitin X xn x sequentially"
  show "f x \<le> liminf (\<lambda>n. f (xn n))"
    unfolding le_Liminf_iff eventually_sequentially
  proof safe
    fix y
    assume y:"y < f x"
    show "\<exists>N. \<forall>n\<ge>N. y < f (xn n)"
    proof(rule ccontr)
      assume "\<nexists>N. \<forall>n\<ge>N. y < f (xn n)"
      then have hc:"\<And>N. \<exists>n\<ge>N. y \<ge> f (xn n)"
        by (meson verit_comp_simplify1(3))
      define a :: "nat \<Rightarrow> nat" where "a \<equiv> rec_nat (SOME n. f (xn n) \<le> y) (\<lambda>n an. SOME m. m > an \<and> f (xn m) \<le> y)"
      have "strict_mono a"
      proof(rule strict_monoI_Suc)
        fix n
        have [simp]:"a (Suc n) = (SOME m. m > a n \<and> f (xn m) \<le> y)"
          by(auto simp: a_def)
        show "a n < a (Suc n)"
          by simp (metis (no_types, lifting) Suc_le_lessD \<open>\<nexists>N. \<forall>n\<ge>N. y < f (xn n)\<close> not_le someI_ex)
      qed
      have *:"f (xn (a n)) \<le> y" for n
      proof(cases n)
        case 0
        then show ?thesis
          using hc[of 0] by(auto simp: a_def intro!: someI_ex)
      next
        case (Suc n')
        then show ?thesis
          by(simp add: a_def) (metis (mono_tags, lifting) Suc_le_lessD hc someI_ex)
      qed
      have "\<exists>N. \<forall>n\<ge>N. (xn \<circ> a) n \<in> {x \<in> topspace X. f x > y}"
        using limitin_subsequence[OF \<open>strict_mono a\<close> h(2)] h(1)[rule_format,of y] y
        by(fastforce simp: limitin_sequentially)
      with * show False
        using leD by auto
    qed
  qed
next
  fix a
  assume h:" \<forall>xn x. limitin X xn x sequentially \<longrightarrow> f x \<le> liminf (\<lambda>n. f (xn n))"
  show "openin X {x \<in> topspace X. a < f x}"
    unfolding limitin_openin_sequentially[OF assms]
  proof safe
    fix x xn
    assume h':"limitin X xn x sequentially" "x \<in> topspace X" "f x > a"
    with h have "f x \<le> liminf (\<lambda>n. f (xn n))"
      by auto
    with h'(3) obtain N where N:"\<And>n. n\<ge>N \<Longrightarrow> f (xn n) > a"
      by(auto simp: le_Liminf_iff eventually_sequentially)
    obtain N' where N': "\<And>n. n\<ge>N' \<Longrightarrow> xn n \<in> topspace X"
      by (meson h'(1) limitin_sequentially openin_topspace)
    thus "\<exists>N. \<forall>n\<ge>N. xn n \<in> {x \<in> topspace X. f x > a}"
      using h'(3) N by(auto  intro!: exI[where x="max N N'"])
  qed
qed

lemma lower_semicontinuous_map_liminf_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "first_countable X"
  shows "lower_semicontinuous_map X f \<longleftrightarrow> (\<forall>xn x. limitin X xn x sequentially \<longrightarrow> f x \<le> liminf (\<lambda>n. f (xn n)))"
  unfolding lower_semicontinuous_map_real_iff lower_semicontinuous_map_liminf_iff[OF assms] by simp

end