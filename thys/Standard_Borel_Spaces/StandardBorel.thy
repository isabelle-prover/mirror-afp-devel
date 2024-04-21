(*  Title:   StandardBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open>Standard Borel Spaces\<close>
subsection  \<open>Standard Borel Spaces\<close>
theory StandardBorel
  imports Abstract_Metrizable_Topology
begin

locale standard_borel =
  fixes M :: "'a measure"
  assumes Polish_space: "\<exists>S. Polish_space S \<and> sets M = sets (borel_of S)"
begin

lemma singleton_sets:
  assumes "x \<in> space M"
  shows "{x} \<in> sets M"
proof -
  obtain S where s:"Polish_space S" "sets M = sets (borel_of S)"
    using Polish_space by blast
  have "closedin S {x}"
    using assms by(simp add: sets_eq_imp_space_eq[OF s(2)] closedin_Hausdorff_sing_eq[OF metrizable_imp_Hausdorff_space[OF Polish_space_imp_metrizable_space[OF s(1)]]] space_borel_of)
  thus ?thesis
    using borel_of_closed s by simp
qed

corollary countable_sets:
  assumes "A \<subseteq> space M" "countable A"
  shows "A \<in> sets M"
  using sets.countable[OF singleton_sets assms(2)] assms(1)
  by auto

lemma standard_borel_restrict_space:
  assumes "A \<in> sets M"
  shows "standard_borel (restrict_space M A)"
proof -
  obtain S where s:"Polish_space S" "sets M = sets (borel_of S)"
    using Polish_space by blast
  obtain S' where S':"Polish_space S'" "sets M = sets (borel_of S')" "openin S' A"
    using sets_clopen_topology[OF s(1),simplified s(2)[symmetric],OF assms] by auto
  show ?thesis
    using Polish_space_openin[OF S'(1,3)] S'(2)
    by(auto simp: standard_borel_def borel_of_subtopology sets_restrict_space intro!: exI[where x="subtopology S' A"] )
qed

end

locale standard_borel_ne = standard_borel +
  assumes space_ne: "space M \<noteq> {}"
begin

lemma standard_borel_ne_restrict_space:
  assumes "A \<in> sets M" "A \<noteq> {}"
  shows "standard_borel_ne (restrict_space M A)"
  using assms by(auto simp: standard_borel_ne_def standard_borel_ne_axioms_def standard_borel_restrict_space)

lemma standard_borel: "standard_borel M"
  by(rule standard_borel_axioms)

end

lemma standard_borel_sets:
  assumes "standard_borel M" and "sets M = sets N"
  shows "standard_borel N"
  using assms by(simp add: standard_borel_def)

lemma standard_borel_ne_sets:
  assumes "standard_borel_ne M" and "sets M = sets N"
  shows "standard_borel_ne N"
  using assms by(simp add: standard_borel_def standard_borel_ne_def sets_eq_imp_space_eq[OF assms(2)] standard_borel_ne_axioms_def)

lemma pair_standard_borel:
  assumes "standard_borel M" "standard_borel N"
  shows "standard_borel (M \<Otimes>\<^sub>M N)"
proof -
  obtain S S' where hs:
   "Polish_space S" "sets M = sets (borel_of S)" "Polish_space S'" "sets N = sets (borel_of S')"
    using assms by(auto simp: standard_borel_def)
  have "sets (M \<Otimes>\<^sub>M N) = sets (borel_of (prod_topology S S'))"
    unfolding borel_of_prod[OF Polish_space_imp_second_countable[OF hs(1)] Polish_space_imp_second_countable[OF hs(3)],symmetric]
    using sets_pair_measure_cong[OF hs(2,4)] .
  thus ?thesis
    unfolding standard_borel_def by(auto intro!: exI[where x="prod_topology S S'"] simp: Polish_space_prod[OF hs(1,3)])
qed

lemma pair_standard_borel_ne:
  assumes "standard_borel_ne M" "standard_borel_ne N"
  shows "standard_borel_ne (M \<Otimes>\<^sub>M N)"
  using assms by(auto simp: pair_standard_borel standard_borel_ne_def standard_borel_ne_axioms_def space_pair_measure)

lemma product_standard_borel:
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> standard_borel (M i)"
    shows "standard_borel (\<Pi>\<^sub>M i\<in>I. M i)"
proof -
  obtain S where hs:
   "\<And>i. i \<in> I \<Longrightarrow> Polish_space (S i)" "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (borel_of (S i))"
    using assms(2) by(auto simp: standard_borel_def) metis
  have "sets (\<Pi>\<^sub>M i\<in>I. M i) = sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))"
    using hs(2) by(auto intro!: sets_PiM_cong)
  also have "... = sets (borel_of (product_topology S I))"
    using assms(1) Polish_space_imp_second_countable[OF hs(1)] by(auto intro!: sets_PiM_equal_borel_of)
  finally have 1:"sets (\<Pi>\<^sub>M i\<in>I. M i) = sets (borel_of (product_topology S I))".
  show ?thesis
    unfolding standard_borel_def
    using assms(1) hs(1) by(auto intro!: exI[where x="product_topology S I"] Polish_space_product simp: 1)
qed

lemma product_standard_borel_ne:
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> standard_borel_ne (M i)"
    shows "standard_borel_ne (\<Pi>\<^sub>M i\<in>I. M i)"
  using assms by(auto simp: standard_borel_ne_def standard_borel_ne_axioms_def product_standard_borel)

lemma closed_set_standard_borel[simp]:
  fixes U :: "'a :: topological_space set"
  assumes "Polish_space (euclidean :: 'a topology)" "closed U"
  shows "standard_borel (restrict_space borel U)"
  by(auto simp: standard_borel_def borel_of_euclidean borel_of_subtopology assms intro!: exI[where x="subtopology euclidean U"] Polish_space_closedin)

lemma closed_set_standard_borel_ne[simp]:
  fixes U :: "'a :: topological_space set"
  assumes "Polish_space (euclidean :: 'a topology)" "closed U" "U \<noteq> {}"
  shows "standard_borel_ne (restrict_space borel U)"
  using assms by(simp add: standard_borel_ne_def standard_borel_ne_axioms_def)

lemma open_set_standard_borel[simp]:
  fixes U :: "'a :: topological_space set"
  assumes "Polish_space (euclidean :: 'a topology)" "open U"
  shows "standard_borel (restrict_space borel U)"
  by(auto simp: standard_borel_def borel_of_euclidean borel_of_subtopology assms intro!: exI[where x="subtopology euclidean U"] Polish_space_openin)

lemma open_set_standard_borel_ne[simp]:
  fixes U :: "'a :: topological_space set"
  assumes "Polish_space (euclidean :: 'a topology)" "open U" "U \<noteq> {}"
  shows "standard_borel_ne (restrict_space borel U)"
  using assms by(simp add: standard_borel_ne_def standard_borel_ne_axioms_def)

lemma standard_borel_ne_borel[simp]: "standard_borel_ne (borel :: ('a :: polish_space) measure)"
  and standard_borel_ne_lborel[simp]: "standard_borel_ne lborel"
  unfolding standard_borel_def standard_borel_ne_def standard_borel_ne_axioms_def
  by(auto intro!: exI[where x=euclidean] simp: borel_of_euclidean)

lemma count_space_standard'[simp]:
  assumes "countable I"
  shows "standard_borel (count_space I)"
  by(rule standard_borel_sets[OF _ sets_borel_of_discrete_topology]) (auto simp add: assms Polish_space_discrete_topology standard_borel_def intro!: exI[where x="discrete_topology I"])

lemma count_space_standard_ne[simp]: "standard_borel_ne (count_space (UNIV :: (_ :: countable) set))"
  by (simp add: standard_borel_ne_def standard_borel_ne_axioms_def)

corollary measure_pmf_standard_borel_ne[simp]: "standard_borel_ne (measure_pmf (p :: (_ :: countable) pmf))"
  using count_space_standard_ne sets_measure_pmf_count_space standard_borel_ne_sets by blast

corollary measure_spmf_standard_borel_ne[simp]: "standard_borel_ne (measure_spmf (p :: (_ :: countable) spmf))"
  using count_space_standard_ne sets_measure_spmf standard_borel_ne_sets by blast

corollary countable_standard_ne[simp]:
 "standard_borel_ne (borel :: 'a :: {countable,t2_space} measure)"
  by(simp add: standard_borel_sets[OF _ sets_borel_eq_count_space[symmetric]] standard_borel_ne_def standard_borel_ne_axioms_def)

lemma(in standard_borel) countable_discrete_space:
  assumes "countable (space M)"
  shows "sets M = Pow (space M)"
proof safe
  fix A
  assume "A \<subseteq> space M"
  with assms have "countable A"
    by(simp add: countable_subset)
  thus "A \<in> sets M"
    using \<open>A \<subseteq> space M\<close> singleton_sets
    by(auto intro!: sets.countable[of A])
qed(use sets.sets_into_space in auto)

lemma(in standard_borel) measurable_isomorphic_standard:
  assumes "M measurable_isomorphic N"
  shows "standard_borel N"
proof -
  obtain S where S:"Polish_space S" "sets M = sets (borel_of S)"
    using Polish_space by auto
  from measurable_isomorphic_borels[OF S(2) assms]
  obtain S' where S': "S homeomorphic_space S' \<and> sets N = sets (borel_of S')"
    by auto
  thus ?thesis
    by(auto simp: standard_borel_def homeomorphic_Polish_space_aux[OF S(1)] intro!:exI[where x=S'])
qed

lemma(in standard_borel_ne) measurable_isomorphic_standard_ne:
  assumes "M measurable_isomorphic N"
  shows "standard_borel_ne N"
  using measurable_ismorphic_empty2[OF _ assms] by(auto simp: measurable_isomorphic_standard[OF assms] standard_borel_ne_def standard_borel_ne_axioms_def space_ne)

lemma(in standard_borel) standard_borel_embed_measure:
  assumes"inj_on f (space M)"
  shows "standard_borel (embed_measure M f)"
  using measurable_embed_measure2'[OF assms]
  by(auto intro!: measurable_isomorphic_standard exI[where x=f] simp: measurable_isomorphic_def measurable_isomorphic_map_def assms in_sets_embed_measure measurable_def sets.sets_into_space space_embed_measure the_inv_into_into the_inv_into_vimage bij_betw_def)

corollary(in standard_borel_ne) standard_borel_ne_embed_measure:
  assumes"inj_on f (space M)"
  shows "standard_borel_ne (embed_measure M f)"
  by (simp add: assms space_embed_measure space_ne standard_borel_embed_measure standard_borel_ne_axioms_def standard_borel_ne_def)

lemma
  shows standard_ne_ereal: "standard_borel_ne (borel :: ereal measure)"
    and standard_ne_ennreal: "standard_borel_ne (borel :: ennreal measure)"
  using Polish_space_ereal Polish_space_ennreal by(auto simp: standard_borel_ne_def standard_borel_ne_axioms_def standard_borel_def borel_of_euclidean)

text \<open> Cantor space $\mathscr{C}$ \<close>
definition Cantor_space :: "(nat \<Rightarrow> real) measure" where
"Cantor_space \<equiv> (\<Pi>\<^sub>M i\<in> UNIV. restrict_space borel {0,1})"

lemma Cantor_space_standard_ne: "standard_borel_ne Cantor_space"
  by(auto simp: Cantor_space_def intro!: product_standard_borel_ne)

lemma Cantor_space_borel:
 "sets (borel_of Cantor_space_topology) = sets Cantor_space"
  (is "?lhs = _")
proof -
  have "?lhs = sets (\<Pi>\<^sub>M i\<in> UNIV. borel_of (top_of_set {0,1}))"
    by(auto intro!: sets_PiM_equal_borel_of[symmetric] second_countable_subtopology)
  thus ?thesis
    by(simp add: borel_of_subtopology Cantor_space_def borel_of_euclidean)
qed

text \<open> Hilbert cube $\mathscr{H}$ \<close>
definition Hilbert_cube :: "(nat \<Rightarrow> real) measure" where
"Hilbert_cube \<equiv> (\<Pi>\<^sub>M i\<in> UNIV. restrict_space borel {0..1})"

lemma Hilbert_cube_standard_ne: "standard_borel_ne Hilbert_cube"
  by(auto simp: Hilbert_cube_def intro!: product_standard_borel_ne)

lemma Hilbert_cube_borel:
 "sets (borel_of Hilbert_cube_topology) = sets Hilbert_cube" (is "?lhs = _")
proof -
  have "?lhs = sets (\<Pi>\<^sub>M i\<in> UNIV. borel_of (top_of_set {0..1}))"
    by(auto intro!: sets_PiM_equal_borel_of[symmetric] second_countable_subtopology)
  thus ?thesis
    by(simp add: borel_of_subtopology Hilbert_cube_def borel_of_euclidean)
qed

subsection \<open> Isomorphism between $\mathscr{C}$ and $\mathscr{H}$\<close>
lemma Cantor_space_isomorphic_to_Hilbert_cube:
 "Cantor_space measurable_isomorphic Hilbert_cube"
proof -
  text \<open> Isomorphism between $\mathscr{C}$ and $[0,1]$\<close>

  have Cantor_space_isomorphic_to_01closed: "Cantor_space measurable_isomorphic (restrict_space borel {0..1::real})"
  proof -
    have space_Cantor_space: "space Cantor_space = (\<Pi>\<^sub>E i\<in> UNIV. {0,1})"
      by(simp add: Cantor_space_def space_PiM)
    have space_Cantor_space_01[simp]: "0 \<le> x n" "x n \<le> 1" "x n \<in> {0,1}" if "x \<in> space Cantor_space" for x n
      using PiE_mem[OF that[simplified space_Cantor_space],of n]
      by auto
    have Cantor_minus_abs_cantor: "(\<lambda>n. \<bar>x n - y n\<bar>) \<in> space Cantor_space" if assms:"x \<in> space Cantor_space" "y \<in> space Cantor_space" for x y
      unfolding space_Cantor_space
    proof safe
      fix n
      assume "\<bar>x n - y n\<bar> \<noteq> 0"
      then consider "x n = 0 \<and> y n = 1" | "x n = 1 \<and> y n = 0"
        using space_Cantor_space_01[OF assms(1),of n] space_Cantor_space_01[OF assms(2),of n]
        by auto
      thus "\<bar>x n - y n\<bar> = 1"
        by cases auto
    qed simp

    define Cantor_to_01 :: "(nat \<Rightarrow> real) \<Rightarrow> real" where
      "Cantor_to_01 \<equiv> (\<lambda>x. (\<Sum>n. (1/3)^(Suc n)* x n))"
    text \<open> @{term Cantor_to_01} is a measurable injective embedding.\<close>
    have Cantor_to_01_summable'[simp]: "summable (\<lambda>n. (1/3)^(Suc n)* x n)" if "x \<in> space Cantor_space" for x
    proof(rule summable_comparison_test'[where g="\<lambda>n. (1/3)^ n" and N=0])
      show "norm ((1 / 3) ^ Suc n * x n) \<le> (1 / 3) ^ n" for n
        using space_Cantor_space_01[OF that,of n] by auto
    qed simp

    have Cantor_to_01_summable[simp]: "\<And>x. x \<in> space Cantor_space \<Longrightarrow> summable (\<lambda>n. (1/3)^ n* x n)"
      using Cantor_to_01_summable' by simp

    have Cantor_to_01_subst_summable[simp]: "summable (\<lambda>n. (1/3)^ n* (x n - y n))" if assms:"x \<in> space Cantor_space" "y \<in> space Cantor_space" for x y
    proof(rule summable_comparison_test'[where g="\<lambda>n. (1/3)^ n" and N=0])
      show " norm ((1 / 3) ^ n * (x n - y n)) \<le> (1 / 3) ^ n" for n
        using space_Cantor_space_01[OF Cantor_minus_abs_cantor[OF assms],of n]
        by(auto simp: idom_abs_sgn_class.abs_mult)
    qed simp

    have Cantor_to_01_image: "Cantor_to_01 \<in> space Cantor_space \<rightarrow> {0..1}"
    proof
      fix x
      assume h:"x \<in> space Cantor_space"
      have "Cantor_to_01 x \<le> (\<Sum>n. (1/3)^(Suc n))"
        unfolding Cantor_to_01_def
        by(rule suminf_le) (use h Cantor_to_01_summable[OF h] in auto)
      also have "... = (\<Sum>n. (1 / 3) ^ n) - (1::real)"
        using suminf_minus_initial_segment[OF complete_algebra_summable_geometric[of "1/3::real"],of 1]
        by auto
      finally have "Cantor_to_01 x \<le> 1"
        by(simp add: suminf_geometric[of "1/3"])
      moreover have "0 \<le> Cantor_to_01 x"
        unfolding Cantor_to_01_def
        by(rule suminf_nonneg) (use Cantor_to_01_summable[OF h] h in auto)
      ultimately show "Cantor_to_01 x \<in> {0..1}"
        by simp
    qed
    have Cantor_to_01_measurable: "Cantor_to_01 \<in> Cantor_space \<rightarrow>\<^sub>M restrict_space borel {0..1}"
    proof(rule measurable_restrict_space2)
      show "Cantor_to_01 \<in> borel_measurable Cantor_space"
        unfolding Cantor_to_01_def
      proof(rule borel_measurable_suminf)
        fix n
        have "(\<lambda>x. x n) \<in> Cantor_space \<rightarrow>\<^sub>M restrict_space borel {0, 1}"
          by(simp add: Cantor_space_def)
        hence "(\<lambda>x. x n) \<in> borel_measurable Cantor_space"
          by(simp add: measurable_restrict_space2_iff)
        thus "(\<lambda>x. (1 / 3) ^ Suc n * x n) \<in> borel_measurable Cantor_space"
          by simp
      qed
    qed(rule Cantor_to_01_image)

    have Cantor_to_01_inj: "inj_on Cantor_to_01 (space Cantor_space)"
      and Cantor_to_01_preserves_sets: "A \<in> sets Cantor_space \<Longrightarrow> Cantor_to_01 ` A \<in> sets (restrict_space borel {0..1})" for A
    proof -
      have sets_Cantor: "sets Cantor_space = sets (borel_of (product_topology (\<lambda>_. subtopology euclidean {0,1}) UNIV))"
        (is "?lhs = _")
      proof -
        have "?lhs =  sets (\<Pi>\<^sub>M i\<in> UNIV. borel_of (subtopology euclidean {0,1}))"
          by (simp add: Cantor_space_def borel_of_euclidean borel_of_subtopology)
        thus ?thesis
          by(auto intro!: sets_PiM_equal_borel_of second_countable_subtopology Polish_space_imp_second_countable[of "euclideanreal"])
      qed
      have s:"space Cantor_space = topspace (product_topology (\<lambda>_. subtopology euclidean {0,1}) UNIV)"
        by(simp add: space_Cantor_space)

      let ?d = "\<lambda>x y::real. if (x = 0 \<or> x = 1) \<and> (y = 0 \<or> y = 1) then dist x y else 0"
      interpret d01: Metric_space "{0,1::real}" ?d
        by(auto simp: Metric_space_def)
      have d01: "d01.mtopology = top_of_set {0,1}" d01.mcomplete
      proof -
        interpret Metric_space "{0,1}" dist
          by (simp add: Met_TC.subspace)
        have "d01.mtopology = mtopology"
          by(auto intro!: Metric_space_eq_mtopology simp: Metric_space_def metric_space_class.dist_commute)
        also have "... = top_of_set {0,1}"
          by(auto intro!: Submetric.mtopology_submetric[of UNIV dist "{0,1::real}",simplified] simp: Submetric_def Metric_space_def Submetric_axioms_def dist_real_def)
        finally show "d01.mtopology = top_of_set {0,1}" .
        show d01.mcomplete
          using Metric_space_eq_mcomplete[OF d01.Metric_space_axioms,of dist] d01.compact_space_eq_Bolzano_Weierstrass d01.compact_space_imp_mcomplete finite.emptyI finite_subset by blast
      qed
      interpret pd: Product_metric "1/3" UNIV id id "\<lambda>_. {0,1::real}" "\<lambda>_. ?d" 1
        by(auto intro!: product_metric_natI d01.Metric_space_axioms)
      have mpd_top: "pd.Product_metric.mtopology = Cantor_space_topology"
        by(auto simp: pd.Product_metric_mtopology_eq[symmetric] d01 intro!: product_topology_cong)
      have pd_mcomplete: pd.Product_metric.mcomplete
        by(auto intro!: pd.mcomplete_Mi_mcomplete_M d01)
      interpret m01: Submetric UNIV dist "{0..1::real}"
        by(simp add: Submetric_def Submetric_axioms_def Met_TC.Metric_space_axioms)
      have "restrict_space borel {0..1} = borel_of m01.sub.mtopology"
        by (simp add: borel_of_euclidean borel_of_subtopology m01.mtopology_submetric)
      have pd_def: "pd.product_dist x y = (\<Sum>n. (1/3)^n * \<bar>x n - y n\<bar>)" if "x \<in> space Cantor_space" "y \<in> space Cantor_space" for x y
        using space_Cantor_space_01[OF that(1)] space_Cantor_space_01[OF that(2)] that by(auto simp: product_dist_def dist_real_def)
      have 1: "\<bar>Cantor_to_01 x - Cantor_to_01 y\<bar> \<le> pd.product_dist x y" (is "?lhs \<le> ?rhs") if "x \<in> space Cantor_space" "y \<in> space Cantor_space" for x y
      proof -
        have "?lhs = \<bar>(\<Sum>n. (1/3)^(Suc n)* x n - (1/3)^(Suc n)* y n)\<bar>"
          using that by(simp add: suminf_diff Cantor_to_01_def)
        also have "... = \<bar>\<Sum>n. (1/3)^(Suc n) * (x n - y n) \<bar>"
          by (simp add: right_diff_distrib)
        also have "... \<le> (\<Sum>n. \<bar>(1/3)^(Suc n) * (x n - y n)\<bar>)"
        proof(rule summable_rabs)
          have "(\<lambda>n. \<bar>(1 / 3) ^ Suc n * (x n - y n)\<bar>) = (\<lambda>n. (1 / 3) ^ Suc n * \<bar>(x n - y n)\<bar>)"
            by (simp add: abs_mult_pos mult.commute)
          moreover have "summable ..."
            using Cantor_minus_abs_cantor[OF that] by simp
          ultimately show "summable (\<lambda>n. \<bar>(1 / 3) ^ Suc n * (x n - y n)\<bar>)" by simp
        qed
        also have "... = (\<Sum>n. (1/3)^(Suc n) * \<bar>x n - y n\<bar>)"
          by (simp add: abs_mult_pos mult.commute)
        also have "... \<le> pd.product_dist x y"
          unfolding pd_def[OF that]
          by(rule suminf_le) (use Cantor_minus_abs_cantor[OF that] in auto)
        finally show ?thesis .
      qed

      have 2:"\<bar>Cantor_to_01 x - Cantor_to_01 y\<bar> \<ge>  1 / 9 * pd.product_dist x y" (is "?lhs \<le> ?rhs") if "x \<in> space Cantor_space" "y \<in> space Cantor_space" for x y
      proof(cases "x = y")
        case True
        then show ?thesis
          using pd.Product_metric.zero[of x y] that by(simp add: space_Cantor_space)
      next
        case False
        then obtain n' where "x n' \<noteq> y n'" by auto
        define n where "n \<equiv> Min {n. n \<le> n' \<and> x n \<noteq> y n}"
        have "n \<le> n'"
          using \<open>x n' \<noteq> y n'\<close> n_def by fastforce
        have "x n \<noteq> y n"
          using \<open>x n' \<noteq> y n'\<close> linorder_class.Min_in[of "{n. n \<le> n' \<and> x n \<noteq> y n}"]
          by(auto simp: n_def)
        have "\<forall>i<n. x i = y i"
        proof safe
          fix i
          assume "i < n"
          show "x i = y i"
          proof(rule ccontr)
            assume "x i \<noteq> y i"
            then have "i \<in> {n. n \<le> n' \<and> x n \<noteq> y n}"
              using \<open>n \<le> n'\<close> \<open>i < n\<close> by auto
            thus False
              using \<open>i < n\<close> linorder_class.Min_gr_iff[of "{n. n \<le> n' \<and> x n \<noteq> y n}" i] \<open>x n' \<noteq> y n'\<close>
              by(auto simp: n_def)
          qed
        qed
        have u1: "(1/3) ^ (Suc n) * (1/2) \<le> \<bar>Cantor_to_01 x - Cantor_to_01 y\<bar>"
        proof -
          have "(1/3) ^ (Suc n) * (1/2) \<le> \<bar>(\<Sum>m. (1/3)^(Suc (m + Suc n)) * (x (m + Suc n) - y (m + Suc n))) + (1 / 3) ^ Suc n * (x n - y n)\<bar>"
          proof -
            have "(1 / 3) ^ Suc n - (1/3)^(n + 2) * 3/2 \<le> (1 / 3) ^ Suc n -  \<bar>(\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n)))\<bar>"
            proof -
              have "\<bar>(\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n)))\<bar> \<le> (1/3)^(n + 2) * 3/2"
                (is "?lhs \<le> _")
              proof -
                have "?lhs \<le> (\<Sum>m. \<bar>(1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n))\<bar>)"
                  apply(rule summable_rabs,rule summable_ignore_initial_segment[of _ "Suc n"])
                  using Cantor_minus_abs_cantor[OF that(2,1)] by(simp add: abs_mult)
                also have "... = (\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * \<bar>y (m + Suc n) - x (m + Suc n)\<bar>)"
                  by(simp add: abs_mult)
                also have "... \<le> (\<Sum>m. (1 / 3) ^ Suc (m + Suc n))"
                  apply(rule suminf_le)
                  using space_Cantor_space_01[OF Cantor_minus_abs_cantor[OF that(2,1)]]
                    apply simp
                   apply(rule summable_ignore_initial_segment[of _ "Suc n"])
                  using Cantor_minus_abs_cantor[OF that(2,1)] by auto
                also have "... = (\<Sum>m. (1 / 3) ^ (m + Suc (Suc n)) * 1)" by simp
                also have "... = (1/3)^(n + 2) * 3/(2::real)"
                  by(simp only: pd.nsum_of_rK[of "Suc (Suc n)"],simp)
                finally show ?thesis .
              qed
              thus ?thesis by simp
            qed
            also have "... = \<bar>(1 / 3) ^ Suc n * (x n - y n)\<bar> - \<bar>\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n))\<bar>"
              using \<open>x n \<noteq> y n\<close> space_Cantor_space_01[OF Cantor_minus_abs_cantor[OF that],of n] by(simp add: abs_mult)
            also have "... \<le> \<bar>(1 / 3) ^ Suc n * (x n - y n) - (\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n)))\<bar>"
              by simp
            also have "... = \<bar>(1 / 3) ^ Suc n * (x n - y n) + (\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (x (m + Suc n) - y (m + Suc n)))\<bar>"
            proof -
              have "(\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (x (m + Suc n) - y (m + Suc n))) = (\<Sum>m. - ((1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n))))"
              proof -
                { fix nn :: nat
                  have "\<And>r ra rb. - ((- (r::real) + ra) / (1 / rb)) = (- ra + r) / (1 / rb)"
                    by (simp add: left_diff_distrib)
                  then have "- ((y (Suc (n + nn)) + - x (Suc (n + nn))) * (1 / 3) ^ Suc (Suc (n + nn))) = (x (Suc (n + nn)) + - y (Suc (n + nn))) * (1 / 3) ^ Suc (Suc (n + nn))"
                    by fastforce
                  then have "- ((1 / 3) ^ Suc (nn + Suc n) * (y (nn + Suc n) - x (nn + Suc n))) = (1 / 3) ^ Suc (nn + Suc n) * (x (nn + Suc n) - y (nn + Suc n))"
                    by (simp add: add.commute mult.commute) }
                then show ?thesis
                  by presburger
              qed
              also have "... = - (\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (y (m + Suc n) - x (m + Suc n)))"
                apply(rule suminf_minus)
                apply(rule summable_ignore_initial_segment[of _ "Suc n"])
                using that by simp
              finally show ?thesis by simp
            qed
            also have "... = \<bar>(\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (x (m + Suc n) - y (m + Suc n))) + (1 / 3) ^ Suc n * (x n - y n)\<bar>"
              using 1 by simp
            finally show ?thesis by simp
          qed
          also have "... = \<bar>(\<Sum>m. (1/3)^(Suc (m + Suc n)) * (x (m + Suc n) - y (m + Suc n))) + (\<Sum>m<Suc n. (1/3)^(Suc m) * (x m - y m))\<bar>"
            using \<open>\<forall>i<n. x i = y i\<close> by auto
          also have "... = \<bar>\<Sum>n. (1/3)^(Suc n) * (x n - y n)\<bar>"
          proof -
            have "(\<Sum>n. (1 / 3) ^ Suc n * (x n - y n)) = (\<Sum>m. (1 / 3) ^ Suc (m + Suc n) * (x (m + Suc n) - y (m + Suc n))) + (\<Sum>m<Suc n. (1 / 3) ^ Suc m * (x m - y m))"
              by(rule suminf_split_initial_segment) (use that in simp)
            thus ?thesis by simp
          qed
          also have "... = \<bar>(\<Sum>n. (1/3)^(Suc n)* x n - (1/3)^(Suc n)* y n)\<bar>"
            by (simp add: right_diff_distrib)
          also have "... = \<bar>Cantor_to_01 x - Cantor_to_01 y\<bar>"
            using that by(simp add: suminf_diff Cantor_to_01_def)
          finally show ?thesis .
        qed
        have u2: "(1/9) * pd.product_dist x y \<le> (1/3) ^ (Suc n) * (1/2)"
        proof -
          have "pd.product_dist x y = (\<Sum>m. (1/3)^m * \<bar>x m - y m\<bar>)"
            by(simp add: that pd_def)
          also have "... = (\<Sum>m. (1/3)^(m + n) * \<bar>x (m + n) - y (m + n)\<bar>) + (\<Sum>m<n. (1/3)^m * \<bar>x m - y m\<bar>)"
            using Cantor_minus_abs_cantor[OF that] by(auto intro!: suminf_split_initial_segment)
          also have "... = (\<Sum>m. (1/3)^(m + n) * \<bar>x (m + n) - y (m + n)\<bar>)"
            using \<open>\<forall>i<n. x i = y i\<close>  by simp
          also have "... \<le> (\<Sum>m. (1/3)^(m + n))"
            using space_Cantor_space_01[OF Cantor_minus_abs_cantor[OF that]] Cantor_minus_abs_cantor[OF that]
            by(auto intro!: suminf_le summable_ignore_initial_segment[of _ n])
          also have "... =  (1 / 3) ^ n * (3 / 2)"
            using pd.nsum_of_rK[of n] by auto
          finally show ?thesis
            by auto
        qed
        from u1 u2 show ?thesis by simp
      qed

      have inj: "inj_on Cantor_to_01 (space Cantor_space)"
      proof
        fix x y
        assume h:"x \<in> space Cantor_space" "y \<in> space Cantor_space"
                 "Cantor_to_01 x = Cantor_to_01 y"
        then have "pd.product_dist x y = 0"
          using 2[OF h(1,2)] pd.Product_metric.nonneg[of x y]
          by simp
        thus "x = y"
          using pd.Product_metric.zero[of x y] h(1,2)
          by(simp add: space_Cantor_space)
      qed

      have closed: "closedin m01.sub.mtopology (Cantor_to_01 ` (space Cantor_space))"
        unfolding m01.sub.metric_closedin_iff_sequentially_closed
      proof safe
        show "a \<in> space Cantor_space \<Longrightarrow> Cantor_to_01 a \<in> {0..1}" for a
          using Cantor_to_01_image by auto
      next
        fix xn x
        assume h:"range xn \<subseteq> Cantor_to_01 ` space Cantor_space" "limitin m01.sub.mtopology xn x sequentially"
        have "\<And>n. xn n \<in> {0..1}"
          using h(1) measurable_space[OF Cantor_to_01_measurable]
          by (metis (no_types, lifting) UNIV_I atLeastAtMost_borel image_subset_iff space_restrict_space2 subsetD)
        with h(2) have xnC:"m01.sub.MCauchy xn"
          by(auto intro!: m01.sub.convergent_imp_MCauchy)
        have "\<forall>n. \<exists>x\<in>space Cantor_space. xn n = Cantor_to_01 x" using h(1) by auto
        then obtain yn where hx:"\<And>n. yn n \<in> space Cantor_space" "\<And>n. xn n = Cantor_to_01 (yn n)" by metis
        have "pd.Product_metric.MCauchy yn"
          unfolding pd.Product_metric.MCauchy_def
        proof safe
          fix \<epsilon>
          assume "(0 :: real) < \<epsilon>"
          hence "0 < \<epsilon> / 9" by auto
          then obtain N' where "\<And>n m. n \<ge> N' \<Longrightarrow> m \<ge> N' \<Longrightarrow> \<bar>xn n - xn m\<bar> < \<epsilon> / 9"
            using xnC m01.sub.MCauchy_def xnC unfolding dist_real_def by blast
          thus "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> pd.product_dist (yn n) (yn n') < \<epsilon>"
            using order.strict_trans1[OF 2[OF hx(1) hx(1)],of _ _ "\<epsilon>/9"] hx(1)
            by(auto intro!: exI[where x=N'] simp: hx(2) space_Cantor_space)
        qed(use hx space_Cantor_space in auto)
        then obtain y where y:"limitin pd.Product_metric.mtopology yn y sequentially"
          using pd_mcomplete pd.Product_metric.mcomplete_def by blast
        hence "y \<in> space Cantor_space"
          by (simp add: pd.Product_metric.limitin_mspace space_Cantor_space)
        have "limitin m01.sub.mtopology xn (Cantor_to_01 y) sequentially"
          unfolding m01.sub.limit_metric_sequentially
        proof safe
          show "Cantor_to_01 y \<in> {0..1}"
            using h(1) funcset_image[OF Cantor_to_01_image] \<open>y \<in> space Cantor_space\<close> by blast
        next
          fix \<epsilon>
          assume "(0 :: real) < \<epsilon>"
          then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> pd.product_dist (yn n) y < \<epsilon>" "\<And>n. n \<ge> N \<Longrightarrow> yn n \<in> UNIV \<rightarrow>\<^sub>E {0, 1}"
            using y by(fastforce simp: pd.Product_metric.limit_metric_sequentially)
          with \<open>\<And>n. xn n \<in> {0..1}\<close> show "\<exists>N. \<forall>n\<ge>N. xn n \<in> {0..1} \<and> dist (xn n) (Cantor_to_01 y) < \<epsilon>"
            by(auto intro!: exI[where x=N] order.strict_trans1[OF 1[OF hx(1) \<open>y \<in> space Cantor_space\<close>]] simp: submetric_def \<open>0 < \<epsilon>\<close> hx(2) dist_real_def)
        qed
        hence "Cantor_to_01 y = x"
          using h(2) by(auto dest: m01.sub.limitin_metric_unique)
        with \<open>y \<in> space Cantor_space\<close> show "x \<in> Cantor_to_01 ` space Cantor_space"
          by auto
      qed

      have open_map:"open_map pd.Product_metric.mtopology (subtopology m01.sub.mtopology (Cantor_to_01 ` (space Cantor_space))) Cantor_to_01"
      proof -
        have "open_map (mtopology_of pd.Product_metric.Self) (subtopology (mtopology_of m01.sub.Self) (Cantor_to_01 ` mspace pd.Product_metric.Self)) Cantor_to_01"
        proof(rule Metric_space_open_map_from_dist)
          fix x \<epsilon>
          assume "(0 :: real) < \<epsilon>" " x \<in> mspace pd.Product_metric.Self"
          then have "x \<in> (UNIV :: nat set) \<rightarrow>\<^sub>E {0, 1::real}"
            by simp
          show "\<exists>\<delta>>0. \<forall>y\<in>mspace pd.Product_metric.Self. mdist m01.sub.Self (Cantor_to_01 x) (Cantor_to_01 y) < \<delta> \<longrightarrow> mdist pd.Product_metric.Self x y < \<epsilon>"
            unfolding pd.Product_metric.mspace_Self pd.Product_metric.mdist_Self m01.sub.mdist_Self
          proof(safe intro!: exI[where x="\<epsilon>/9"])
            fix y
            assume h:"y \<in> (UNIV :: nat set) \<rightarrow>\<^sub>E {0, 1::real}" "dist (Cantor_to_01 x) (Cantor_to_01 y) < \<epsilon> / 9"
            then have sc:"x \<in> space Cantor_space" "y \<in> space Cantor_space"
              using \<open>x \<in> UNIV \<rightarrow>\<^sub>E {0, 1}\<close> by(simp_all add: space_Cantor_space)
            have "\<bar>Cantor_to_01 x - Cantor_to_01 y\<bar> < \<epsilon> / 9"
              using h by(simp add: dist_real_def)
            with 2[OF sc] show "pd.product_dist x y < \<epsilon> "
              by simp
          qed (use \<open>\<epsilon> > 0\<close> in auto)
        qed(use Cantor_to_01_image space_Cantor_space in auto)
        thus ?thesis
          by (simp add: mtopology_of_def space_Cantor_space)
      qed
      have "Cantor_to_01 ` A \<in> sets (restrict_space borel {0..1})" if "A \<in> sets Cantor_space" for A
        using open_map_preserves_sets'[of pd.Product_metric.mtopology m01.sub.mtopology Cantor_to_01 A] borel_of_closed[OF closed] inj sets_Cantor open_map that mpd_top \<open>restrict_space borel {0..1} = borel_of m01.sub.mtopology\<close>
        by (simp add: space_Cantor_space)
      with inj show "inj_on Cantor_to_01 (space Cantor_space)"
        and"A \<in> sets Cantor_space \<Longrightarrow> Cantor_to_01 ` A \<in> sets (restrict_space borel {0..1})"
        by simp_all
    qed

    text \<open> Next, we construct measurable embedding from $[0,1]$ to ${0,1}^{\mathbb{N}}$.\<close>
    define to_Cantor_from_01 :: "real \<Rightarrow> nat \<Rightarrow> real"  where
      "to_Cantor_from_01 \<equiv> (\<lambda>r n. if r = 1 then 1 else real_of_int (\<lfloor>2^(Suc n) * r\<rfloor> mod 2))"

    text \<open> @{term to_Cantor_from_01} is a measurable injective embedding into Cantor space.\<close>
    have to_Cantor_from_01_image': "to_Cantor_from_01 r n \<in> {0,1}" for r n
      unfolding to_Cantor_from_01_def by auto
    have to_Cantor_from_01_image'': "\<And>r n. 0 \<le> to_Cantor_from_01 r n" "\<And>r n. to_Cantor_from_01 r n \<le> 1"
      by (auto simp add: to_Cantor_from_01_def)
    have to_Cantor_from_01_image: "to_Cantor_from_01 \<in> {0..1} \<rightarrow> space Cantor_space"
      using to_Cantor_from_01_image' by(auto simp: space_Cantor_space)
    have to_Cantor_from_01_measurable:
      "to_Cantor_from_01 \<in> restrict_space borel {0..1} \<rightarrow>\<^sub>M Cantor_space"
      unfolding to_Cantor_from_01_def Cantor_space_def
      by(auto intro!: measurable_restrict_space3 measurable_abs_UNIV)
    have to_Cantor_from_01_summable[simp]:
      "summable (\<lambda>n. (1/2)^n * to_Cantor_from_01 r n)" for r
    proof(rule summable_comparison_test'[where g="\<lambda>n. (1/2)^ n"])
      show "norm ((1 / 2) ^ n * to_Cantor_from_01 r n) \<le> (1 / 2) ^ n" for n
        using to_Cantor_from_01_image'[of r n] by auto
    qed simp

    have to_Cantor_from_sumn': "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> r"
      "r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^n"
      "to_Cantor_from_01 r n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i)"
      "to_Cantor_from_01 r n = 0 \<longleftrightarrow> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^(Suc n)" if assms:"r \<in> {0..<1}" for r n
    proof -
      let ?f = "to_Cantor_from_01 r"
      have f_simp: "?f l = real_of_int (\<lfloor> 2^(Suc l) * r\<rfloor> mod 2)" for l
        using assms by(simp add: to_Cantor_from_01_def)
      define S where "S = (\<lambda>n. \<Sum>i<n. (1/2)^(Suc i)*?f i)"
      have SSuc:"S (Suc k) = S k + (1/2)^(Suc k) * to_Cantor_from_01 r k" for k
        by(simp add: S_def)
      have Sfloor: "\<lfloor>2^(Suc m) * (l - S m)\<rfloor> mod 2 = \<lfloor>2^(Suc m) * l\<rfloor> mod 2" for l m
      proof -
        have "\<exists>z. 2^(Suc m) * ((1/2)^(Suc k) * ?f k) = 2*real_of_int z" if "k < m" for k
        proof -
          have 0:"(2::real) ^ m * (1 / 2) ^ k = 2 * 2^(m-k-1)"
            using that by (simp add: power_diff_conv_inverse)
          consider "?f k = 0" | "?f k = 1"
            using to_Cantor_from_01_image'[of r k] by auto
          thus ?thesis
            apply cases using that 0 by auto
        qed
        then obtain z where "\<And>k. k < m \<Longrightarrow> 2^(Suc m) * ((1/2)^(Suc k) * ?f k) = 2*real_of_int (z k)"
          by metis
        hence Sm: "2^(Suc m) * S m = real_of_int (2 * (\<Sum>k<m. (z k)))"
          by(auto simp: S_def sum_distrib_left)
        have "\<lfloor>2^(Suc m) * (l - S m)\<rfloor> mod 2 = \<lfloor>2^(Suc m) * l - 2^(Suc m) *  S m\<rfloor> mod 2"
          by (simp add: right_diff_distrib)
        also have "... = \<lfloor>2^(Suc m) * l\<rfloor> mod 2"
          unfolding Sm
          by(simp only: floor_diff_of_int) presburger
        finally show ?thesis .
      qed
      have "S n \<le> r \<and> r - S n < (1/2)^n \<and> (?f n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - S n) \<and> (?f n = 0 \<longleftrightarrow> r - S n < (1/2)^(Suc n))"
      proof(induction n)
        case 0
        then show ?case
          using assms by(auto simp: S_def to_Cantor_from_01_def) linarith+
      next
        case (Suc n)
        hence ih: "S n \<le> r" "r - S n < (1 / 2) ^ n"
          "?f n = 1 \<Longrightarrow> (1 / 2) ^ Suc n \<le> r - S n"
          "?f n = 0 \<Longrightarrow> r - S n < (1 / 2) ^ Suc n"
          by simp_all
        have SSuc':"?f n = 0 \<and> S (Suc n) = S n \<or> ?f n = 1 \<and> S (Suc n) = S n + (1/2)^(Suc n)"
          using to_Cantor_from_01_image'[of r n] by(simp add: SSuc)
        have goal1:"S (Suc n) \<le> r"
          using SSuc' ih(1) ih(3) by auto
        have goal2: "r - S (Suc n) < (1 / 2) ^ Suc n"
          using SSuc' ih(4) ih(2) by auto
        have goal3_1: "(1 / 2) ^ Suc (Suc n) \<le> r - S (Suc n)" if "?f (Suc n) = 1"
        proof(rule ccontr)
          assume "\<not> (1 / 2) ^ Suc (Suc n) \<le> r - S (Suc n)"
          then have "r - S (Suc n) < (1 / 2) ^ Suc (Suc n)" by simp
          hence h:"2 ^ Suc (Suc n) * (r - S (Suc n)) < 1"
            using mult_less_cancel_left_pos[of "2 ^ Suc (Suc n)" "r - S (Suc n)" "(1 / 2) ^ Suc (Suc n)"]
            by (simp add: power_one_over)
          moreover have "0 \<le> 2 ^ Suc (Suc n) * (r - S (Suc n))"
            using goal1 by simp
          ultimately have "\<lfloor>2 ^ Suc (Suc n) * (r - S (Suc n))\<rfloor> = 0"
            by linarith
          thus False
            using that[simplified f_simp] Sfloor[of "Suc n" r]
            by fastforce
        qed
        have goal3_2: "?f (Suc n) = 1" if "(1 / 2) ^ Suc (Suc n) \<le> r - S (Suc n)"
        proof -
          have "1 \<le> 2 ^ Suc (Suc n) * (r - S (Suc n))"
            using that[simplified f_simp] mult_le_cancel_left_pos[of "2 ^ Suc (Suc n)" "(1 / 2) ^ Suc (Suc n)" "r - S (Suc n)"]
            by (simp add: power_one_over)
          moreover have "2 ^ Suc (Suc n) * (r - S (Suc n)) < 2"
            using mult_less_cancel_left_pos[of "2 ^ Suc (Suc n)" "r - S (Suc n)" "(1 / 2) ^ Suc n"] goal2
            by (simp add: power_one_over)
          ultimately have "\<lfloor>2 ^ Suc (Suc n) * (r - S (Suc n))\<rfloor> = 1"
            by linarith
          thus ?thesis
            using Sfloor[of "Suc n" r] by(auto simp: f_simp)
        qed
        have goal4_1: "r - S (Suc n) < (1 / 2) ^ Suc (Suc n)" if "?f (Suc n) = 0"
        proof(rule ccontr)
          assume "\<not> r - S (Suc n) < (1 / 2) ^ Suc (Suc n)"
          then have "(1 / 2) ^ Suc (Suc n) \<le> r - S (Suc n)" by simp 
          hence "1 \<le> 2 ^ Suc (Suc n) * (r - S (Suc n))"
            using mult_le_cancel_left_pos[of "2 ^ Suc (Suc n)" "(1 / 2) ^ Suc (Suc n)" "r - S (Suc n)"]
            by (simp add: power_one_over)
          moreover have "2 ^ Suc (Suc n) * (r - S (Suc n)) < 2"
            using mult_less_cancel_left_pos[of "2 ^ Suc (Suc n)" "r - S (Suc n)" "(1 / 2) ^ Suc n"] goal2
            by (simp add: power_one_over)
          ultimately have "\<lfloor>2 ^ Suc (Suc n) * (r - S (Suc n))\<rfloor> = 1"
            by linarith
          thus False
            using that Sfloor[of "Suc n" r] by(auto simp: f_simp)
        qed
        have goal4_2: "?f (Suc n) = 0" if "r - S (Suc n) < (1 / 2) ^ Suc (Suc n)"
        proof -
          have h:"2 ^ Suc (Suc n) * (r - S (Suc n)) < 1"
            using mult_less_cancel_left_pos[of "2 ^ Suc (Suc n)" "r - S (Suc n)" "(1 / 2) ^ Suc (Suc n)"] that
            by (simp add: power_one_over)
          moreover have "0 \<le> 2 ^ Suc (Suc n) * (r - S (Suc n))"
            using goal1 by simp
          ultimately have "\<lfloor>2 ^ Suc (Suc n) * (r - S (Suc n))\<rfloor> = 0"
            by linarith
          thus ?thesis
            using Sfloor[of "Suc n" r] by(auto simp: f_simp)
        qed
        show ?case
          using goal1 goal2 goal3_1 goal3_2 goal4_1 goal4_2 by blast
      qed
      thus "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> r"
        and "r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^n"
        and "to_Cantor_from_01 r n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i)"
        and "to_Cantor_from_01 r n = 0 \<longleftrightarrow> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^(Suc n)"
        by(simp_all add: S_def)
    qed
    have to_Cantor_from_sumn: "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> r"
      "r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> (1/2)^n"
      "to_Cantor_from_01 r n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i)"
      "to_Cantor_from_01 r n = 0 \<longleftrightarrow> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^(Suc n)" if assms:"r \<in> {0..1}" for r n
    proof -
      have nsum:"(\<Sum>i<n. (1/2)^(Suc i)) = 1 - (1 / (2::real)) ^ n"
        using one_diff_power_eq[of "1/(2::real)" n] by(auto simp: sum_divide_distrib[symmetric])

      consider "r = 1" | "r \<in>{0..<1}" using assms by fastforce
      hence "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> r \<and> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> (1/2)^n \<and> (to_Cantor_from_01 r n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i)) \<and> (to_Cantor_from_01 r n = 0 \<longleftrightarrow> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^(Suc n))"
      proof cases
        case 1
        then show ?thesis
          using nsum by(auto simp: to_Cantor_from_01_def)
      next
        case 2
        from to_Cantor_from_sumn'[OF this]
        show ?thesis
          using less_eq_real_def by blast
      qed
      thus "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> r"
        and "r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) \<le> (1/2)^n"
        and "to_Cantor_from_01 r n = 1 \<longleftrightarrow> (1/2)^(Suc n) \<le> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i)"
        and "to_Cantor_from_01 r n = 0 \<longleftrightarrow> r - (\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) < (1/2)^(Suc n)"
        by simp_all
    qed

    have to_Cantor_from_sum: "(\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n) = r" if assms:"r \<in> {0..1}" for r
    proof -
      have 1:"r \<le> (\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n)"
      proof -
        have 0:"r \<le> (1 / 2) ^ n + (\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n)" for n
        proof -
          have "r \<le> (1 / 2) ^ n + (\<Sum>i<n. (1 / 2) ^ Suc i * to_Cantor_from_01 r i)"
            using to_Cantor_from_sumn(2)[OF assms,of n] by auto
          also have "... \<le> (1 / 2) ^ n + (\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n)"
            using to_Cantor_from_01_image''[of r] by(auto intro!: sum_le_suminf)
          finally show ?thesis .
        qed
        have 00:"\<exists>no. \<forall>n\<ge>no. (1 / 2) ^ n < r" if "r>0" for r :: real
        proof -
          obtain n0 where "(1 / 2) ^ n0 < r"
            using reals_power_lt_ex[of _ "2 :: real",OF \<open>r>0\<close>] by auto
          thus ?thesis
            using order.strict_trans1[OF power_decreasing[of n0 _ "1/2::real"]]
            by(auto intro!: exI[where x=n0])
        qed
        show ?thesis
          apply(rule Lim_bounded2[where f="\<lambda>n. (1 / 2) ^ n + (\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n)" and N=0])
          using 0 00 by(auto simp: LIMSEQ_iff)
      qed
      have 2:"(\<Sum>n. (1/2)^(Suc n)*to_Cantor_from_01 r n) \<le> r"
        using to_Cantor_from_sumn[OF assms] by(auto intro!: suminf_le_const)
      show ?thesis
        using 1 2 by simp
    qed
    have to_Cantor_from_sum': "(\<Sum>i<n. (1/2)^(Suc i)*to_Cantor_from_01 r i) = r - (\<Sum>m. (1/2)^(Suc (m + n))*to_Cantor_from_01 r (m + n))" if assms:"r \<in> {0..1}" for r n
      using suminf_minus_initial_segment[of "\<lambda>n. (1 / 2) ^ Suc n * to_Cantor_from_01 r n" n] to_Cantor_from_sum[OF assms]
      by auto

    have to_Cantor_from_01_exist0: "\<forall>n.\<exists>k\<ge>n. to_Cantor_from_01 r k = 0" if assms:"r \<in> {0..<1}" for r
    proof(rule ccontr)
      assume "\<not> (\<forall>n.\<exists>k\<ge>n. to_Cantor_from_01 r k = 0)"
      then obtain n0 where hn0:
        "\<And>k. k \<ge> n0 \<Longrightarrow> to_Cantor_from_01 r k = 1"
        using to_Cantor_from_01_image'[of r] by auto
      define n where "n = Min {i. i \<le> n0 \<and> (\<forall>k\<ge>i. to_Cantor_from_01 r k = 1)}"
      have n0in: "n0 \<in> {i. i \<le> n0 \<and> (\<forall>k\<ge>i. to_Cantor_from_01 r k = 1)}"
        using hn0 by auto
      have hn:"n \<le> n0" "\<And>k. k \<ge> n \<Longrightarrow> to_Cantor_from_01 r k = 1"
        using n0in Min_in[of "{i. i \<le> n0 \<and> (\<forall>k\<ge>i. to_Cantor_from_01 r k = 1)}"]
        by(auto simp: n_def)
      show False
      proof(cases n)
        case 0
        then have "r = (\<Sum>n. (1 / 2) ^ Suc n)"
          using to_Cantor_from_sum[of r] assms hn(2) by simp
        also have "... = 1"
          using nsum_of_r'[of "1/2" 1 1] by auto
        finally show ?thesis
          using assms by auto
      next
        case eqn:(Suc n')
        have "to_Cantor_from_01 r n' = 0"
        proof(rule ccontr)
          assume "to_Cantor_from_01 r n' \<noteq> 0"
          then have "to_Cantor_from_01 r n' = 1"
            using to_Cantor_from_01_image'[of r n'] by auto
          hence "n' \<in> {i. i \<le> n0 \<and> (\<forall>k\<ge>i. to_Cantor_from_01 r k = 1)}"
            using hn eqn not_less_eq_eq order_antisym_conv by fastforce
          hence "n \<le> n'"
            using Min.coboundedI[of "{i. i \<le> n0 \<and> (\<forall>k\<ge>i. to_Cantor_from_01 r k = 1)}" n']
            by(simp add: n_def)
          thus False
            using eqn by simp
        qed
        hence le1:"r - (\<Sum>i<n'. (1 / 2) ^ Suc i * to_Cantor_from_01 r i) < (1 / 2) ^ n"
          using to_Cantor_from_sumn'(4)[OF assms,of n'] by (simp add: eqn)
        have "r - (\<Sum>i<n'. (1 / 2) ^ Suc i * to_Cantor_from_01 r i) = (1 / 2) ^ n"
          (is "?lhs = _")
        proof -
          have "?lhs = (\<Sum>m. (1/2)^(m + Suc n')*to_Cantor_from_01 r (m + n'))"
            using to_Cantor_from_sum'[of r n'] assms by simp
          also have "... = (\<Sum>m. (1/2)^(m + Suc n)*to_Cantor_from_01 r (m + n))"
          proof -
            have "(\<Sum>n. (1 / 2) ^ (Suc n + Suc n') * to_Cantor_from_01 r (Suc n + n')) = (\<Sum>m. (1 / 2) ^ (m + Suc n') * to_Cantor_from_01 r (m + n')) - (1 / 2) ^ (0 + Suc n') * to_Cantor_from_01 r (0 + n')"
              by(rule suminf_split_head) (auto intro!: summable_ignore_initial_segment)
            thus ?thesis
              using \<open>to_Cantor_from_01 r n' = 0\<close> by(simp add: eqn)
          qed
          also have "... = (\<Sum>m. (1/2)^(m + Suc n))"
            using hn by simp
          also have "... = (1 / 2) ^ n"
            using nsum_of_r'[of "1/2" "Suc n" 1,simplified] by simp
          finally show ?thesis .
        qed
        with le1 show False
          by simp
      qed
    qed
    have to_Cantor_from_01_if_exist0: "to_Cantor_from_01 (\<Sum>n. (1 / 2) ^ Suc n * a n) = a" if assms:"\<And>n. a n \<in> {0,1}" "\<forall>n.\<exists>k\<ge>n. a k = 0" for a
    proof
      fix n
      have [simp]: "summable (\<lambda>n. (1 / 2) ^ n * a n)"
      proof(rule summable_comparison_test'[where g="\<lambda>n. (1/2)^ n"])
        show "norm ((1 / 2) ^ n * a n) \<le> (1 / 2) ^ n" for n
          using assms(1)[of n] by auto
      qed simp
      let ?r = "\<Sum>n. (1 / 2) ^ Suc n * a n"
      have "?r \<in> {0..1}"
        using assms(1) space_Cantor_space_01[of a,simplified space_Cantor_space] nsum_of_r_leq[of "1/2" a 1 1 0]
        by auto
      show "to_Cantor_from_01 ?r n = a n"
      proof(rule less_induct)
        fix x
        assume ih:"y < x \<Longrightarrow> to_Cantor_from_01 ?r y = a y" for y
        have eq1:"?r - (\<Sum>i<x. (1/2)^(Suc i)*to_Cantor_from_01 ?r i) = (\<Sum>n. (1/2)^(Suc (n + x))* a (n + x))"
          (is "?lhs = ?rhs")
        proof -
          have "?lhs = (\<Sum>n. (1 / 2) ^ Suc (n + x) * a (n + x)) + (\<Sum>i<x. (1/2)^(Suc i)* a i) - (\<Sum>i<x. (1/2)^(Suc i)*to_Cantor_from_01 ?r i)"
            using suminf_split_initial_segment[of "\<lambda>n. (1 / 2) ^ (Suc n) * a n" x] by simp
          also have "... = (\<Sum>n. (1 / 2) ^ Suc (n + x) * a (n + x)) + (\<Sum>i<x. (1/2)^(Suc i)* a i) - (\<Sum>i<x. (1/2)^(Suc i)*a i)"
            using ih by simp
          finally show ?thesis by simp
        qed
        define Sn where "Sn = (\<Sum>n. (1/2)^(Suc (n + x))* a (n + x))"
        define Sn' where "Sn' = (\<Sum>n. (1/2)^(Suc (n + (Suc x)))* a (n + (Suc x)))"
        have SnSn':"Sn = (1/2)^(Suc x) * a x + Sn'"
          using suminf_split_head[of "\<lambda>n. (1/2)^(Suc (n + x))* a (n + x)",OF summable_ignore_initial_segment]
          by(auto simp: Sn_def Sn'_def)
        have hsn:"0 \<le> Sn'" "Sn' < (1/2)^(Suc x)"
        proof -
          show "0 \<le> Sn'"
            unfolding Sn'_def
            by(rule suminf_nonneg,rule summable_ignore_initial_segment) (use assms(1) space_Cantor_space_01[of a,simplified space_Cantor_space] in fastforce)+
        next
          have "\<exists>n'\<ge>Suc x. a n' < 1"
            using assms by fastforce
          thus "Sn' <  (1/2)^(Suc x)"
            using nsum_of_r_le[of "1/2" a 1 "Suc x" "Suc (Suc x)"] assms(1) space_Cantor_space_01[of a,simplified space_Cantor_space]
            by(auto simp: Sn'_def)
        qed
        have goal1: "to_Cantor_from_01 ?r x = 1 \<longleftrightarrow> a x = 1"
        proof -
          have "to_Cantor_from_01 ?r x = 1 \<longleftrightarrow> (1 / 2) ^ Suc x \<le> Sn"
            using to_Cantor_from_sumn(3)[OF \<open>?r \<in> {0..1}\<close>] eq1
            by(fastforce simp: Sn_def)
          also have "... \<longleftrightarrow> (1 / 2) ^ Suc x \<le> (1/2)^(Suc x) * a x + Sn'"
            by(simp add: SnSn')
          also have "... \<longleftrightarrow> a x = 1"
          proof -
            have "a x = 1" if "(1 / 2) ^ Suc x \<le> (1/2)^(Suc x) * a x + Sn'"
            proof(rule ccontr)
              assume "a x \<noteq> 1"
              then have "a x = 0"
                using assms(1) by auto
              hence "(1 / 2) ^ Suc x \<le> Sn'"
                using that by simp
              thus False
                using hsn by auto
            qed
            thus ?thesis
              by(auto simp: hsn)
          qed
          finally show ?thesis .
        qed
        have goal2: "to_Cantor_from_01 ?r x = 0 \<longleftrightarrow> a x = 0"
        proof -
          have "to_Cantor_from_01 ?r x = 0 \<longleftrightarrow> Sn < (1 / 2) ^ Suc x"
            using to_Cantor_from_sumn(4)[OF \<open>?r \<in> {0..1}\<close>] eq1
            by(fastforce simp: Sn_def)
          also have "... \<longleftrightarrow> (1/2)^(Suc x) * a x + Sn' < (1 / 2) ^ Suc x"
            by(simp add: SnSn')
          also have "... \<longleftrightarrow> a x = 0"
          proof -
            have "a x = 0" if "(1/2)^(Suc x) * a x + Sn' < (1 / 2) ^ Suc x"
            proof(rule ccontr)
              assume "a x \<noteq> 0"
              then have "a x = 1"
                using assms(1) by auto
              thus False
                using that hsn by auto
            qed
            thus ?thesis
              using hsn by auto
          qed
          finally show ?thesis .
        qed
        show "to_Cantor_from_01 ?r x = a x"
          using goal1 goal2 to_Cantor_from_01_image'[of ?r x] by auto
      qed
    qed
    have to_Cantor_from_01_sum_of_to_Cantor_from_01: "to_Cantor_from_01 (\<Sum>n. (1 / 2) ^ Suc n * to_Cantor_from_01 r n) = to_Cantor_from_01 r" if assms:"r \<in> {0..1}" for r
    proof -
      consider "r = 1" | "r \<in> {0..<1}"
        using assms by fastforce
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          using nsum_of_r'[of "1/2" 1 1]
          by(auto simp: to_Cantor_from_01_def)
      next
        case 2
        from to_Cantor_from_01_if_exist0[OF to_Cantor_from_01_image' to_Cantor_from_01_exist0[OF this]]
        show ?thesis .
      qed
    qed
    have to_Cantor_from_01_inj: "inj_on to_Cantor_from_01 (space (restrict_space borel {0..1}))"
    proof
      fix x y :: real
      assume "x \<in> space (restrict_space borel {0..1})" "y \<in> space (restrict_space borel {0..1})"
        and h:"to_Cantor_from_01 x = to_Cantor_from_01 y"
      then have xyin:"x \<in> {0..1}" "y \<in> {0..1}"
        by simp_all
      show "x = y"
        using to_Cantor_from_sum[OF xyin(1)] to_Cantor_from_sum[OF xyin(2)] h
        by simp
    qed
    have to_Cantor_from_01_preserves_sets: "to_Cantor_from_01 ` A \<in> sets Cantor_space" if assms: "A \<in> sets (restrict_space borel {0..1})" for A
    proof -
      define f :: "(nat \<Rightarrow> real) \<Rightarrow> real" where "f \<equiv> (\<lambda>x. \<Sum>n. (1/2)^(Suc n)* x n)"
      have f_meas:"f \<in> Cantor_space \<rightarrow>\<^sub>M restrict_space borel {0..1}"
      proof -
        have "f \<in> borel_measurable Cantor_space"
          unfolding Cantor_to_01_def f_def
        proof(rule borel_measurable_suminf)
          fix n
          have "(\<lambda>x. x n) \<in> Cantor_space \<rightarrow>\<^sub>M restrict_space borel {0, 1}"
            by(simp add: Cantor_space_def)
          hence "(\<lambda>x. x n) \<in> borel_measurable Cantor_space"
            by(simp add: measurable_restrict_space2_iff)
          thus "(\<lambda>x. (1 / 2) ^ Suc n * x n) \<in> borel_measurable Cantor_space"
            by simp
        qed
        moreover have "0 \<le> f x" "f x \<le> 1" if "x \<in> space Cantor_space" for x
        proof -
          have [simp]:"summable (\<lambda>n. (1/2)^n* x n)"
          proof(rule summable_comparison_test'[where g="\<lambda>n. (1/2)^ n"])
            show "norm ((1 / 2) ^ n * x n) \<le> (1 / 2) ^ n" for n
              using that by simp
          qed simp
          show "0 \<le> f x"
            using that by(auto intro!: suminf_nonneg simp: f_def)
          show "f x \<le> 1"
          proof -
            have "f x \<le> (\<Sum>n. (1/2)^(Suc n))"
              using that by(auto intro!: suminf_le simp: f_def)
            also have "... = 1"
              using nsum_of_r'[of "1/2" 1 1] by simp
            finally show ?thesis .
          qed
        qed
        ultimately show ?thesis
          by(auto intro!: measurable_restrict_space2)
      qed
      have image_sets:"to_Cantor_from_01 ` (space (restrict_space borel {0..1})) \<in> sets Cantor_space"
        (is "?A \<in> _")
      proof -
        have "?A \<subseteq> space Cantor_space"
          using to_Cantor_from_01_image by auto
        have comple_sets:"(\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A \<in> sets Cantor_space"
        proof -
          have eq1:"?A = {\<lambda>n. 1} \<union> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)}"
          proof
            show "?A \<subseteq> {\<lambda>n. 1} \<union> {x. (\<forall>n. x n \<in> {0, 1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)}"
            proof
              fix x
              assume "x \<in> ?A"
              then obtain r where hr:"r \<in> {0..1}" "x = to_Cantor_from_01 r"
                by auto
              then consider "r = 1" | "r \<in> {0..<1}" by fastforce
              thus "x \<in> {\<lambda>n. 1} \<union> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)}"
              proof cases
                case 1
                then show ?thesis
                  by(simp add: hr(2) to_Cantor_from_01_def)
              next
                case 2
                from to_Cantor_from_01_exist0[OF this] to_Cantor_from_01_image'
                show ?thesis by(auto simp: hr(2))
              qed
            qed
          next
            show "{\<lambda>n. 1} \<union> {x. (\<forall>n. x n \<in> {0, 1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)} \<subseteq> ?A"
            proof
              fix x :: "nat \<Rightarrow> real"
              assume "x \<in> {\<lambda>n. 1} \<union> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)}"
              then consider "x = (\<lambda>n. 1)" | "(\<forall>n. x n \<in> {0,1}) \<and> (\<forall>n. \<exists>k\<ge>n. x k = 0)"
                by auto
              thus "x \<in> ?A"
              proof cases
                case 1
                then show ?thesis
                  by(auto intro!: image_eqI[where x=1] simp: to_Cantor_from_01_def)
              next
                case 2
                hence "\<And>n. 0 \<le> x n" "\<And>n. x n \<le> 1"
                  by (metis dual_order.refl empty_iff insert_iff zero_less_one_class.zero_le_one)+
                with 2 to_Cantor_from_01_if_exist0[of x] nsum_of_r_leq[of "1/2" x 1 1 0]
                show ?thesis
                  by(auto intro!: image_eqI[where x="\<Sum>n. (1 / 2) ^ Suc n * x n"])
              qed
            qed
          qed
          have "(\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A = {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<exists>n. \<forall>k\<ge>n. x k = 1)} - {\<lambda>n. 1}"
          proof
            show "(\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A \<subseteq> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<exists>n. \<forall>k\<ge>n. x k = 1)} - {\<lambda>n. 1}"
            proof
              fix x :: "nat \<Rightarrow> real"
              assume "x \<in> (\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A"
              then have "\<forall>n. x n \<in> {0,1}" "\<not> (\<forall>n. \<exists>k\<ge>n. x k = 0)" "x \<noteq> (\<lambda>n. 1)"
                using eq1 by blast+
              thus "x \<in> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<exists>n. \<forall>k\<ge>n. x k = 1)} - {\<lambda>n. 1}"
                by blast
            qed
          next
            show "(\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A \<supseteq> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<exists>n. \<forall>k\<ge>n. x k = 1)} - {\<lambda>n. 1}"
            proof
              fix x :: "nat \<Rightarrow> real"
              assume h:"x \<in> {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<exists>n. \<forall>k\<ge>n. x k = 1)} - {\<lambda>n. 1}"
              then have "\<forall>n. x n \<in> {0,1}" "\<exists>n. \<forall>k\<ge>n. x k = 1" "x \<noteq> (\<lambda>n. 1)"
                by blast+
              hence "\<not> (\<forall>n. \<exists>k\<ge>n. x k = 0)"
                by fastforce
              with \<open>\<forall>n. x n \<in> {0,1}\<close> \<open>x \<noteq> (\<lambda>n. 1)\<close>
              show "x \<in> (\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A"
                using eq1 by blast
            qed
          qed
          also have "... = (\<Union> ((\<lambda>n. {x. (\<forall>n. x n \<in> {0,1}) \<and> (\<forall>k\<ge>n. x k = 1)}) ` UNIV)) - {\<lambda>n. 1}"
            by blast
          also have "... \<in> sets Cantor_space" (is "?B \<in> _")
          proof -
            have "countable ?B"
            proof -
              have "countable {x :: nat \<Rightarrow> real. (\<forall>n. x n = 0 \<or> x n = 1) \<and> (\<forall>k\<ge>m. x k = 1)}" for m :: nat
              proof -
                let ?C = "{x::nat \<Rightarrow> real. (\<forall>n. x n = 0 \<or> x n = 1) \<and> (\<forall>k\<ge>m. x k = 1)}"
                define g where "g = (\<lambda>(x::nat \<Rightarrow> real) n. if n < m then x n else undefined)"
                have 1:"g ` ?C = (\<Pi>\<^sub>E i \<in>{..<m}. {0,1})"
                proof(standard; standard)
                  fix x
                  assume "x \<in> g ` ?C"
                  then show "x \<in> (\<Pi>\<^sub>E i \<in>{..<m}. {0,1})"
                    by(auto simp: g_def PiE_def extensional_def)
                next
                  fix x
                  assume h:"x \<in> (\<Pi>\<^sub>E i \<in>{..<m}. {0,1::real})"
                  then have "x = g (\<lambda>n. if n < m then x n else 1)"
                    by(auto simp add: g_def PiE_def extensional_def)
                  moreover have "(\<lambda>n. if n < m then x n else 1) \<in> ?C"
                    using h by auto
                  ultimately show "x \<in> g ` ?C"
                    by auto
                qed
                have 2:"inj_on g ?C"
                proof
                  fix x y
                  assume hxyg:"x \<in> ?C" "y :  ?C" "g x = g y"
                  show "x = y"
                  proof
                    fix n
                    consider "n < m" | "m \<le> n" by fastforce
                    thus "x n = y n"
                    proof cases
                      case 1
                      then show ?thesis
                        using fun_cong[OF hxyg(3),of n] by(simp add: g_def)
                    next
                      case 2
                      then show ?thesis
                        using hxyg(1,2) by auto
                    qed
                  qed
                qed
                show "countable {x::nat \<Rightarrow> real. (\<forall>n. x n = 0 \<or> x n = 1) \<and> (\<forall>k\<ge>m. x k = 1)}"
                  by(rule countable_image_inj_on[OF _ 2]) (auto intro!: countable_PiE simp: 1)
              qed
              thus ?thesis
                by auto
            qed
            moreover have "?B \<subseteq> space Cantor_space"
              by(auto simp: space_Cantor_space)
            ultimately show ?thesis
              using Cantor_space_standard_ne by(simp add: standard_borel.countable_sets standard_borel_ne_def)
          qed
          finally show ?thesis .
        qed
        moreover have "space Cantor_space - ((\<Pi>\<^sub>E i\<in> UNIV. {0,1}) - ?A) = ?A"
          using \<open>?A \<subseteq> space Cantor_space\<close> space_Cantor_space  by blast
        ultimately show ?thesis
          using sets.compl_sets[OF comple_sets] by auto
      qed
      have "to_Cantor_from_01 ` A = f -` A \<inter> to_Cantor_from_01 ` (space (restrict_space borel {0..1}))"
      proof
        show "to_Cantor_from_01 ` A  \<subseteq> f -` A \<inter> to_Cantor_from_01 ` space (restrict_space borel {0..1})"
        proof
          fix x
          assume "x \<in> to_Cantor_from_01 ` A"
          then obtain a where ha:"a \<in> A" "x = to_Cantor_from_01 a" by auto
          hence "a \<in> {0..1}"
            using sets.sets_into_space[OF assms] by auto
          have "f x = a"
            using to_Cantor_from_sum[OF \<open>a \<in> {0..1}\<close>] by(simp add: f_def ha(2))
          thus " x \<in> f -` A \<inter> to_Cantor_from_01 ` space (restrict_space borel {0..1})"
            using sets.sets_into_space[OF assms] ha by auto
        qed
      next
        show "to_Cantor_from_01 ` A \<supseteq> f -` A \<inter> to_Cantor_from_01 ` space (restrict_space borel {0..1})"
        proof
          fix x
          assume h:"x \<in> f -` A \<inter> to_Cantor_from_01 ` space (restrict_space borel {0..1})"
          then obtain r where "r \<in> {0..1}" "x = to_Cantor_from_01 r"
            by auto
          from h have "f x \<in> A"
            by simp
          hence "to_Cantor_from_01 (f x) = x"
            using to_Cantor_from_01_sum_of_to_Cantor_from_01[OF \<open>r \<in> {0..1}\<close>]
            by(simp add: f_def \<open>x = to_Cantor_from_01 r\<close>)
          with \<open>f x \<in> A\<close>
          show "x \<in> to_Cantor_from_01 ` A"
            by (simp add: rev_image_eqI)
        qed
      qed
      also have "... \<in> sets Cantor_space"
      proof -
        have " f -` A \<inter> space Cantor_space \<inter> to_Cantor_from_01 ` space (restrict_space borel {0..1}) = f -` A \<inter> to_Cantor_from_01 ` (space (restrict_space borel {0..1}))"
          using to_Cantor_from_01_image sets.sets_into_space[OF assms,simplified] by auto
        thus ?thesis
          using sets.Int[OF measurable_sets[OF f_meas assms] image_sets]
          by fastforce
      qed
      finally show ?thesis .
    qed
    show ?thesis
      using Schroeder_Bernstein_measurable[OF Cantor_to_01_measurable Cantor_to_01_preserves_sets Cantor_to_01_inj to_Cantor_from_01_measurable to_Cantor_from_01_preserves_sets to_Cantor_from_01_inj]
      by(simp add: measurable_isomorphic_def)
  qed
  have 1:"Cantor_space measurable_isomorphic (\<Pi>\<^sub>M (i::nat,j::nat)\<in> UNIV \<times> UNIV. restrict_space borel {0,1::real})"
    unfolding Cantor_space_def
    by(auto intro!: measurable_isomorphic_sym[OF countable_infinite_isomorphisc_to_nat_index] simp: split_beta' finite_prod)
  have 2:"(\<Pi>\<^sub>M (i::nat,j::nat)\<in> UNIV \<times> UNIV. restrict_space borel {0,1::real}) measurable_isomorphic (\<Pi>\<^sub>M (i::nat)\<in> UNIV. Cantor_space)"
    unfolding Cantor_space_def by(rule measurable_isomorphic_sym[OF PiM_PiM_isomorphic_to_PiM])
  have 3:"(\<Pi>\<^sub>M (i::nat)\<in> UNIV. Cantor_space) measurable_isomorphic Hilbert_cube"
    unfolding Hilbert_cube_def by(rule measurable_isomorphic_lift_product[OF Cantor_space_isomorphic_to_01closed])
  show ?thesis
    by(rule measurable_isomorphic_trans[OF measurable_isomorphic_trans[OF 1 2] 3])
qed

subsection \<open> Final Results \<close>
lemma(in standard_borel) embedding_into_Hilbert_cube:
 "\<exists>A \<in> sets Hilbert_cube. M measurable_isomorphic (restrict_space Hilbert_cube A)"
proof -
  obtain S where S:"Polish_space S" "sets (borel_of S) = sets M"
    using Polish_space by blast
  obtain A where A:"gdelta_in Hilbert_cube_topology A" "S homeomorphic_space subtopology Hilbert_cube_topology A"
    using embedding_into_Hilbert_cube_gdelta_in[OF S(1)] by blast
  show ?thesis
    using borel_of_gdelta_in[OF A(1)] homeomorphic_space_measurable_isomorphic[OF A(2)]  measurable_isomorphic_sets_cong[OF S(2),of "borel_of (subtopology Hilbert_cube_topology A)" "restrict_space Hilbert_cube A"] Hilbert_cube_borel sets_restrict_space_cong[OF Hilbert_cube_borel]
    by(auto intro!: bexI[where x=A] simp: borel_of_subtopology)
qed

lemma(in standard_borel) embedding_from_Cantor_space:
  assumes "uncountable (space M)"
  shows "\<exists>A \<in> sets M. Cantor_space measurable_isomorphic (restrict_space M A)"
proof -
  obtain S where S:"Polish_space S" "sets (borel_of S) = sets M"
    using Polish_space by blast
  then obtain A where A:"gdelta_in S A" "Cantor_space_topology homeomorphic_space subtopology S A"
    using embedding_from_Cantor_space[of S] assms sets_eq_imp_space_eq[OF S(2)]
    by(auto simp: space_borel_of)
  show ?thesis
    using borel_of_gdelta_in[OF A(1)] S(2) homeomorphic_space_measurable_isomorphic[OF A(2)] measurable_isomorphic_sets_cong[OF Cantor_space_borel restrict_space_sets_cong[OF refl S(2)],of A]
    by(auto intro!: bexI[where x=A] simp: borel_of_subtopology)
qed

corollary(in standard_borel) uncountable_isomorphic_to_Hilbert_cube:
  assumes "uncountable (space M)"
  shows "Hilbert_cube measurable_isomorphic M"
proof -
  obtain A B where AB:
   "M measurable_isomorphic (restrict_space Hilbert_cube A)" "Cantor_space measurable_isomorphic (restrict_space M B)"
   "A \<in> sets Hilbert_cube""B \<in> sets M" 
    using embedding_into_Hilbert_cube embedding_from_Cantor_space[OF assms] by auto
  show ?thesis
    by(rule measurable_isomorphic_antisym[OF AB measurable_isomorphic_sym[OF Cantor_space_isomorphic_to_Hilbert_cube]])
qed

corollary(in standard_borel) uncountable_isomorphic_to_real:
  assumes "uncountable (space M)"
  shows "M measurable_isomorphic (borel :: real measure)"
proof -
  interpret r: standard_borel_ne "borel :: real measure"
    by simp
  show ?thesis
    by(auto intro!: measurable_isomorphic_trans[OF measurable_isomorphic_sym[OF uncountable_isomorphic_to_Hilbert_cube[OF assms]] r.uncountable_isomorphic_to_Hilbert_cube] simp: uncountable_UNIV_real)
qed

lemma(in standard_borel) isomorphic_subset_real:
  assumes "A \<in> sets (borel :: real measure)" "uncountable A"
  obtains B where "B \<in> sets borel" "B \<subseteq> A" "M measurable_isomorphic restrict_space borel B"
proof(cases "countable (space M)")
  assume count:"countable (space M)"
  have "\<exists>B\<subseteq>A. space M \<approx> B"
  proof(cases "finite (space M)")
    assume fin:"finite (space M)"
    then obtain B where B:"card B = card (space M)" "finite B" "B \<subseteq> A"
      by (meson assms(2) countable_finite infinite_arbitrarily_large)
    thus ?thesis
      using fin by(auto intro!: exI[where x=B] simp:eqpoll_iff_card)
  next
    assume inf:"infinite (space M)"
    obtain B where B: "B \<subseteq> A" "countable B" "infinite B"
      using assms(2) countable_finite infinite_countable_subset' that by auto
    thus ?thesis
      using bij_betw_from_nat_into[OF count inf] bij_betw_from_nat_into[OF B(2,3)]
      by (meson eqpoll_def eqpoll_sym eqpoll_trans)
  qed
  then obtain B where B:"B \<subseteq> A" "space M \<approx> B" "countable B"
    by (metis countable_eqpoll eqpoll_sym count)
  then obtain f where f:"bij_betw f (space M) B"
    using eqpoll_def by blast
  have 1:"C \<in> sets borel" if C:"C \<subseteq> B" for C
  proof -
    have "C = (\<Union>c\<in>C. {c})"
      by auto
    also have "... \<in> sets borel"
      using B C by(intro sets.countable_UN') (auto simp: countable_subset)
    finally show ?thesis .
  qed
  have 2:"sets M = sets (count_space (space M))"
    by (simp add: countable_discrete_space count)
  have 3:"sets (restrict_space borel B) = sets (count_space B)"
    using 1 by(auto simp: sets_restrict_space)
  have [simp]:"measurable M (restrict_space borel B) = measurable (count_space (space M)) (count_space B)"
    "measurable (restrict_space borel B) M = measurable (count_space B) (count_space (space M))"
    using 2 3 by(auto intro!: measurable_cong_sets)
  have "M measurable_isomorphic restrict_space borel B"
    using bij_betw_the_inv_into[OF f] f by(auto simp: measurable_isomorphic_def measurable_isomorphic_map_def space_restrict_space intro!: exI[where x=f] dest: bij_betwE)
  with 1 B that show ?thesis
    by blast
next
  assume "uncountable (space M)"
  then have "M measurable_isomorphic (borel :: real measure)"
    using uncountable_isomorphic_to_real by blast
  moreover have "restrict_space borel A measurable_isomorphic (borel :: real measure)"
    by(auto intro!: standard_borel.uncountable_isomorphic_to_real standard_borel.standard_borel_restrict_space[OF standard_borel_ne.standard_borel] simp: assms space_restrict_space)
  ultimately have "M measurable_isomorphic restrict_space borel A"
    using measurable_isomorphic_sym measurable_isomorphic_trans by blast
  with assms(1) that show ?thesis
    by blast
qed

lemma(in standard_borel) countable_isomorphic_to_subset_real:
  assumes "countable (space M)"
  obtains A :: "real set"
  where "countable A" "A \<in> sets borel" "M measurable_isomorphic restrict_space borel A"
proof -
  obtain A :: "real set" where A:"A \<in> sets borel" "M measurable_isomorphic restrict_space borel A"
    using isomorphic_subset_real[of UNIV] uncountable_UNIV_real by auto
  moreover have "countable A"
    using measurable_isomorphic_cardinality_eq[OF A(2)] assms(1)
    by(simp add: space_restrict_space countable_eqpoll[OF _ eqpoll_sym])
  ultimately show ?thesis
    using that by blast
qed

theorem Borel_isomorphism_theorem:
  assumes "standard_borel M" "standard_borel N"
  shows "space M \<approx> space N \<longleftrightarrow> M measurable_isomorphic N"
proof
  assume h:"space M \<approx> space N"
  interpret M: standard_borel M by fact
  interpret N: standard_borel N by fact
  consider "countable (space M)" "countable (space N)" | "uncountable (space M)" "uncountable (space N)"
    by (meson countable_eqpoll eqpoll_sym h)
  thus "M measurable_isomorphic N"
  proof cases
    case 1
    then have 2:"sets M = sets (count_space (space M))" "sets N = sets (count_space (space N))"
      by (simp_all add: M.countable_discrete_space N.countable_discrete_space)
    show ?thesis
      by(simp add: measurable_isomorphic_sets_cong[OF 2] measurable_isomorphic_count_spaces h)
  next
    case 2
    then have "M measurable_isomorphic (borel :: real measure)" "N measurable_isomorphic (borel :: real measure)"
      by(simp_all add: M.uncountable_isomorphic_to_real N.uncountable_isomorphic_to_real)
    thus ?thesis
      using measurable_isomorphic_sym measurable_isomorphic_trans by blast
  qed
qed(rule measurable_isomorphic_cardinality_eq)

definition to_real_on :: "'a measure \<Rightarrow> 'a \<Rightarrow> real" where
"to_real_on M \<equiv> (if uncountable (space M) then (SOME f. measurable_isomorphic_map M (borel :: real measure) f) else (real \<circ> to_nat_on (space M)))"

definition from_real_into :: "'a measure \<Rightarrow> real \<Rightarrow> 'a" where
"from_real_into M \<equiv> (if uncountable (space M) then the_inv_into (space M) (to_real_on M) else (\<lambda>r. from_nat_into (space M) (nat \<lfloor>r\<rfloor>)))"

context standard_borel
begin

abbreviation "to_real   \<equiv> to_real_on M"
abbreviation "from_real \<equiv> from_real_into M"

lemma to_real_def_countable:
  assumes "countable (space M)"
  shows "to_real = (\<lambda>r. real (to_nat_on (space M) r))"
  using assms by(auto simp: to_real_on_def)

lemma from_real_def_countable:
  assumes "countable (space M)"
  shows "from_real = (\<lambda>r. from_nat_into (space M) (nat \<lfloor>r\<rfloor>))"
  using assms by(simp add: from_real_into_def)

lemma from_real_to_real[simp]:
  assumes "x \<in> space M"
  shows "from_real (to_real x) = x"
proof -
  have [simp]: "space M \<noteq> {}"
    using assms by auto
  consider "countable (space M)" | "uncountable (space M)" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(simp add: to_real_def_countable from_real_def_countable assms)
  next
    case 2
    then obtain f where f: "measurable_isomorphic_map M (borel :: real measure) f"
      using uncountable_isomorphic_to_real by(auto simp: measurable_isomorphic_def)
    have 1:"to_real = Eps (measurable_isomorphic_map M borel)" "from_real = the_inv_into (space M) (Eps (measurable_isomorphic_map M borel))"
      by(simp_all add: to_real_on_def 2 from_real_into_def)
    show ?thesis
      unfolding 1
      by(rule someI2[of "measurable_isomorphic_map M (borel :: real measure)" f,OF f])
        (meson assms bij_betw_imp_inj_on measurable_isomorphic_map_def the_inv_into_f_f)
  qed
qed

lemma to_real_measurable[measurable]:
 "to_real \<in> M \<rightarrow>\<^sub>M borel"
proof(cases "countable (space M)")
  case 1:True
  then have "sets M = Pow (space M)"
    by(rule countable_discrete_space)
  then show ?thesis
    by(simp add: to_real_def_countable 1 borel_measurableI_le)
next
  case 1:False
  then obtain f where f: "measurable_isomorphic_map M (borel :: real measure) f"
    using uncountable_isomorphic_to_real by(auto simp: measurable_isomorphic_def)
  have 2:"to_real = Eps (measurable_isomorphic_map M borel)"
    by(simp add: to_real_on_def 1 from_real_into_def)
  show ?thesis
    unfolding 2
    by(rule someI2[of "measurable_isomorphic_map M (borel :: real measure)" f,OF f],simp add: measurable_isomorphic_map_def)
qed

lemma from_real_measurable':
  assumes "space M \<noteq> {}"
  shows "from_real \<in> borel \<rightarrow>\<^sub>M M"
proof(cases "countable (space M)")
  case 1:True
  then have 2:"sets M = Pow (space M)"
    by(rule countable_discrete_space)
  have [measurable]:"from_nat_into (space M) \<in> count_space UNIV \<rightarrow>\<^sub>M M"
    using from_nat_into[OF assms] by auto
  show ?thesis
    by(simp add: from_real_def_countable 1 borel_measurableI_le)
next
  case 2:False
  then obtain f where f: "measurable_isomorphic_map M (borel :: real measure) f"
    using uncountable_isomorphic_to_real by(auto simp: measurable_isomorphic_def)
  have 1: "from_real = the_inv_into (space M) (Eps (measurable_isomorphic_map M borel))"
    by(simp add: to_real_on_def 2 from_real_into_def)
  show ?thesis
    unfolding 1
    by(rule someI2[of "measurable_isomorphic_map M (borel :: real measure)" f,OF f],simp add: measurable_isomorphic_map_def)
qed

lemma to_real_from_real:
  assumes "uncountable (space M)"
  shows "to_real (from_real r) = r"
proof -
  obtain f where f: "measurable_isomorphic_map M (borel :: real measure) f"
    using assms uncountable_isomorphic_to_real by(auto simp: measurable_isomorphic_def)
  have 1:"to_real = Eps (measurable_isomorphic_map M borel)" "from_real = the_inv_into (space M) (Eps (measurable_isomorphic_map M borel))"
    by(simp_all add: to_real_on_def assms from_real_into_def)
  show ?thesis
    unfolding 1
    by(rule someI2[of "measurable_isomorphic_map M (borel :: real measure)" f,OF f])
      (metis UNIV_I f_the_inv_into_f_bij_betw measurable_isomorphic_map_def space_borel)
qed

end

lemma(in standard_borel_ne) from_real_measurable[measurable]: "from_real \<in> borel \<rightarrow>\<^sub>M M"
  by(simp add: from_real_measurable' space_ne)

end