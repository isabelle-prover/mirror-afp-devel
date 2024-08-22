(*  Title:   Lemmas_Coproduct_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> Preliminaries \<close>
theory Lemmas_Coproduct_Measure
  imports "HOL-Probability.Probability"
          "Standard_Borel_Spaces.Abstract_Metrizable_Topology"
begin

(* TODO: Move the following to Standard_Borel_Spaces.Abstract_Metrizable_Topology *)
lemma metrizable_space_metric_space:
  assumes d:"Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean"
  shows "class.metric_space d (\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}) open"
proof -
  interpret Metric_space UNIV d by fact
  show ?thesis
  proof
    show "open U \<longleftrightarrow> (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in \<Sqinter>e\<in>{0<..}. principal {(F, y). d F y < e}.  x' = x \<longrightarrow> y \<in> U)" for U
    proof(subst eventually_INF_base)
      show "a \<in> {0<..} \<Longrightarrow> b \<in> {0<..} \<Longrightarrow> \<exists>x\<in>{0<..}. principal {(F, y). d F y < x} \<le> principal {(F, y). d F y < a} \<sqinter> principal {(F, y). d F y < b}" for a b
        by(auto intro!: bexI[where x="min a b"])
    next
      show "open U \<longleftrightarrow> (\<forall>x\<in>U. \<exists>b\<in>{0<..}. \<forall>\<^sub>F (x', y) in principal {(F, y). d F y < b}. x' = x \<longrightarrow> y \<in> U)"
        by(fastforce simp: openin_mtopology[simplified d(2),simplified] eventually_principal)
    qed simp
  qed(auto simp: triangle')
qed

corollary metrizable_space_metric_space_ex:
  assumes "metrizable_space (euclidean :: 'a :: topological_space topology)"
  shows "\<exists>(d :: 'a \<Rightarrow> 'a \<Rightarrow> real) F. class.metric_space d F open"
proof -
  from assms obtain d :: "'a \<Rightarrow> 'a \<Rightarrow> real" where "Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean"
    by (metis Metric_space.topspace_mtopology metrizable_space_def topspace_euclidean)
  from metrizable_space_metric_space[OF this] show ?thesis
    by blast
qed

lemma completely_metrizable_space_metric_space:
  assumes "Metric_space (UNIV :: 'a ::topological_space set) d" "Metric_space.mtopology UNIV d = euclidean" "Metric_space.mcomplete UNIV d"
  shows "class.complete_space d (\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}) open"
proof -
  interpret Metric_space UNIV d by fact
  interpret m:metric_space d "\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}" "open"
    by(auto intro!: metrizable_space_metric_space assms)
  (* Why do we need the following? *)
  have [simp]:"topological_space.convergent (open :: 'a set \<Rightarrow> bool) = convergent"
  proof
    fix x :: "nat \<Rightarrow> 'a"
    have *:"class.topological_space (open :: 'a set \<Rightarrow> bool)"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def[OF *] topological_space.nhds_def[OF *] convergent_def nhds_def)
  qed
  show ?thesis
    apply unfold_locales
    using assms(3) by(auto simp: mcomplete_def assms(2) MCauchy_def m.Cauchy_def convergent_def)
qed

lemma completely_metrizable_space_metric_space_ex:
  assumes "completely_metrizable_space (euclidean :: 'a :: topological_space topology)"
  shows "\<exists>(d :: 'a \<Rightarrow> 'a \<Rightarrow> real) F. class.complete_space d F open"
proof -
  from assms obtain d :: "'a \<Rightarrow> 'a \<Rightarrow> real" where "Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean" "Metric_space.mcomplete UNIV d"
    by (metis Metric_space.topspace_mtopology completely_metrizable_space_def topspace_euclidean)
  from completely_metrizable_space_metric_space[OF this] show ?thesis
    by blast
qed

subsection \<open> Polishness of Extended Reals and Non-Negative Extended Reals\<close>
text \<open> We instantiate @{class polish_space} for @{typ ereal} and @{typ ennreal} with
       \emph{non-canonical} metrics in order to change the order of @{term infsum}
       using the lemma \isa{infsum{\isacharunderscore}Sigma}.\<close>
instantiation ereal :: metric_space
begin

definition dist_ereal :: "ereal \<Rightarrow> ereal \<Rightarrow> real"
  where "dist_ereal \<equiv> SOME d. Metric_space UNIV d \<and>
                               Metric_space.mtopology UNIV d = euclidean \<and>
                               Metric_space.mcomplete UNIV d"

definition uniformity_ereal :: "(ereal \<times> ereal) filter"
  where "uniformity_ereal \<equiv> \<Sqinter>e\<in>{0<..}. principal {(x,y). dist x y < e}"

instance
proof -
  let ?open = "open :: ereal set \<Rightarrow> bool"
  interpret c:complete_space dist uniformity ?open
  proof -
    have "\<exists>d. Metric_space (UNIV :: ereal set) d \<and>
              Metric_space.mtopology UNIV d = euclidean \<and>
              Metric_space.mcomplete UNIV d"
      by (metis Polish_space_ereal Metric_space.topspace_mtopology Polish_space_def completely_metrizable_space_def topspace_euclidean)
    hence "Metric_space (UNIV :: ereal set) dist \<and>
           Metric_space.mtopology (UNIV :: ereal set) dist = euclidean \<and>
           Metric_space.mcomplete (UNIV :: ereal set) dist"
      unfolding dist_ereal_def by(rule someI_ex)
    with completely_metrizable_space_metric_space show "class.complete_space dist uniformity ?open"
      by(fastforce simp: uniformity_ereal_def)
  qed
  have [simp]:"topological_space.convergent ?open = convergent"
  proof
    fix x :: "nat \<Rightarrow> ereal"
    have *:"class.topological_space ?open"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def topological_space.nhds_def * convergent_def nhds_def)
  qed
  show "OFCLASS(ereal, metric_space_class)"
    by standard (use uniformity_ereal_def c.open_uniformity c.dist_triangle2 c.Cauchy_convergent in auto)
qed

end

instantiation ereal :: polish_space
begin

instance
proof
  let ?open = "open :: ereal set \<Rightarrow> bool"
  interpret c:complete_space dist uniformity ?open
  proof -
    have "\<exists>d. Metric_space (UNIV :: ereal set) d \<and>
              Metric_space.mtopology UNIV d = euclidean \<and>
              Metric_space.mcomplete UNIV d"
      by (metis Polish_space_ereal Metric_space.topspace_mtopology Polish_space_def completely_metrizable_space_def topspace_euclidean)
    hence "Metric_space (UNIV :: ereal set) dist \<and>
           Metric_space.mtopology (UNIV :: ereal set) dist = euclidean \<and>
           Metric_space.mcomplete (UNIV :: ereal set) dist"
      unfolding dist_ereal_def by(rule someI_ex)
    with completely_metrizable_space_metric_space show "class.complete_space dist uniformity ?open"
      by(fastforce simp: uniformity_ereal_def)
  qed
  have [simp]:"topological_space.convergent ?open = convergent"
  proof
    fix x :: "nat \<Rightarrow> ereal"
    have *:"class.topological_space ?open"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def topological_space.nhds_def * convergent_def nhds_def)
  qed
  have [simp]:"uniform_space.Cauchy (uniformity :: (ereal \<times> ereal) filter) = Cauchy"
    by(auto simp add: metric_space.Cauchy_def[OF metric_space_axioms] Cauchy_def)
  fix x :: "nat \<Rightarrow> ereal"
  show "Cauchy x \<Longrightarrow> convergent x"
    using c.Cauchy_convergent by(auto simp: Cauchy_def)
qed

end

instantiation ennreal :: metric_space
begin

definition dist_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> real"
  where "dist_ennreal \<equiv> SOME d. Metric_space UNIV d \<and>
                                 Metric_space.mtopology UNIV d = euclidean \<and>
                                 Metric_space.mcomplete UNIV d"

definition uniformity_ennreal :: "(ennreal \<times> ennreal) filter"
  where "uniformity_ennreal \<equiv> \<Sqinter>e\<in>{0<..}. principal {(x,y). dist x y < e}"

instance
proof -
  let ?open = "open :: ennreal set \<Rightarrow> bool"
  interpret c:complete_space dist uniformity ?open
  proof -
    have "\<exists>d. Metric_space (UNIV :: ennreal set) d \<and>
              Metric_space.mtopology UNIV d = euclidean \<and>
              Metric_space.mcomplete UNIV d"
      by (metis Polish_space_ennreal Metric_space.topspace_mtopology Polish_space_def completely_metrizable_space_def topspace_euclidean)
    hence "Metric_space (UNIV :: ennreal set) dist \<and>
           Metric_space.mtopology (UNIV :: ennreal set) dist = euclidean \<and>
           Metric_space.mcomplete (UNIV :: ennreal set) dist"
      unfolding dist_ennreal_def by(rule someI_ex)
    with completely_metrizable_space_metric_space show "class.complete_space dist uniformity ?open"
      by(fastforce simp: uniformity_ennreal_def)
  qed
  have [simp]:"topological_space.convergent ?open = convergent"
  proof
    fix x :: "nat \<Rightarrow> ennreal"
    have *:"class.topological_space ?open"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def[OF *] topological_space.nhds_def[OF *] convergent_def nhds_def)
  qed
  show "OFCLASS(ennreal, metric_space_class)"
    by standard (use uniformity_ennreal_def c.open_uniformity c.dist_triangle2 c.Cauchy_convergent in auto)
qed

end

instantiation ennreal :: polish_space
begin

instance
proof
  let ?open = "open :: ennreal set \<Rightarrow> bool"
  interpret c:complete_space dist uniformity ?open
  proof -
    have "\<exists>d. Metric_space (UNIV :: ennreal set) d \<and>
              Metric_space.mtopology UNIV d = euclidean \<and>
              Metric_space.mcomplete UNIV d"
      by (metis Polish_space_ennreal Metric_space.topspace_mtopology Polish_space_def completely_metrizable_space_def topspace_euclidean)
    hence "Metric_space (UNIV :: ennreal set) dist \<and>
           Metric_space.mtopology (UNIV :: ennreal set) dist = euclidean \<and>
           Metric_space.mcomplete (UNIV :: ennreal set) dist"
      unfolding dist_ennreal_def by(rule someI_ex)
    with completely_metrizable_space_metric_space show "class.complete_space dist uniformity ?open"
      by(fastforce simp: uniformity_ennreal_def)
  qed
  have [simp]:"topological_space.convergent ?open = convergent"
  proof
    fix x :: "nat \<Rightarrow> ennreal"
    have *:"class.topological_space ?open"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def topological_space.nhds_def * convergent_def nhds_def)
  qed
  have [simp]:"uniform_space.Cauchy (uniformity :: (ennreal \<times> ennreal) filter) = Cauchy"
    by(auto simp add: metric_space.Cauchy_def[OF metric_space_axioms] Cauchy_def)
  fix x :: "nat \<Rightarrow> ennreal"
  show "Cauchy x \<Longrightarrow> convergent x"
    using c.Cauchy_convergent by(auto simp: Cauchy_def)
qed

end

subsection \<open> Lemmas for Infinite Sum \<close>
lemma uniformly_continuous_add_ennreal: "isUCont (\<lambda>(x::ennreal, y). x + y)"
proof(safe intro!: compact_uniformly_continuous)
  have "compact (UNIV \<times> UNIV :: (ennreal \<times> ennreal) set)"
    by(intro compact_Times compact_UNIV)
  thus "compact (UNIV :: (ennreal \<times> ennreal) set)"
    by simp
qed(auto intro!: continuous_on_add_ennreal continuous_on_fst continuous_on_snd simp: split_beta')

lemma infsum_eq_suminf:
  assumes "f summable_on UNIV"
  shows "(\<Sum>\<^sub>\<infinity> n\<in>UNIV. f n) = suminf f"
  using has_sum_imp_sums[OF has_sum_infsum[OF assms]]
  by (simp add: sums_iff)

lemma infsum_Sigma_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  shows "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
  by(auto intro!: uniformly_continuous_add_ennreal infsum_Sigma nonneg_summable_on_complete)

lemma infsum_swap_ennreal:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> ennreal"
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
  by(auto intro!: infsum_swap uniformly_continuous_add_ennreal nonneg_summable_on_complete)

lemma has_sum_cmult_right_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "c < \<top>"  "(f has_sum a) A"
  shows "((\<lambda>x. c * f x) has_sum c * a) A"
  using ennreal_tendsto_cmult[OF assms(1)] assms(2)
  by (force simp add: has_sum_def sum_distrib_left)

lemma infsum_cmult_right_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "c < \<top>"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. c * f x) = c * infsum f A"
  by (simp add: assms has_sum_cmult_right_ennreal infsumI nonneg_summable_on_complete)

lemma ennreal_sum_SUP_eq:
  fixes f :: "nat \<Rightarrow> _ \<Rightarrow> ennreal"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> incseq (\<lambda>j. f j x)"
  shows "(\<Sum>i\<in>A. \<Squnion>n. f n i) = (\<Squnion>n. \<Sum>i\<in>A. f n i)"
  using assms
proof induction
  case empty
  then show ?case
    by simp
next
  case ih:(insert x F)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Squnion>n. f n x) + (\<Squnion>n. sum (f n) F)"
      using ih by simp
    also have "... = (\<Squnion>n. f n x + sum (f n) F)"
      using ih by(auto intro!: incseq_sumI2 ennreal_SUP_add[symmetric])
    also have "... = ?rhs"
      using ih by simp
    finally show ?thesis .
  qed
qed 

lemma ennreal_infsum_Sup_eq:
  fixes f :: "nat \<Rightarrow> _ \<Rightarrow> ennreal"
  assumes "\<And>x. x \<in> A \<Longrightarrow> incseq (\<lambda>j. f j x)"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. (SUP j. f j x)) = (SUP j. (\<Sum>\<^sub>\<infinity>x\<in>A. f j x))" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Squnion> (sum (\<lambda>x. \<Squnion>j. f j x) ` {F. finite F \<and> F \<subseteq> A}))"
    by(auto intro!: nonneg_infsum_complete simp: SUP_upper2 assms)
  also have "... = (\<Squnion>A\<in>{F. finite F \<and> F \<subseteq> A}. \<Squnion>j. sum (f j) A)"
    using assms by(auto intro!: SUP_cong ennreal_sum_SUP_eq)
  also have "... = (\<Squnion>j. \<Squnion>A\<in>{F. finite F \<and> F \<subseteq> A}. sum (f j) A)"
    using SUP_commute by fast
  also have "... = ?rhs"
    by(subst nonneg_infsum_complete) (use assms in auto)
  finally show ?thesis .
qed

lemma bounded_infsum_summable:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) < top"
  shows "f summable_on A"
proof(rule nonneg_bdd_above_summable_on)
  from assms(2) obtain K where K:"(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) \<le> ennreal K" "K \<ge> 0"
    using less_top_ennreal by force
  show "bdd_above (sum f ` {F. F \<subseteq> A \<and> finite F})"
  proof(safe intro!: bdd_aboveI[where M=K])
    fix A'
    assume A':"A' \<subseteq> A" "finite A'"
    have "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = (\<Squnion> (sum (\<lambda>x. ennreal (f x)) ` {F. finite F \<and> F \<subseteq> A}))"
      by (simp add: nonneg_infsum_complete)
    also have "... = (\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A}))"
      by(auto intro!: SUP_cong sum_ennreal assms)
    finally have "(\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A})) \<le> ennreal K"
      using K by order
    hence "ennreal (sum f A') \<le> ennreal K"
      by (simp add: A' SUP_le_iff)
    thus "sum f A' \<le> K"
      by (simp add: K(2))
  qed
qed fact

lemma infsum_less_top_dest:
  fixes f :: "_ \<Rightarrow> _::{ordered_comm_monoid_add, topological_comm_monoid_add, t2_space, complete_linorder, linorder_topology}"
  assumes "(\<Sum>\<^sub>\<infinity>x\<in>A. f x) < top" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" "x \<in> A"
  shows "f x < top"
proof(rule ccontr)
  assume f:"\<not> f x < top"
  have "(\<Sum>\<^sub>\<infinity>x\<in>A. f x) = (\<Sum>\<^sub>\<infinity>y\<in>A - {x} \<union> {x}. f y)"
    by(rule arg_cong[where f="infsum _"]) (use assms in auto)
  also have "... = (\<Sum>\<^sub>\<infinity>y\<in>A- {x}. f y) + (\<Sum>\<^sub>\<infinity>y\<in>{x}. f y)"
    using assms(2) by(intro infsum_Un_disjoint) (auto intro!: nonneg_summable_on_complete)
  also have "... =  (\<Sum>\<^sub>\<infinity>y\<in>A- {x}. f y) + top"
    using f top.not_eq_extremum by fastforce
  also have "... = top"
    by(auto intro!: add_top infsum_nonneg assms)
  finally show False
    using assms(1) by simp
qed

lemma infsum_ennreal_eq:
  assumes "f summable_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = ennreal (\<Sum>\<^sub>\<infinity>x\<in>A. f x)"
proof -
  have "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = (\<Squnion> (sum (\<lambda>x. ennreal (f x)) ` {F. finite F \<and> F \<subseteq> A}))"
    by (simp add: nonneg_infsum_complete)
  also have "... = (\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A}))"
    by(auto intro!: SUP_cong sum_ennreal assms)
  also have "... = ennreal (\<Sum>\<^sub>\<infinity>x\<in>A. f x)"
    using infsum_nonneg_is_SUPREMUM_ennreal[OF assms] by simp
  finally show ?thesis .
qed

lemma abs_summable_on_integrable_iff:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "Infinite_Sum.abs_summable_on f A \<longleftrightarrow> integrable (count_space A) f"
  by (simp add: abs_summable_equivalent abs_summable_on_def)

lemma infsum_eq_integral:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "Infinite_Sum.abs_summable_on f A"
  shows "infsum f A = integral\<^sup>L (count_space A) f"
  using assms infsetsum_infsum[of f A,symmetric]
  by(auto simp: abs_summable_on_integrable_iff abs_summable_on_def infsetsum_def)

end