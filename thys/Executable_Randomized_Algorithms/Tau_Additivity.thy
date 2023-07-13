section \<open>$\tau$-Additivity\<close>

theory Tau_Additivity
  imports "HOL-Analysis.Regularity"
begin

text \<open>In this section we show $\tau$-additivity for measures, that are compatible with a
second-countable topology. This will be essential for the verification of the Scott-continuity
of the monad morphisms. To understand the property, let us recall that for general countable chains
of measurable sets, it is possible to deduce that the supremum
of the measures of the sets is equal to the measure of the union of the family:
\[
  \mu \left( \bigcup{\mathcal X} \right) = \sup_{X \in \mathcal X} \mu (X)
\]
this is shown in @{thm [source] SUP_emeasure_incseq}.

It is possible to generalize that to arbitrary chains
\footnote{More generally families closed under pairwise unions.} of open sets for some measures
without the restriction of countability, such measures are called
$\tau$-additive~\cite{fremlin2000}.

In the following this property is derived for measures that are at least borel (i.e. every open
set is measurable) in a complete second-countable topology. The result is an immediate consequence
of inner-regularity. The latter is already verified in @{theory "HOL-Analysis.Regularity"}.\<close>

definition "op_stable op F = (\<forall>x y. x \<in> F \<and> y \<in> F \<longrightarrow> op x y \<in> F)"

lemma op_stableD:
  assumes "op_stable op F"
  assumes "x \<in> F" "y \<in> F"
  shows "op x y \<in> F"
  using assms unfolding op_stable_def by auto

lemma tau_additivity_aux:
  fixes M::"'a::{second_countable_topology, complete_space} measure"
  assumes sb: "sets M = sets borel"
  assumes fin: "emeasure M (space M) \<noteq> \<infinity>"
  assumes of: "\<And>a. a \<in> A \<Longrightarrow> open a"
  assumes ud: "op_stable (\<union>) A"
  shows "emeasure M (\<Union>A) = (SUP a \<in> A. emeasure M a)" (is "?L = ?R")
proof (cases "A \<noteq> {}")
  case True

  have "open (\<Union>A)" using of by auto
  hence "\<Union>A \<in> sets borel" by simp
  hence usets: "\<Union>A \<in> sets M" using assms(1) by simp

  have 0:"a \<in> sets borel" if "a \<in> A" for a
    using of that by simp

  have 1:"\<Union>T \<in> A" if "finite T" "T \<noteq> {}" "T \<subseteq> A" for T
    using that op_stableD[OF ud] by (induction T rule:finite_ne_induct) auto

  have 2:"emeasure M K \<le> ?R" if K_def: "compact K" "K \<subseteq> \<Union>A" for K
  proof (cases "K \<noteq> {}")
    case True
    obtain T where T_def: "K \<subseteq> \<Union>T" "T \<subseteq> A" "finite T"
      using compactE[OF K_def of] that by metis
    have T_ne: "T \<noteq> {}" using T_def(1) True by auto
    define t where "t = \<Union>T"
    have t_in: "t \<in> A"
      unfolding t_def by (intro 1 T_ne T_def)
    have "K \<subseteq> t"
      unfolding t_def using T_def by simp
    hence "emeasure M K \<le> emeasure M t"
      using 0 sb t_in by (intro emeasure_mono) auto
    also have "... \<le> ?R"
      using t_in by (intro cSup_upper) auto
    finally show ?thesis
      by simp
  next
    case False
    hence "K = {}" by simp
    thus ?thesis by simp
  qed

  have "?L = (SUP K \<in> {K. K \<subseteq> \<Union> A \<and> compact K}. emeasure M K)"
    using usets unfolding sb by (intro inner_regular[OF sb fin]) auto
  also have "... \<le> ?R"
    using 2 by (intro cSup_least) auto
  finally have "?L \<le> ?R" by simp
  moreover have "emeasure M a \<le> emeasure M (\<Union>A)" if "a \<in> A" for a
    using that by (intro emeasure_mono usets) auto
  hence "?R \<le> ?L"
    using True by (intro cSup_least) auto
  ultimately show ?thesis by auto
next
  case False
  thus ?thesis by (simp add:bot_ennreal)
qed

lemma chain_imp_union_stable:
  assumes "Complete_Partial_Order.chain (\<subseteq>) F"
  shows "op_stable (\<union>) F"
proof -
  have "x \<union> y \<in> F" if "x \<in> F" "y \<in> F" for x y
  proof (cases "x \<subseteq> y")
    case True
    then show ?thesis using that sup.absorb2[OF True] by simp
  next
    case False
    hence 0:"y \<subseteq> x"
      using assms that unfolding Complete_Partial_Order.chain_def by auto
    then show ?thesis using that sup.absorb1[OF 0] by simp
  qed
  thus ?thesis
    unfolding op_stable_def by auto
qed

theorem tau_additivity:
  fixes M :: "'a::{second_countable_topology, complete_space} measure"
  assumes sb: "\<And>x. open x \<Longrightarrow> x \<in> sets M"
  assumes fin: "emeasure M (space M) \<noteq> \<infinity>"
  assumes of: "\<And>a. a \<in> A \<Longrightarrow> open a"
  assumes ud: "op_stable (\<union>) A"
  shows "emeasure M (\<Union>A) = (SUP a \<in> A. emeasure M a)" (is "?L = ?R")
proof -
  have "UNIV \<in> sets M"
    using open_UNIV sb by auto
  hence space_M[simp]:"space M = UNIV"
    using sets.sets_into_space by blast

  have id_borel: "(\<lambda>x. x) \<in> M \<rightarrow>\<^sub>M borel"
    using sb by (intro borel_measurableI) auto

  have "open (\<Union>A)" using of by auto
  hence usets: "(\<Union>A) \<in> sets borel" by simp

  define N where "N = distr M borel (\<lambda>x. x)"
  have sets_N: "sets N = sets borel"
    unfolding N_def by simp
  have fin_N: "emeasure N (space N) \<noteq> \<infinity>"
    using fin id_borel unfolding N_def
    by (subst emeasure_distr) auto

  have "?L = emeasure N (\<Union>A)"
    unfolding N_def by (subst emeasure_distr[OF id_borel usets]) auto
  also have "... = (SUP a \<in> A. emeasure N a)"
    by (intro tau_additivity_aux sets_N of ud fin_N) auto
  also have "... = (SUP a\<in>A. emeasure M ((\<lambda>x. x) -` a \<inter> space M))"
    unfolding N_def using of
    by (intro arg_cong[where f="Sup"] image_cong emeasure_distr id_borel) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end