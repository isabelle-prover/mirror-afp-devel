(*
  Title:  Example Completeness Proof for a Propositional Tableau Calculus
  Author: Asta Halkjær From
*)

chapter \<open>Example: Propositional Tableau Calculus\<close>

theory Example_Propositional_Tableau imports Refutations begin

section \<open>Syntax\<close>

datatype 'p fm
  = Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Neg \<open>'p fm\<close> (\<open>\<^bold>\<not> _\<close> [70] 70)
  | Imp \<open>'p fm\<close> \<open>'p fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)

section \<open>Semantics\<close>

type_synonym 'p model = \<open>'p \<Rightarrow> bool\<close>

fun semantics :: \<open>'p model \<Rightarrow> 'p fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>T\<close> 50) where
  \<open>I \<Turnstile>\<^sub>T \<^bold>\<cdot>P \<longleftrightarrow> I P\<close>
| \<open>I \<Turnstile>\<^sub>T \<^bold>\<not> p \<longleftrightarrow> \<not> I \<Turnstile>\<^sub>T p\<close>
| \<open>I \<Turnstile>\<^sub>T p \<^bold>\<longrightarrow> q \<longleftrightarrow> I \<Turnstile>\<^sub>T p \<longrightarrow> I \<Turnstile>\<^sub>T q\<close>

section \<open>Calculus\<close>

inductive Calculus :: \<open>'p fm list \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>T _\<close> [50] 50) where
  Axiom [simp]: \<open>\<turnstile>\<^sub>T \<^bold>\<cdot>P # \<^bold>\<not> \<^bold>\<cdot>P # A\<close>
| NegI [intro]: \<open>\<turnstile>\<^sub>T p # A \<Longrightarrow> \<turnstile>\<^sub>T \<^bold>\<not> \<^bold>\<not> p # A\<close>
| ImpP [intro]: \<open>\<turnstile>\<^sub>T \<^bold>\<not> p # A \<Longrightarrow> \<turnstile>\<^sub>T q # A \<Longrightarrow> \<turnstile>\<^sub>T (p \<^bold>\<longrightarrow> q) # A\<close>
| ImpN [intro]: \<open>\<turnstile>\<^sub>T p # \<^bold>\<not> q # A \<Longrightarrow> \<turnstile>\<^sub>T \<^bold>\<not> (p \<^bold>\<longrightarrow> q) # A\<close>
| Weak: \<open>\<turnstile>\<^sub>T A \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> \<turnstile>\<^sub>T B\<close>

lemma Weak2:
  assumes \<open>\<turnstile>\<^sub>T p # A\<close> \<open>\<turnstile>\<^sub>T q # B\<close>
  shows \<open>\<turnstile>\<^sub>T p # A @ B \<and> \<turnstile>\<^sub>T q # A @ B\<close>
  using assms Weak[where A=\<open>_ # _\<close> and B=\<open>_ # A @ B\<close>] by fastforce

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile>\<^sub>T A \<Longrightarrow> \<exists>p \<in> set A. \<not> I \<Turnstile>\<^sub>T p\<close>
  by (induct A rule: Calculus.induct) auto

corollary soundness': \<open>\<turnstile>\<^sub>T [\<^bold>\<not> p] \<Longrightarrow> I \<Turnstile>\<^sub>T p\<close>
  using soundness by fastforce

corollary \<open>\<not> \<turnstile>\<^sub>T []\<close>
  using soundness by fastforce

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>'p fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> \<turnstile>\<^sub>T A\<close>

interpretation MCS_No_Witness_UNIV consistent
proof
  show \<open>infinite (UNIV :: 'p fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Refutations_MCS consistent Calculus
proof
  fix A B :: \<open>'p fm list\<close>
  assume \<open>\<turnstile>\<^sub>T A\<close> \<open>set A = set B\<close>
  then show \<open>\<turnstile>\<^sub>T B\<close>
    using Weak by blast
next
  fix S :: \<open>'p fm set\<close>
  show \<open>consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> \<turnstile>\<^sub>T A)\<close>
    unfolding consistent_def ..
qed

section \<open>Truth Lemma\<close>

abbreviation (input) canonical :: \<open>'p fm set \<Rightarrow> 'p model\<close> (\<open>\<M>\<^sub>T\<close>) where
  \<open>\<M>\<^sub>T(S) \<equiv> \<lambda>P. \<^bold>\<cdot>P \<in> S\<close>

locale Hintikka =
  fixes H :: \<open>'a fm set\<close>
  assumes AxiomH: \<open>\<And>P. \<^bold>\<cdot>P \<in> H \<Longrightarrow> \<^bold>\<not> \<^bold>\<cdot>P \<in> H \<Longrightarrow> False\<close>
    and NegIH: \<open>\<And>p. \<^bold>\<not> \<^bold>\<not> p \<in> H \<Longrightarrow> p \<in> H\<close>
    and ImpPH: \<open>\<And>p q. p \<^bold>\<longrightarrow> q \<in> H \<Longrightarrow> \<^bold>\<not> p \<in> H \<or> q \<in> H\<close>
    and ImpNH: \<open>\<And>p q. \<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> H \<Longrightarrow> p \<in> H \<and> \<^bold>\<not> q \<in> H\<close>

lemma Hintikka_model:
  assumes \<open>Hintikka H\<close>
  shows \<open>(p \<in> H \<longrightarrow> \<M>\<^sub>T(H) \<Turnstile>\<^sub>T p) \<and> (\<^bold>\<not> p \<in> H \<longrightarrow> \<not> \<M>\<^sub>T(H) \<Turnstile>\<^sub>T p)\<close>
  using assms by (induct p) (unfold Hintikka_def semantics.simps; blast)+

lemma MCS_Hintikka:
  assumes \<open>MCS H\<close>
  shows \<open>Hintikka H\<close>
proof
  fix P
  assume \<open>\<^bold>\<cdot>P \<in> H\<close> \<open>\<^bold>\<not> \<^bold>\<cdot>P \<in> H\<close>
  then have \<open>set [\<^bold>\<cdot>P, \<^bold>\<not> \<^bold>\<cdot>P] \<subseteq> H\<close>
    by simp
  moreover have \<open>\<turnstile>\<^sub>T [\<^bold>\<cdot>P, \<^bold>\<not> \<^bold>\<cdot>P]\<close>
    by simp
  ultimately show False
    using assms unfolding consistent_def by blast
next
  fix p
  assume \<open>\<^bold>\<not> \<^bold>\<not> p \<in> H\<close>
  then show \<open>p \<in> H\<close>
    using assms MCS_refute by blast
next
  fix p q
  assume *: \<open>p \<^bold>\<longrightarrow> q \<in> H\<close>
  show \<open>\<^bold>\<not> p \<in> H \<or> q \<in> H\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<^bold>\<not> p \<in> H \<or> q \<in> H)\<close>
    then have \<open>\<^bold>\<not> p \<notin> H\<close> \<open>q \<notin> H\<close>
      by blast+
    then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T \<^bold>\<not> p # A\<close> \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T q # A\<close>
      using assms MCS_refute by blast+
    then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T \<^bold>\<not> p # A \<and> \<turnstile>\<^sub>T q # A\<close>
      using Weak2[where p=\<open>\<^bold>\<not> p\<close> and q=q] by (metis Un_least set_append)
    then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T (p \<^bold>\<longrightarrow> q) # A\<close>
      by blast
    then have \<open>p \<^bold>\<longrightarrow> q \<notin> H\<close>
      using assms unfolding consistent_def by auto
    then show False
      using * ..
  qed
next
  fix p q
  assume *: \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> H\<close>
  show \<open>p \<in> H \<and> \<^bold>\<not> q \<in> H\<close>
  proof (rule ccontr)
    assume \<open>\<not> (p \<in> H \<and> \<^bold>\<not> q \<in> H)\<close>
    then consider \<open>p \<notin> H\<close> | \<open>\<^bold>\<not> q \<notin> H\<close>
      by blast
    then show False
    proof cases
      case 1
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T p # A\<close>
        using assms MCS_refute by blast
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T p # \<^bold>\<not> q # A\<close>
        using Weak[where B=\<open>p # \<^bold>\<not> q # _\<close>] by fastforce
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T \<^bold>\<not> (p \<^bold>\<longrightarrow> q) # A\<close>
        by fast
      then have \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<notin> H\<close>
        using assms unfolding consistent_def by auto
      then show False
        using * ..
    next
      case 2
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T \<^bold>\<not> q # A\<close>
        using assms MCS_refute by blast
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T p # \<^bold>\<not> q # A\<close>
        using Weak by (metis set_subset_Cons)
      then have \<open>\<exists>A. set A \<subseteq> H \<and> \<turnstile>\<^sub>T \<^bold>\<not> (p \<^bold>\<longrightarrow> q) # A\<close>
        by fast
      then have \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<notin> H\<close>
        using assms unfolding consistent_def by auto
      then show False
        using * ..
    qed
  qed
qed

lemma truth_lemma:
  assumes \<open>MCS H\<close> \<open>p \<in> H\<close>
  shows \<open>\<M>\<^sub>T(H) \<Turnstile>\<^sub>T p\<close>
  using Hintikka_model MCS_Hintikka assms by blast

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M. (\<forall>q \<in> X. M \<Turnstile>\<^sub>T q) \<longrightarrow> M \<Turnstile>\<^sub>T p\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> \<turnstile>\<^sub>T \<^bold>\<not> p # A\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> \<turnstile>\<^sub>T \<^bold>\<not> p # A\<close>
  then have *: \<open>\<forall>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<longrightarrow> \<not> \<turnstile>\<^sub>T A\<close>
    using refute_split1 by (metis Weak insert_is_Un set_subset_Cons subset_insert)

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using * by blast
  then have \<open>MCS ?H\<close>
    using MCS_Extend' by blast
  then have \<open>p \<in> ?H \<longrightarrow> \<M>\<^sub>T(?H) \<Turnstile>\<^sub>T p\<close> for p
    using truth_lemma by blast
  then have \<open>p \<in> ?S \<longrightarrow> \<M>\<^sub>T(?H) \<Turnstile>\<^sub>T p\<close> for p
    using Extend_subset by blast
  then have \<open>\<M>\<^sub>T(?H) \<Turnstile>\<^sub>T \<^bold>\<not> p\<close> \<open>\<forall>q \<in> X. \<M>\<^sub>T(?H) \<Turnstile>\<^sub>T q\<close>
    by blast+
  moreover from this have \<open>\<M>\<^sub>T(?H) \<Turnstile>\<^sub>T p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>'p fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M. M \<Turnstile>\<^sub>T p\<close>

theorem completeness:
  assumes \<open>valid p\<close>
  shows \<open>\<turnstile>\<^sub>T [\<^bold>\<not> p]\<close>
  using assms strong_completeness[where X=\<open>{}\<close>] by auto

theorem main: \<open>valid p \<longleftrightarrow> \<turnstile>\<^sub>T [\<^bold>\<not> p]\<close>
  using completeness soundness' by blast

end
