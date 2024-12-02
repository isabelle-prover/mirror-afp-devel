(*
  Title:  Example Completeness Proof for a Propositional Sequent Calculus
  Author: Asta Halkjær From
*)

chapter \<open>Example: Propositional Sequent Calculus\<close>

theory Example_Propositional_SC imports Derivations begin

section \<open>Syntax\<close>

datatype 'p fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>'p fm\<close> \<open>'p fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym 'p model = \<open>'p \<Rightarrow> bool\<close>

fun semantics :: \<open>'p model \<Rightarrow> 'p fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>S\<close> 50) where
  \<open>_ \<Turnstile>\<^sub>S \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>I \<Turnstile>\<^sub>S \<^bold>\<cdot>P \<longleftrightarrow> I P\<close>
| \<open>I \<Turnstile>\<^sub>S p \<^bold>\<longrightarrow> q \<longleftrightarrow> I \<Turnstile>\<^sub>S p \<longrightarrow> I \<Turnstile>\<^sub>S q\<close>

section \<open>Calculus\<close>

inductive Calculus :: \<open>'p fm list \<Rightarrow> 'p fm list \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>S\<close> 50) where
  Axiom [simp]: \<open>p # A \<turnstile>\<^sub>S p # B\<close>
| FlsL [simp]: \<open>\<^bold>\<bottom> # A \<turnstile>\<^sub>S B\<close>
| FlsR [elim]: \<open>A \<turnstile>\<^sub>S \<^bold>\<bottom> # B \<Longrightarrow> A \<turnstile>\<^sub>S B\<close>
| ImpL [intro]: \<open>A \<turnstile>\<^sub>S p # B \<Longrightarrow> q # A \<turnstile>\<^sub>S B \<Longrightarrow> (p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>S B\<close>
| ImpR [intro]: \<open>p # A \<turnstile>\<^sub>S q # B \<Longrightarrow> A \<turnstile>\<^sub>S (p \<^bold>\<longrightarrow> q) # B\<close>
| Cut: \<open>A \<turnstile>\<^sub>S [p] \<Longrightarrow> p # A \<turnstile>\<^sub>S B \<Longrightarrow> A \<turnstile>\<^sub>S B\<close>
| WeakL: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> set A \<subseteq> set A' \<Longrightarrow> A' \<turnstile>\<^sub>S B\<close>
| WeakR: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> set B \<subseteq> set B' \<Longrightarrow> A \<turnstile>\<^sub>S B'\<close>

lemma Boole: \<open>\<^bold>\<not> p # A \<turnstile>\<^sub>S [] \<Longrightarrow> A \<turnstile>\<^sub>S [p]\<close>
  by (meson Axiom Cut ImpL ImpR WeakR set_subset_Cons)

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> \<forall>q \<in> set A. I \<Turnstile>\<^sub>S q \<Longrightarrow> \<exists>p \<in> set B. I \<Turnstile>\<^sub>S p\<close>
  by (induct A B rule: Calculus.induct) auto

corollary soundness': \<open>[] \<turnstile>\<^sub>S [p] \<Longrightarrow> I \<Turnstile>\<^sub>S p\<close>
  using soundness by fastforce

corollary \<open>\<not> [] \<turnstile>\<^sub>S []\<close>
  using soundness by fastforce

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>'p fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>S [\<^bold>\<bottom>]\<close>

interpretation MCS_No_Witness_UNIV consistent
proof
  show \<open>infinite (UNIV :: 'p fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Derivations_Cut_MCS consistent \<open>\<lambda>A p. A \<turnstile>\<^sub>S [p]\<close>
proof
  fix A B and p :: \<open>'p fm\<close>
  assume \<open>A \<turnstile>\<^sub>S [p]\<close> \<open>set A = set B\<close>
  then show \<open>B \<turnstile>\<^sub>S [p]\<close>
    using WeakL by blast
next
  fix S :: \<open>'p fm set\<close>
  show \<open>consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile>\<^sub>S [q]))\<close>
    unfolding consistent_def using Cut FlsL by blast
next
  fix A and p :: \<open>'p fm\<close>
  assume \<open>p \<in> set A\<close>
  then show \<open>A \<turnstile>\<^sub>S [p]\<close>
    by (metis Axiom WeakL set_ConsD subsetI)
next
  fix A B and p q :: \<open>'p fm\<close>
  assume \<open>A \<turnstile>\<^sub>S [p]\<close> \<open>p # B \<turnstile>\<^sub>S [q]\<close>
  then have \<open>A @ B \<turnstile>\<^sub>S [p]\<close> \<open>p # A @ B \<turnstile>\<^sub>S [q]\<close>
    by (fastforce intro: WeakL)+
  then show \<open>A @ B \<turnstile>\<^sub>S [q]\<close>
    using Cut by blast
qed

interpretation Derivations_Bot consistent \<open>\<lambda>A p. A \<turnstile>\<^sub>S [p]\<close> \<open>\<^bold>\<bottom>\<close>
proof
  show \<open>\<And>A r. A \<turnstile>\<^sub>S [\<^bold>\<bottom>] \<Longrightarrow> A \<turnstile>\<^sub>S [r]\<close>
    using Cut FlsL by blast
qed

interpretation Derivations_Imp consistent \<open>\<lambda>A p. A \<turnstile>\<^sub>S [p]\<close> \<open>\<lambda>p q. p \<^bold>\<longrightarrow> q\<close>
proof
  show \<open>\<And>A p q. A \<turnstile>\<^sub>S [p] \<Longrightarrow> A \<turnstile>\<^sub>S [p \<^bold>\<longrightarrow> q] \<Longrightarrow> A \<turnstile>\<^sub>S [q]\<close>
    by (meson Axiom Cut ImpL)
qed fast+

section \<open>Truth Lemma\<close>

abbreviation canonical :: \<open>'p fm set \<Rightarrow> 'p model\<close> (\<open>\<M>\<^sub>S\<close>) where
  \<open>\<M>\<^sub>S(S) \<equiv> \<lambda>P. \<^bold>\<cdot>P \<in> S\<close>

fun semics :: \<open>'p model \<Rightarrow> ('p model \<Rightarrow> 'p fm \<Rightarrow> bool) \<Rightarrow> 'p fm \<Rightarrow> bool\<close>
  (\<open>_ \<lbrakk>_\<rbrakk>\<^sub>S _\<close> [55, 0, 55] 55) where
  \<open>_ \<lbrakk>_\<rbrakk>\<^sub>S \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>I \<lbrakk>_\<rbrakk>\<^sub>S \<^bold>\<cdot>P \<longleftrightarrow> I P\<close>
| \<open>I \<lbrakk>\<R>\<rbrakk>\<^sub>S p \<^bold>\<longrightarrow> q \<longleftrightarrow> \<R> I p \<longrightarrow> \<R> I q\<close>

fun rel :: \<open>'p fm set \<Rightarrow> 'p model \<Rightarrow> 'p fm \<Rightarrow> bool\<close> (\<open>\<R>\<^sub>S\<close>) where
  \<open>\<R>\<^sub>S(S) _ p \<longleftrightarrow> p \<in> S\<close>

theorem saturated_model:
  assumes \<open>\<And>p. \<forall>M\<in>{\<M>\<^sub>S(S)}. M \<lbrakk>\<R>\<^sub>S(S)\<rbrakk>\<^sub>S p = \<R>\<^sub>S(S) M p\<close> \<open>M \<in> {\<M>\<^sub>S(S)}\<close>
  shows \<open>\<R>\<^sub>S(S) M p \<longleftrightarrow> M \<Turnstile>\<^sub>S p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms(1)[of x] assms(2) by (cases x) simp_all
qed

theorem saturated_MCS:
  assumes \<open>MCS S\<close> \<open>M \<in> {\<M>\<^sub>S(S)}\<close>
  shows \<open>M \<lbrakk>\<R>\<^sub>S(S)\<rbrakk>\<^sub>S p \<longleftrightarrow> \<R>\<^sub>S(S) M p\<close>
  using assms by (cases p) auto

interpretation Truth_No_Witness semics semantics \<open>\<lambda>S. {\<M>\<^sub>S(S)}\<close> rel consistent
proof
  fix p and M :: \<open>'p model\<close>
  show \<open>(M \<Turnstile>\<^sub>S p) = M \<lbrakk>(\<Turnstile>\<^sub>S)\<rbrakk>\<^sub>S p\<close>
    by (induct p) auto
qed (use saturated_model saturated_MCS in blast)+

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M. (\<forall>q \<in> X. M \<Turnstile>\<^sub>S q) \<longrightarrow> M \<Turnstile>\<^sub>S p\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>S [p]\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>S [p]\<close>
  then have *: \<open>\<forall>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<longrightarrow> \<not> A \<turnstile>\<^sub>S [\<^bold>\<bottom>]\<close>
    using derive_split1 botE Boole FlsR by (metis (full_types) insert_is_Un subset_insert_iff)

  let ?X = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?S = \<open>Extend ?X\<close>

  have \<open>consistent ?X\<close>
    unfolding consistent_def using * .
  then have \<open>MCS ?S\<close>
    using MCS_Extend' by blast
  then have \<open>p \<in> ?S \<longleftrightarrow> \<M>\<^sub>S ?S \<Turnstile>\<^sub>S p\<close> for p
    using truth_lemma by fastforce
  then have \<open>p \<in> ?X \<longrightarrow> \<M>\<^sub>S ?S \<Turnstile>\<^sub>S p\<close> for p
    using Extend_subset by blast
  then have \<open>\<M>\<^sub>S ?S \<Turnstile>\<^sub>S \<^bold>\<not> p\<close> \<open>\<forall>q \<in> X. \<M>\<^sub>S ?S \<Turnstile>\<^sub>S q\<close>
    by blast+
  moreover from this have \<open>\<M>\<^sub>S ?S \<Turnstile>\<^sub>S p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>'p fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M. M \<Turnstile>\<^sub>S p\<close>

theorem completeness:
  assumes \<open>valid p\<close>
  shows \<open>[] \<turnstile>\<^sub>S [p]\<close>
  using assms strong_completeness[where X=\<open>{}\<close>] by auto

theorem main: \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>S [p]\<close>
  using completeness soundness' by blast

end
