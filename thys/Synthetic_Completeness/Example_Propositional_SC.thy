(*
  Title:  Example Completeness Proof for a Propositional Sequent Calculus
  Author: Asta Halkjær From
*)

chapter \<open>Example: Propositional Sequent Calculus\<close>

theory Example_Propositional_SC imports Derivations begin

section \<open>Syntax\<close>

datatype 'p fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<ddagger>\<close>)
  | Imp \<open>'p fm\<close> \<open>'p fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym 'p model = \<open>'p \<Rightarrow> bool\<close>

fun semantics :: \<open>'p model \<Rightarrow> 'p fm \<Rightarrow> bool\<close> (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  \<open>\<lbrakk>_\<rbrakk> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<lbrakk>I\<rbrakk> (\<^bold>\<ddagger>P) \<longleftrightarrow> I P\<close>
| \<open>\<lbrakk>I\<rbrakk> (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> \<lbrakk>I\<rbrakk> p \<longrightarrow> \<lbrakk>I\<rbrakk> q\<close>

section \<open>Calculus\<close>

inductive Calculus :: \<open>'p fm list \<Rightarrow> 'p fm list \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>S _\<close> [50, 50] 50) where
  Axiom [intro]: \<open>p # A \<turnstile>\<^sub>S p # B\<close>
| FlsL [intro]: \<open>\<^bold>\<bottom> # A \<turnstile>\<^sub>S B\<close>
| FlsR [dest]: \<open>A \<turnstile>\<^sub>S \<^bold>\<bottom> # B \<Longrightarrow> A \<turnstile>\<^sub>S B\<close>
| ImpL [intro]: \<open>A \<turnstile>\<^sub>S p # B \<Longrightarrow> q # A \<turnstile>\<^sub>S B \<Longrightarrow> (p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>S B\<close>
| ImpR [intro]: \<open>p # A \<turnstile>\<^sub>S q # B \<Longrightarrow> A \<turnstile>\<^sub>S (p \<^bold>\<longrightarrow> q) # B\<close>
| Cut [elim]: \<open>A \<turnstile>\<^sub>S p # B \<Longrightarrow> p # C \<turnstile>\<^sub>S D \<Longrightarrow> A @ C \<turnstile>\<^sub>S B @ D\<close>
| WeakenL: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> set A \<subseteq> set A' \<Longrightarrow> A' \<turnstile>\<^sub>S B\<close>
| WeakenR: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> set B \<subseteq> set B' \<Longrightarrow> A \<turnstile>\<^sub>S B'\<close>

lemma Boole: \<open>\<^bold>\<not> p # A \<turnstile>\<^sub>S [] \<Longrightarrow> A \<turnstile>\<^sub>S [p]\<close>
  by (metis Axiom Cut ImpR WeakenR append_self_conv2 self_append_conv set_subset_Cons)

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>S B \<Longrightarrow> \<forall>q \<in> set A. \<lbrakk>I\<rbrakk> q \<Longrightarrow> \<exists>p \<in> set B. \<lbrakk>I\<rbrakk> p\<close>
  by (induct A B rule: Calculus.induct) auto

corollary soundness': \<open>[] \<turnstile>\<^sub>S [p] \<Longrightarrow> \<lbrakk>I\<rbrakk> p\<close>
  using soundness by fastforce

corollary \<open>\<not> ([] \<turnstile>\<^sub>S [])\<close>
  using soundness by fastforce

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>'p fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>S [\<^bold>\<bottom>]\<close>

interpretation MCS_No_Saturation consistent
proof
  fix S S' :: \<open>'p fm set\<close>
  assume \<open>consistent S\<close> \<open>S' \<subseteq> S\<close>
  then show \<open>consistent S'\<close>
    unfolding consistent_def by fast
next
  fix S :: \<open>'p fm set\<close>
  assume \<open>\<not> consistent S\<close>
  then show \<open>\<exists>S'\<subseteq>S. finite S' \<and> \<not> consistent S'\<close>
    unfolding consistent_def by blast
next
  show \<open>infinite (UNIV :: 'p fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed

interpretation Derivations_MCS_Cut \<open>\<lambda>A p. A \<turnstile>\<^sub>S [p]\<close> consistent \<open>\<^bold>\<bottom>\<close>
proof
  fix A B and p :: \<open>'p fm\<close>
  assume \<open>A \<turnstile>\<^sub>S [p]\<close> \<open>set A \<subseteq> set B\<close>
  then show \<open>B \<turnstile>\<^sub>S [p]\<close>
    using WeakenL by blast
next
  fix S :: \<open>'p fm set\<close>
  show \<open>consistent S \<longleftrightarrow> (\<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>S [\<^bold>\<bottom>])\<close>
    unfolding consistent_def ..
next
  fix A and p :: \<open>'p fm\<close>
  assume \<open>p \<in> set A\<close>
  then show \<open>A \<turnstile>\<^sub>S [p]\<close>
    by (metis Axiom WeakenL set_ConsD subsetI)
next
  fix A B and p q :: \<open>'p fm\<close>
  assume \<open>A \<turnstile>\<^sub>S [p]\<close> \<open>p # B \<turnstile>\<^sub>S [q]\<close>
  then show \<open>A @ B \<turnstile>\<^sub>S [q]\<close>
    using Cut by fastforce
qed

section \<open>Truth Lemma\<close>

abbreviation hmodel :: \<open>'p fm set \<Rightarrow> 'p model\<close> where
  \<open>hmodel H \<equiv> \<lambda>P. \<^bold>\<ddagger>P \<in> H\<close>

fun semics :: \<open>'p model \<Rightarrow> ('p model \<Rightarrow> 'p fm \<Rightarrow> bool) \<Rightarrow> 'p fm \<Rightarrow> bool\<close> where
  \<open>semics _ _ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>semics I _ (\<^bold>\<ddagger>P) \<longleftrightarrow> I P\<close>
| \<open>semics I rel (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> rel I p \<longrightarrow> rel I q\<close>

fun rel :: \<open>'p fm set \<Rightarrow> 'p model \<Rightarrow> 'p fm \<Rightarrow> bool\<close> where
  \<open>rel H _ p = (p \<in> H)\<close>

theorem Hintikka_model':
  assumes \<open>\<And>p. semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
  shows \<open>p \<in> H \<longleftrightarrow> \<lbrakk>hmodel H\<rbrakk> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms[of x] by (cases x) simp_all
qed

lemma Hintikka_Extend:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
proof (cases p)
  case Fls
  have \<open>\<^bold>\<bottom> \<notin> H\<close>
    using assms MCS_derive consistent_def by blast
  then show ?thesis
    using Fls by simp
next
  case (Imp p q)
  have \<open>A \<turnstile>\<^sub>S [q] \<Longrightarrow> A \<turnstile>\<^sub>S [p \<^bold>\<longrightarrow> q]\<close> for A
    by (meson ImpR WeakenL set_subset_Cons)
  moreover have \<open>p # A \<turnstile>\<^sub>S [\<^bold>\<bottom>] \<Longrightarrow> A \<turnstile>\<^sub>S [p \<^bold>\<longrightarrow> q]\<close> for A
    by (meson FlsR ImpR WeakenR set_subset_Cons)
  moreover have \<open>A \<turnstile>\<^sub>S [p \<^bold>\<longrightarrow> q] \<Longrightarrow> B \<turnstile>\<^sub>S [p] \<Longrightarrow> A @ B \<turnstile>\<^sub>S [q]\<close> for A B
    using Cut by (metis Axiom ImpL append_Nil append_Nil2)
  ultimately have \<open>(p \<in> H \<longrightarrow> q \<in> H) \<longleftrightarrow> p \<^bold>\<longrightarrow> q \<in> H\<close>
    using assms MCS_derive MCS_derive_fls Axiom
    by (metis append_Cons append_Nil insert_subset list.simps(15))
  then show ?thesis
    using Imp by simp
qed simp

interpretation Truth_No_Saturation consistent semics semantics \<open>\<lambda>H. {hmodel H}\<close> rel
proof
  fix p and M :: \<open>'p model\<close>
  show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> semics M semantics p\<close>
    by (induct p) auto
next
  fix p and H :: \<open>'p fm set\<close> and M :: \<open>'p model\<close>
  assume \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close> \<open>M \<in> {hmodel H}\<close>
  then show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_model' by auto
next
  fix H :: \<open>'p fm set\<close>
  assume \<open>consistent H\<close> \<open>maximal H\<close>
  then show \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_Extend by auto
qed

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M :: 'p model. (\<forall>q \<in> X. \<lbrakk>M\<rbrakk> q) \<longrightarrow> \<lbrakk>M\<rbrakk> p\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>S [p]\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>S [p]\<close>
  then have \<open>\<nexists>A. set A \<subseteq> X \<and> \<^bold>\<not> p # A \<turnstile>\<^sub>S []\<close>
    using Boole by blast
  then have \<open>\<nexists>A. set A \<subseteq> X \<and> \<^bold>\<not> p # A \<turnstile>\<^sub>S [\<^bold>\<bottom>]\<close>
    by fast
  then have *: \<open>\<nexists>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<and> A \<turnstile>\<^sub>S [\<^bold>\<bottom>]\<close>
    using derive_split1 by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using * by blast
  then have \<open>consistent ?H\<close> \<open>maximal ?H\<close>
    using MCS_Extend' by blast+
  then have \<open>p \<in> ?H \<longleftrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using truth_lemma_no_saturation by fastforce
  then have \<open>p \<in> ?S \<longrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using Extend_subset by blast
  then have \<open>\<lbrakk>hmodel ?H\<rbrakk> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> X. \<lbrakk>hmodel ?H\<rbrakk> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>hmodel ?H\<rbrakk> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>'p fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M. \<lbrakk>M\<rbrakk> p\<close>

theorem completeness:
  assumes \<open>valid p\<close>
  shows \<open>[] \<turnstile>\<^sub>S [p]\<close>
  using assms strong_completeness[where X=\<open>{}\<close>] by auto

theorem main: \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>S [p]\<close>
  using completeness soundness' by blast

end
