(*
  Title:  Example Completeness Proof for System K
  Author: Asta Halkjær From
*)

chapter \<open>Example: Modal Logic\<close>

theory Example_Modal_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype ('i, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('i, 'p) fm\<close> \<open>('i, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Box 'i \<open>('i, 'p) fm\<close> (\<open>\<^bold>\<box>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where
  \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

datatype ('i, 'p, 'w) model =
  Model (W: \<open>'w set\<close>) (R: \<open>'i \<Rightarrow> 'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'p \<Rightarrow> bool\<close>)

type_synonym ('i, 'p, 'w) ctx = \<open>('i, 'p, 'w) model \<times> 'w\<close>

fun semantics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<box>\<close> 50) where
  \<open>_ \<Turnstile>\<^sub>\<box> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, w) \<Turnstile>\<^sub>\<box> \<^bold>\<cdot>P \<longleftrightarrow> V M w P\<close>
| \<open>(M, w) \<Turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q \<longleftrightarrow> (M, w) \<Turnstile>\<^sub>\<box> p \<longrightarrow> (M, w) \<Turnstile>\<^sub>\<box> q\<close>
| \<open>(M, w) \<Turnstile>\<^sub>\<box> \<^bold>\<box> i p \<longleftrightarrow> (\<forall>v \<in> W M \<inter> R M i w. (M, v) \<Turnstile>\<^sub>\<box> p)\<close>

section \<open>Calculus\<close>

primrec eval :: \<open>('p \<Rightarrow> bool) \<Rightarrow> (('i, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (\<^bold>\<cdot>P) = g P\<close>
| \<open>eval g h (p \<^bold>\<longrightarrow> q) = (eval g h p \<longrightarrow> eval g h q)\<close>
| \<open>eval _ h (\<^bold>\<box> i p) = h (\<^bold>\<box> i p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

inductive Calculus :: \<open>('i, 'p) fm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>\<box> _\<close> [50] 50) where
  A1: \<open>tautology p \<Longrightarrow> \<turnstile>\<^sub>\<box> p\<close>
| A2: \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> \<^bold>\<box> i p \<^bold>\<longrightarrow> \<^bold>\<box> i q\<close>
| R1: \<open>\<turnstile>\<^sub>\<box> p \<Longrightarrow> \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile>\<^sub>\<box> q\<close>
| R2: \<open>\<turnstile>\<^sub>\<box> p \<Longrightarrow> \<turnstile>\<^sub>\<box> \<^bold>\<box> i p\<close>

primrec imply :: \<open>('i, 'p) fm list \<Rightarrow> ('i, 'p) fm \<Rightarrow> ('i, 'p) fm\<close> (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> p) = p\<close>
| \<open>(q # A \<^bold>\<leadsto> p) = (q \<^bold>\<longrightarrow> A \<^bold>\<leadsto> p)\<close>

abbreviation Calculus_assms (infix \<open>\<turnstile>\<^sub>\<box>\<close> 50) where
  \<open>A \<turnstile>\<^sub>\<box> p \<equiv> \<turnstile>\<^sub>\<box> A \<^bold>\<leadsto> p\<close>

section \<open>Soundness\<close>

lemma eval_semantics: \<open>eval (g w) (\<lambda>q. (Model Ws r g, w) \<Turnstile>\<^sub>\<box> q) p = ((Model Ws r g, w) \<Turnstile>\<^sub>\<box> p)\<close>
  by (induct p) simp_all

lemma tautology:
  assumes \<open>tautology p\<close>
  shows \<open>(M, w) \<Turnstile>\<^sub>\<box> p\<close>
proof -
  from assms have \<open>eval (g w) (\<lambda>q. (Model Ws r g, w) \<Turnstile>\<^sub>\<box> q) p\<close> for Ws g r
    by simp
  then have \<open>(Model Ws r g, w) \<Turnstile>\<^sub>\<box> p\<close> for Ws g r
    using eval_semantics by fast
  then show \<open>(M, w) \<Turnstile>\<^sub>\<box> p\<close>
    by (metis model.exhaust)
qed

theorem soundness: \<open>\<turnstile>\<^sub>\<box> p \<Longrightarrow> w \<in> W M \<Longrightarrow> (M, w) \<Turnstile>\<^sub>\<box> p\<close>
  by (induct p arbitrary: w rule: Calculus.induct) (auto simp: tautology)

section \<open>Admissible rules\<close>

lemma K_imply_head: \<open>p # A \<turnstile>\<^sub>\<box> p\<close>
proof -
  have \<open>tautology (p # A \<^bold>\<leadsto> p)\<close>
    by (induct A) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>A \<turnstile>\<^sub>\<box> q\<close>
  shows \<open>p # A \<turnstile>\<^sub>\<box> q\<close>
  using assms by (auto simp: A1 intro: R1)

lemma K_right_mp:
  assumes \<open>A \<turnstile>\<^sub>\<box> p\<close> \<open>A \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q\<close>
  shows \<open>A \<turnstile>\<^sub>\<box> q\<close>
proof -
  have \<open>tautology (A \<^bold>\<leadsto> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> A \<^bold>\<leadsto> q)\<close>
    by (induct A) simp_all
  with A1 have \<open>\<turnstile>\<^sub>\<box> A \<^bold>\<leadsto> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> A \<^bold>\<leadsto> q\<close> .
  then show ?thesis
    using assms R1 by blast
qed

lemma deduct1: \<open>A \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile>\<^sub>\<box> q\<close>
  by (meson K_right_mp K_imply_Cons K_imply_head)

lemma imply_append [iff]: \<open>(A @ B \<^bold>\<leadsto> r) = (A \<^bold>\<leadsto> B \<^bold>\<leadsto> r)\<close>
  by (induct A) simp_all

lemma imply_swap_append: \<open>A @ B \<turnstile>\<^sub>\<box> r \<Longrightarrow> B @ A \<turnstile>\<^sub>\<box> r\<close>
proof (induct B arbitrary: A)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma K_ImpI: \<open>p # A \<turnstile>\<^sub>\<box> q \<Longrightarrow> A \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemma imply_mem [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<box> p\<close>
  using K_imply_head K_imply_Cons by (induct A) fastforce+

lemma add_imply [simp]: \<open>\<turnstile>\<^sub>\<box> q \<Longrightarrow> A \<turnstile>\<^sub>\<box> q\<close>
  using K_imply_head R1 by auto

lemma K_imply_weaken: \<open>A \<turnstile>\<^sub>\<box> q \<Longrightarrow> set A \<subseteq> set A' \<Longrightarrow> A' \<turnstile>\<^sub>\<box> q\<close>
  by (induct A arbitrary: q) (simp, metis K_right_mp K_ImpI imply_mem insert_subset list.set(2))

lemma K_Boole:
  assumes \<open>(\<^bold>\<not> p) # A \<turnstile>\<^sub>\<box> \<^bold>\<bottom>\<close>
  shows \<open>A \<turnstile>\<^sub>\<box> p\<close>
proof -
  have \<open>A \<turnstile>\<^sub>\<box> \<^bold>\<not> \<^bold>\<not> p\<close>
    using assms K_ImpI by blast
  moreover have \<open>tautology (A \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> p)\<close>
    by (induct A) simp_all
  then have \<open>\<turnstile>\<^sub>\<box> (A \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (A \<^bold>\<leadsto> q)\<close>
  shows \<open>map (\<^bold>\<box> i) A \<turnstile>\<^sub>\<box> \<^bold>\<box> i q\<close>
proof -
  have \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (\<^bold>\<box> i) A \<^bold>\<leadsto> \<^bold>\<box> i q\<close>
  proof (induct A)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a A)
    have \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>\<box> i a \<^bold>\<longrightarrow> \<^bold>\<box> i (A \<^bold>\<leadsto> q)\<close>
      by (simp add: A2)
    moreover have
      \<open>\<turnstile>\<^sub>\<box> ((\<^bold>\<box> i (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>\<box> i a \<^bold>\<longrightarrow> \<^bold>\<box> i (A \<^bold>\<leadsto> q)) \<^bold>\<longrightarrow>
        (\<^bold>\<box> i (A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (\<^bold>\<box> i) A \<^bold>\<leadsto> \<^bold>\<box> i q) \<^bold>\<longrightarrow>
        (\<^bold>\<box> i (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>\<box> i a \<^bold>\<longrightarrow> map (\<^bold>\<box> i) A \<^bold>\<leadsto> \<^bold>\<box> i q))\<close>
      by (simp add: A1)
    ultimately have \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>\<box> i a \<^bold>\<longrightarrow> map (\<^bold>\<box> i) A \<^bold>\<leadsto> \<^bold>\<box> i q\<close>
      using Cons R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('i, 'p) fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>\<box> \<^bold>\<bottom>\<close>

interpretation MCS_No_Witness_UNIV consistent
proof
  show \<open>infinite (UNIV :: ('i, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Derivations_Cut_MCS consistent Calculus_assms
proof
  fix A B and p :: \<open>('i, 'p) fm\<close>
  assume \<open>\<turnstile>\<^sub>\<box> A \<^bold>\<leadsto> p\<close> \<open>set A = set B\<close>
  then show \<open>\<turnstile>\<^sub>\<box> B \<^bold>\<leadsto> p\<close>
    using K_imply_weaken by blast
next
  fix S :: \<open>('i, 'p) fm set\<close>
  show \<open>consistent S = (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile>\<^sub>\<box> q))\<close>
    unfolding consistent_def using K_Boole K_imply_Cons by blast
next
  fix A B and p q :: \<open>('i, 'p) fm\<close>
  assume \<open>A \<turnstile>\<^sub>\<box> p\<close> \<open>p # B \<turnstile>\<^sub>\<box> q\<close>
  then show \<open>A @ B \<turnstile>\<^sub>\<box> q\<close>
    by (metis K_right_mp add_imply imply.simps(2) imply_append)
qed simp

interpretation Derivations_Bot consistent Calculus_assms \<open>\<^bold>\<bottom>\<close>
proof
  show \<open>\<And>A r. A \<turnstile>\<^sub>\<box> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<box> r\<close>
    using K_Boole K_imply_Cons by blast
qed

interpretation Derivations_Imp consistent Calculus_assms \<open>\<lambda>p q. p \<^bold>\<longrightarrow> q\<close>
proof
  show \<open>\<And>A p q. p # A \<turnstile>\<^sub>\<box> q \<Longrightarrow> A \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q\<close>
    using K_ImpI by blast
  show \<open>\<And>A p q. A \<turnstile>\<^sub>\<box> p \<Longrightarrow> A \<turnstile>\<^sub>\<box> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>\<box> q\<close>
    using K_right_mp by blast
qed

theorem deriv_in_maximal:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>\<turnstile>\<^sub>\<box> p\<close>
  shows \<open>p \<in> S\<close>
  using assms MCS_derive by fastforce

section \<open>Truth Lemma\<close>

abbreviation known :: \<open>('i, 'p) fm set \<Rightarrow> 'i \<Rightarrow> ('i, 'p) fm set\<close> where
  \<open>known S i \<equiv> {p. \<^bold>\<box> i p \<in> S}\<close>

abbreviation reach :: \<open>'i \<Rightarrow> ('i, 'p) fm set \<Rightarrow> ('i, 'p) fm set set\<close> where
  \<open>reach i S \<equiv> {S'. known S i \<subseteq> S' \<and> MCS S'}\<close>

abbreviation canonical :: \<open>('i, 'p) fm set \<Rightarrow> ('i, 'p, ('i, 'p) fm set) ctx\<close> (\<open>\<M>\<^sub>\<box>\<close>) where
  \<open>\<M>\<^sub>\<box>(S) \<equiv> (Model {S. MCS S} reach (\<lambda>S P. \<^bold>\<cdot>P \<in> S), S)\<close>

fun semics ::
  \<open>('i, 'p, 'w) ctx \<Rightarrow> (('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close>
  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<box> _)\<close> [55, 0, 55] 55) where
  \<open>_ \<lbrakk>_\<rbrakk>\<^sub>\<box> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, w) \<lbrakk>_\<rbrakk>\<^sub>\<box> \<^bold>\<cdot>P \<longleftrightarrow> V M w P\<close>
| \<open>(M, w) \<lbrakk>\<R>\<rbrakk>\<^sub>\<box> p \<^bold>\<longrightarrow> q \<longleftrightarrow> \<R> (M, w) p \<longrightarrow> \<R> (M, w) q\<close>
| \<open>(M, w) \<lbrakk>\<R>\<rbrakk>\<^sub>\<box> \<^bold>\<box> i p \<longleftrightarrow> (\<forall>v \<in> W M \<inter> R M i w. \<R> (M, v) p)\<close>

fun rel :: \<open>('i, 'p) fm set \<Rightarrow> ('i, 'p, ('i, 'p) fm set) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (\<open>\<R>\<^sub>\<box>\<close>) where
  \<open>\<R>\<^sub>\<box>(_) (_, w) p \<longleftrightarrow> p \<in> w\<close>

theorem saturated_model:
  fixes S :: \<open>('i, 'p) fm set\<close>
  assumes \<open>\<And>(S :: ('i, 'p) fm set) p. MCS S \<Longrightarrow> \<M>\<^sub>\<box>(S) \<lbrakk>\<R>\<^sub>\<box>(S')\<rbrakk>\<^sub>\<box> p \<longleftrightarrow> p \<in> S\<close>
  shows \<open>MCS S \<Longrightarrow> \<M>\<^sub>\<box>(S) \<Turnstile>\<^sub>\<box> p \<longleftrightarrow> p \<in> S\<close>
proof (induct p arbitrary: S rule: wf_induct[where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms[of S x] by (cases x) auto
qed

theorem saturated_MCS:
  assumes \<open>MCS S\<close>
  shows \<open>\<M>\<^sub>\<box>(S) \<lbrakk>\<R>\<^sub>\<box>(S')\<rbrakk>\<^sub>\<box> p \<longleftrightarrow> \<R>\<^sub>\<box>(S')  (\<M>\<^sub>\<box>(S)) p\<close>
proof (cases p)
  case Fls
  have \<open>\<^bold>\<bottom> \<notin> S\<close>
    using assms MCS_derive unfolding consistent_def by blast
  then show ?thesis
    using Fls by simp
next
  case (Imp p q)
  then show ?thesis
    using assms by auto
next
  case (Box i p)
  have \<open>(\<forall>S' \<in> reach i S. p \<in> S') \<longleftrightarrow> \<^bold>\<box> i p \<in> S\<close>
  proof
    assume \<open>\<^bold>\<box> i p \<in> S\<close>
    then show \<open>\<forall>S' \<in> reach i S. p \<in> S'\<close>
      by auto
  next
    assume *: \<open>\<forall>S' \<in> reach i S. p \<in> S'\<close>
    have \<open>\<not> consistent ({\<^bold>\<not> p} \<union> known S i)\<close>
    proof
      assume \<open>consistent ({\<^bold>\<not> p} \<union> known S i)\<close>
      then obtain S' where S': \<open>{\<^bold>\<not> p} \<union> known S i \<subseteq> S'\<close> \<open>MCS S'\<close>
        using \<open>MCS S\<close> MCS_Extend' Extend_subset by metis
      then show False
        using * MCS_impE MCS_bot by force
    qed
    then obtain A where A: \<open>\<^bold>\<not> p # A \<turnstile>\<^sub>\<box> \<^bold>\<bottom>\<close> \<open>set A \<subseteq> known S i\<close>
      unfolding consistent_def using derive_split1 K_imply_Cons
      by (metis (no_types, lifting) insert_is_Un subset_insert)
    then have \<open>\<turnstile>\<^sub>\<box> A \<^bold>\<leadsto> p\<close>
      using K_Boole by blast
    then have \<open>\<turnstile>\<^sub>\<box> \<^bold>\<box> i (A \<^bold>\<leadsto> p)\<close>
      using R2 by fast
    then have \<open>map (\<^bold>\<box> i) A \<turnstile>\<^sub>\<box> \<^bold>\<box> i p\<close>
      using K_distrib_K_imp by fast
    then have \<open>(map (\<^bold>\<box> i) A \<^bold>\<leadsto> \<^bold>\<box> i p) \<in> S\<close>
      using deriv_in_maximal \<open>MCS S\<close> by blast
    then show \<open>\<^bold>\<box> i p \<in> S\<close>
      using A(2)
    proof (induct A)
      case (Cons a L)
      then have \<open>\<^bold>\<box> i a \<in> S\<close>
        by auto
      then have \<open>(map (\<^bold>\<box> i) L \<^bold>\<leadsto> \<^bold>\<box> i p) \<in> S\<close>
        using Cons(2) \<open>MCS S\<close> MCS_impE by auto
      then show ?case
        using Cons by simp
    qed simp
  qed
  then show ?thesis
    using Box by auto
qed simp

interpretation Truth_No_Witness semics semantics \<open>\<lambda>_. {\<M>\<^sub>\<box>(S) |S. MCS S}\<close> rel consistent
proof
  fix p and M :: \<open>('i, 'p, ('i, 'p) fm set) ctx\<close>
  show \<open>(M \<Turnstile>\<^sub>\<box> p) = M \<lbrakk>semantics\<rbrakk>\<^sub>\<box> p\<close>
    by (cases M, induct p) simp_all
next
  fix p and S :: \<open>('i, 'p) fm set\<close> and M :: \<open>('i, 'p, ('i, 'p) fm set) ctx\<close>
  assume \<open>\<forall>p. \<forall>M\<in>{\<M>\<^sub>\<box>(S) |S. MCS S}. M \<lbrakk>\<R>\<^sub>\<box>(S)\<rbrakk>\<^sub>\<box> p \<longleftrightarrow> \<R>\<^sub>\<box>(S) M p\<close> \<open>M \<in> {\<M>\<^sub>\<box>(S) |S. MCS S}\<close>
  then show \<open>M \<Turnstile>\<^sub>\<box> p \<longleftrightarrow> \<R>\<^sub>\<box>(S) M p\<close>
    using saturated_model[of S _ p] by auto
next
  fix S :: \<open>('i, 'p) fm set\<close> and M :: \<open>('i, 'p, ('i, 'p) fm set) ctx\<close>
  assume \<open>MCS S\<close>
  then show \<open>\<forall>p. \<forall>M\<in>{\<M>\<^sub>\<box>(S) |S. MCS S}. M \<lbrakk>\<R>\<^sub>\<box>(S)\<rbrakk>\<^sub>\<box> p \<longleftrightarrow> \<R>\<^sub>\<box>(S) M p\<close>
    using saturated_MCS by blast
qed

lemma Truth_lemma:
  assumes \<open>MCS S\<close>
  shows \<open>\<M>\<^sub>\<box>(S) \<Turnstile>\<^sub>\<box> p \<longleftrightarrow> p \<in> S\<close>
  using assms truth_lemma by fastforce

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M :: ('i, 'p, ('i, 'p) fm set) model. \<forall>w \<in> W M.
    (\<forall>q \<in> X. (M, w) \<Turnstile>\<^sub>\<box> q) \<longrightarrow> (M, w) \<Turnstile>\<^sub>\<box> p\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<box> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<box> p\<close>
  then have *: \<open>\<forall>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<longrightarrow> \<not> A \<turnstile>\<^sub>\<box> \<^bold>\<bottom>\<close>
    using K_Boole botE by (metis derive_split1 insert_is_Un subset_insert)

  let ?X = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?S = \<open>Extend ?X\<close>

  have \<open>consistent ?X\<close>
    using * unfolding consistent_def .
  then have \<open>MCS ?S\<close>
    using MCS_Extend' by blast
  moreover have \<open>\<^bold>\<not> p \<in> ?S\<close> \<open>X \<subseteq> ?S\<close>
    using Extend_subset by fast+
  ultimately have \<open>\<M>\<^sub>\<box> ?S \<Turnstile>\<^sub>\<box> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> X. \<M>\<^sub>\<box> ?S \<Turnstile>\<^sub>\<box> q\<close>
    using assms Truth_lemma by fast+
  then have \<open>\<M>\<^sub>\<box> ?S \<Turnstile>\<^sub>\<box> p\<close>
    using assms \<open>MCS ?S\<close> by simp
  then show False
    using \<open>\<M>\<^sub>\<box> ?S \<Turnstile>\<^sub>\<box> (\<^bold>\<not> p)\<close> by simp
qed

abbreviation valid :: \<open>('i, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(M :: ('i, 'p, ('i, 'p) fm set) model). \<forall>w \<in> W M. (M, w) \<Turnstile>\<^sub>\<box> p\<close>

corollary completeness: \<open>valid p \<Longrightarrow> \<turnstile>\<^sub>\<box> p\<close>
  using strong_completeness[where X=\<open>{}\<close>] by simp

theorem main: \<open>valid p \<longleftrightarrow> \<turnstile>\<^sub>\<box> p\<close>
  using soundness completeness by meson

end
