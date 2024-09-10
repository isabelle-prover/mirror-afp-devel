(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for First-Order Logic
  Author: Asta Halkjær From
*)

chapter \<open>Example: First-Order Logic\<close>

theory Example_First_Order_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<bullet>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<bullet>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym ('a, 'f, 'p) model = \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> ('p \<Rightarrow> 'a list \<Rightarrow> bool)\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(E, _)\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>(E, F)\<rparr> (\<^bold>\<bullet>f ts) = F f (map \<lparr>(E, F)\<rparr> ts)\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<Zsemi>\<close> 0) where
  \<open>(t \<Zsemi> s) 0 = t\<close>
| \<open>(t \<Zsemi> s) (Suc n) = s n\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  \<open>_ \<Turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<longleftrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p \<longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> q\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> \<^bold>\<forall>p \<longleftrightarrow> (\<forall>x. (x \<Zsemi> E, F, G) \<Turnstile>\<^sub>\<forall> p)\<close>

section \<open>Operations\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm s (\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map (sub_tm s) ts)\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fm (\<^bold>#0 \<Zsemi> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'f tm \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<Zsemi> \<^bold>#)\<close>

abbreviation \<open>params' S \<equiv> \<Union>p \<in> S. params_fm p\<close>

abbreviation \<open>params l \<equiv> params' (set l)\<close>

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>(E, F(f := x))\<rparr> t = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> (E, F(f := x), G) \<Turnstile>\<^sub>\<forall> p \<longleftrightarrow> (E, F, G)\<Turnstile>\<^sub>\<forall> p\<close>
  by (induct p arbitrary: E) (auto cong: map_cong)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

lemma env [simp]: \<open>P ((x \<Zsemi> E) n) = (P x \<Zsemi> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma: \<open>\<lparr>(x \<Zsemi> E, F)\<rparr> (lift_tm t) = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics: \<open>\<lparr>(E, F)\<rparr> (sub_tm s t) = \<lparr>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> sub_fm s p \<longleftrightarrow> (\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F, G) \<Turnstile>\<^sub>\<forall> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

lemma sub_tm_Var [simp]: \<open>sub_tm \<^bold># t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma reduce_Var [simp]: \<open>(\<^bold># 0 \<Zsemi> \<lambda>n. \<^bold># (Suc n)) = \<^bold>#\<close>
proof (rule ext)
  fix n
  show \<open>(\<^bold># 0 \<Zsemi> \<lambda>n. \<^bold># (Suc n)) n = \<^bold>#n\<close>
    by (induct n) simp_all
qed

lemma sub_fm_Var [simp]:
  fixes p :: \<open>('f, 'p) fm\<close>
  shows \<open>sub_fm \<^bold># p = p\<close>
proof (induct p)
  case (Pre P ts)
  then show ?case
    by (auto cong: map_cong)
qed simp_all

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm :: \<open>('f, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

section \<open>Calculus\<close>

inductive Calculus :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  Assm [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| ImpI [intro]: \<open>p # A \<turnstile>\<^sub>\<forall> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> q\<close>
| UniI [intro]: \<open>A \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> params (p # A) \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
| UniE [dest]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
| Clas: \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| Weak: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> q # A \<turnstile>\<^sub>\<forall> p\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> \<forall>q \<in> set A. (E, F, G) \<Turnstile>\<^sub>\<forall> q \<Longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p\<close>
proof (induct p arbitrary: F rule: Calculus.induct)
  case (UniI A a p)
  moreover have \<open>\<forall>q \<in> set A. (E, F(a := x), G) \<Turnstile>\<^sub>\<forall> q\<close> for x
    using UniI(3-4) by simp
  then have \<open>(E, F(a := x), G) \<Turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p\<close> for x
    using UniI by blast
  ultimately show ?case
    by fastforce
qed auto

corollary soundness': \<open>[] \<turnstile>\<^sub>\<forall> p \<Longrightarrow> M \<Turnstile>\<^sub>\<forall> p\<close>
  using soundness by (cases M) fastforce

corollary \<open>\<not> ([] \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>)\<close>
  using soundness' by fastforce

section \<open>Admissible Rules\<close>

lemma Assm_head: \<open>p # A \<turnstile>\<^sub>\<forall> p\<close>
  by auto

lemma deduct1: \<open>A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile>\<^sub>\<forall> q\<close>
  by (meson ImpE Weak Assm_head)

lemma Boole: \<open>(\<^bold>\<not> p) # A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
  using Clas FlsE by blast

lemma Weak': \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> B @ A \<turnstile>\<^sub>\<forall> p\<close>
  by (induct B) (simp, metis Weak append_Cons)

lemma Weaken: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> B \<turnstile>\<^sub>\<forall> p\<close>
proof (induct A arbitrary: p)
  case Nil
  then show ?case
    using Weak' by fastforce
next
  case (Cons q A)
  then show ?case
    by (metis Assm ImpE ImpI list.set_intros(1-2) subset_code(1))
qed

interpretation Derivations Calculus
proof
  show \<open>\<And>A p. p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
    by simp
next
  fix A B and p :: \<open>('f, 'p) fm\<close>
  assume \<open>A \<turnstile>\<^sub>\<forall> p\<close> \<open>set A = set B\<close>
  then show \<open>B \<turnstile>\<^sub>\<forall> p\<close>
    using Weaken by blast
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('f, 'p) fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>

fun witness :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm set \<Rightarrow> ('f, 'p) fm set\<close> where
  \<open>witness (\<^bold>\<not> \<^bold>\<forall>p) S = (let a = SOME a. a \<notin> params' ({p} \<union> S) in {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p})\<close>
| \<open>witness _ _ = {}\<close>

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> S\<close> \<open>a \<notin> params' S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof safe
  fix A
  assume \<open>set A \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> S\<close> \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  then obtain A' where \<open>set A' \<subseteq> S\<close> \<open>(\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p) # A' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using assms derive_split1 by (metis consistent_def insert_is_Un subset_insert)
  then have \<open>A' \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p\<close>
    using Boole by blast
  moreover have \<open>a \<notin> params_fm p\<close> \<open>\<forall>p \<in> set A'. a \<notin> params_fm p\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2-3) by auto
  then have \<open>a \<notin> params' ({p} \<union> set A')\<close>
    using calculation by fast
  ultimately have \<open>A' \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
    by fastforce
  then have \<open>\<^bold>\<not> \<^bold>\<forall>p # A' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using Assm_head Weak by blast
  moreover have \<open>set ((\<^bold>\<not> \<^bold>\<forall>p) # A') \<subseteq> S\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_witness':
  assumes \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params' S)\<close>
  shows \<open>consistent (witness p S \<union> {p} \<union> S)\<close>
  using assms
proof (induct p S rule: witness.induct)
  case (1 p S)
  have \<open>infinite (UNIV - params' ({p} \<union> S))\<close>
    using 1(2) finite_params_fm by (simp add: infinite_Diff_fin_Un)
  then have \<open>\<exists>a. a \<notin> params' ({p} \<union> S)\<close>
    by (simp add: not_finite_existsD set_diff_eq)
  then have \<open>(SOME a. a \<notin> params' ({p} \<union> S)) \<notin> params' ({p} \<union> S)\<close>
    by (rule someI_ex)
  then obtain a where a: \<open>witness (\<^bold>\<not> \<^bold>\<forall>p) S = {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p}\<close> \<open>a \<notin> params' ({\<^bold>\<not>\<^bold>\<forall>p} \<union> S)\<close>
    by simp
  then show ?case
    using 1(1-2) a(1) consistent_add_witness[where S=\<open>{\<^bold>\<not>\<^bold>\<forall>p} \<union> S\<close>] by fastforce
qed (auto simp: assms)

interpretation MCS_Witness_UNIV consistent params_fm witness
proof
  fix p and S :: \<open>('f, 'p) fm set\<close>
  show \<open>finite (params' (witness p S))\<close>
    by (induct p S rule: witness.induct) simp_all
next
  fix p and S :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params' S)\<close>
  then show \<open>consistent (witness p S \<union> {p} \<union> S)\<close>
    using consistent_witness' by fast
next
  show \<open>infinite (UNIV :: ('f, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Derivations_Cut_MCS Calculus consistent \<open>\<^bold>\<bottom>\<close>
proof
  fix S :: \<open>('f, 'p) fm set\<close>
  show \<open>consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>)\<close>
    unfolding consistent_def ..
next
  fix A B and p q :: \<open>('f, 'p) fm\<close>
  assume \<open>A \<turnstile>\<^sub>\<forall> p\<close> \<open>p # B \<turnstile>\<^sub>\<forall> q\<close>
  then show \<open>A @ B \<turnstile>\<^sub>\<forall> q\<close>
    by (metis Calculus.simps Un_upper1 Weak' Weaken set_append)
qed

interpretation Derivations_Bot Calculus consistent \<open>\<^bold>\<bottom>\<close>
proof qed fast

interpretation Derivations_Imp Calculus consistent \<open>\<^bold>\<bottom>\<close> \<open>\<lambda>p q. p \<^bold>\<longrightarrow> q\<close>
proof qed fast+

section \<open>Truth Lemma\<close>

abbreviation canonical :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model\<close> (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  \<open>\<lbrakk>S\<rbrakk> \<equiv> (\<^bold>#, \<^bold>\<bullet>, \<lambda>P ts. \<^bold>\<cdot>P ts \<in> S)\<close>

fun semics ::
  \<open>('a, 'f, 'p) model \<Rightarrow> (('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close>
  (\<open>_ \<langle>_\<rangle>=\<^sub>\<forall> _\<close> [55, 0, 55] 55) where
  \<open>_ \<langle>_\<rangle>=\<^sub>\<forall> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(E, F, G) \<langle>_\<rangle>=\<^sub>\<forall> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>(E, F, G) \<langle>\<R>\<rangle>=\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<longleftrightarrow> \<R> (E, F, G) p \<longrightarrow> \<R> (E, F, G) q\<close>
| \<open>(E, F, G) \<langle>\<R>\<rangle>=\<^sub>\<forall> \<^bold>\<forall>p \<longleftrightarrow> (\<forall>x. \<R> (x \<Zsemi> E, F, G) p)\<close>

fun rel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>\<R>\<^sub>\<forall>\<close>) where
  \<open>\<R>\<^sub>\<forall> S (E, _, _) p \<longleftrightarrow> sub_fm E p \<in> S\<close>

theorem saturated_model:
  assumes \<open>\<And>p. \<forall>M \<in> {\<lbrakk>S\<rbrakk>}. M \<langle>\<R>\<^sub>\<forall> S\<rangle>=\<^sub>\<forall> p = \<R>\<^sub>\<forall> S M p\<close> \<open>M \<in> {\<lbrakk>S\<rbrakk>}\<close>
  shows \<open>\<R>\<^sub>\<forall> S M p \<longleftrightarrow> M \<Turnstile>\<^sub>\<forall> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms(1)[of x] assms(2) by (cases x) simp_all
qed

theorem saturated_MCS:
  assumes \<open>MCS S\<close>
  shows \<open>\<lbrakk>S\<rbrakk> \<langle>\<R>\<^sub>\<forall> S\<rangle>=\<^sub>\<forall> p \<longleftrightarrow> \<R>\<^sub>\<forall> S \<lbrakk>S\<rbrakk> p\<close>
  using assms
proof (cases p)
  case (Uni p)
  moreover have \<open>(\<forall>x. \<langle>x\<rangle>p \<in> S) \<longleftrightarrow> \<^bold>\<forall>p \<in> S\<close>
    using assms unfolding witnessed_def
    by (metis MCS_derive MCS_not_xor UniE insert_subset witness.simps(1))
  ultimately show ?thesis
    by simp
qed (auto cong: map_cong)

interpretation Truth_Witness semics semantics_fm \<open>\<lambda>S. {\<lbrakk>S\<rbrakk>}\<close> \<open>\<R>\<^sub>\<forall>\<close> consistent params_fm witness
proof
  fix p and M :: \<open>('f tm, 'f, 'p) model\<close>
  show \<open>M \<Turnstile>\<^sub>\<forall> p \<longleftrightarrow> M \<langle>\<lambda>N q. N \<Turnstile>\<^sub>\<forall> q\<rangle>=\<^sub>\<forall> p\<close>
    by (cases M, induct p) auto
qed (use saturated_model saturated_MCS in blast)+

section \<open>Cardinalities\<close>

datatype marker = VarM | FunM | TmM | FlsM | PreM | ImpM | UniM

type_synonym ('f, 'p) enc = \<open>('f + 'p) + marker \<times> nat\<close>

abbreviation \<open>FUNS f \<equiv> Inl (Inl f)\<close>
abbreviation \<open>PRES p \<equiv> Inl (Inr p)\<close>

abbreviation \<open>VAR n \<equiv> Inr (VarM, n)\<close>
abbreviation \<open>FUN n \<equiv> Inr (FunM, n)\<close>
abbreviation \<open>TM n \<equiv> Inr (TmM, n)\<close>

abbreviation \<open>PRE n \<equiv> Inr (PreM, n)\<close>
abbreviation \<open>FLS \<equiv> Inr (FlsM, 0)\<close>
abbreviation \<open>IMP n \<equiv> Inr (FlsM, n)\<close>
abbreviation \<open>UNI \<equiv> Inr (UniM, 0)\<close>

primrec
  encode_tm :: \<open>'f tm \<Rightarrow> ('f, 'p) enc list\<close> and
  encode_tms :: \<open>'f tm list \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_tm (\<^bold>#n) = [VAR n]\<close>
| \<open>encode_tm (\<^bold>\<bullet>f ts) = FUN (length ts) # FUNS f # encode_tms ts\<close>
| \<open>encode_tms [] = []\<close>
| \<open>encode_tms (t # ts) = TM (length (encode_tm t)) # encode_tm t @ encode_tms ts\<close>

lemma encode_tm_ne [simp]: \<open>encode_tm t \<noteq> []\<close>
  by (induct t) auto

lemma inj_encode_tm':
  \<open>(encode_tm t :: ('f, 'p) enc list) = encode_tm s \<Longrightarrow> t = s\<close>
  \<open>(encode_tms ts :: ('f, 'p) enc list) = encode_tms ss \<Longrightarrow> ts = ss\<close>
proof (induct t and ts arbitrary: s and ss rule: encode_tm.induct encode_tms.induct)
  case (Var n)
  then show ?case
    by (cases s) auto
next
  case (Fun f fts)
  then show ?case
    by (cases s) auto
next
  case Nil_tm
  then show ?case
    by (cases ss) auto
next
  case (Cons_tm t ts)
  then show ?case
    by (cases ss) auto
qed

lemma inj_encode_tm: \<open>inj encode_tm\<close>
  unfolding inj_def using inj_encode_tm' by blast

primrec encode_fm :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_fm \<^bold>\<bottom> = [FLS]\<close>
| \<open>encode_fm (\<^bold>\<cdot>P ts) = PRE (length ts) # PRES P # encode_tms ts\<close>
| \<open>encode_fm (p \<^bold>\<longrightarrow> q) = IMP (length (encode_fm p)) # encode_fm p @ encode_fm q\<close>
| \<open>encode_fm (\<^bold>\<forall>p) = UNI # encode_fm p\<close>

lemma encode_fm_ne [simp]: \<open>encode_fm p \<noteq> []\<close>
  by (induct p) auto

lemma inj_encode_fm': \<open>encode_fm p = encode_fm q \<Longrightarrow> p = q\<close>
proof (induct p arbitrary: q)
  case Fls
  then show ?case
    by (cases q) auto
next
  case (Pre P ts)
  then show ?case
    by (cases q) (auto simp: inj_encode_tm')
next
  case (Imp p1 p2)
  then show ?case
    by (cases q) auto
next
  case (Uni p)
  then show ?case
    by (cases q) auto
qed

lemma inj_encode_fm: \<open>inj encode_fm\<close>
  unfolding inj_def using inj_encode_fm' by blast

lemma finite_marker: \<open>finite (UNIV :: marker set)\<close>
proof -
  have \<open>p \<in> {VarM, FunM, TmM, FlsM, PreM, ImpM, UniM}\<close> for p
    by (cases p) auto
  then show ?thesis
    by (meson ex_new_if_finite finite.emptyI finite_insert)
qed

lemma card_of_fm:
  assumes \<open>infinite (UNIV :: 'f set)\<close>
  shows \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: 'f set| +c |UNIV :: 'p set|\<close>
proof -
  have \<open>|UNIV :: marker set| \<le>o |UNIV :: nat set|\<close>
    using finite_marker by (simp add: ordLess_imp_ordLeq)
  moreover have \<open>infinite (UNIV :: ('f + 'p) set)\<close>
    using assms by simp
  ultimately have \<open>|UNIV :: ('f, 'p) enc list set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using card_of_params_marker_lists by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f, 'p) enc list set|\<close>
    using card_of_ordLeq inj_encode_fm by blast
  ultimately have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using ordLeq_transitive by blast
  then show ?thesis
    unfolding csum_def by simp
qed

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M :: ('f tm, 'f, 'p) model. (\<forall>q \<in> X. M \<Turnstile>\<^sub>\<forall> q) \<longrightarrow> M \<Turnstile>\<^sub>\<forall> p\<close>
    \<open>infinite (UNIV :: 'f set)\<close>
    \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' X|\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<forall> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<forall> p\<close>
  then have *: \<open>\<forall>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<longrightarrow> \<not> A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using Boole FlsE by (metis derive_split1 insert_is_Un subset_insert)

  let ?X = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?S = \<open>Extend ?X\<close>

  have \<open>consistent ?X\<close>
    unfolding consistent_def using * by blast
  moreover have \<open>infinite (UNIV - params' X)\<close>
    using assms(2-3)
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' X - params_fm (\<^bold>\<not> p)|\<close>
    using assms(3) finite_params_fm card_of_infinite_diff_finite
    by (metis ordIso_iff_ordLeq ordLeq_transitive)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - (params' X \<union> params_fm (\<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' ?X|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV - params' ?X|\<close>
    using assms card_of_fm ordLeq_transitive by blast
  ultimately have \<open>MCS ?S\<close>
    using MCS_Extend by fast
  then have \<open>p \<in> ?S \<longleftrightarrow> \<lbrakk>?S\<rbrakk> \<Turnstile>\<^sub>\<forall> p\<close> for p
    using truth_lemma by fastforce
  then have \<open>p \<in> ?X \<longrightarrow> \<lbrakk>?S\<rbrakk> \<Turnstile>\<^sub>\<forall> p\<close> for p
    using Extend_subset by blast
  then have \<open>\<lbrakk>?S\<rbrakk> \<Turnstile>\<^sub>\<forall> \<^bold>\<not> p\<close> \<open>\<forall>q \<in> X. \<lbrakk>?S\<rbrakk> \<Turnstile>\<^sub>\<forall> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>?S\<rbrakk> \<Turnstile>\<^sub>\<forall> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M :: ('f tm, _, _) model. M \<Turnstile>\<^sub>\<forall> p\<close>

theorem completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>valid p\<close> \<open>infinite (UNIV :: 'f set)\<close> \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>[] \<turnstile>\<^sub>\<forall> p\<close>
proof -
  have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
    using assms(2-3) by (simp add: cinfinite_def csum_absorb1 ordIso_imp_ordLeq)
  then show ?thesis
    using assms strong_completeness[where X=\<open>{}\<close>] infinite_UNIV_listI by auto
qed

corollary completeness':
  fixes p :: \<open>('f, 'f) fm\<close>
  assumes \<open>valid p\<close> \<open>infinite (UNIV :: 'f set)\<close>
  shows \<open>[] \<turnstile>\<^sub>\<forall> p\<close>
  using assms completeness[of p] by simp

theorem main:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>infinite (UNIV :: 'f set)\<close> \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>\<forall> p\<close>
  using assms completeness soundness' by blast

corollary main':
  fixes p :: \<open>('f, 'f) fm\<close>
  assumes \<open>infinite (UNIV :: 'f set)\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>\<forall> p\<close>
  using assms completeness' soundness' by blast

end
