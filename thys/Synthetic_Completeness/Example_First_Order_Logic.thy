(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for First-Order Logic
  Author: Asta Halkjær From
*)

chapter \<open>Example: First-Order Logic\<close>

theory Example_First_Order_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<dagger>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<dagger>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<ddagger>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym ('a, 'f, 'p) model = \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> ('p \<Rightarrow> 'a list \<Rightarrow> bool)\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(E, _)\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>(E, F)\<rparr> (\<^bold>\<dagger>f ts) = F f (map \<lparr>(E, F)\<rparr> ts)\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<Zsemi>\<close> 0) where
  \<open>(t \<Zsemi> s) 0 = t\<close>
| \<open>(t \<Zsemi> s) (Suc n) = s n\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  \<open>\<lbrakk>_\<rbrakk> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<lbrakk>(E, F, G)\<rbrakk> (\<^bold>\<ddagger>P ts) \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>\<lbrakk>(E, F, G)\<rbrakk> (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> \<lbrakk>(E, F, G)\<rbrakk> p \<longrightarrow> \<lbrakk>(E, F, G)\<rbrakk> q\<close>
| \<open>\<lbrakk>(E, F, G)\<rbrakk> (\<^bold>\<forall>p) \<longleftrightarrow> (\<forall>x. \<lbrakk>(x \<Zsemi> E, F, G)\<rbrakk> p)\<close>

section \<open>Operations\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm s (\<^bold>\<ddagger>P ts) = \<^bold>\<ddagger>P (map (sub_tm s) ts)\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fm (\<^bold>#0 \<Zsemi> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'f tm \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<Zsemi> \<^bold>#)\<close>

abbreviation \<open>params' S \<equiv> \<Union>p \<in> S. params_fm p\<close>

abbreviation \<open>params l \<equiv> params' (set l)\<close>

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>(E, F(f := x))\<rparr> t = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> \<lbrakk>(E, F(f := x), G)\<rbrakk> p = \<lbrakk>(E, F, G)\<rbrakk> p\<close>
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

lemma sub_fm_semantics [simp]: \<open>\<lbrakk>(E, F, G)\<rbrakk> (sub_fm s p) = \<lbrakk>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F, G)\<rbrakk> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

lemma sub_tm_Var: \<open>sub_tm \<^bold># t = t\<close>
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
    by (auto cong: map_cong simp: sub_tm_Var)
qed simp_all

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<^bold>#, \<^bold>\<dagger>)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<^bold>#, \<^bold>\<dagger>)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm :: \<open>('f, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<ddagger>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

section \<open>Calculus\<close>

inductive Calculus :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  Assm [intro]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| ImpI [intro]: \<open>p # A \<turnstile>\<^sub>\<forall> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
| ImpE [elim]: \<open>A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> q\<close>
| UniI [intro]: \<open>A \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> params (p # A) \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
| UniE [elim]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
| Clas: \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| Weak: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> q # A \<turnstile>\<^sub>\<forall> p\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> list_all \<lbrakk>(E, F, G)\<rbrakk> A \<Longrightarrow> \<lbrakk>(E, F, G)\<rbrakk> p\<close>
proof (induct p arbitrary: F rule: Calculus.induct)
  case (UniI A a p)
  moreover have \<open>list_all \<lbrakk>(E, F(a := x), G)\<rbrakk> A\<close> for x
    using UniI(3-4) by (simp add: list.pred_mono_strong)
  then have \<open>\<lbrakk>(E, F(a := x), G)\<rbrakk> (\<langle>\<^bold>\<star>a\<rangle>p)\<close> for x
    using UniI by blast
  ultimately show ?case
    by fastforce
qed (auto simp: list_all_iff)

corollary soundness': \<open>[] \<turnstile>\<^sub>\<forall> p \<Longrightarrow> \<lbrakk>M\<rbrakk> p\<close>
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
  fix A B and p :: \<open>('f, 'p) fm\<close>
  assume \<open>A \<turnstile>\<^sub>\<forall> p\<close> \<open>set A \<subseteq> set B\<close>
  then show \<open>B \<turnstile>\<^sub>\<forall> p\<close>
    using Weaken by blast
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('f, 'p) fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>

fun witness :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm set \<Rightarrow> ('f, 'p) fm set\<close> where
  \<open>witness (\<^bold>\<not> (\<^bold>\<forall>p)) S = {\<^bold>\<not> \<langle>\<^bold>\<star>(SOME a. a \<notin> params' ({p} \<union> S))\<rangle>p}\<close>
| \<open>witness _ _ = {}\<close>

lemma consistent_add_instance:
  assumes \<open>consistent S\<close> \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>consistent ({\<langle>t\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>t\<rangle>p} \<union> S \<and> S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> \<open>\<langle>t\<rangle>p # S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using assms derive_split1 by metis
  then have \<open>\<^bold>\<forall>p # S' \<turnstile>\<^sub>\<forall> \<^bold>\<not> \<langle>t\<rangle>p\<close>
    using Weak by blast
  moreover have \<open>\<^bold>\<forall>p # S' \<turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
    using Assm_head by fast
  ultimately have \<open>\<^bold>\<forall>p # S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    by fast
  moreover have \<open>set ((\<^bold>\<forall>p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> S\<close> \<open>a \<notin> params' S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> S \<and> S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> \<open>(\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p) # S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using assms derive_split1 by metis
  then have \<open>S' \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p\<close>
    using Boole by blast
  moreover have \<open>a \<notin> params_fm p\<close> \<open>\<forall>p \<in> set S'. a \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2-3) by auto
  then have \<open>a \<notin> params' ({p} \<union> set S')\<close>
    using calculation by fast
  ultimately have \<open>S' \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
    by fastforce
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>p) # S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using Weak Assm_head by fast
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>p)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
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
  then obtain a where a: \<open>witness (\<^bold>\<not> (\<^bold>\<forall>p)) S = {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p}\<close> \<open>a \<notin> params' ({\<^bold>\<not>\<^bold>\<forall>p} \<union> S)\<close>
    by simp
  then show ?case
    using 1(1-2) a(1) consistent_add_witness[where S=\<open>{\<^bold>\<not>\<^bold>\<forall>p} \<union> S\<close>] by fastforce
qed (auto simp: assms)

interpretation MCS_Saturation consistent params_fm witness
proof
  fix S S' :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent S\<close> \<open>S' \<subseteq> S\<close>
  then show \<open>consistent S'\<close>
    unfolding consistent_def by fast
next
  fix S :: \<open>('f, 'p) fm set\<close>
  assume \<open>\<not> consistent S\<close>
  then show \<open>\<exists>S'\<subseteq>S. finite S' \<and> \<not> consistent S'\<close>
    unfolding consistent_def by blast
next
  fix p :: \<open>('f, 'p) fm\<close>
  show \<open>finite (params_fm p)\<close>
    by simp
next
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
qed

interpretation Derivations_MCS_Cut Calculus consistent \<open>\<^bold>\<bottom>\<close>
proof
  fix S :: \<open>('f, 'p) fm set\<close>
  show \<open>consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>)\<close>
    unfolding consistent_def ..
next
  fix A and p :: \<open>('f, 'p) fm\<close>
  assume \<open>p \<in> set A\<close>
  then show \<open>A \<turnstile>\<^sub>\<forall> p\<close>
    by blast
next
  fix A B and p q :: \<open>('f, 'p) fm\<close>
  assume \<open>A \<turnstile>\<^sub>\<forall> p\<close> \<open>p # B \<turnstile>\<^sub>\<forall> q\<close>
  then show \<open>A @ B \<turnstile>\<^sub>\<forall> q\<close>
    using Weaken ImpI ImpE by (metis Un_upper2 inf_sup_ord(3) set_append)
qed

section \<open>Truth Lemma\<close>

abbreviation hmodel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model\<close> where
  \<open>hmodel H \<equiv> (\<^bold>#, \<^bold>\<dagger>, \<lambda>P ts. \<^bold>\<ddagger>P ts \<in> H)\<close>

fun semics ::
  \<open>('a, 'f, 'p) model \<Rightarrow> (('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>semics _ _ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>semics (E, F, G) _ (\<^bold>\<ddagger>P ts) \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>semics (E, F, G) rel (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> rel (E, F, G) p \<longrightarrow> rel (E, F, G) q\<close>
| \<open>semics (E, F, G) rel (\<^bold>\<forall>p) \<longleftrightarrow> (\<forall>x. rel (x \<Zsemi> E, F, G) p)\<close>

fun rel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>rel H (E, _, _) p = (sub_fm E p \<in> H)\<close>

theorem Hintikka_model':
  assumes \<open>\<And>p. semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
  shows \<open>p \<in> H \<longleftrightarrow> \<lbrakk>hmodel H\<rbrakk> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms[of x] by (cases x) simp_all
qed

lemma Hintikka_Extend:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  shows \<open>semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
proof (cases p)
  case Fls
  have \<open>\<^bold>\<bottom> \<notin> H\<close>
    using assms MCS_derive unfolding consistent_def by blast
  then show ?thesis
    using Fls by simp
next
  case (Imp p q)
  have \<open>p # A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close> \<open>A \<turnstile>\<^sub>\<forall> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close> for A
    by (auto simp: Weak)
  moreover have \<open>A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile>\<^sub>\<forall> q\<close> for A
    using deduct1 .
  ultimately have \<open>(p \<in> H \<longrightarrow> q \<in> H) \<longleftrightarrow> p \<^bold>\<longrightarrow> q \<in> H\<close>
    using assms(1-2) MCS_derive MCS_derive_fls by (metis insert_subset list.simps(15))
  then show ?thesis
    using Imp by simp
next
  case (Uni p)
  have \<open>(\<forall>x. \<langle>x\<rangle>p \<in> H) \<longleftrightarrow> (\<^bold>\<forall>p \<in> H)\<close>
  proof
    assume \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close>
    show \<open>\<^bold>\<forall>p \<in> H\<close>
    proof (rule ccontr)
      assume \<open>\<^bold>\<forall>p \<notin> H\<close>
      then have \<open>consistent ({\<^bold>\<not> \<^bold>\<forall>p} \<union> H)\<close>
        using Boole assms(1-2) MCS_derive derive_split1 by (metis consistent_derive_fls)
      then have \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> H\<close>
        using assms(2) unfolding maximal_def by blast
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p \<in> H\<close>
        using assms(3) unfolding saturated_def by fastforce
      moreover have \<open>\<langle>\<^bold>\<star>a\<rangle>p \<in> H\<close>
        using \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close> by blast
      ultimately show False
        using assms(1-2) MCS_derive by (metis consistent_def deduct1 insert_subset list.simps(15))
    qed
  next
    assume \<open>\<^bold>\<forall>p \<in> H\<close>
    then show \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close>
      using assms(1-2) consistent_add_instance maximal_def by blast
  qed
  then show ?thesis
    using Uni by simp
qed simp

interpretation Truth_Saturation
  consistent params_fm witness semics semantics_fm \<open>\<lambda>H. {hmodel H}\<close> rel
proof unfold_locales
  fix p and M :: \<open>('a tm, 'f, 'p) model\<close>
  show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> semics M semantics_fm p\<close>
    by (cases M, induct p) auto
next
  fix p and H :: \<open>('f, 'p) fm set\<close> and M :: \<open>('f tm, 'f, 'p) model\<close>
  assume \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close> \<open>M \<in> {hmodel H}\<close>
  then show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_model' by auto
next
  fix H :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  then show \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_Extend by auto
qed

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
| \<open>encode_tm (\<^bold>\<dagger>f ts) = FUN (length ts) # FUNS f # encode_tms ts\<close>
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
| \<open>encode_fm (\<^bold>\<ddagger>P ts) = PRE (length ts) # PRES P # encode_tms ts\<close>
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
  assumes \<open>\<forall>M :: ('f tm, 'f, 'p) model. (\<forall>q \<in> X. \<lbrakk>M\<rbrakk> q) \<longrightarrow> \<lbrakk>M\<rbrakk> p\<close>
    \<open>infinite (UNIV :: 'f set)\<close>
    \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' X|\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<forall> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<forall> p\<close>
  then have *: \<open>\<nexists>A. set A \<subseteq> X \<and> \<^bold>\<not> p # A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S\<close>

  have \<open>consistent ?S\<close>
    using * by (meson consistent_def derive_split1)
  moreover have \<open>infinite (UNIV - params' X)\<close>
    using assms(2-3)
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' X - params_fm (\<^bold>\<not> p)|\<close>
    using assms(3) finite_params_fm card_of_infinite_diff_finite
    by (metis ordIso_iff_ordLeq ordLeq_transitive)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - (params' X \<union> params_fm (\<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params' ?S|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV - params' ?S|\<close>
    using assms card_of_fm ordLeq_transitive by blast
  ultimately have \<open>consistent ?H\<close> \<open>maximal ?H\<close> \<open>saturated ?H\<close>
    using MCS_Extend by fast+
  then have \<open>p \<in> ?H \<longleftrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using truth_lemma_saturation by fastforce
  then have \<open>p \<in> ?S \<longrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using Extend_subset by blast
  then have \<open>\<lbrakk>hmodel ?H\<rbrakk> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> X. \<lbrakk>hmodel ?H\<rbrakk> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>hmodel ?H\<rbrakk> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M :: ('f tm, _, _) model. \<lbrakk>M\<rbrakk> p\<close>

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
