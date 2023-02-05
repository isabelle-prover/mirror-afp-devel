(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for Basic Hybrid Logic
  Author: Asta Halkjær From
*)

chapter \<open>Example: Hybrid Logic\<close>

theory Example_Hybrid_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype (nominals_fm: 'i, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<ddagger>\<close>)
  | Nom 'i (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('i, 'p) fm\<close> \<open>('i, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Dia \<open>('i, 'p) fm\<close> (\<open>\<^bold>\<diamond>\<close>)
  | Sat 'i \<open>('i, 'p) fm\<close> (\<open>\<^bold>@\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

type_synonym ('i, 'p) lbd = \<open>'i \<times> ('i, 'p) fm\<close>

primrec nominals_lbd :: \<open>('i, 'p) lbd \<Rightarrow> 'i set\<close> where
  \<open>nominals_lbd (i, p) = {i} \<union> nominals_fm p\<close>

abbreviation nominals :: \<open>('i, 'p) lbd set \<Rightarrow> 'i set\<close> where
  \<open>nominals S \<equiv> \<Union>ip \<in> S. nominals_lbd ip\<close>

lemma finite_nominals_fm: \<open>finite (nominals_fm p)\<close>
  by (induct p) simp_all

lemma finite_nominals_lbd: \<open>finite (nominals_lbd p)\<close>
  by (cases p) (simp add: finite_nominals_fm)

section \<open>Semantics\<close>

datatype ('w, 'p) model =
  Model (R: \<open>'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'p \<Rightarrow> bool\<close>)

type_synonym ('i, 'p, 'w) ctx = \<open>('w, 'p) model \<times> ('i \<Rightarrow> 'w) \<times> 'w\<close>

fun semantics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<Turnstile> _\<close> [50, 50] 50) where
  \<open>(M, g, w) \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, _, w) \<Turnstile> \<^bold>\<ddagger>P \<longleftrightarrow> V M w P\<close>
| \<open>(_, g, w) \<Turnstile> \<^bold>\<cdot>i \<longleftrightarrow> w = g i\<close>
| \<open>(M, g, w) \<Turnstile> (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> (M, g, w) \<Turnstile> p \<longrightarrow> (M, g, w) \<Turnstile> q\<close>
| \<open>(M, g, w) \<Turnstile> \<^bold>\<diamond> p \<longleftrightarrow> (\<exists>v \<in> R M w. (M, g, v) \<Turnstile> p)\<close>
| \<open>(M, g, _) \<Turnstile> \<^bold>@i p \<longleftrightarrow> (M, g, g i) \<Turnstile> p\<close>

lemma semantics_fresh: \<open>i \<notin> nominals_fm p \<Longrightarrow> ((M, g, w) \<Turnstile> p) = ((M, g(i := v), w) \<Turnstile> p)\<close>
  by (induct p arbitrary: w) auto

lemma semantics_fresh_lbd:
  \<open>k \<notin> nominals_lbd (i, p) \<Longrightarrow> ((M, g, w) \<Turnstile> p) = ((M, g(k := v), w) \<Turnstile> p)\<close>
  by (induct p arbitrary: w) auto

section \<open>Calculus\<close>

inductive Calculus :: \<open>('i, 'p) lbd list \<Rightarrow> ('i, 'p) lbd \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>@ _\<close> [50, 50] 50) where
  Assm [intro]: \<open>(i, p) \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
| Ref [intro]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>i)\<close>
| Nom [intro]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>k) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| ImpI [intro]: \<open>(i, p) # A \<turnstile>\<^sub>@ (i, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q)\<close>
| ImpE [elim]: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, q)\<close>
| SatI [intro]: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, \<^bold>@i p)\<close>
| SatE [elim]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>@k p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| DiaI [intro]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p)\<close>
| DiaE [elim]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p) \<Longrightarrow> k \<notin> nominals ({(i, p), (j, q)} \<union> set A) \<Longrightarrow>
    (k, p) # (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) # A \<turnstile>\<^sub>@ (j, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (j, q)\<close>
| Clas: \<open>(i, p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
| Weak: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> (k, q) # A \<turnstile>\<^sub>@ (i, p)\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> list_all (\<lambda>(i, p). (M, g, g i) \<Turnstile> p) A \<Longrightarrow> (M, g, g i) \<Turnstile> p\<close>
proof (induct \<open>(i, p)\<close> arbitrary: i p g rule: Calculus.induct)
  case (Nom A i k p)
  then show ?case
    by fastforce
next
  case (DiaE A i p k j q)
  then have \<open>(M, g, g i) \<Turnstile> \<^bold>\<diamond> p\<close>
    by blast
  then obtain v where v: \<open>v \<in> R M (g i)\<close> \<open>(M, g, v) \<Turnstile> p\<close>
    by auto
  let ?g = \<open>g(k := v)\<close>
  have \<open>(M, ?g, ?g k) \<Turnstile> p\<close> \<open>(M, ?g, ?g i) \<Turnstile> \<^bold>\<diamond> (\<^bold>\<cdot>k)\<close>
    using v fun_upd_same DiaE(3) semantics_fresh_lbd by fastforce+
  moreover have \<open>list_all (\<lambda>(i, p). (M, ?g, ?g i) \<Turnstile> p) A\<close>
    using DiaE.prems DiaE.hyps(3) semantics_fresh_lbd by (induct A) fastforce+
  ultimately have \<open>list_all (\<lambda>(i, p). (M, ?g, ?g i) \<Turnstile> p) ((k, p) # (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) # A)\<close>
    by simp
  then have \<open>(M, ?g, ?g j) \<Turnstile> q\<close>
    using DiaE.hyps by fast
  then show ?case
    using DiaE.hyps(3) semantics_fresh_lbd by fastforce
qed (auto simp: list_all_iff)

corollary soundness': \<open>[] \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> i \<notin> nominals_fm p \<Longrightarrow> (M, g, w) \<Turnstile> p\<close>
  using soundness semantics_fresh by (metis fun_upd_same list.pred_inject(1))

corollary \<open>\<not> ([] \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>))\<close>
  using soundness' by fastforce

section \<open>Admissible Rules\<close>

lemma Assm_head: \<open>(p, i) # A \<turnstile>\<^sub>@ (p, i)\<close>
  by auto

lemma deduct1: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> (i, p) # A \<turnstile>\<^sub>@ (i, q)\<close>
  by (meson ImpE Weak Assm_head)

lemma Boole: \<open>(i, \<^bold>\<not> p) # A \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
  using Clas FlsE by meson

lemma Weak': \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> B @ A \<turnstile>\<^sub>@ (i, p)\<close>
proof (induct B)
  case (Cons b B)
  then show ?case
    by (cases b) (metis Cons Weak append_Cons)
qed simp

lemma ImpI':
  assumes \<open>(k, q) # A \<turnstile>\<^sub>@ (i, p)\<close>
  shows \<open>A \<turnstile>\<^sub>@ (i, (\<^bold>@k q) \<^bold>\<longrightarrow> p)\<close>
  using assms
proof -
  have \<open>(k, q) # A \<turnstile>\<^sub>@ (k, \<^bold>@i p)\<close>
    using assms by fast
  then show ?thesis
    by (meson Assm_head ImpE ImpI SatE Weak)
qed

lemma Weaken: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> B \<turnstile>\<^sub>@ (i, p)\<close>
proof (induct A arbitrary: i p)
  case Nil
  then show ?case
    using Weak' by fastforce
next
  case (Cons kq A)
  then show ?case
  proof (cases kq)
    case (Pair k q)
    then show ?thesis
      using Cons by (meson Assm ImpI' ImpE SatI list.set_intros(1) set_subset_Cons subset_eq)
  qed
qed

interpretation Derivations Calculus
proof
  fix A B and p :: \<open>('i, 'p) lbd\<close>
  assume \<open>A \<turnstile>\<^sub>@ p\<close> \<open>set A \<subseteq> set B\<close>
  then show \<open>B \<turnstile>\<^sub>@ p\<close>
    by (cases p) (metis Weaken)
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('i, 'p) lbd set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S' a. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> \<open>(i, \<^bold>\<diamond> p) \<in> S\<close> \<open>k \<notin> nominals S\<close>
  shows \<open>consistent ({(k, p), (i, \<^bold>\<diamond> (\<^bold>\<cdot>k))} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S' a. set S' \<subseteq> {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<cdot>k))} \<union> S \<and> S' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
  then obtain S' a where \<open>set S' \<subseteq> S\<close> \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) # S' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
    using assms derive_split[where X=S and B=\<open>[(k, p), (i, \<^bold>\<diamond> (\<^bold>\<cdot>k))]\<close>]
    by (metis append_Cons append_Nil list.simps(15) set_empty)
  then have \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) # S' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by fast
  then have \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) # (i, \<^bold>\<diamond> p) # S' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by (fastforce intro: Weaken)
  moreover have \<open>k \<notin> nominals ({(i, p), (i, \<^bold>\<bottom>)} \<union> set ((i, \<^bold>\<diamond> p) # S'))\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2-3) by auto
  moreover have \<open>(i, \<^bold>\<diamond> p) # S' \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p)\<close>
    by auto
  ultimately have \<open>(i, \<^bold>\<diamond> p) # S' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by fastforce
  moreover have \<open>set ((i, \<^bold>\<diamond> p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

fun witness :: \<open>('i, 'p) lbd \<Rightarrow> ('i, 'p) lbd set \<Rightarrow> ('i, 'p) lbd set\<close> where
  \<open>witness (i, \<^bold>\<diamond> p) S = (let k = (SOME k. k \<notin> nominals ({(i, p)} \<union> S)) in {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<cdot>k))})\<close>
| \<open>witness (_, _) _ = {}\<close>

lemma consistent_witness':
  assumes \<open>consistent ({(i, p)} \<union> S)\<close> \<open>infinite (UNIV - nominals S)\<close>
  shows \<open>consistent (witness (i, p) S \<union> {(i, p)} \<union> S)\<close>
  using assms
proof (induct \<open>(i, p)\<close> S arbitrary: i p rule: witness.induct)
  case (1 i p S)
  have \<open>infinite (UNIV - nominals ({(i, p)} \<union> S))\<close>
    using 1(2) finite_nominals_lbd
    by (metis UN_Un finite.emptyI finite.insertI finite_UN_I infinite_Diff_fin_Un)
  then have \<open>\<exists>k. k \<notin> nominals ({(i, p)} \<union> S)\<close>
    by (simp add: not_finite_existsD set_diff_eq)
  then have \<open>(SOME k. k \<notin> nominals ({(i, p)} \<union> S)) \<notin> nominals ({(i, p)} \<union> S)\<close>
    by (rule someI_ex)
  then obtain k where \<open>witness (i, \<^bold>\<diamond> p) S = {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<cdot>k))}\<close>
    \<open>k \<notin> nominals ({(i, \<^bold>\<diamond> p)} \<union> S)\<close>
    by (simp add: Let_def)
  then show ?case
    using 1(1-2) consistent_add_witness[where S=\<open>{(i, \<^bold>\<diamond> p)} \<union> S\<close>] by simp
qed (auto simp: assms)

interpretation MCS_Saturation consistent nominals_lbd witness
proof
  fix S S' :: \<open>('i, 'p) lbd set\<close>
  assume \<open>consistent S\<close> \<open>S' \<subseteq> S\<close>
  then show \<open>consistent S'\<close>
    unfolding consistent_def by fast
next
  fix S :: \<open>('i, 'p) lbd set\<close>
  assume \<open>\<not> consistent S\<close>
  then show \<open>\<exists>S'\<subseteq>S. finite S' \<and> \<not> consistent S'\<close>
    unfolding consistent_def by blast
next
  fix ip :: \<open>('i, 'p) lbd\<close>
  show \<open>finite (nominals_lbd ip)\<close>
    using finite_nominals_fm by (cases ip) simp
next
  fix ip :: \<open>('i, 'p) lbd\<close> and S :: \<open>('i, 'p) lbd set\<close>
  show \<open>finite (nominals (witness ip S))\<close>
    by (induct ip S rule: witness.induct) (auto simp: finite_nominals_fm Let_def)
next
  fix ip and S :: \<open>('i, 'p) lbd set\<close>
  assume \<open>consistent ({ip} \<union> S)\<close> \<open>infinite (UNIV - nominals S)\<close>
  then show \<open>consistent (witness ip S \<union> {ip} \<union> S)\<close>
    using consistent_witness' by (cases ip) simp
next
  have \<open>infinite (UNIV :: ('i, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<^bold>\<diamond>\<close>] by simp
  then show \<open>infinite (UNIV :: ('i, 'p) lbd set)\<close>
    using finite_prod by blast
qed

interpretation Derivations_MCS_Cut Calculus consistent \<open>(undefined, \<^bold>\<bottom>)\<close>
proof
  fix S :: \<open>('i, 'p) lbd set\<close>
  show \<open>consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>@ (undefined, \<^bold>\<bottom>))\<close>
    unfolding consistent_def by fast
next
  fix A and p :: \<open>('i, 'p) lbd\<close>
  assume \<open>p \<in> set A\<close>
  then show \<open>A \<turnstile>\<^sub>@ p\<close>
    by (metis Assm surj_pair)
next
  fix A B and p q :: \<open>('i, 'p) lbd\<close>
  assume \<open>A \<turnstile>\<^sub>@ p\<close> \<open>p # B \<turnstile>\<^sub>@ q\<close>
  then have \<open>A @ B \<turnstile>\<^sub>@ p\<close> \<open>p # A @ B \<turnstile>\<^sub>@ q\<close>
    by (simp_all add: derive_struct subsetI)
  then show \<open>A @ B \<turnstile>\<^sub>@ q\<close>
    by (cases p, cases q) (meson ImpE ImpI' SatI)
qed

lemma saturated: \<open>saturated H \<Longrightarrow> (i, \<^bold>\<diamond>p) \<in> H \<Longrightarrow> \<exists>k. (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H \<and> (k, p) \<in> H\<close>
  unfolding saturated_def by (metis insert_subset witness.simps(1))

section \<open>Nominals\<close>

lemma MCS_Nom_refl:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>(i, \<^bold>\<cdot>i) \<in> S\<close>
  using assms Ref by (metis MCS_derive MCS_derive_fls)

lemma MCS_Nom_sym:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>(i, \<^bold>\<cdot>k) \<in> S\<close>
  shows \<open>(k, \<^bold>\<cdot>i) \<in> S\<close>
  using assms Nom Ref by (metis MCS_derive)

lemma MCS_Nom_trans:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>(i, \<^bold>\<cdot>j) \<in> S\<close> \<open>(j, \<^bold>\<cdot>k) \<in> S\<close>
  shows \<open>(i, \<^bold>\<cdot>k) \<in> S\<close>
proof -
  have \<open>\<exists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>j)\<close>
    using assms MCS_derive by blast
  then have \<open>\<exists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>j) \<and> S' \<turnstile>\<^sub>@ (j, \<^bold>\<cdot>k)\<close>
    by (metis Assm_head Calculus.intros(12) assms(4) insert_subset list.set(2))
  then have \<open>\<exists>S'. set S' \<subseteq> S \<and> S' \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>k)\<close>
    using Nom Ref by metis
  then show ?thesis
    using assms MCS_derive by blast
qed

section \<open>Truth Lemma\<close>

fun semics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> (('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close>
  where
    \<open>semics _ _ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
  | \<open>semics (M, _, w) _ (\<^bold>\<ddagger>P) \<longleftrightarrow> V M w P\<close>
  | \<open>semics (_, g, w) _ (\<^bold>\<cdot>i) \<longleftrightarrow> w = g i\<close>
  | \<open>semics (M, g, w) rel (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> rel (M, g, w) p \<longrightarrow> rel (M, g, w) q\<close>
  | \<open>semics (M, g, w) rel (\<^bold>\<diamond> p) \<longleftrightarrow> (\<exists>v \<in> R M w. rel (M, g, v) p)\<close>
  | \<open>semics (M, g, _) rel (\<^bold>@ i p) \<longleftrightarrow> rel (M, g, g i) p\<close>

fun rel :: \<open>('i, 'p) lbd set \<Rightarrow> ('i, 'p, 'i) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> where
  \<open>rel H (_, _, i) p = ((i, p) \<in> H)\<close>

definition val :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'p \<Rightarrow> bool\<close> where
  \<open>val H i P \<equiv> (i, \<^bold>\<ddagger>P) \<in> H\<close>

definition hequiv :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool\<close> where
  \<open>hequiv H i k \<equiv> (i, \<^bold>\<cdot>k) \<in> H\<close>

lemma hequiv_reflp:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>reflp (hequiv H)\<close>
  unfolding hequiv_def reflp_def using assms MCS_Nom_refl by fast

lemma hequiv_symp:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>symp (hequiv H)\<close>
  unfolding hequiv_def symp_def using assms MCS_Nom_sym by fast

lemma hequiv_transp:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>transp (hequiv H)\<close>
  unfolding hequiv_def transp_def using assms MCS_Nom_trans by fast

lemma hequiv_equivp:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>equivp (hequiv H)\<close>
  using assms by (simp add: equivpI hequiv_reflp hequiv_symp hequiv_transp)

definition assign :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'i\<close> where
  \<open>assign H i \<equiv> minim ( |UNIV| ) {k. hequiv H i k}\<close>

lemma hequiv_ne:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>{k. hequiv H i k} \<noteq> {}\<close>
  unfolding hequiv_def using assms MCS_Nom_refl by fast

lemma hequiv_assign:
  assumes \<open>consistent H\<close> \<open>maximal H\<close>
  shows \<open>hequiv H i (assign H i)\<close>
  unfolding assign_def using assms hequiv_ne wo_rel.minim_in
  by (metis Field_card_of card_of_well_order_on mem_Collect_eq top.extremum wo_rel_def)

lemma hequiv_Nom:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>hequiv H i k\<close> \<open>(i, p) \<in> H\<close>
  shows \<open>(k, p) \<in> H\<close>
proof -
  have \<open>\<exists>A. set A \<subseteq> H \<and> A \<turnstile>\<^sub>@ (i, p)\<close>
    using assms MCS_derive by fast
  then have \<open>\<exists>A. set A \<subseteq> H \<and> A \<turnstile>\<^sub>@ (i, p) \<and> A \<turnstile>\<^sub>@ (i, \<^bold>\<cdot>k)\<close>
    using assms(3) unfolding hequiv_def by (metis Assm_head Weak insert_subset list.simps(15))
  then have \<open>\<exists>A. set A \<subseteq> H \<and> A \<turnstile>\<^sub>@ (k, p)\<close>
    using Nom by fast
  then show ?thesis
    using assms MCS_derive by fast
qed

definition reach :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'i set\<close> where
  \<open>reach H i \<equiv> {assign H k |k. (i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H}\<close>

abbreviation canonical :: \<open>('i \<times> ('i, 'p) fm) set \<Rightarrow> 'i \<Rightarrow> ('i, 'p, 'i) ctx\<close> where
  \<open>canonical H i \<equiv> (Model (reach H) (val H), assign H, assign H i)\<close>

lemma Hintikka_model':
  assumes \<open>\<And>i p. semics (canonical H i) (rel H) p \<longleftrightarrow> rel H (canonical H i) p\<close>
  shows \<open>(canonical H i \<Turnstile> p) \<longleftrightarrow> rel H (canonical H i) p\<close>
proof (induct p arbitrary: i rule: wf_induct[where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms[of i x] by (cases x) (auto simp: reach_def)
qed

lemma Hintikka_Extend':
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  shows \<open>semics (canonical H i) (rel H) p \<longleftrightarrow> rel H (canonical H i) p\<close>
proof (cases p)
  case Fls
  have \<open>(assign H i, \<^bold>\<bottom>) \<notin> H\<close>
    using assms(1-2) MCS_derive unfolding consistent_def by fast
  then show ?thesis
    using Fls by simp
next
  case (Pro P)
  have \<open>val H (assign H i) P \<longleftrightarrow> (assign H i, \<^bold>\<ddagger>P) \<in> H\<close>
    unfolding val_def ..
  then show ?thesis
    using Pro by simp
next
  case (Nom k)
  have \<open>assign H i = assign H k \<longleftrightarrow> (assign H i, \<^bold>\<cdot>k) \<in> H\<close>
    using assms(1-2) hequiv_equivp hequiv_assign by (metis assign_def equivp_def hequiv_def)
  then show ?thesis
    using Nom by simp
next
  case (Imp p q)
  have \<open>(i, p) # A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q)\<close> \<open>A \<turnstile>\<^sub>@ (i, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q)\<close> for A a i
    by (auto simp: Weak)
  moreover have \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> (i, p) # A \<turnstile>\<^sub>@ (i, q)\<close> for A i
    using deduct1 .
  ultimately have \<open>((assign H i, p) \<in> H \<longrightarrow> (assign H i, q) \<in> H) \<longleftrightarrow> (assign H i, p \<^bold>\<longrightarrow> q) \<in> H\<close>
    using assms(1-2) MCS_derive MCS_derive_fls by (metis insert_subset list.simps(15))
  then show ?thesis
    using Imp by simp
next
  case (Dia p)
  have \<open>(\<exists>k \<in> reach H (assign H i). (k, p) \<in> H) \<longleftrightarrow> (assign H i, \<^bold>\<diamond> p) \<in> H\<close>
  proof
    assume \<open>\<exists>k \<in> reach H (assign H i). (k, p) \<in> H\<close>
    then have \<open>\<exists>k. (assign H i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H \<and> (assign H k, p) \<in> H\<close>
      unfolding reach_def by fast
    then have \<open>\<exists>k. (assign H i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H \<and> (k, p) \<in> H\<close>
      by (metis assms(1-2) hequiv_Nom hequiv_assign hequiv_symp sympD)
    then have \<open>\<exists>k. \<exists>A. set A \<subseteq> H \<and> A \<turnstile>\<^sub>@ (assign H i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<and> A \<turnstile>\<^sub>@ (k, p)\<close>
      by (metis Assm_head Weak assms(1-2) MCS_derive insert_subset list.simps(15))
    then have \<open>\<exists>A. set A \<subseteq> H \<and> A \<turnstile>\<^sub>@ (assign H i, \<^bold>\<diamond> p)\<close>
      by fast
    then show \<open>(assign H i, \<^bold>\<diamond> p) \<in> H\<close>
      by (simp add: assms(1-2) MCS_derive)
  next
    assume \<open>(assign H i, \<^bold>\<diamond> p) \<in> H\<close>
    then have \<open>\<exists>k. (assign H i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H \<and> (k, p) \<in> H\<close>
      using assms(3) saturated by fast
    then have \<open>\<exists>k. (assign H i, \<^bold>\<diamond> (\<^bold>\<cdot>k)) \<in> H \<and> (assign H k, p) \<in> H\<close>
      by (meson assms(1-2) hequiv_Nom hequiv_assign)
    then show \<open>\<exists>k \<in> reach H (assign H i). (k, p) \<in> H\<close>
      unfolding reach_def by fast
  qed
  then show ?thesis
    using Dia by simp
next
  case (Sat k p)
  have \<open>(assign H k, p) \<in> H \<longleftrightarrow> (assign H i, \<^bold>@k p) \<in> H\<close>
    by (metis SatE SatI assms(1-2) MCS_derive hequiv_Nom hequiv_assign hequiv_symp sympD)
  then show ?thesis
    using Sat by simp
qed

interpretation Truth_Saturation
  consistent nominals_lbd witness semics semantics \<open>\<lambda>H. {canonical H i |i. True}\<close> rel
proof unfold_locales
  fix p and M :: \<open>('i, 'p, 'w) ctx\<close>
  show \<open>(M \<Turnstile> p) = semics M semantics p\<close>
    by (cases M, induct p) auto
next
  fix p H and M :: \<open>('i, 'p, 'i) ctx\<close>
  assume \<open>\<forall>M \<in> {canonical H i |i. True}. \<forall>p. semics M (rel H) p = rel H M p\<close>
    \<open>M \<in> {canonical H i |i. True}\<close>
  then show \<open>(M \<Turnstile> p) = rel H M p\<close>
    using Hintikka_model' by fast
next
  fix H :: \<open>('i, 'p) lbd set\<close>
  assume \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  then show \<open>\<forall>M\<in>{canonical H i |i. True}. \<forall>p. semics M (rel H) p = rel H M p\<close>
    using Hintikka_Extend' by fast
qed

lemma Truth_lemma:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  shows \<open>(canonical H i \<Turnstile> p) \<longleftrightarrow> (i, p) \<in> H\<close>
proof -
  have \<open>(canonical H i \<Turnstile> p) \<longleftrightarrow> (assign H i, p) \<in> H\<close>
    using truth_lemma_saturation assms by fastforce
  then show ?thesis
    using assms by (meson MCS_Nom_sym hequiv_Nom hequiv_assign hequiv_def)
qed

section \<open>Cardinalities\<close>

datatype marker = FlsM | ImpM | DiaM | SatM

type_synonym ('i, 'p) enc = \<open>('i + 'p) + marker \<times> nat\<close>

abbreviation \<open>NOM i \<equiv> Inl (Inl i)\<close>
abbreviation \<open>PRO x \<equiv> Inl (Inr x)\<close>
abbreviation \<open>FLS \<equiv> Inr (FlsM, 0)\<close>
abbreviation \<open>IMP n \<equiv> Inr (FlsM, n)\<close>
abbreviation \<open>DIA \<equiv> Inr (DiaM, 0)\<close>
abbreviation \<open>SAT \<equiv> Inr (SatM, 0)\<close>

primrec encode :: \<open>('i, 'p) fm \<Rightarrow> ('i, 'p) enc list\<close> where
  \<open>encode \<^bold>\<bottom> = [FLS]\<close>
| \<open>encode (\<^bold>\<ddagger>P) = [PRO P]\<close>
| \<open>encode (\<^bold>\<cdot>i) = [NOM i]\<close>
| \<open>encode (p \<^bold>\<longrightarrow> q) = IMP (length (encode p)) # encode p @ encode q\<close>
| \<open>encode (\<^bold>\<diamond> p) = DIA # encode p\<close>
| \<open>encode (\<^bold>@ i p) = SAT # NOM i # encode p\<close>

lemma encode_ne [simp]: \<open>encode p \<noteq> []\<close>
  by (induct p) auto

lemma inj_encode': \<open>encode p = encode q \<Longrightarrow> p = q\<close>
proof (induct p arbitrary: q)
  case Fls
  then show ?case 
    by (cases q) auto
next
  case (Pro P)
  then show ?case 
    by (cases q) auto
next
  case (Nom i)
  then show ?case 
    by (cases q) auto
next
  case (Imp p1 p2)
  then show ?case 
    by (cases q) auto
next
  case (Dia p)
  then show ?case 
    by (cases q) auto
next
  case (Sat x1a p)
  then show ?case 
    by (cases q) auto
qed

lemma inj_encode: \<open>inj encode\<close>
  unfolding inj_def using inj_encode' by blast

primrec encode_lbd :: \<open>('i, 'p) lbd \<Rightarrow> ('i, 'p) enc list\<close> where
  \<open>encode_lbd (i, p) = NOM i # encode p\<close>

lemma inj_encode_lbd': \<open>encode_lbd (i, p) = encode_lbd (k, q) \<Longrightarrow> i = k \<and> p = q\<close>
  using inj_encode' by auto

lemma inj_encode_lbd: \<open>inj encode_lbd\<close>
  unfolding inj_def using inj_encode_lbd' by auto

lemma finite_marker: \<open>finite (UNIV :: marker set)\<close>
proof -
  have \<open>p \<in> {FlsM, ImpM, DiaM, SatM}\<close> for p
    by (cases p) auto
  then show ?thesis
    by (meson ex_new_if_finite finite.emptyI finite_insert)
qed

lemma card_of_lbd:
  assumes \<open>infinite (UNIV :: 'i set)\<close>
  shows \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |UNIV :: 'i set| +c |UNIV :: 'p set|\<close>
proof -
  have \<open>|UNIV :: marker set| \<le>o |UNIV :: nat set|\<close>
    using finite_marker by (simp add: ordLess_imp_ordLeq)
  moreover have \<open>infinite (UNIV :: ('i + 'p) set)\<close>
    using assms by simp
  ultimately have \<open>|UNIV :: ('i, 'p) enc list set| \<le>o |UNIV :: ('i + 'p) set|\<close>
    using card_of_params_marker_lists by blast
  moreover have \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |UNIV :: ('i, 'p) enc list set|\<close>
    using card_of_ordLeq inj_encode_lbd by blast
  ultimately have \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |UNIV :: ('i + 'p) set|\<close>
    using ordLeq_transitive by blast
  then show ?thesis
    unfolding csum_def by simp
qed

section \<open>Completeness\<close>

theorem strong_completeness:
  fixes p :: \<open>('i, 'p) fm\<close>
  assumes \<open>\<forall>M :: ('i, 'p) model. \<forall>g w.
      (\<forall>(k, q) \<in> X. (M, g, g k) \<Turnstile> q) \<longrightarrow> (M, g, w) \<Turnstile> p\<close>
    \<open>infinite (UNIV :: 'i set)\<close>
    \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals X|\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>@ (i, p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>@ (i, p)\<close>
  then have *: \<open>\<nexists>A. \<exists>a. set A \<subseteq> X \<and> ((i, \<^bold>\<not> p) # A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>))\<close>
    using Boole FlsE by metis

  let ?S = \<open>{(i, \<^bold>\<not> p)} \<union> X\<close>
  let ?H = \<open>Extend ?S\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using * derive_split1 by metis
  moreover have \<open>infinite (UNIV - nominals X)\<close>
    using assms(2-3)
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals X - nominals_lbd (i, \<^bold>\<not> p)|\<close>
    using assms(3) finite_nominals_lbd card_of_infinite_diff_finite
    by (metis ordIso_iff_ordLeq ordLeq_transitive)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - (nominals X \<union> nominals_lbd (i, \<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals ?S|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |UNIV - nominals ?S|\<close>
    using assms card_of_lbd ordLeq_transitive by blast
  ultimately have \<open>consistent ?H\<close> \<open>maximal ?H\<close> \<open>saturated ?H\<close>
    using MCS_Extend by fast+
  then have \<open>canonical ?H i \<Turnstile> p \<longleftrightarrow> (i, p) \<in> ?H\<close> for i p
    using Truth_lemma by fast
  then have \<open>(i, p) \<in> ?S \<Longrightarrow> canonical ?H i \<Turnstile> p\<close> for i p
    using Extend_subset by blast
  then have \<open>canonical ?H i \<Turnstile> \<^bold>\<not> p\<close> \<open>\<forall>(k, q) \<in> X. canonical ?H k \<Turnstile> q\<close>
    by blast+
  moreover from this have \<open>canonical ?H i \<Turnstile> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>('i, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(M :: ('i, 'p) model) g w. (M, g, w) \<Turnstile> p\<close>

theorem completeness:
  fixes p :: \<open>('i, 'p) fm\<close>
  assumes \<open>valid p\<close> \<open>infinite (UNIV :: 'i set)\<close> \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'i set|\<close>
  shows \<open>[] \<turnstile>\<^sub>@ (i, p)\<close>
proof -
  have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV :: 'i set|\<close>
    using assms(2-3) by (simp add: cinfinite_def csum_absorb1 ordIso_imp_ordLeq)
  then show ?thesis
    using assms strong_completeness[where X=\<open>{}\<close> and p=p] infinite_UNIV_listI by auto
qed

corollary completeness':
  fixes p :: \<open>('i, 'i) fm\<close>
  assumes \<open>valid p\<close> \<open>infinite (UNIV :: 'i set)\<close>
  shows \<open>[] \<turnstile>\<^sub>@ (i, p)\<close>
  using assms completeness[of p] by simp

theorem main:
  fixes p :: \<open>('i, 'p) fm\<close>
  assumes \<open>i \<notin> nominals_fm p\<close> \<open>infinite (UNIV :: 'i set)\<close> \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'i set|\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>@ (i, p)\<close>
  using assms completeness soundness' by metis

corollary main':
  fixes p :: \<open>('i, 'i) fm\<close>
  assumes \<open>i \<notin> nominals_fm p\<close> \<open>infinite (UNIV :: 'i set)\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>@ (i, p)\<close>
  using assms completeness' soundness' by metis

end
