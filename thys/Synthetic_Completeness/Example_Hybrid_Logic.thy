(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for Basic Hybrid Logic
  Author: Asta Halkjær From
*)

chapter \<open>Example: Hybrid Logic\<close>

theory Example_Hybrid_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype (nominals_fm: 'i, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Nom 'i (\<open>\<^bold>\<bullet>\<close>)
  | Imp \<open>('i, 'p) fm\<close> \<open>('i, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Dia \<open>('i, 'p) fm\<close> (\<open>\<^bold>\<diamond>\<close>)
  | Sat 'i \<open>('i, 'p) fm\<close> (\<open>\<^bold>@\<close>)
  | All \<open>('i, 'p) fm\<close> (\<open>\<^bold>A\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Con (infixr \<open>\<^bold>\<and>\<close> 35) where \<open>p \<^bold>\<and> q \<equiv> \<^bold>\<not> (p \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>

type_synonym ('i, 'p) lbd = \<open>'i \<times> ('i, 'p) fm\<close>

primrec nominals_lbd :: \<open>('i, 'p) lbd \<Rightarrow> 'i set\<close> where
  \<open>nominals_lbd (i, p) = {i} \<union> nominals_fm p\<close>

abbreviation nominals :: \<open>('i, 'p) lbd set \<Rightarrow> 'i set\<close> where
  \<open>nominals S \<equiv> \<Union>ip \<in> S. nominals_lbd ip\<close>

lemma finite_nominals_fm [simp]: \<open>finite (nominals_fm p)\<close>
  by (induct p) simp_all

lemma finite_nominals_lbd: \<open>finite (nominals_lbd p)\<close>
  by (cases p) simp

section \<open>Semantics\<close>

datatype ('w, 'p) model =
  Model (W: \<open>'w set\<close>) (R: \<open>'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'p \<Rightarrow> bool\<close>)

type_synonym ('i, 'p, 'w) ctx = \<open>('w, 'p) model \<times> ('i \<Rightarrow> 'w) \<times> 'w\<close>

fun semantics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>@\<close> 50) where
  \<open>(M, g, w) \<Turnstile>\<^sub>@ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, _, w) \<Turnstile>\<^sub>@ \<^bold>\<cdot>P \<longleftrightarrow> V M w P\<close>
| \<open>(_, g, w) \<Turnstile>\<^sub>@ \<^bold>\<bullet>i \<longleftrightarrow> w = g i\<close>
| \<open>(M, g, w) \<Turnstile>\<^sub>@ p \<^bold>\<longrightarrow> q \<longleftrightarrow> (M, g, w) \<Turnstile>\<^sub>@ p \<longrightarrow> (M, g, w) \<Turnstile>\<^sub>@ q\<close>
| \<open>(M, g, w) \<Turnstile>\<^sub>@ \<^bold>\<diamond> p \<longleftrightarrow> (\<exists>v \<in> W M \<inter> R M w. (M, g, v) \<Turnstile>\<^sub>@ p)\<close>
| \<open>(M, g, _) \<Turnstile>\<^sub>@ \<^bold>@i p \<longleftrightarrow> (M, g, g i) \<Turnstile>\<^sub>@ p\<close>
| \<open>(M, g, _) \<Turnstile>\<^sub>@ \<^bold>A p \<longleftrightarrow> (\<forall>v \<in> W M. (M, g, v) \<Turnstile>\<^sub>@ p)\<close>

lemma semantics_fresh: \<open>i \<notin> nominals_fm p \<Longrightarrow> (M, g, w) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (M, g(i := v), w) \<Turnstile>\<^sub>@ p\<close>
  by (induct p arbitrary: w) auto

lemma semantics_fresh_lbd:
  \<open>k \<notin> nominals_lbd (i, p) \<Longrightarrow> (M, g, w) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (M, g(k := v), w) \<Turnstile>\<^sub>@ p\<close>
  by (induct p arbitrary: w) auto

section \<open>Calculus\<close>

inductive Calculus :: \<open>('i, 'p) lbd list \<Rightarrow> ('i, 'p) lbd \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>@\<close> 50) where
  Assm [simp]: \<open>(i, p) \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
| Ref [simp]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<bullet>i)\<close>
| Nom [dest]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<bullet>k) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| ImpI [intro]: \<open>(i, p) # A \<turnstile>\<^sub>@ (i, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q)\<close>
| ImpE [dest]: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, q)\<close>
| SatI [intro]: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, \<^bold>@i p)\<close>
| SatE [dest]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>@k p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| DiaI [intro]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p)\<close>
| DiaE [elim]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p) \<Longrightarrow> k \<notin> nominals ({(i, p), (j, q)} \<union> set A) \<Longrightarrow>
    (k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) # A \<turnstile>\<^sub>@ (j, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (j, q)\<close>
| AllI [intro]: \<open>A \<turnstile>\<^sub>@ (k, p) \<Longrightarrow> k \<notin> nominals ({(i, p)} \<union> set A) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, \<^bold>A p)\<close>
| AllE [dest]: \<open>A \<turnstile>\<^sub>@ (i, \<^bold>A p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
| Clas: \<open>(i, p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
| Cut: \<open>A \<turnstile>\<^sub>@ (k, q) \<Longrightarrow> (k, q) # B \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A @ B \<turnstile>\<^sub>@ (i, p)\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> list_all (\<lambda>(i, p). (M, g, g i) \<Turnstile>\<^sub>@ p) A \<Longrightarrow> range g \<subseteq> W M \<Longrightarrow> (M, g, g i) \<Turnstile>\<^sub>@ p\<close>
proof (induct \<open>(i, p)\<close> arbitrary: i p g rule: Calculus.induct)
  case (Nom A i k p)
  then show ?case
    by (metis semantics.simps(3))
next
  case (DiaE A i p k j q)
  then have \<open>(M, g, g i) \<Turnstile>\<^sub>@ \<^bold>\<diamond> p\<close>
    by blast
  then obtain v where v: \<open>v \<in> W M \<inter> R M (g i)\<close> \<open>(M, g, v) \<Turnstile>\<^sub>@ p\<close>
    by auto
  let ?g = \<open>g(k := v)\<close>
  have \<open>(M, ?g, ?g k) \<Turnstile>\<^sub>@ p\<close> \<open>(M, ?g, ?g i) \<Turnstile>\<^sub>@ \<^bold>\<diamond> (\<^bold>\<bullet>k)\<close>
    using v fun_upd_same DiaE(3) semantics_fresh_lbd by fastforce+
  moreover have \<open>list_all (\<lambda>(i, p). (M, ?g, ?g i) \<Turnstile>\<^sub>@ p) A\<close>
    using DiaE.prems(1) DiaE.hyps(3) semantics_fresh_lbd by (fastforce simp: list_all_iff)
  ultimately have \<open>list_all (\<lambda>(i, p). (M, ?g, ?g i) \<Turnstile>\<^sub>@ p) ((k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) # A)\<close>
    by simp
  moreover have \<open>range ?g \<subseteq> W M\<close>
    using DiaE.prems v by auto
  ultimately have \<open>(M, ?g, ?g j) \<Turnstile>\<^sub>@ q\<close>
    using DiaE.hyps by blast
  then show ?case
    using DiaE.hyps(3) semantics_fresh_lbd by fastforce
next
  case (AllI A k p i)
  {
    fix v
    assume \<open>v \<in> W M\<close>
    let ?g = \<open>g(k := v)\<close>
    have \<open>\<forall>v. list_all (\<lambda>(i, p). (M, ?g, ?g i) \<Turnstile>\<^sub>@ p) A\<close>
      using AllI.prems(1) AllI.hyps(3) semantics_fresh_lbd by (fastforce simp: list_all_iff)
    moreover have \<open>range ?g \<subseteq> W M\<close>
      using AllI.prems \<open>v \<in> W M\<close> by auto
    ultimately have \<open>(M, ?g, ?g k) \<Turnstile>\<^sub>@ p\<close>
      using AllI.hyps by fast
  }
  then have \<open>\<forall>v \<in> W M. (M, g(k := v), v) \<Turnstile>\<^sub>@ p\<close>
    by simp
  then have \<open>\<forall>v \<in> W M. (M, g, v) \<Turnstile>\<^sub>@ p\<close>
    using AllI.hyps(3) semantics_fresh_lbd by fast
  then show ?case
    by simp
next
  case (AllE A i p k)
  then show ?case
    by fastforce
qed (auto simp: list_all_iff)

corollary soundness':
  assumes \<open>[] \<turnstile>\<^sub>@ (i, p)\<close> \<open>i \<notin> nominals_fm p\<close>
    and \<open>range g \<subseteq> W M\<close> \<open>w \<in> W M\<close>
  shows \<open>(M, g, w) \<Turnstile>\<^sub>@ p\<close>
proof -
  let ?g = \<open>g(i := w)\<close>
  have \<open>range ?g \<subseteq> W M\<close>
    using assms(3-4) by auto
  then have \<open>(M, ?g, ?g i) \<Turnstile>\<^sub>@ p\<close>
    using assms(1, 4) soundness by (metis list_all_simps(2))
  then have \<open>(M, ?g, w) \<Turnstile>\<^sub>@ p\<close>
    by simp
  then show ?thesis
    using assms(2) semantics_fresh by fast
qed

corollary \<open>\<not> ([] \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>))\<close>
  by (metis list.pred_inject(1) model.sel(1) semantics.simps(1) soundness subset_refl)

section \<open>Admissible Rules\<close>

lemma Assm_head [simp]: \<open>(p, i) # A \<turnstile>\<^sub>@ (p, i)\<close>
  by auto

lemma SatE':
  assumes \<open>(k, q) # A \<turnstile>\<^sub>@ (i, p)\<close>
  shows \<open>(j, \<^bold>@k q) # A \<turnstile>\<^sub>@ (i, p)\<close>
proof -
  have \<open>[(j, \<^bold>@k q)] \<turnstile>\<^sub>@ (k, q)\<close>
    by (meson Assm_head SatE)
  then show ?thesis
    using assms by (auto dest: Cut)
qed

lemma ImpI':
  assumes \<open>(k, q) # A \<turnstile>\<^sub>@ (i, p)\<close>
  shows \<open>A \<turnstile>\<^sub>@ (i, (\<^bold>@k q) \<^bold>\<longrightarrow> p)\<close>
  using assms SatE' by fast

lemma Weak': \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A @ B \<turnstile>\<^sub>@ (i, p)\<close>
  by (simp add: Cut)

lemma Weaken: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> B \<turnstile>\<^sub>@ (i, p)\<close>
proof (induct A arbitrary: p)
  case Nil
  then show ?case
    by (metis Weak' append_Nil)
next
  case (Cons kq A)
  then show ?case
  proof (cases kq)
    case (Pair k q)
    then have \<open>B \<turnstile>\<^sub>@ (i, \<^bold>@k q \<^bold>\<longrightarrow> p)\<close>
      using Cons by (simp add: ImpI')
    then show ?thesis
      using Pair Cons(3) by fastforce
  qed
qed

lemma Weak: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> (k, q) # A \<turnstile>\<^sub>@ (i, p)\<close>
  using Weaken[where A=A and B=\<open>(k, q) # A\<close>] by auto

lemma deduct1: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> (i, p) # A \<turnstile>\<^sub>@ (i, q)\<close>
  by (meson ImpE Weak Assm_head)

lemma Boole: \<open>(i, \<^bold>\<not> p) # A \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
  using Clas FlsE by meson

interpretation Derivations Calculus
proof
  fix A and p :: \<open>('i, 'p) lbd\<close>
  show \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>@(p)\<close>
    by (cases p) simp
next
  fix A B and p :: \<open>('i, 'p) lbd\<close>
  assume \<open>A \<turnstile>\<^sub>@(p)\<close> \<open>set A = set B\<close>
  then show \<open>B \<turnstile>\<^sub>@(p)\<close>
    by (cases p) (simp add: Weaken)
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('i, 'p) lbd set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A a. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>

lemma consistent_add_diamond_witness:
  assumes \<open>consistent S\<close> \<open>(i, \<^bold>\<diamond> p) \<in> S\<close> \<open>k \<notin> nominals S\<close>
  shows \<open>consistent ({(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))} \<union> S)\<close>
  unfolding consistent_def
proof safe
  fix A a
  assume A: \<open>set A \<subseteq> {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))} \<union> S\<close> \<open>A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
  then obtain A' a B where \<open>set A' \<subseteq> S\<close> \<open>B @ A' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close> \<open>set B = {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))} \<inter> set A\<close>
    using assms derive_split[where p=\<open>(a, \<^bold>\<bottom>)\<close> and X=S and B=\<open>[(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))]\<close>]
    by (metis Int_commute empty_set list.simps(15))
  then have \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) # A' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
    by (auto intro: Weaken)
  then have \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) # A' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by fast
  then have \<open>(k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) # (i, \<^bold>\<diamond> p) # A' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by (fastforce intro: Weaken)
  moreover have \<open>k \<notin> nominals ({(i, p), (i, \<^bold>\<bottom>)} \<union> set ((i, \<^bold>\<diamond> p) # A'))\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2-3) by auto
  moreover have \<open>(i, \<^bold>\<diamond> p) # A' \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p)\<close>
    by auto
  ultimately have \<open>(i, \<^bold>\<diamond> p) # A' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by fast
  moreover have \<open>set ((i, \<^bold>\<diamond> p) # A') \<subseteq> S\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_global_witness:
  assumes \<open>consistent S\<close> \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> S\<close> \<open>k \<notin> nominals S\<close>
  shows \<open>consistent ({(k, \<^bold>\<not> p)} \<union> S)\<close>
  unfolding consistent_def
proof safe
  fix A a
  assume \<open>set A \<subseteq> {(k, \<^bold>\<not> p)} \<union> S \<close> \<open>A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
  then obtain A' where \<open>set A' \<subseteq> S\<close> \<open>(k, \<^bold>\<not> p) # A' \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
    using assms derive_split1 by (metis consistent_def insert_is_Un subset_insert)
  then have \<open>(k, \<^bold>\<not> p) # A' \<turnstile>\<^sub>@ (k, \<^bold>\<bottom>)\<close>
    by fast
  then have \<open>A' \<turnstile>\<^sub>@ (k, p)\<close>
    by (meson Boole)
  moreover have \<open>k \<notin> nominals ({(i, p), (i, \<^bold>\<bottom>)} \<union> set ((i, \<^bold>A p) # A'))\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2-3) by auto
  ultimately have \<open>A' \<turnstile>\<^sub>@ (i, \<^bold>A p)\<close>
    by fastforce
  then have \<open>(i, \<^bold>\<not> \<^bold>A p) # A' \<turnstile>\<^sub>@ (i, \<^bold>\<bottom>)\<close>
    by (meson Assm_head ImpE Weak)
  moreover have \<open>set ((i, \<^bold>\<not> \<^bold>A p) # A') \<subseteq> S\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

fun witness :: \<open>('i, 'p) lbd \<Rightarrow> ('i, 'p) lbd set \<Rightarrow> ('i, 'p) lbd set\<close> where
  \<open>witness (i, \<^bold>\<diamond> p) S = (let k = SOME k. k \<notin> nominals ({(i, p)} \<union> S) in {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))})\<close>
| \<open>witness (i, \<^bold>\<not> \<^bold>A p) S = (let k = SOME k. k \<notin> nominals ({(i, p)} \<union> S) in {(k, \<^bold>\<not> p)})\<close>
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
  then obtain k where \<open>witness (i, \<^bold>\<diamond> p) S = {(k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))}\<close>
    \<open>k \<notin> nominals ({(i, \<^bold>\<diamond> p)} \<union> S)\<close>
    by (simp add: Let_def)
  then show ?case
    using 1(1) consistent_add_diamond_witness[where S=\<open>{(i, \<^bold>\<diamond> p)} \<union> S\<close>] by simp
next
  case (2 i p S)
  have \<open>infinite (UNIV - nominals ({(i, p)} \<union> S))\<close>
    using 2(2) finite_nominals_lbd
    by (metis UN_Un finite.emptyI finite.insertI finite_UN_I infinite_Diff_fin_Un)
  then have \<open>\<exists>k. k \<notin> nominals ({(i, p)} \<union> S)\<close>
    by (simp add: not_finite_existsD set_diff_eq)
  then have \<open>(SOME k. k \<notin> nominals ({(i, p)} \<union> S)) \<notin> nominals ({(i, p)} \<union> S)\<close>
    by (rule someI_ex)
  then obtain k where \<open>witness (i, \<^bold>\<not> \<^bold>A p) S = {(k, \<^bold>\<not> p)}\<close> \<open>k \<notin> nominals ({(i, \<^bold>\<not> \<^bold>A p)} \<union> S)\<close>
    by (simp add: Let_def)
  then show ?case
    using 2(1) consistent_add_global_witness[where S=\<open>{(i, \<^bold>\<not> \<^bold>A p)} \<union> S\<close>] by auto
qed (auto simp: assms)

interpretation MCS_Witness_UNIV consistent witness nominals_lbd
proof
  fix ip :: \<open>('i, 'p) lbd\<close> and S :: \<open>('i, 'p) lbd set\<close>
  show \<open>finite (nominals (witness ip S))\<close>
    by (induct ip S rule: witness.induct) (auto simp: Let_def)
next
  fix ip and S :: \<open>('i, 'p) lbd set\<close>
  assume \<open>consistent ({ip} \<union> S)\<close> \<open>infinite (UNIV - nominals S)\<close>
  then show \<open>consistent ({ip} \<union> S \<union> witness ip S)\<close>
    using consistent_witness' by (cases ip) (simp add: sup_commute)
next
  have \<open>infinite (UNIV :: ('i, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<^bold>\<diamond>\<close>] by simp
  then show \<open>infinite (UNIV :: ('i, 'p) lbd set)\<close>
    using finite_prod by blast
qed (auto simp: consistent_def)

lemma witnessed_diamond: \<open>witnessed S \<Longrightarrow> (i, \<^bold>\<diamond> p) \<in> S \<Longrightarrow> \<exists>k. (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S \<and> (k, p) \<in> S\<close>
  unfolding witnessed_def by (metis insert_subset witness.simps(1))

lemma witnessed_global: \<open>witnessed S \<Longrightarrow> (i, \<^bold>\<not> \<^bold>A p) \<in> S \<Longrightarrow> \<exists>k. (k, \<^bold>\<not> p) \<in> S\<close>
  unfolding witnessed_def by (metis insert_subset witness.simps(2))

interpretation Derivations_Cut_MCS consistent Calculus
proof
  show \<open>\<And>S. consistent S = (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile>\<^sub>@(q)))\<close>
    unfolding consistent_def using FlsE by fast
next
  fix A B and p q :: \<open>('i, 'p) lbd\<close>
  assume \<open>A \<turnstile>\<^sub>@(p)\<close> \<open>p # B \<turnstile>\<^sub>@(q)\<close>
  then show \<open>A @ B \<turnstile>\<^sub>@(q)\<close>
    by (cases p, cases q) (meson Cut)
qed

interpretation Derivations_Bot consistent Calculus \<open>(i, \<^bold>\<bottom>)\<close>
proof qed auto

interpretation Derivations_Not consistent Calculus \<open>(i, \<^bold>\<bottom>)\<close> \<open>\<lambda>(i, p). (i, \<^bold>\<not> p)\<close>
proof qed auto

lemma MCS_impE': \<open>consistent S \<Longrightarrow> maximal S \<Longrightarrow> (i, p \<^bold>\<longrightarrow> q) \<in> S \<Longrightarrow> (i, p) \<in> S \<longrightarrow> (i, q) \<in> S\<close>
  by (metis MCS_derive deduct1 insert_subset list.simps(15))

interpretation Derivations_Uni consistent witness nominals_lbd Calculus \<open>(i, \<^bold>\<bottom>)\<close> \<open>\<lambda>(i, p). (i, \<^bold>\<not> p)\<close>
  \<open>\<lambda>(i, p). (i, \<^bold>A p)\<close> \<open>\<lambda>k (i, p). (k, p)\<close>
proof
  have \<open>\<And>S S' i p. MCS S \<Longrightarrow> witness (i, \<^bold>\<not> \<^bold>A p) S' \<subseteq> S \<Longrightarrow> \<exists>k. (k, \<^bold>\<not> p) \<in> S\<close>
    by auto
  then show \<open>\<And>S S' p. MCS S \<Longrightarrow>
       witness (case case p of (i, p) \<Rightarrow> (i, \<^bold>A p) of (i, p) \<Rightarrow> (i, \<^bold>\<not> p)) S' \<subseteq> S \<Longrightarrow>
       \<exists>t. (case case p of (i, p) \<Rightarrow> (t, p) of (i, p) \<Rightarrow> (i, \<^bold>\<not> p)) \<in> S\<close>
    by fast
next
  have \<open>\<And>A i p k. A \<turnstile>\<^sub>@ (i, \<^bold>A p) \<Longrightarrow> A \<turnstile>\<^sub>@ (k, p)\<close>
    ..
  then show \<open>\<And>A p t. A \<turnstile>\<^sub>@ (case p of (i, p) \<Rightarrow> (i, \<^bold>A p)) \<Longrightarrow> A \<turnstile>\<^sub>@ (case p of (i, p) \<Rightarrow> (t, p))\<close>
    by fast
qed

lemma conE1 [elim]: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<and> q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p)\<close>
  by (meson Clas FlsE deduct1)

lemma conE2 [elim]: \<open>A \<turnstile>\<^sub>@ (i, p \<^bold>\<and> q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, q)\<close>
  by (meson Assm_head Boole ImpE ImpI Weak)

lemma conI [intro]: \<open>A \<turnstile>\<^sub>@ (i, p) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, q) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, p \<^bold>\<and> q)\<close>
  by (meson Assm_head ImpE ImpI Weak)

lemma MCS_con:
  assumes \<open>MCS S\<close>
  shows \<open>(i, p \<^bold>\<and> q) \<in> S \<longleftrightarrow> (i, p) \<in> S \<and> (i, q) \<in> S\<close>
  using assms MCS_derive conE1 conE2
  by (metis Boole MCS_explode MCS_impE' derive_assm list.set_intros(1))

interpretation Derivations_Exi consistent witness nominals_lbd Calculus
  \<open>\<lambda>(i, p). (i, \<^bold>\<diamond> p)\<close> \<open>\<lambda>k (i, p). (i, \<^bold>@k p \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<bullet>k))\<close>
proof
  have \<open>\<And>S S' i p. MCS S \<Longrightarrow> witness (i, \<^bold>\<diamond> p) S' \<subseteq> S \<Longrightarrow> \<exists>k. (i, \<^bold>@ k p \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<bullet> k)) \<in> S\<close>
    unfolding witness.simps using MCS_con by (metis MCS_derive SatI insert_subset)
  then show \<open>\<And>S S' p. MCS S \<Longrightarrow> witness (case p of (i, p) \<Rightarrow> (i, \<^bold>\<diamond> p)) S' \<subseteq> S \<Longrightarrow> \<exists>t. (case p of (i, p) \<Rightarrow> (i, \<^bold>@ t p \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<bullet> t))) \<in> S\<close>
    by fast
next
  have \<open>\<And>A i k p. A \<turnstile>\<^sub>@ (i, \<^bold>@ k p \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<bullet> k)) \<Longrightarrow> A \<turnstile>\<^sub>@ (i, \<^bold>\<diamond> p)\<close>
    by (metis DiaI SatE conE1 conE2)
  then show \<open>\<And>A p t. A \<turnstile>\<^sub>@ (case p of (i, p) \<Rightarrow> (i, \<^bold>@ t p \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<bullet> t))) \<Longrightarrow> A \<turnstile>\<^sub>@ (case p of (i, p) \<Rightarrow> (i, \<^bold>\<diamond> p))\<close>
    by fast
qed

corollary MCS_uni':
  assumes \<open>MCS S\<close> \<open>witnessed S\<close>
  shows \<open>(i, \<^bold>A p) \<in> S \<longleftrightarrow> (\<forall>k. (k, p) \<in> S)\<close>
  using assms MCS_uni by fastforce

corollary MCS_exi':
  assumes \<open>MCS S\<close> \<open>witnessed S\<close>
  shows \<open>(i, \<^bold>\<diamond> p) \<in> S \<longleftrightarrow> (\<exists>k. (i, \<^bold>@k p \<^bold>\<and> \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S)\<close>
  using assms MCS_exi by fastforce

section \<open>Nominals\<close>

lemma MCS_Nom_refl:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>(i, \<^bold>\<bullet>i) \<in> S\<close>
  using assms Ref by (metis MCS_derive MCS_explode)

lemma MCS_Nom_sym:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(k, \<^bold>\<bullet>i) \<in> S\<close>
  using assms Nom Ref by (metis MCS_derive)

lemma MCS_Nom_trans:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>(i, \<^bold>\<bullet>j) \<in> S\<close> \<open>(j, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
proof -
  have \<open>[(i, \<^bold>\<bullet>j), (j, \<^bold>\<bullet>k)] \<turnstile>\<^sub>@ (i, \<^bold>\<bullet>j)\<close> \<open>[(i, \<^bold>\<bullet>j), (j, \<^bold>\<bullet>k)] \<turnstile>\<^sub>@ (j, \<^bold>\<bullet>k)\<close>
    by simp_all
  then have \<open>[(i, \<^bold>\<bullet>j), (j, \<^bold>\<bullet>k)] \<turnstile>\<^sub>@ (i, \<^bold>\<bullet>k)\<close>
    using Nom Ref by metis
  then show ?thesis
    using assms MCS_derive
    by (metis bot.extremum insert_subset list.set(1) list.simps(15))
qed

section \<open>Truth Lemma\<close>

fun semics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> (('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close>
  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>@ _)\<close> [55, 0, 55] 55) where
  \<open>_ \<lbrakk>_\<rbrakk>\<^sub>@ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, _, w) \<lbrakk>_\<rbrakk>\<^sub>@ \<^bold>\<cdot>P \<longleftrightarrow> V M w P\<close>
| \<open>(_, g, w) \<lbrakk>_\<rbrakk>\<^sub>@ \<^bold>\<bullet>i \<longleftrightarrow> w = g i\<close>
| \<open>(M, g, w) \<lbrakk>\<R>\<rbrakk>\<^sub>@(p) \<^bold>\<longrightarrow> q \<longleftrightarrow> \<R> (M, g, w) p \<longrightarrow> \<R> (M, g, w) q\<close>
| \<open>(M, g, w) \<lbrakk>\<R>\<rbrakk>\<^sub>@ \<^bold>\<diamond> p \<longleftrightarrow> (\<exists>v \<in> W M \<inter> R M w. \<R> (M, g, v) p)\<close>
| \<open>(M, g, _) \<lbrakk>\<R>\<rbrakk>\<^sub>@ \<^bold>@i p \<longleftrightarrow> \<R> (M, g, g i) p\<close>
| \<open>(M, g, _) \<lbrakk>\<R>\<rbrakk>\<^sub>@ \<^bold>A p \<longleftrightarrow> (\<forall>v \<in> W M. \<R> (M, g, v) p)\<close>

fun rel :: \<open>('i, 'p) lbd set \<Rightarrow> ('i, 'p, 'i) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (\<open>\<R>\<^sub>@\<close>) where
  \<open>\<R>\<^sub>@(S) (_, _, i) p \<longleftrightarrow> (i, p) \<in> S\<close>

definition equiv_nom :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool\<close> where
  \<open>equiv_nom S i k \<equiv> (i, \<^bold>\<bullet>k) \<in> S\<close>

lemma equiv_nom_reflp:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>reflp (equiv_nom S)\<close>
  unfolding equiv_nom_def reflp_def using assms MCS_Nom_refl by fast

lemma equiv_nom_symp:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>symp (equiv_nom S)\<close>
  unfolding equiv_nom_def symp_def using assms MCS_Nom_sym by fast

lemma equiv_nom_transp:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>transp (equiv_nom S)\<close>
  unfolding equiv_nom_def transp_def using assms MCS_Nom_trans by fast

lemma equiv_nom_equivp:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>equivp (equiv_nom S)\<close>
  using assms by (simp add: equivpI equiv_nom_reflp equiv_nom_symp equiv_nom_transp)

definition assign :: \<open>'i \<Rightarrow> ('i, 'p) lbd set \<Rightarrow> 'i\<close> (\<open>[_]\<^sub>_\<close> [0, 100] 100) where
  \<open>[i]\<^sub>S \<equiv> minim ( |UNIV| ) {k. equiv_nom S i k}\<close>

lemma equiv_nom_ne:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>{k. equiv_nom S i k} \<noteq> {}\<close>
  unfolding equiv_nom_def using assms MCS_Nom_refl by fast

lemma equiv_nom_assign:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>equiv_nom S i ([i]\<^sub>S)\<close>
  unfolding assign_def using assms equiv_nom_ne wo_rel.minim_in
  by (metis Field_card_of card_of_well_order_on mem_Collect_eq top.extremum wo_rel_def)

lemma equiv_nom_Nom:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>equiv_nom S i k\<close> \<open>(i, p) \<in> S\<close>
  shows \<open>(k, p) \<in> S\<close>
proof -
  have \<open>[(i, \<^bold>\<bullet>k), (i, p)] \<turnstile>\<^sub>@ (k, p)\<close>
    by (meson Assm_head Nom Weak)
  then show ?thesis
    using assms MCS_derive unfolding equiv_nom_def by force
qed

definition reach :: \<open>('i, 'p) lbd set \<Rightarrow> 'i \<Rightarrow> 'i set\<close> where
  \<open>reach S i \<equiv> {[k]\<^sub>S |k. (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S}\<close>

primrec canonical :: \<open>('i, 'p) lbd set \<times> 'i \<Rightarrow> ('i, 'p, 'i) ctx\<close> (\<open>\<M>\<^sub>@\<close>) where
  \<open>\<M>\<^sub>@(S, i) = (Model {[k]\<^sub>S | k. True} (reach S) (\<lambda>i P. (i, \<^bold>\<cdot>P) \<in> S), \<lambda>i. [i]\<^sub>S, [i]\<^sub>S)\<close>

theorem saturated_model:
  assumes \<open>\<And>p i. \<M>\<^sub>@(S, i) \<lbrakk>\<R>\<^sub>@(S)\<rbrakk>\<^sub>@(p) \<longleftrightarrow> \<R>\<^sub>@(S) (\<M>\<^sub>@(S, i)) p\<close> \<open>M \<in> {\<M>\<^sub>@(S, i) |i. True}\<close>
  shows \<open>\<R>\<^sub>@(S) (\<M>\<^sub>@(S, i)) p \<longleftrightarrow> \<M>\<^sub>@(S, i) \<Turnstile>\<^sub>@ p\<close>
proof (induct p arbitrary: i rule: wf_induct[where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms(1)[of i x] assms(2)
    by (cases x) (auto simp: reach_def)
qed

lemma reach_assign: \<open>reach S ([i]\<^sub>S) \<subseteq> {[k]\<^sub>S | k. True}\<close>
  unfolding reach_def assign_def by blast

theorem saturated_MCS:
  assumes \<open>MCS S\<close>
  shows \<open>\<M>\<^sub>@(S, i) \<lbrakk>\<R>\<^sub>@(S)\<rbrakk>\<^sub>@(p) \<longleftrightarrow> \<R>\<^sub>@(S) (\<M>\<^sub>@(S, i)) p\<close>
proof (cases p)
  case (Nom k)
  have \<open>([i]\<^sub>S = [k]\<^sub>S) \<longleftrightarrow> ([i]\<^sub>S, \<^bold>\<bullet>k) \<in> S\<close>
    using assms equiv_nom_equivp equiv_nom_assign by (metis assign_def equivp_def equiv_nom_def)
  then show ?thesis
    using Nom by simp
next
  case (Imp p q)
  have \<open>(([i]\<^sub>S, p) \<in> S \<longrightarrow> ([i]\<^sub>S, q) \<in> S) \<longleftrightarrow> ([i]\<^sub>S, p \<^bold>\<longrightarrow> q) \<in> S\<close>
    using assms MCS_derive MCS_explode MCS_impE' by (metis ImpI Weaken set_subset_Cons)
  then show ?thesis
    using Imp by simp
next
  case (Dia p)
  have \<open>([i]\<^sub>S, \<^bold>\<diamond> p) \<in> S \<longleftrightarrow> (\<exists>k. ([i]\<^sub>S, \<^bold>@k p \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<bullet>k)) \<in> S)\<close>
    using assms MCS_exi by fastforce

  moreover have \<open>([i]\<^sub>S, \<^bold>@k p \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<bullet>k)) \<in> S \<longleftrightarrow> ([i]\<^sub>S, \<^bold>@k p) \<in> S \<and> ([i]\<^sub>S, \<^bold>\<diamond>(\<^bold>\<bullet>k)) \<in> S\<close> for k
    using assms MCS_con by fast
  moreover have \<open>([i]\<^sub>S, \<^bold>@k p) \<in> S \<longleftrightarrow> (k, p) \<in> S\<close> for k
    using assms by (meson MCS_derive SatE SatI)
  moreover have \<open>(k, p) \<in> S \<longleftrightarrow> ([k]\<^sub>S, p) \<in> S\<close> for k
    using assms by (meson MCS_Nom_refl equiv_nom_Nom equiv_nom_assign equiv_nom_def)
  moreover have \<open>([i]\<^sub>S, \<^bold>\<diamond>(\<^bold>\<bullet>k)) \<in> S \<Longrightarrow> [k]\<^sub>S \<in> reach S ([i]\<^sub>S)\<close> for k
    unfolding reach_def by blast

  ultimately have \<open>([i]\<^sub>S, \<^bold>\<diamond> p) \<in> S \<longleftrightarrow> (\<exists>k \<in> reach S ([i]\<^sub>S). (k, p) \<in> S)\<close>
    unfolding reach_def by blast
  then show ?thesis
    using Dia reach_assign by fastforce
next
  case (Sat k p)
  have \<open>([k]\<^sub>S, p) \<in> S \<longleftrightarrow> ([i]\<^sub>S, \<^bold>@k p) \<in> S\<close>
    by (metis SatE SatI assms MCS_derive equiv_nom_Nom equiv_nom_assign equiv_nom_symp sympD)
  then show ?thesis
    using Sat by simp
next
  case (All p)
  have \<open>([i]\<^sub>S, \<^bold>A p) \<in> S \<longleftrightarrow> (\<forall>k. (k, p) \<in> S)\<close>
    using assms MCS_uni by fastforce
  then have \<open>([i]\<^sub>S, \<^bold>A p) \<in> S \<longleftrightarrow> (\<forall>k. ([k]\<^sub>S, p) \<in> S)\<close>
    by (meson MCS_Nom_sym assms equiv_nom_Nom equiv_nom_assign equiv_nom_def)
  then show ?thesis
    using All by auto
qed (use assms in auto)

interpretation Truth_Witness semics semantics \<open>\<lambda>S. {\<M>\<^sub>@(S, i) |i. True}\<close> rel consistent witness nominals_lbd
proof
  fix p and M :: \<open>('i, 'p, 'w) ctx\<close>
  show \<open>(M \<Turnstile>\<^sub>@ p) = M \<lbrakk>semantics\<rbrakk>\<^sub>@(p)\<close>
    by (cases M, induct p) auto
next
  fix p M and S :: \<open>('i, 'p) lbd set\<close>
  assume \<open>\<forall>p. \<forall>M\<in>{\<M>\<^sub>@ (S, i) |i. True}. M \<lbrakk>\<R>\<^sub>@(S)\<rbrakk>\<^sub>@ p \<longleftrightarrow> \<R>\<^sub>@(S) M p\<close> \<open>M \<in> {\<M>\<^sub>@(S, i) |i. True}\<close>
  then show \<open>M \<Turnstile>\<^sub>@ p \<longleftrightarrow> \<R>\<^sub>@(S) M p\<close>
    using saturated_model by fast
next                
  fix S :: \<open>('i, 'p) lbd set\<close>
  assume \<open>MCS S\<close>
  then show \<open>\<forall>p. \<forall>M\<in>{\<M>\<^sub>@(S, i) |i. True}. M \<lbrakk>\<R>\<^sub>@(S)\<rbrakk>\<^sub>@ p \<longleftrightarrow> \<R>\<^sub>@(S) M p\<close>
    using saturated_MCS by fastforce
qed

lemma Truth_lemma:
  assumes \<open>MCS S\<close>
  shows \<open>\<M>\<^sub>@(S, i) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (i, p) \<in> S\<close>
proof -
  have \<open>\<M>\<^sub>@(S, i) \<Turnstile>\<^sub>@ p \<longleftrightarrow> ([i]\<^sub>S, p) \<in> S\<close>
    using assms truth_lemma by fastforce
  then show ?thesis
    using assms by (meson MCS_Nom_sym equiv_nom_Nom equiv_nom_assign equiv_nom_def)
qed

section \<open>Cardinalities\<close>

datatype marker = FlsM | ImpM | DiaM | SatM | AllM

type_synonym ('i, 'p) enc = \<open>('i + 'p) + marker \<times> nat\<close>

abbreviation \<open>NOM i \<equiv> Inl (Inl i)\<close>
abbreviation \<open>PRO x \<equiv> Inl (Inr x)\<close>
abbreviation \<open>FLS \<equiv> Inr (FlsM, 0)\<close>
abbreviation \<open>IMP n \<equiv> Inr (FlsM, n)\<close>
abbreviation \<open>DIA \<equiv> Inr (DiaM, 0)\<close>
abbreviation \<open>SAT \<equiv> Inr (SatM, 0)\<close>
abbreviation \<open>GLO \<equiv> Inr (AllM, 0)\<close>

primrec encode :: \<open>('i, 'p) fm \<Rightarrow> ('i, 'p) enc list\<close> where
  \<open>encode \<^bold>\<bottom> = [FLS]\<close>
| \<open>encode (\<^bold>\<cdot>P) = [PRO P]\<close>
| \<open>encode (\<^bold>\<bullet>i) = [NOM i]\<close>
| \<open>encode (p \<^bold>\<longrightarrow> q) = IMP (length (encode p)) # encode p @ encode q\<close>
| \<open>encode (\<^bold>\<diamond> p) = DIA # encode p\<close>
| \<open>encode (\<^bold>@ i p) = SAT # NOM i # encode p\<close>
| \<open>encode (\<^bold>A p) = GLO # encode p\<close>

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
  case (Sat i p)
  then show ?case
    by (cases q) auto
next
  case (All p)
  then show ?case
    by (cases q) auto
qed

primrec encode_lbd :: \<open>('i, 'p) lbd \<Rightarrow> ('i, 'p) enc list\<close> where
  \<open>encode_lbd (i, p) = NOM i # encode p\<close>

lemma inj_encode_lbd': \<open>encode_lbd (i, p) = encode_lbd (k, q) \<Longrightarrow> i = k \<and> p = q\<close>
  using inj_encode' by auto

lemma inj_encode_lbd: \<open>inj encode_lbd\<close>
  unfolding inj_def using inj_encode_lbd' by auto

lemma finite_marker: \<open>finite (UNIV :: marker set)\<close>
proof -
  have \<open>p \<in> {FlsM, ImpM, DiaM, SatM, AllM}\<close> for p
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
  assumes \<open>\<forall>M :: ('i, 'p) model. \<forall>g. \<forall>w \<in> W M. range g \<subseteq> W M \<longrightarrow>
      (\<forall>(k, q) \<in> X. (M, g, g k) \<Turnstile>\<^sub>@ q) \<longrightarrow> (M, g, w) \<Turnstile>\<^sub>@ p\<close>
    \<open>infinite (UNIV :: 'i set)\<close>
    \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals X|\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>@ (i, p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>@ (i, p)\<close>
  then have *: \<open>\<forall>A a. set A \<subseteq> {(i, \<^bold>\<not> p)} \<union> X \<longrightarrow> \<not> A \<turnstile>\<^sub>@ (a, \<^bold>\<bottom>)\<close>
    using Boole FlsE by (metis derive_split1 insert_is_Un subset_insert)

  let ?X = \<open>{(i, \<^bold>\<not> p)} \<union> X\<close>
  let ?S = \<open>Extend ?X\<close>

  have \<open>consistent ?X\<close>
    unfolding consistent_def using * by blast
  moreover have \<open>infinite (UNIV - nominals X)\<close>
    using assms(2-3)
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals X - nominals_lbd (i, \<^bold>\<not> p)|\<close>
    using assms(3) finite_nominals_lbd card_of_infinite_diff_finite
    by (metis ordIso_iff_ordLeq ordLeq_transitive)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - (nominals X \<union> nominals_lbd (i, \<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'i set| +c |UNIV :: 'p set| \<le>o |UNIV - nominals ?X|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |UNIV - nominals ?X|\<close>
    using assms card_of_lbd ordLeq_transitive by blast
  ultimately have \<open>MCS ?S\<close>
    using MCS_Extend by fast
  then have \<open>\<M>\<^sub>@(?S, i) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (i, p) \<in> ?S\<close> for i p
    using Truth_lemma by fast
  then have \<open>(i, p) \<in> ?X \<Longrightarrow> \<M>\<^sub>@(?S, i) \<Turnstile>\<^sub>@ p\<close> for i p
    using Extend_subset by blast
  then have \<open>\<M>\<^sub>@(?S, i) \<Turnstile>\<^sub>@ \<^bold>\<not> p\<close> \<open>\<forall>(k, q) \<in> X. \<M>\<^sub>@(?S, k) \<Turnstile>\<^sub>@ q\<close>
    by blast+
  moreover from this have \<open>\<M>\<^sub>@(?S, i) \<Turnstile>\<^sub>@ p\<close>
    using assms(1) by force
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>('i, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(M :: ('i, 'p) model) g. \<forall>w \<in> W M. range g \<subseteq> W M \<longrightarrow> (M, g, w) \<Turnstile>\<^sub>@ p\<close>

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
