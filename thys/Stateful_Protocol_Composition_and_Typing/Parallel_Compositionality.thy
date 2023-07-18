(*  Title:      Parallel_Compositionality.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, The University of Sheffield
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Parallel Compositionality of Security Protocols\<close>
theory Parallel_Compositionality
imports Typing_Result Labeled_Strands
begin

text\<open>\label{sec:Parallel-Compositionality}\<close>

subsection \<open>Definitions: Labeled Typed Model Locale\<close>
locale labeled_typed_model = typed_model arity public Ana \<Gamma>
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
    and \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
  +
  fixes label_witness1 and label_witness2::"'lbl"
  assumes at_least_2_labels: "label_witness1 \<noteq> label_witness2"
begin

text \<open>The Ground Sub-Message Patterns (GSMP)\<close>
definition GSMP::"('fun,'var) terms \<Rightarrow> ('fun,'var) terms" where
  "GSMP P \<equiv> {t \<in> SMP P. fv t = {}}"

definition typing_cond where
  "typing_cond \<A> \<equiv>
    wf\<^sub>s\<^sub>t {} \<A> \<and>
    fv\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>s\<^sub>t \<A> = {} \<and>
    tfr\<^sub>s\<^sub>t \<A> \<and>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t \<A>) \<and>
    Ana_invar_subst (ik\<^sub>s\<^sub>t \<A> \<union> assignment_rhs\<^sub>s\<^sub>t \<A>)"


subsection \<open>Definitions: GSMP Disjointness and Parallel Composability\<close>
definition GSMP_disjoint where
  "GSMP_disjoint P1 P2 Secrets \<equiv> GSMP P1 \<inter> GSMP P2 \<subseteq> Secrets \<union> {m. {} \<turnstile>\<^sub>c m}"

definition declassified\<^sub>l\<^sub>s\<^sub>t where
  "declassified\<^sub>l\<^sub>s\<^sub>t (\<A>::('fun,'var,'lbl) labeled_strand) \<I> \<equiv>
    {s. \<Union>{set ts | ts. (\<star>, Receive ts) \<in> set (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>t \<I>)} \<turnstile> s}"

definition par_comp where
  "par_comp (\<A>::('fun,'var,'lbl) labeled_strand) (Secrets::('fun,'var) terms) \<equiv> 
    (\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Secrets) \<and>
    (\<forall>s \<in> Secrets. \<not>{} \<turnstile>\<^sub>c s) \<and>
    ground Secrets"

definition strand_leaks\<^sub>l\<^sub>s\<^sub>t where
  "strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A> Sec \<I> \<equiv> (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I>. \<exists>l. (\<I> \<Turnstile> \<langle>proj_unl l \<A>@[Send1 t]\<rangle>))"


subsection \<open>Definitions: GSMP-Restricted Intruder Deduction Variant\<close>
definition intruder_deduct_hom::
  "('fun,'var) terms \<Rightarrow> ('fun,'var,'lbl) labeled_strand \<Rightarrow> ('fun,'var) term \<Rightarrow> bool"
  ("\<langle>_;_\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P _" 50)
where
  "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t \<equiv> \<langle>M; \<lambda>t. t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)\<rangle> \<turnstile>\<^sub>r t"

lemma intruder_deduct_hom_AxiomH[simp]:
  assumes "t \<in> M"
  shows "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
using intruder_deduct_restricted.AxiomR[of t M] assms
unfolding intruder_deduct_hom_def
by blast

lemma intruder_deduct_hom_ComposeH[simp]:
  assumes "length X = arity f" "public f" "\<And>x. x \<in> set X \<Longrightarrow> \<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P x"
  and "Fun f X \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  shows "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P Fun f X"
using intruder_deduct_restricted.ComposeR[of X f M "\<lambda>t. t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"] assms
unfolding intruder_deduct_hom_def
by blast

lemma intruder_deduct_hom_DecomposeH:
  assumes "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t" "Ana t = (K, T)" "\<And>k. k \<in> set K \<Longrightarrow> \<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P k" "t\<^sub>i \<in> set T"
  shows "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i"
using intruder_deduct_restricted.DecomposeR[of M "\<lambda>t. t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" t] assms
unfolding intruder_deduct_hom_def
by blast

lemma intruder_deduct_hom_induct[consumes 1, case_names AxiomH ComposeH DecomposeH]:
  assumes "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>X f. \<lbrakk>length X = arity f; public f;
                  \<And>x. x \<in> set X \<Longrightarrow> \<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P x;
                  \<And>x. x \<in> set X \<Longrightarrow> P M x;
                  Fun f X \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)
                  \<rbrakk> \<Longrightarrow> P M (Fun f X)"
          "\<And>t K T t\<^sub>i. \<lbrakk>\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t; P M t; Ana t = (K, T);
                       \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P k;
                       \<And>k. k \<in> set K \<Longrightarrow> P M k; t\<^sub>i \<in> set T\<rbrakk> \<Longrightarrow> P M t\<^sub>i"
  shows "P M t"
using intruder_deduct_restricted_induct[of M "\<lambda>t. t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" t "\<lambda>M Q t. P M t"] assms
unfolding intruder_deduct_hom_def
by blast

lemma ideduct_hom_mono:
  "\<lbrakk>\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t; M \<subseteq> M'\<rbrakk> \<Longrightarrow> \<langle>M'; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
using ideduct_restricted_mono[of M _ t M']
unfolding intruder_deduct_hom_def
by fast


subsection \<open>Lemmata: GSMP\<close>
lemma GSMP_disjoint_empty[simp]:
  "GSMP_disjoint {} A Sec" "GSMP_disjoint A {} Sec"
unfolding GSMP_disjoint_def GSMP_def by fastforce+

lemma GSMP_mono:
  assumes "N \<subseteq> M"
  shows "GSMP N \<subseteq> GSMP M"
using SMP_mono[OF assms] unfolding GSMP_def by fast

lemma GSMP_SMP_mono:
  assumes "SMP N \<subseteq> SMP M"
  shows "GSMP N \<subseteq> GSMP M"
using assms unfolding GSMP_def by fast

lemma GSMP_subterm:
  assumes "t \<in> GSMP M" "t' \<sqsubseteq> t"
  shows "t' \<in> GSMP M"
using SMP.Subterm[of t M t'] ground_subterm[of t t'] assms unfolding GSMP_def by auto

lemma GSMP_subterms: "subterms\<^sub>s\<^sub>e\<^sub>t (GSMP M) = GSMP M"
using GSMP_subterm[of _ M] by blast

lemma GSMP_Ana_key:
  assumes "t \<in> GSMP M" "Ana t = (K,T)" "k \<in> set K"
  shows "k \<in> GSMP M"
using SMP.Ana[of t M K T k] Ana_keys_fv[of t K T] assms unfolding GSMP_def by auto

lemma GSMP_union: "GSMP (A \<union> B) = GSMP A \<union> GSMP B"
using SMP_union[of A B] unfolding GSMP_def by auto

lemma GSMP_Union: "GSMP (trms\<^sub>l\<^sub>s\<^sub>t A) = (\<Union>l. GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A))"
proof -
  define P where "P \<equiv> (\<lambda>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A)"
  define Q where "Q \<equiv> trms\<^sub>l\<^sub>s\<^sub>t A"
  have "SMP (\<Union>l. P l) = (\<Union>l. SMP (P l))" "Q = (\<Union>l. P l)"
    unfolding P_def Q_def by (metis SMP_Union, metis trms\<^sub>l\<^sub>s\<^sub>t_union)
  hence "GSMP Q = (\<Union>l. GSMP (P l))" unfolding GSMP_def by auto
  thus ?thesis unfolding P_def Q_def by metis
qed

lemma in_GSMP_in_proj: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A) \<Longrightarrow> \<exists>n. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
using GSMP_Union[of A] by blast

lemma in_proj_in_GSMP: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) \<Longrightarrow> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
using GSMP_Union[of A] by blast

lemma GSMP_disjointE:
  assumes A: "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) Sec"
  shows "GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
using assms unfolding GSMP_disjoint_def by auto

lemma GSMP_disjoint_term:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  shows "t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<or> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) \<or> t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
using assms unfolding GSMP_disjoint_def by blast

lemma GSMP_wt_subst_subset:
  assumes "t \<in> GSMP (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
  shows "t \<in> GSMP M"
using SMP_wt_subst_subset[OF _ assms(2,3), of t M] assms(1) unfolding GSMP_def by simp

lemma GSMP_wt_substI:
  assumes "t \<in> M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "t \<cdot> I \<in> GSMP M"
proof -
  have "t \<in> SMP M" using assms(1) by auto
  hence *: "t \<cdot> I \<in> SMP M" using SMP.Substitution assms(2,3) wf_trm_subst_range_iff[of I] by simp
  moreover have "fv (t \<cdot> I) = {}"
    using assms(1) interpretation_grounds_all'[OF assms(4)]
    by auto
  ultimately show ?thesis unfolding GSMP_def by simp
qed

lemma GSMP_disjoint_subset:
  assumes "GSMP_disjoint L R S" "L' \<subseteq> L" "R' \<subseteq> R"
  shows "GSMP_disjoint L' R' S"
using assms(1) SMP_mono[OF assms(2)] SMP_mono[OF assms(3)]
by (auto simp add: GSMP_def GSMP_disjoint_def)


subsection \<open>Lemmata: Intruder Knowledge and Declassification\<close>
lemma declassified\<^sub>l\<^sub>s\<^sub>t_alt_def:
  "declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I> = {s. (\<Union>{set ts | ts. (\<star>, Receive ts) \<in> set \<A>}) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s}"
proof -
  have 0:
    "(l, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>t \<I>) = (\<exists>ts'. (l, receive\<langle>ts'\<rangle>\<^sub>s\<^sub>t) \<in> set \<A> \<and> ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)"
    (is "?A \<A> = ?B \<A>")
    for ts l
  proof
    show "?A \<A> \<Longrightarrow> ?B \<A>"
    proof (induction \<A>)
      case (Cons a \<A>)
      obtain k b where a: "a = (k,b)" by (metis surj_pair)
      show ?case
      proof (cases "?A \<A>")
        case False
        hence "(l,receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) = a \<cdot>\<^sub>l\<^sub>s\<^sub>t\<^sub>p \<I>" using Cons.prems by auto
        thus ?thesis unfolding a by (cases b) auto
      qed (use Cons.IH in auto)
    qed simp

    show "?B \<A> \<Longrightarrow> ?A \<A>" 
    proof (induction \<A>)
      case (Cons a \<A>)
      obtain k b where a: "a = (k,b)" by (metis surj_pair)
      show ?case
      proof (cases "?B \<A>")
        case False
        hence "\<exists>ts'. a = (l, receive\<langle>ts'\<rangle>\<^sub>s\<^sub>t) \<and> ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>" using Cons.prems by auto
        thus ?thesis unfolding a by (cases b) auto
      qed (use Cons.IH in auto)
    qed simp
  qed


  let ?M = "\<lambda>A. \<Union>{set ts |ts. (\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set A}"

  have 1: "?M (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>t \<I>) = ?M \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix t assume t: "t \<in> ?A"
      then obtain ts where ts: "t \<in> set ts" "(\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>t \<I>)" by blast
      thus "t \<in> ?B" using 0[of \<star> ts] by fastforce
    qed
    show "?B \<subseteq> ?A"
    proof
      fix t assume t: "t \<in> ?B"
      then obtain ts where ts: "t \<in> set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "(\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set \<A>" by blast
      hence "(\<star>, receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>\<rangle>\<^sub>s\<^sub>t) \<in> set (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>t \<I>)" using 0[of \<star> "ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>"] by blast
      thus "t \<in> ?A" using ts(1) by force
    qed
  qed

  show ?thesis using 1 unfolding declassified\<^sub>l\<^sub>s\<^sub>t_def by argo
qed

lemma declassified\<^sub>l\<^sub>s\<^sub>t_star_receive_supset:
  "{t | t ts. (\<star>, Receive ts) \<in> set \<A> \<and> t \<in> set ts} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I>"
unfolding declassified\<^sub>l\<^sub>s\<^sub>t_alt_def by (fastforce intro: intruder_deduct.Axiom)

lemma ik_proj_subst_GSMP_subset:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
proof
  fix t assume "t \<in> ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
  hence *: "t \<in> trms_proj\<^sub>l\<^sub>s\<^sub>t n A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" by auto
  then obtain s where "s \<in> trms_proj\<^sub>l\<^sub>s\<^sub>t n A" "t = s \<cdot> I" by auto
  hence "t \<in> SMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" using SMP_I I(1,2) wf_trm_subst_range_iff[of I] by simp
  moreover have "fv t = {}"
    using * interpretation_grounds_all'[OF I(3)]
    by auto
  ultimately show "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" unfolding GSMP_def by simp
qed

lemma ik_proj_subst_subterms_GSMP_subset:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" (is "?A \<subseteq> ?B")
proof
  fix t assume "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
  then obtain s where "s \<in> ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I" "t \<sqsubseteq> s" by fast
  thus "t \<in> ?B"
    using ik_proj_subst_GSMP_subset[OF I, of n A] ground_subterm[of s t]
          SMP.Subterm[of s "trms\<^sub>l\<^sub>s\<^sub>t (proj n A)" t]
    unfolding GSMP_def 
    by blast
qed

lemma declassified_proj_eq: "declassified\<^sub>l\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>t (proj n A) I"
unfolding declassified\<^sub>l\<^sub>s\<^sub>t_alt_def proj_def by auto

lemma declassified_prefix_subset:
  assumes AB: "prefix A B"
  shows "declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> declassified\<^sub>l\<^sub>s\<^sub>t B I"
proof
  fix t assume t: "t \<in> declassified\<^sub>l\<^sub>s\<^sub>t A I"
  obtain C where C: "B = A@C" using prefixE[OF AB] by metis
  show "t \<in> declassified\<^sub>l\<^sub>s\<^sub>t B I"
    using t ideduct_mono[of
              "\<Union>{set ts |ts. (\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set A} \<cdot>\<^sub>s\<^sub>e\<^sub>t I" t 
              "\<Union>{set ts |ts. (\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set B} \<cdot>\<^sub>s\<^sub>e\<^sub>t I"]
    unfolding C declassified\<^sub>l\<^sub>s\<^sub>t_alt_def by auto
qed

lemma declassified_proj_ik_subset:
  "declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> {s. ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s}"
    (is "?A A \<subseteq> ?P A A")
proof -
  have *: "\<Union>{set ts |ts. (\<star>, receive\<langle>ts\<rangle>\<^sub>s\<^sub>t) \<in> set A} \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<subseteq> ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
    using proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set by fastforce
  show ?thesis
    using ideduct_mono[OF _ *] unfolding declassified\<^sub>l\<^sub>s\<^sub>t_alt_def by blast
qed

lemma deduct_proj_priv_term_prefix_ex:
  assumes A: "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> t"
    and t: "\<not>{} \<turnstile>\<^sub>c t"
  shows "\<exists>B k s. (k = \<star> \<or> k = ln l) \<and> prefix (B@[(k,receive\<langle>s\<rangle>\<^sub>s\<^sub>t)]) A \<and>
                 declassified\<^sub>l\<^sub>s\<^sub>t ((B@[(k,receive\<langle>s\<rangle>\<^sub>s\<^sub>t)])) I = declassified\<^sub>l\<^sub>s\<^sub>t A I \<and>
                 ik\<^sub>s\<^sub>t (proj_unl l (B@[(k,receive\<langle>s\<rangle>\<^sub>s\<^sub>t)])) = ik\<^sub>s\<^sub>t (proj_unl l A)"
using A
proof (induction A rule: List.rev_induct)
  case Nil
  have "ik\<^sub>s\<^sub>t (proj_unl l []) \<cdot>\<^sub>s\<^sub>e\<^sub>t I = {}" by auto
  thus ?case using Nil t deducts_eq_if_empty_ik[of t] by argo
next
  case (snoc a A)
  obtain k b where a: "a = (k,b)" by (metis surj_pair)
  let ?P = "k = \<star> \<or> k = (ln l)"
  let ?Q = "\<exists>ts. b = receive\<langle>ts\<rangle>\<^sub>s\<^sub>t"

  have 0: "ik\<^sub>s\<^sub>t (proj_unl l (A@[a])) = ik\<^sub>s\<^sub>t (proj_unl l A)" when "?P \<Longrightarrow> \<not>?Q"
    using that ik\<^sub>s\<^sub>t_snoc_no_receive_eq[OF that, of I "proj_unl l A"]
    unfolding ik\<^sub>s\<^sub>t_is_rcv_set a by (cases "k = \<star> \<or> k = (ln l)") auto

  have 1: "declassified\<^sub>l\<^sub>s\<^sub>t (A@[a]) I = declassified\<^sub>l\<^sub>s\<^sub>t A I" when "?P \<Longrightarrow> \<not>?Q"
    using that snoc.prems unfolding declassified\<^sub>l\<^sub>s\<^sub>t_alt_def a
    by (metis (no_types, lifting) UnCI UnE empty_iff insert_iff list.set prod.inject set_append)

  note 2 = snoc.prems snoc.IH 0 1

  show ?case
  proof (cases ?P)
    case True
    note T = this
    thus ?thesis
    proof (cases ?Q)
      case True thus ?thesis using T unfolding a by blast
    qed (use 2 in auto)
  qed (use 2 in auto)
qed


subsection \<open>Lemmata: Homogeneous and Heterogeneous Terms (Deprecated Theory)\<close>
text \<open>The following theory is no longer needed for the compositionality result\<close>
context
begin
private definition proj_specific where
  "proj_specific n t \<A> Secrets \<equiv> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>) - (Secrets \<union> {m. {} \<turnstile>\<^sub>c m})"

private definition heterogeneous\<^sub>l\<^sub>s\<^sub>t where
  "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets \<equiv> (
    (\<exists>l1 l2. \<exists>s1 \<in> subterms t. \<exists>s2 \<in> subterms t.
      l1 \<noteq> l2 \<and> proj_specific l1 s1 \<A> Secrets \<and> proj_specific l2 s2 \<A> Secrets))"

private abbreviation homogeneous\<^sub>l\<^sub>s\<^sub>t where
  "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets \<equiv> \<not>heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets"

private definition intruder_deduct_hom'::
  "('fun,'var) terms \<Rightarrow> ('fun,'var,'lbl) labeled_strand \<Rightarrow> ('fun,'var) terms \<Rightarrow> ('fun,'var) term
  \<Rightarrow> bool" ("\<langle>_;_;_\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m _" 50)
where
  "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t \<equiv> \<langle>M; \<lambda>t. homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec \<and> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)\<rangle> \<turnstile>\<^sub>r t"

private lemma GSMP_disjoint_fst_specific_not_snd_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec" "l \<noteq> l'"
  and "proj_specific l m \<A> Sec"
  shows "\<not>proj_specific l' m \<A> Sec"
using assms by (fastforce simp add: GSMP_disjoint_def proj_specific_def)

private lemma GSMP_disjoint_snd_specific_not_fst_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and "proj_specific l' m \<A> Sec"
  shows "\<not>proj_specific l m \<A> Sec"
using assms by (auto simp add: GSMP_disjoint_def proj_specific_def)

private lemma GSMP_disjoint_intersection_not_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and "t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
  shows "\<not>proj_specific l t \<A> Sec" "\<not>proj_specific l t \<A> Sec"
using assms by (auto simp add: GSMP_disjoint_def proj_specific_def)

private lemma proj_specific_secrets_anti_mono:
  assumes "proj_specific l t \<A> Sec" "Sec' \<subseteq> Sec"
  shows "proj_specific l t \<A> Sec'"
using assms unfolding proj_specific_def by fast

private lemma heterogeneous_secrets_anti_mono:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "Sec' \<subseteq> Sec"
  shows "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec'"
using assms proj_specific_secrets_anti_mono unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by metis

private lemma homogeneous_secrets_mono:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec'" "Sec' \<subseteq> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
using assms heterogeneous_secrets_anti_mono by blast

private lemma heterogeneous_supterm:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t \<sqsubseteq> t'"
  shows "heterogeneous\<^sub>l\<^sub>s\<^sub>t t' \<A> Sec"
proof -
  obtain l1 l2 s1 s2 where *:
      "l1 \<noteq> l2"
      "s1 \<sqsubseteq> t" "proj_specific l1 s1 \<A> Sec"
      "s2 \<sqsubseteq> t" "proj_specific l2 s2 \<A> Sec"
    using assms(1) unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  thus ?thesis
    using term.order_trans[OF *(2) assms(2)] term.order_trans[OF *(4) assms(2)]
    by (auto simp add: heterogeneous\<^sub>l\<^sub>s\<^sub>t_def)
qed

private lemma homogeneous_subterm:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t' \<sqsubseteq> t"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t' \<A> Sec"
by (metis assms heterogeneous_supterm)

private lemma proj_specific_subterm:
  assumes "t \<sqsubseteq> t'" "proj_specific l t' \<A> Sec"
  shows "proj_specific l t \<A> Sec \<or> t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
using GSMP_subterm[OF _ assms(1)] assms(2) by (auto simp add: proj_specific_def)

private lemma heterogeneous_term_is_Fun:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t A S" shows "\<exists>f T. t = Fun f T"
using assms by (cases t) (auto simp add: GSMP_def heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def)

private lemma proj_specific_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "proj_specific l m \<A> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
proof
  assume "heterogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
  then obtain s l' where s: "s \<in> subterms m" "proj_specific l' s \<A> Sec" "l \<noteq> l'"
    unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  hence "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)"
    using t by (auto simp add: GSMP_def proj_specific_def)
  hence "s \<in> Sec \<or> {} \<turnstile>\<^sub>c s"
    using \<A> s(3) by (auto simp add: GSMP_disjoint_def)
  thus False using s(2) by (auto simp add: proj_specific_def)
qed

private lemma deduct_synth_homogeneous:
  assumes "{} \<turnstile>\<^sub>c t"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  have "\<forall>s \<in> subterms t. {} \<turnstile>\<^sub>c s" using deduct_synth_subterm[OF assms] by auto
  thus ?thesis unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def by auto
qed

private lemma GSMP_proj_is_homogeneous:
  assumes "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l A) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' A) Sec"
  and "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A)" "t \<notin> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t A Sec"
proof
  assume "heterogeneous\<^sub>l\<^sub>s\<^sub>t t A Sec"
  then obtain s l' where s: "s \<in> subterms t" "proj_specific l' s A Sec" "l \<noteq> l'"
    unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  hence "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A)" "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' A)"
    using assms by (auto simp add: GSMP_def proj_specific_def)
  hence "s \<in> Sec \<or> {} \<turnstile>\<^sub>c s" using assms(1) s(3) by (auto simp add: GSMP_disjoint_def)
  thus False using s(2) by (auto simp add: proj_specific_def)
qed

private lemma homogeneous_is_not_proj_specific:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
  shows "\<exists>l::'lbl. \<not>proj_specific l m \<A> Sec"
proof -
  let ?P = "\<lambda>l s. proj_specific l s \<A> Sec"
  have "\<forall>l1 l2. \<forall>s1\<in>subterms m. \<forall>s2\<in>subterms m. (l1 \<noteq> l2 \<longrightarrow> (\<not>?P l1 s1 \<or> \<not>?P l2 s2))"
    using assms heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by metis
  then obtain l1 l2 where "l1 \<noteq> l2" "\<not>?P l1 m \<or> \<not>?P l2 m"
    by (metis term.order_refl at_least_2_labels)
  thus ?thesis by metis
qed

private lemma secrets_are_homogeneous:
  assumes "\<forall>s \<in> Sec. P s \<longrightarrow> (\<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec)" "s \<in> Sec" "P s"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t s \<A> Sec"
using assms by (auto simp add: heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def)

private lemma GSMP_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" "t \<notin> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  obtain n where n: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)" using in_GSMP_in_proj[OF t(1)] by moura
  show ?thesis using GSMP_proj_is_homogeneous[OF \<A> n t(2)] by metis
qed

private lemma GSMP_intersection_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
    and t: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)" "l \<noteq> l'"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  define M where "M \<equiv> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
  define M' where "M' \<equiv> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)"

  have t_in: "t \<in> M \<inter> M'" "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    using t(1) in_proj_in_GSMP[of t _ \<A>]
    unfolding M_def M'_def by blast+

  have "M \<inter> M' \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
    using \<A> GSMP_disjointE[of l \<A> l' Sec] t(2)
    unfolding M_def M'_def by presburger
  moreover have "subterms\<^sub>s\<^sub>e\<^sub>t (M \<inter> M') = M \<inter> M'"
    using GSMP_subterms unfolding M_def M'_def by blast
  ultimately have *: "subterms\<^sub>s\<^sub>e\<^sub>t (M \<inter> M') \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
    by blast

  show ?thesis
  proof (cases "t \<in> Sec")
    case True thus ?thesis
      using * secrets_are_homogeneous[of Sec "\<lambda>t. t \<in> M \<inter> M'", OF _ _ t_in(1)]
      by fast
  qed (metis GSMP_is_homogeneous[OF \<A> t_in(2)])
qed

private lemma GSMP_is_homogeneous':
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
         "t \<notin> Sec - \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
using GSMP_is_homogeneous[OF \<A> t(1)] GSMP_intersection_is_homogeneous[OF \<A>] t(2)
by blast

private lemma Ana_keys_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  and k: "Ana t = (K,T)" "k \<in> set K"
         "k \<notin> Sec - \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t k \<A> Sec"
proof (cases "k \<in> \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}")
  case False
  hence "k \<notin> Sec" using k(3) by fast
  moreover have "k \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    using t SMP.Ana[OF _ k(1,2)] Ana_keys_fv[OF k(1)] k(2)
    unfolding GSMP_def by auto
  ultimately show ?thesis using GSMP_is_homogeneous[OF \<A>, of k] by metis
qed (use GSMP_intersection_is_homogeneous[OF \<A>] in blast)

end


subsection \<open>Lemmata: Intruder Deduction Equivalences\<close>
lemma deduct_if_hom_deduct: "\<langle>M;A\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P m \<Longrightarrow> M \<turnstile> m"
using deduct_if_restricted_deduct unfolding intruder_deduct_hom_def by blast

lemma hom_deduct_if_hom_ik:
  assumes "\<langle>M;A\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P m" "\<forall>m \<in> M. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
  shows "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
proof -
  let ?Q = "\<lambda>m. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
  have "?Q t'" when "?Q t" "t' \<sqsubseteq> t" for t t'
    using GSMP_subterm[OF _ that(2)] that(1)
    by blast
  thus ?thesis
    using assms(1) restricted_deduct_if_restricted_ik[OF _ assms(2)]
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma deduct_hom_if_synth:
  assumes hom: "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  and m: "M \<turnstile>\<^sub>c m"
  shows "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P m"
proof -
  let ?Q = "\<lambda>m. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  have "?Q t'" when "?Q t" "t' \<sqsubseteq> t" for t t'
    using GSMP_subterm[OF _ that(2)] that(1)
    by blast
  thus ?thesis
    using assms deduct_restricted_if_synth[of ?Q]
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma hom_deduct_if_deduct:
  assumes M: "\<forall>m \<in> M. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    and m: "M \<turnstile> m" "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  shows "\<langle>M; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P m"
proof -
  let ?P = "\<lambda>x. x \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"

(*   have GSMP_hom: "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" when "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" for t
    using \<A> GSMP_is_homogeneous[of \<A> Sec t]
          secrets_are_homogeneous[of Sec "\<lambda>x. True" t \<A>] that
    unfolding par_comp_def by blast *)

  have P_Ana: "?P k" when "?P t" "Ana t = (K, T)" "k \<in> set K" for t K T k
    using GSMP_Ana_key[OF _ that(2,3), of "trms\<^sub>l\<^sub>s\<^sub>t \<A>"] that (* GSMP_hom *)
    by presburger

  have P_subterm: "?P t'" when "?P t" "t' \<sqsubseteq> t" for t t'
    using GSMP_subterm[of _ "trms\<^sub>l\<^sub>s\<^sub>t \<A>"] (* homogeneous_subterm[of _ \<A> Sec] *) that
    by blast

  have P_m: "?P m"
    using (* GSMP_hom[OF m(2)] *) m(2)
    by metis

  show ?thesis
    using restricted_deduct_if_deduct'[OF M _ _ m(1) P_m] P_Ana P_subterm
    unfolding intruder_deduct_hom_def
    by fast
qed


subsection \<open>Lemmata: Deduction Reduction of Parallel Composable Constraints\<close>
lemma par_comp_hom_deduct:
  assumes \<A>: "par_comp \<A> Sec"
  and M: "\<forall>l. M l \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
         "\<forall>l. Discl \<subseteq> {s. M l \<turnstile> s}"
  and Sec: "\<forall>l. \<forall>s \<in> Sec - Discl. \<not>(\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P s)"
  and t: "\<langle>\<Union>l. M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
  shows "t \<notin> Sec - Discl" (is ?A)
        "\<forall>l. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t" (is ?B)
proof -
  have M': "\<forall>l. \<forall>m \<in> M l. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  proof (intro allI ballI)
    fix l m show "m \<in> M l \<Longrightarrow> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using M(1) in_proj_in_GSMP[of m l \<A>] by blast
  qed

  have Discl_hom_deduct: "\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P u" when u: "u \<in> Discl" "u \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" for l u
  proof-
    have "M l \<turnstile> u" using M(2) u by auto
    thus ?thesis using hom_deduct_if_deduct[of "M l" \<A> u] M(1) M' u by auto
  qed

  show ?A ?B using t
  proof (induction t rule: intruder_deduct_hom_induct)
    case (AxiomH t)
    then obtain lt where t_in_proj_ik: "t \<in> M lt" by moura
    show t_not_Sec: "t \<notin> Sec - Discl"
    proof
      assume "t \<in> Sec - Discl"
      hence "\<forall>l. \<not>(\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t)" using Sec by auto
      thus False using intruder_deduct_hom_AxiomH[OF t_in_proj_ik] by metis
    qed
    
    have 1: "\<forall>l. t \<in> M l \<longrightarrow> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      using M(1,2) AxiomH by auto
  
    have 3: "{} \<turnstile>\<^sub>c t \<or> t \<in> Discl"
      when "l1 \<noteq> l2" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>)" for l1 l2
      using \<A> t_not_Sec that by (auto simp add: par_comp_def GSMP_disjoint_def)
  
    have 4: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using M(1) M' t_in_proj_ik by auto
    
    show "\<forall>l. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
      by (metis (lifting) Int_iff empty_subsetI
            1 3 4 Discl_hom_deduct t_in_proj_ik
            intruder_deduct_hom_AxiomH[of t _ \<A>]
            deduct_hom_if_synth[of t \<A> "{}"]
            ideduct_hom_mono[of "{}" \<A> t])
  next
    case (ComposeH T f)
    show "\<forall>l. Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P Fun f T"
    proof (intro allI impI)
      fix l
      assume "Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      hence "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" when "t \<in> set T" for t
        using that GSMP_subterm[OF _ subtermeqI''] by auto
      thus "\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P Fun f T"
        using ComposeH.IH(2) intruder_deduct_hom_ComposeH[OF ComposeH.hyps(1,2) _ ComposeH.hyps(4)]
        by simp
    qed
    thus "Fun f T \<notin> Sec - Discl"
      using Sec ComposeH.hyps(4) trms\<^sub>l\<^sub>s\<^sub>t_union[of \<A>] GSMP_Union[of \<A>] by blast
  next
    case (DecomposeH t K T t\<^sub>i)
    have ti_subt: "t\<^sub>i \<sqsubseteq> t" using Ana_subterm[OF DecomposeH.hyps(2)] \<open>t\<^sub>i \<in> set T\<close> by auto
    have t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using DecomposeH.hyps(1) hom_deduct_if_hom_ik M(1) M' by auto
    have ti: "t\<^sub>i \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
      using intruder_deduct_hom_DecomposeH[OF DecomposeH.hyps] hom_deduct_if_hom_ik M(1) M' by auto

    obtain l where l: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      using in_GSMP_in_proj[of _ \<A>] ti t by presburger

    have K_IH: "\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P k" when "k \<in> set K" for k
      using that GSMP_Ana_key[OF _ DecomposeH.hyps(2)] DecomposeH.IH(4) l by auto

    have ti_IH: "\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i"
      using K_IH DecomposeH.IH(2) l
            intruder_deduct_hom_DecomposeH[OF _ DecomposeH.hyps(2) _ \<open>t\<^sub>i \<in> set T\<close>]
      by blast
    thus ti_not_Sec: "t\<^sub>i \<notin> Sec - Discl" using Sec by blast
    
    have "{} \<turnstile>\<^sub>c t\<^sub>i \<or> t\<^sub>i \<in> Discl" when "t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)" "l' \<noteq> l" for l'
    proof - 
      have "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) Sec"
        using that(2) \<A> by (simp add: par_comp_def)
      thus ?thesis
        using ti_not_Sec GSMP_subterm[OF l ti_subt] that(1) by (auto simp add: GSMP_disjoint_def)
    qed
    hence "\<langle>M l'; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i" when "t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)" "l' \<noteq> l" for l'
      using that Discl_hom_deduct[OF _ ti]
            deduct_hom_if_synth[OF ti, THEN ideduct_hom_mono[OF _ empty_subsetI]]
      by (cases "t\<^sub>i \<in> Discl") simp_all
    thus "\<forall>l. t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i"
      using ti_IH by blast
  qed
qed

lemma par_comp_deduct_proj:
  assumes \<A>: "par_comp \<A> Sec"
  and M: "\<forall>l. M l \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
         "\<forall>l. Discl \<subseteq> {s. M l \<turnstile> s}"
  and t: "(\<Union>l. M l) \<turnstile> t" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
  shows "M l \<turnstile> t \<or> (\<exists>s \<in> Sec - Discl. \<exists>l. M l \<turnstile> s)"
using t
proof (induction t rule: intruder_deduct_induct)
  case (Axiom t)
  then obtain l' where t_in_ik_proj: "t \<in> M l'" by moura
  show ?case
  proof (cases "t \<in> Sec - Discl \<or> {} \<turnstile>\<^sub>c t")
    case True thus ?thesis
      by (cases "t \<in> Sec - Discl")
         (metis intruder_deduct.Axiom[OF t_in_ik_proj],
          use ideduct_mono[of "{}" t "M l"] in blast)
  next
    case False
    hence "t \<notin> Sec - Discl" "\<not>{} \<turnstile>\<^sub>c t" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" using Axiom by auto
    hence "(\<forall>l'. l \<noteq> l' \<longrightarrow> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)) \<or> t \<in> Discl"
      using \<A> unfolding GSMP_disjoint_def par_comp_def by auto
    hence "(\<forall>l'. l \<noteq> l' \<longrightarrow> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)) \<or> M l \<turnstile> t \<or> {} \<turnstile>\<^sub>c t"
      using M by blast
    thus ?thesis
      by (cases "\<exists>s \<in> M l. t \<sqsubseteq> s \<and> {s} \<turnstile> t")
         (blast intro: ideduct_mono[of _ t "M l"],
          metis (no_types, lifting) False M(1) intruder_deduct.Axiom subsetCE t_in_ik_proj)
  qed
next
  case (Compose T f)
  hence "Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" using Compose.prems by auto
  hence "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" when "t \<in> set T" for t using that unfolding GSMP_def by auto
  hence IH: "M l \<turnstile> t \<or> (\<exists>s \<in> Sec - Discl. \<exists>l. M l \<turnstile> s)" when "t \<in> set T" for t
    using that Compose.IH by auto
  show ?case
    by (cases "\<forall>t \<in> set T. M l \<turnstile> t")
       (metis intruder_deduct.Compose[OF Compose.hyps(1,2)], metis IH)
next
  case (Decompose t K T t\<^sub>i)
  have hom_ik: "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" when m: "m \<in> M l" for m l
    using in_proj_in_GSMP[of m l \<A>] M(1) m by blast

  have "\<langle>\<Union>l. M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i"
    using intruder_deduct.Decompose[OF Decompose.hyps]
          hom_deduct_if_deduct[of "\<Union>l. M l"] hom_ik in_proj_in_GSMP[OF Decompose.prems(1)]
    by blast
  hence "(\<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t\<^sub>i) \<or> (\<exists>s \<in> Sec-Discl. \<exists>l. \<langle>M l; \<A>\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P s)"
    using par_comp_hom_deduct(2)[OF \<A> M] Decompose.prems(1)
    by blast
  thus ?case using deduct_if_hom_deduct[of _ \<A>] by auto
qed


subsection \<open>Theorem: Parallel Compositionality for Labeled Constraints\<close>
lemma par_comp_prefix: assumes "par_comp (A@B) M" shows "par_comp A M"
proof -
  let ?L = "\<lambda>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A \<union> trms_proj\<^sub>l\<^sub>s\<^sub>t l B"
  have "GSMP_disjoint (?L l1) (?L l2) M" when "l1 \<noteq> l2" for l1 l2
    using that assms unfolding par_comp_def
    by (metis trms\<^sub>s\<^sub>t_append proj_append(2) unlabel_append)
  hence "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 A) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 A) M" when "l1 \<noteq> l2" for l1 l2
    using that SMP_union by (auto simp add: GSMP_def GSMP_disjoint_def)
  thus ?thesis using assms unfolding par_comp_def by blast
qed

theorem par_comp_constr_typed:
  assumes \<A>: "par_comp \<A> Sec"
    and \<I>: "\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
  shows "(\<forall>l. (\<I> \<Turnstile> \<langle>proj_unl l \<A>\<rangle>)) \<or>
         (\<exists>\<A>' l' t. prefix \<A>' \<A> \<and> suffix [(l', receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] \<A>' \<and> (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>' Sec \<I>))"
proof -
  let ?sem = "\<lambda>\<A>. \<lbrakk>{}; \<A>\<rbrakk>\<^sub>d \<I>"
  let ?Q = "\<lambda>\<A>. \<forall>l. ?sem (proj_unl l \<A>)"
  let ?L = "\<lambda>\<A>'. \<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>. \<exists>l. ?sem (proj_unl l \<A>'@[send\<langle>[t]\<rangle>\<^sub>s\<^sub>t])"
  let ?P = "\<lambda>\<A> \<A>' l' ts. prefix (\<A>'@[(l',receive\<langle>ts\<rangle>\<^sub>s\<^sub>t)]) \<A> \<and> ?L (\<A>'@[(l',receive\<langle>ts\<rangle>\<^sub>s\<^sub>t)])"

  have "\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>" using \<I> by (simp add: constr_sem_d_def)
  with \<A> have aux: "?Q \<A> \<or> (\<exists>\<A>'. prefix \<A>' \<A> \<and> ?L \<A>')"
  proof (induction "unlabel \<A>" arbitrary: \<A> rule: List.rev_induct)
    case Nil
    hence "\<A> = []" using unlabel_nil_only_if_nil by simp
    thus ?case by auto
  next
    case (snoc b B \<A>)
    hence disj: "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
      when "l1 \<noteq> l2" for l1 l2
      using that by (auto simp add: par_comp_def)

    obtain a A n where a: "\<A> = A@[a]" "a = (ln n, b) \<or> a = (\<star>, b)"
      using unlabel_snoc_inv[OF snoc.hyps(2)[symmetric]] by moura
    hence A: "\<A> = A@[(ln n, b)] \<or> \<A> = A@[(\<star>, b)]" by metis

    have 1: "B = unlabel A" using a snoc.hyps(2) unlabel_append[of A "[a]"] by auto
    have 2: "par_comp A Sec" using par_comp_prefix snoc.prems(1) a by metis
    have 3: "\<lbrakk>{}; unlabel A\<rbrakk>\<^sub>d \<I>" by (metis 1 snoc.prems(2) snoc.hyps(2) strand_sem_split(3))
    have IH: "(\<forall>l. \<lbrakk>{}; proj_unl l A\<rbrakk>\<^sub>d \<I>) \<or> (\<exists>\<A>'. prefix \<A>' A \<and> ?L \<A>')"
      by (rule snoc.hyps(1)[OF 1 2 3])

    show ?case
    proof (cases "\<forall>l. \<lbrakk>{}; proj_unl l A\<rbrakk>\<^sub>d \<I>")
      case False
      then obtain \<A>' where \<A>': "prefix \<A>' A" "?L \<A>'" by (metis IH)
      hence "prefix \<A>' (A@[a])" using a prefix_prefix[of _ A "[a]"] by simp
      thus ?thesis using \<A>'(2) a by auto
    next
      case True
      note IH' = True
      show ?thesis
      proof (cases b)
        case (Send ts)
        hence "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>t (unlabel A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> strand_sem_split(2)[of "{}" "unlabel A" "unlabel [a]" \<I>]
                unlabel_append[of A "[a]"]
          by auto
        hence *: "\<forall>t \<in> set ts. (\<Union>l. (ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)) \<turnstile> t \<cdot> \<I>"
          using proj_ik_union_is_unlabel_ik image_UN by metis

        have "ik\<^sub>s\<^sub>t (proj_unl l \<A>) = ik\<^sub>s\<^sub>t (proj_unl l A)" for l
          using Send A 
          by (metis append_Nil2 ik\<^sub>s\<^sub>t.simps(3) proj_unl_cons(3) proj_nil(2)
                    singleton_lst_proj(1,2) proj_ik_append)
        hence **: "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" for l
          using ik_proj_subst_GSMP_subset[OF \<I>(3,4,2), of _ \<A>]
          by auto

        note Discl =
          declassified_proj_ik_subset(1)[of A \<I>]

        have Sec: "ground Sec"
          using \<A> by (auto simp add: par_comp_def)

(*         have Sec_hom: "homogeneous\<^sub>l\<^sub>s\<^sub>t s \<A> Sec" when "s \<in> Sec" for s
          using that secrets_are_homogeneous[of Sec "\<lambda>_. True" s \<A>] snoc.prems(1)
          unfolding par_comp_def by auto *)

        have "\<forall>m\<in>ik\<^sub>s\<^sub>t (proj_unl l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
             "ik\<^sub>s\<^sub>t (proj_unl l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
          for l
          using ik_proj_subst_GSMP_subset[OF \<I>(3,4,2), of _ \<A>] GSMP_Union[of \<A>] by auto
        moreover have "ik\<^sub>s\<^sub>t (proj_unl l [a]) = {}" for l
          using Send proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set[of _ "[a]"] a(2) by auto
        ultimately have M: "\<forall>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
          using a(1) proj_ik_append[of _ A "[a]"] by auto

        have prefix_A: "prefix A \<A>" using A by auto

        have "s \<cdot> \<I> = s"
          when "s \<in> Sec" for s
          using that Sec by auto
        hence leakage_case: "\<lbrakk>{}; proj_unl l A@[Send1 s]\<rbrakk>\<^sub>d \<I>"
          when "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s" for l s
          using that strand_sem_append(2) IH' by auto

        have proj_deduct_case_n:
            "\<forall>m. m \<noteq> n \<longrightarrow> \<lbrakk>{}; proj_unl m (A@[a])\<rbrakk>\<^sub>d \<I>"
            "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> \<lbrakk>{}; proj_unl n (A@[a])\<rbrakk>\<^sub>d \<I>"
          when "a = (ln n, Send ts)"
          using that IH' proj_append(2)[of _ A] by auto

        have proj_deduct_case_star:
            "\<lbrakk>{}; proj_unl l (A@[a])\<rbrakk>\<^sub>d \<I>"
          when "a = (\<star>, Send ts)" "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" for l
          using that IH' proj_append(2)[of _ A] by auto

        show ?thesis
        proof (cases "\<exists>l. \<exists>m \<in> ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. m \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>")
          case True
          then obtain l s where ls: "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s"
            using intruder_deduct.Axiom by metis
          thus ?thesis using leakage_case prefix_A by blast
        next
          case False
          have A_decl_subset:
              "\<forall>l. declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<subseteq> {s. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s}"
            using Discl unfolding a(1) by auto

          note deduct_proj_lemma = par_comp_deduct_proj[OF snoc.prems(1) M A_decl_subset]

          from a(2) show ?thesis
          proof
            assume "a = (ln n, b)"
            hence "a = (ln n, Send ts)" "\<forall>t \<in> set ts. t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)"
              using Send a(1) trms_proj\<^sub>l\<^sub>s\<^sub>t_append[of n A "[a]"]
                    GSMP_wt_substI[OF _ \<I>(3,4,2)]
              by (metis, force)
            hence
                "a = (ln n, Send ts)"
                "\<forall>m. m \<noteq> n \<longrightarrow> \<lbrakk>{}; proj_unl m (A@[a])\<rbrakk>\<^sub>d \<I>"
                "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> \<lbrakk>{}; proj_unl n (A@[a])\<rbrakk>\<^sub>d \<I>"
                "\<forall>t \<in> set ts. t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)"
              using proj_deduct_case_n
              by auto
            hence "(\<forall>l. \<lbrakk>{}; proj_unl l \<A>\<rbrakk>\<^sub>d \<I>) \<or>
                   (\<exists>s \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>t A \<I>. \<exists>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s)"
              using deduct_proj_lemma * unfolding a(1) list_all_iff by metis
            thus ?thesis using leakage_case prefix_A by metis
          next
            assume "a = (\<star>, b)"
            hence ***: "a = (\<star>, Send ts)" "list_all (\<lambda>t. t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)) ts" for l
              using Send a(1) GSMP_wt_substI[OF _ \<I>(3,4,2)] unfolding list_all_iff by (metis, force)
            hence "t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or>
                   t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or>
                   t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m}"
              when "t \<in> set ts" for t
              using that snoc.prems(1) a(1) at_least_2_labels
              unfolding par_comp_def GSMP_disjoint_def list_all_iff
              by blast
            hence "(\<exists>t \<in> set ts. t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>) \<or>
                   (\<forall>t \<in> set ts. t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or> t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m})"
              by blast
            thus ?thesis
            proof
              assume "\<exists>t \<in> set ts. t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
              then obtain t where t:
                  "t \<in> set ts" "t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
                  "(\<Union>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile> t \<cdot> \<I>"
                using * unfolding list_all_iff by blast
              have "\<exists>s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>. \<exists>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s"
                using t(1,2) deduct_proj_lemma[OF t(3)] ***(2) A a Discl
                unfolding list_all_iff by blast
              thus ?thesis using prefix_A leakage_case by blast
            next
              assume t: "\<forall>t \<in> set ts. t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or> t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m}"
              moreover {
                fix t l assume "t \<in> set ts" "t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
                hence "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
                  using intruder_deduct.Axiom Discl(1)[of l] 
                        ideduct_mono[of _ "t \<cdot> \<I>" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"]
                  by blast
              } moreover {
                fix t l assume "t \<in> set ts" "t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m}"
                hence "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
                  using ideduct_mono[OF deduct_if_synth] by blast
              } ultimately have "\<forall>t \<in> set ts. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" for l
                  by blast
              thus ?thesis using proj_deduct_case_star[OF ***(1)] a(1) by fast
            qed
          qed
        qed
      next
        case (Receive t)
        hence "\<lbrakk>{}; proj_unl l \<A>\<rbrakk>\<^sub>d \<I>" for l
          using IH' a proj_append(2)[of l A "[a]"]
          unfolding unlabel_def proj_def by auto
        thus ?thesis by metis
      next
        case (Equality ac t t')
        hence *: "\<lbrakk>M; [Equality ac t t']\<rbrakk>\<^sub>d \<I>" for M
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> unlabel_append[of A "[a]"]
          by auto
        show ?thesis
          using a proj_append(2)[of _ A "[a]"] Equality
                strand_sem_append(2)[OF _ *] IH'
          unfolding unlabel_def proj_def by auto
      next
        case (Inequality X F)
        hence *: "\<lbrakk>M; [Inequality X F]\<rbrakk>\<^sub>d \<I>" for M
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> unlabel_append[of A "[a]"]
          by auto
        show ?thesis
          using a proj_append(2)[of _ A "[a]"] Inequality
                strand_sem_append(2)[OF _ *] IH'
          unfolding unlabel_def proj_def by auto
      qed
    qed
  qed
  
  from aux have "?Q \<A> \<or> (\<exists>\<A>' l' t. ?P \<A> \<A>' l' t)"
  proof
    assume "\<exists>\<A>'. prefix \<A>' \<A> \<and> ?L \<A>'"
    then obtain \<A>' t l where \<A>':
        "prefix \<A>' \<A>" "t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>" "?sem (proj_unl l \<A>'@[send\<langle>[t]\<rangle>\<^sub>s\<^sub>t])"
      by blast

    have *: "ik\<^sub>s\<^sub>t (proj_unl l \<A>') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" "\<not>{} \<turnstile>\<^sub>c t \<cdot> \<I>"
      using \<A>'(2) \<A> subst_ground_ident[of t \<I>] strand_sem_split(4)[OF \<A>'(3)]
      unfolding par_comp_def by (simp, fastforce)

    obtain B k s where B:
        "k = \<star> \<or> k = ln l" "prefix (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)]) \<A>'"
        "declassified\<^sub>l\<^sub>s\<^sub>t (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)]) \<I> = declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>"
        "ik\<^sub>s\<^sub>t (proj_unl l (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)])) = ik\<^sub>s\<^sub>t (proj_unl l \<A>')"
      using deduct_proj_priv_term_prefix_ex[OF *] by force
    
    have "prefix (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)]) \<A>" using B(2) \<A>'(1) unfolding prefix_def by force
    moreover have "t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)]) \<I>" using B(3) \<A>'(2) by blast
    moreover have "?sem (proj_unl l (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)])@[send\<langle>[t]\<rangle>\<^sub>s\<^sub>t])"
      using *(1)[unfolded B(4)[symmetric]]
            prefix_proj(2)[OF B(2), of l, unfolded prefix_def]
            strand_sem_split(3)[OF \<A>'(3)]
            strand_sem_append(2)[
              of _ _ \<I>  "[send\<langle>[t]\<rangle>\<^sub>s\<^sub>t]",
              OF strand_sem_split(3)[of "{}" "proj_unl l (B@[(k, receive\<langle>s\<rangle>\<^sub>s\<^sub>t)])"]]
      by force
    ultimately show ?thesis by blast
  qed simp
  thus ?thesis
    using \<I>(1) unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>t_def suffix_def constr_sem_d_def by blast
qed

end

locale labeled_typing =
  labeled_typed_model arity public Ana \<Gamma> label_witness1 label_witness2
+ typing_result arity public Ana \<Gamma>
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
    and \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
begin

theorem par_comp_constr:
  assumes \<A>: "par_comp \<A> Sec" "typing_cond (unlabel \<A>)"
  and \<I>: "\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel \<A>\<rangle>) \<and>
              ((\<forall>l. (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl l \<A>\<rangle>)) \<or>
               (\<exists>\<A>' l' t. prefix \<A>' \<A> \<and> suffix [(l', receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] \<A>' \<and>
                          (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>)))"
proof -
  from \<A>(2) have *:
      "wf\<^sub>s\<^sub>t {} (unlabel \<A>)"
      "fv\<^sub>s\<^sub>t (unlabel \<A>) \<inter> bvars\<^sub>s\<^sub>t (unlabel \<A>) = {}"
      "tfr\<^sub>s\<^sub>t (unlabel \<A>)"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t (unlabel \<A>))"
      "Ana_invar_subst (ik\<^sub>s\<^sub>t (unlabel \<A>) \<union> assignment_rhs\<^sub>s\<^sub>t (unlabel \<A>))"
    unfolding typing_cond_def tfr\<^sub>s\<^sub>t_def by metis+

  obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>: "\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
    using wt_attack_if_tfr_attack_d[OF * \<I>(2,1)] by metis

  show ?thesis using par_comp_constr_typed[OF \<A>(1) \<I>\<^sub>\<tau>] \<I>\<^sub>\<tau> by auto
qed

end


subsection \<open>Automated GSMP Disjointness\<close>
locale labeled_typed_model' = typed_model' arity public Ana \<Gamma> +
  labeled_typed_model arity public Ana \<Gamma> label_witness1 label_witness2
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,(('fun,'atom::finite) term_type \<times> nat)) term
              \<Rightarrow> (('fun,(('fun,'atom) term_type \<times> nat)) term list
                 \<times> ('fun,(('fun,'atom) term_type \<times> nat)) term list)"
    and \<Gamma>::"('fun,(('fun,'atom) term_type \<times> nat)) term \<Rightarrow> ('fun,'atom) term_type"
    and label_witness1 label_witness2::'lbl
begin

lemma GSMP_disjointI:
  fixes A' A B B'::"('fun, ('fun, 'atom) term \<times> nat) terms"
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "\<delta> \<equiv> var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t A))"
  assumes A'_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity A'"
    and B'_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity B'"
    and A_inst: "has_all_wt_instances_of \<Gamma> A' A"
    and B_inst: "has_all_wt_instances_of \<Gamma> B' (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    and A_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> A"
    and B_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    and AB_trms_disj:
      "\<forall>t \<in> A. \<forall>s \<in> B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>. \<Gamma> t = \<Gamma> s \<and> mgu t s \<noteq> None \<longrightarrow>
        (intruder_synth' public arity {} t) \<or> ((\<exists>u \<in> Sec. is_wt_instance_of_cond \<Gamma> t u))"
    and Sec_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s Sec"
  shows "GSMP_disjoint A' B' ((f Sec) - {m. {} \<turnstile>\<^sub>c m})"
proof -
  have A_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s A" and B_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    and A'_wf': "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s A'" and B'_wf': "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s B'"
    and A_finite: "finite A" and B_finite: "finite (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    using finite_SMP_representationD[OF A_SMP_repr]
          finite_SMP_representationD[OF B_SMP_repr]
          A'_wf B'_wf
    unfolding wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] list_all_iff by blast+

  have AB_fv_disj: "fv\<^sub>s\<^sub>e\<^sub>t A \<inter> fv\<^sub>s\<^sub>e\<^sub>t (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) = {}"
    using var_rename_fv_set_disjoint'[of A B, unfolded \<delta>_def[symmetric]] A_finite by simp

  have "GSMP_disjoint A (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) ((f Sec) - {m. {} \<turnstile>\<^sub>c m})"
    using ground_SMP_disjointI[OF AB_fv_disj A_SMP_repr B_SMP_repr Sec_wf AB_trms_disj]
    unfolding GSMP_def GSMP_disjoint_def f_def by blast
  moreover have "SMP A' \<subseteq> SMP A" "SMP B' \<subseteq> SMP (B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    using SMP_I'[OF A'_wf' A_wf A_inst] SMP_SMP_subset[of A' A]
          SMP_I'[OF B'_wf' B_wf B_inst] SMP_SMP_subset[of B' "B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"]
    by (blast, blast)
  ultimately show ?thesis unfolding GSMP_def GSMP_disjoint_def by auto
qed

end

end
