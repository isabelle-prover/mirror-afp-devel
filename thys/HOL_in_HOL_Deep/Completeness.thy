theory Completeness
  imports Soundness "HOL-Library.Countable_Set"
begin

section \<open>Completeness\<close>

text \<open>Henkin completeness via the model-existence / abstract-consistency method
  of BKK Section 6 (Corollary 7.7), with the term model realised as a
  term evaluation (BKK Definition 3.35) --- then strengthened to arbitrary infinite value
  carriers, signatures with infinitely many parameters, and open formulas.\<close>

subsection \<open>Model existence and completeness (BKK Section 6, Corollary 7.7)\<close>

text \<open>We build a Henkin term model from a maximal consistent, saturated set of sentences, following
  BKK's model-existence route (BKK Section 6).  This file develops \<open>NK\<close>-consistency and its
  closure properties (BKK Lemma 7.5), the maximal saturated extension (BKK Lemma 6.32), the term
  model with its truth lemma (BKK Theorem 6.33), and the completeness theorem itself
  (BKK Corollary 7.7).\<close>

subsubsection \<open>Consistency (BKK Definition 7.4)\<close>

text \<open>A set of sentences is @{emph \<open>NK-consistent\<close>} (BKK Definition 7.4) if falsity is not derivable
  from it.\<close>

definition con :: "'p tm set \<Rightarrow> bool" where "con \<Phi> \<longleftrightarrow> \<not> (\<Phi> \<turnstile> \<^bold>\<bottom>)"
lemma con_I: "(\<Phi> \<turnstile> \<^bold>\<bottom> \<Longrightarrow> False) \<Longrightarrow> con \<Phi>" by (auto simp: con_def)

text \<open>Subsets of a consistent set are consistent (using weakening).\<close>

lemma con_mono: "con \<Psi> \<Longrightarrow> \<Phi> \<subseteq> \<Psi> \<Longrightarrow> freep \<Psi> \<Longrightarrow> con \<Phi>" unfolding con_def
    using bprov_weaken by blast

text \<open>Consistency is of finite character (compactness, BKK Definition 6.1): a set is consistent
  as soon as all its finite subsets are.\<close>

lemma con_compact:
  "(\<And>\<Phi>0::'p::infinite tm set. finite \<Phi>0 \<Longrightarrow> \<Phi>0 \<subseteq> \<Phi> \<Longrightarrow> con \<Phi>0) \<Longrightarrow> con \<Phi>"
  using bprov_finite unfolding con_def by blast

text \<open>The central step of a maximal-consistent extension (the \<open>\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close> case of BKK Lemma 7.5;
  property \<open>\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close> is BKK Definition 6.5): from a consistent set, adding a proposition or its
  negation keeps it consistent.\<close>

lemma con_split: assumes "con \<Phi>" and "wff\<^bsub>\<o>\<^esub>(A)"
  shows "con (insert A \<Phi>) \<or> con (insert (\<^bold>\<not> A) \<Phi>)"
proof (rule ccontr)
  assume "\<not>?thesis"
  hence "\<Phi> \<union> {A} \<turnstile> \<^bold>\<bottom>" and "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<bottom>" by (auto simp: con_def)
  from \<open>\<Phi> \<union> {A} \<turnstile> \<^bold>\<bottom>\<close> have "\<Phi> \<turnstile> \<^bold>\<not> A" using assms(2)
      by (rule bprov.NegI)
  moreover from \<open>\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<bottom>\<close> have "\<Phi> \<turnstile> A" using assms(2)
      by (rule bprov.Contr)
  ultimately have "\<Phi> \<turnstile> \<^bold>\<bottom>" using wff_FalseB by (rule bprov.NegE)
  thus False using assms(1) by (simp add: con_def)
qed

text \<open>A consistent set does not contain both a proposition and its negation.\<close>

lemma con_not_both: "con \<Phi> \<Longrightarrow> A \<in> \<Phi> \<Longrightarrow> \<^bold>\<not> A \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> False"
  by (metis con_def wff_FalseB NegE Hyp)

subsubsection \<open>Some admissible rules\<close>

lemma freep_un: "freep \<Phi> \<Longrightarrow> freep (\<Phi> \<union> {A})"
  by (metis freep_add Un_insert_right sup_bot.right_neutral)

text \<open>Double-negation elimination (derivable from the classical rule \<open>NK(Contr)\<close>).\<close>

lemma dneg: "\<Phi> \<turnstile> \<^bold>\<not> (Neg \<^bold>\<cdot> X) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(X) \<Longrightarrow> freep \<Phi> \<Longrightarrow> \<Phi> \<turnstile> X"
  by (metis (no_types, lifting) Contr Hyp NegE Un_insert_right bprov_weaken
            freep_add insertI1 subset_insertI sup_bot.right_neutral wff_FalseB)

text \<open>Excluded middle and implication introduction (derivable in the classical calculus).\<close>

lemma bprov_em: assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" shows "\<Phi> \<turnstile> (\<^bold>\<not> A) \<^bold>\<or> A"
proof -
  let ?D = "(\<^bold>\<not> A) \<^bold>\<or> A"
  have wnA: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> A)" using wA by (rule wff_Not)
  have wD: "wff\<^bsub>\<o>\<^esub>(?D)" using wnA wA by (rule wff_Or)
  have "\<Phi> \<union> {\<^bold>\<not> ?D} \<turnstile> \<^bold>\<not> A"
  proof (rule bprov.NegI[OF _ wA])
    have "(\<Phi> \<union> {\<^bold>\<not> ?D}) \<union> {A} \<turnstile> A" by (auto intro: bprov.Hyp)
    hence "(\<Phi> \<union> {\<^bold>\<not> ?D}) \<union> {A} \<turnstile> ?D" using wnA by (rule bprov.DisIR)
    moreover have "(\<Phi> \<union> {\<^bold>\<not> ?D}) \<union> {A} \<turnstile> \<^bold>\<not> ?D"
        by (auto intro: bprov.Hyp)
    ultimately show "(\<Phi> \<union> {\<^bold>\<not> ?D}) \<union> {A} \<turnstile> \<^bold>\<bottom>" using wff_FalseB
        by (metis bprov.NegE)
  qed
  hence "\<Phi> \<union> {\<^bold>\<not> ?D} \<turnstile> ?D" using wA by (rule bprov.DisIL)
  moreover have "\<Phi> \<union> {\<^bold>\<not> ?D} \<turnstile> \<^bold>\<not> ?D" by (auto intro: bprov.Hyp)
  ultimately have "\<Phi> \<union> {\<^bold>\<not> ?D} \<turnstile> \<^bold>\<bottom>" using wff_FalseB by (metis bprov.NegE)
  thus ?thesis using wD by (rule bprov.Contr)
qed
lemma bprov_ImpE: assumes AB: "\<Phi> \<turnstile> A \<^bold>\<supset> B" and A: "\<Phi> \<turnstile> A"
    and fp: "freep \<Phi>"
    and wA: "wff\<^bsub>\<o>\<^esub>(A)" and wB: "wff\<^bsub>\<o>\<^esub>(B)" shows "\<Phi> \<turnstile> B"
proof -
  have wnA: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> A)" using wA by (rule wff_Not)
  have disj: "\<Phi> \<turnstile> (\<^bold>\<not> A) \<^bold>\<or> B" using AB by (simp add: ImpB_def)
  have b1: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> B"
    by (meson A Hyp NegE bprov_weaken fp freep_un inf_sup_ord(4) insertCI sup_ge1 wB)
  have b2: "\<Phi> \<union> {B} \<turnstile> B" by (auto intro: bprov.Hyp)
  show ?thesis by (rule bprov.DisE[OF disj b1 b2 wnA wB])
qed
lemma bprov_TrueB: "\<Phi> \<turnstile> \<^bold>\<top>" by (simp add: Hyp TrueB_def bprov.intros(3))

subsubsection \<open>Witnessing a false universal
  (BKK property \<open>\<nabla>\<^sub>\<exists>\<close>, Definition 6.5; the \<open>\<nabla>\<^sub>\<exists>\<close> case of Lemma 7.5)\<close>

text \<open>If \<open>\<not>\<Pi>\<^bsub>\<alpha>\<^esub> G\<close> is consistent with \<open>\<Phi>\<close>, then it stays consistent when we add a witness
  \<open>\<not> (G c)\<close> for a fresh parameter \<open>c\<close>.  This is the key step for making the extension saturated.\<close>

lemma con_witness:
  assumes con: "con (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>)"
      and wG: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" and fp: "freep \<Phi>"
      and c: "c \<notin> usedp \<Phi>" "c \<notin> pars G"
    shows "con (insert (\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>))"
proof (rule con_I)
  define \<Gamma> where "\<Gamma> = \<Phi> \<union> {\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)}"
  have fpG: "freep \<Gamma>" unfolding \<Gamma>_def by (rule freep_un[OF fp])
  assume "insert (\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>) \<turnstile> \<^bold>\<bottom>"
  hence "\<Gamma> \<union> {\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))} \<turnstile> \<^bold>\<bottom>" by (simp add: \<Gamma>_def insert_commute)
  hence "\<Gamma> \<turnstile> \<^bold>\<not> (Neg \<^bold>\<cdot> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)))"
    using wff_Not[OF wff_App[OF wG wff_Par]] by (rule bprov.NegI)
  hence "\<Gamma> \<turnstile> G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)"
    using wff_App[OF wG wff_Par] fpG by (rule dneg)
  moreover have "c \<notin> pars G" and "\<forall>D \<in> \<Gamma>. c \<notin> pars D" using c
    by (auto simp: \<Gamma>_def usedp_def)
  ultimately have piG: "\<Gamma> \<turnstile> (Pi \<alpha>) \<^bold>\<cdot> G" using wG
    by (blast intro: bprov.PiI)
  have "\<Gamma> \<turnstile> \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)" by (auto simp: \<Gamma>_def intro: bprov.Hyp)
  from this piG have "\<Gamma> \<turnstile> \<^bold>\<bottom>" using wff_FalseB by (rule bprov.NegE)
  thus False using con by (simp add: con_def \<Gamma>_def)
qed

subsubsection \<open>Maximal consistent, saturated extension (BKK's abstract extension lemma 6.32)\<close>

text \<open>We enumerate the (countably many) sentences and, step by step, decide each one or its
  negation (\<open>con_split\<close>), immediately adding a Henkin witness for a decided negated universal
  (\<open>con_witness\<close>).  The union of the chain is a maximal consistent, saturated set.\<close>

definition freshc :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p" where
 "freshc S G \<equiv> SOME c. c \<notin> usedp S \<and> c \<notin> pars G"

lemma freshc_fresh: "freep S \<Longrightarrow> freshc S G \<notin> usedp S \<and> freshc S G \<notin> pars G"
  by (metis (lifting) finite_pars freep_fresh freshc_def someI_ex)

fun wit :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" where
  \<open>wit S (\<^bold>\<not>App (Pi \<alpha>) G) = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}\<close>
| \<open>wit _ _ = {}\<close>

lemma wit_cases: "wit S A = {} \<or> (\<exists>\<alpha> G. A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<and>
   wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))})"
  by (induct S A rule: wit.induct) auto
lemma finite_wit: "finite (wit S A)"
  by (induct S A rule: wit.induct) auto
definition step :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" where
  "step S A \<equiv> if cwff \<o> A
   then (if con (insert A S) then insert A S \<union> wit S A else insert (\<^bold>\<not> A) S)
   else S"

primrec ext :: "'p::{countable,infinite} tm set \<Rightarrow> nat \<Rightarrow> 'p tm set" where
  "ext \<Phi> 0 = \<Phi>"
| "ext \<Phi> (Suc n) = step (ext \<Phi> n) (from_nat n)"

definition Hset :: "'p::{countable,infinite} tm set \<Rightarrow> 'p tm set" where
  "Hset \<Phi> = (\<Union>n. ext \<Phi> n)"

text \<open>The chain is increasing and each stage stays finite-in-parameters and consistent.\<close>

lemma ext_mono: "ext \<Phi> n \<subseteq> ext \<Phi> (Suc n)"
  by (induct n) (auto simp: step_def)
lemma ext_mono': "m \<le> n \<Longrightarrow> ext \<Phi> m \<subseteq> ext \<Phi> n"
    using ext_mono lift_Suc_mono_le by blast
lemma freep_un_finite: "freep S \<Longrightarrow> finite T \<Longrightarrow> freep (S \<union> T)"
proof -
  assume "freep S" "finite T"
  hence "finite (usedp T)" by (auto simp: usedp_def)
  moreover have "- usedp (S \<union> T) = - usedp S - usedp T"
    by (auto simp: usedp_def)
  ultimately show ?thesis using \<open>freep S\<close>
    by (metis freep_def Diff_infinite_finite)
qed
lemma freep_step: "freep S \<Longrightarrow> freep (step S A)"
  by (simp add: finite_wit freep_add freep_un_finite step_def)
lemma freep_ext: "freep \<Phi> \<Longrightarrow> freep (ext \<Phi> n)"
  by (induction n) (auto simp: freep_step)
lemma con_step: assumes "con S" and "freep S" shows "con (step S A)"
proof (cases "cwff \<o> A")
  case False
  with assms(1) show ?thesis by (auto simp: step_def)
next case True
  show ?thesis 
  proof (cases "con (insert A S)")
    case False
    hence "con (insert (\<^bold>\<not> A) S)"
      using con_split[OF assms(1)] cwff_wff[OF True] by blast
    thus ?thesis using False True by (simp add: step_def)
  next
    case True
    have "con (insert A S \<union> wit S A)" using wit_cases[of S A]  
    proof
      assume "wit S A = {}" thus ?thesis using True by simp
    next
      assume "\<exists>\<alpha> G. A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<and> wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}"
      then obtain \<alpha> G where AG: "A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)"
        and w: "wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}" by blast
      have wG: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" using cwff_wff[OF \<open>cwff \<o> A\<close>] AG
        by (auto dest: wff_unique)
      have fr: "freshc S G \<notin> usedp S" "freshc S G \<notin> pars G"
        using freshc_fresh[OF assms(2)] by auto
      have "con (insert (\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert A S))"
        by (metis AG True assms(2) con_witness fr(1,2) wG)
      thus ?thesis using w by simp
    qed
    thus ?thesis using True \<open>cwff \<o> A\<close> by (simp add: step_def)
  qed
qed
lemma con_ext: "con \<Phi> \<Longrightarrow> freep \<Phi> \<Longrightarrow> con (ext \<Phi> n)"
  by (induction n) (auto simp: con_step freep_ext)

text \<open>\<open>Hset \<Phi>\<close> extends \<open>\<Phi>\<close> and, by compactness, is consistent.\<close>

lemma Phi_sub_Hset: "\<Phi> \<subseteq> Hset \<Phi>" unfolding Hset_def using ext.simps(1)
  by blast
lemma finite_sub_ext: "finite F \<Longrightarrow> F \<subseteq> Hset \<Phi> \<Longrightarrow> \<exists>N. F \<subseteq> ext \<Phi> N"
proof (induction F rule: finite_induct)
  case empty thus ?case by blast
next
  case (insert x F)
  then obtain N where N: "F \<subseteq> ext \<Phi> N" by auto
  from insert.prems obtain M where M: "x \<in> ext \<Phi> M"
    by (auto simp: Hset_def)
  have "insert x F \<subseteq> ext \<Phi> (max N M)"
    using N M ext_mono'[of N "max N M" \<Phi>] ext_mono'[of M "max N M" \<Phi>] by auto
  thus ?case by blast
qed
lemma con_Hset: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes "con \<Phi>" and "freep \<Phi>"
  shows "con (Hset \<Phi>)"
  by (metis assms(1,2) con_compact con_ext con_mono finite_sub_ext freep_ext)

text \<open>Crucially, \<open>freep (Hset \<Phi>)\<close> fails (a maximal set uses every parameter), so we never weaken
  @{emph \<open>to\<close>} \<open>Hset\<close>.  Instead we use that every @{emph \<open>finite\<close>} subset of \<open>Hset\<close> is consistent
      ---
  finite contexts are always \<open>freep\<close>, which is all the proof rules need.\<close>

lemma Hset_finite_con: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes "con \<Phi>" and "freep \<Phi>" and "finite F" and "F \<subseteq> Hset \<Phi>"
  shows "con F" 
  by (meson assms(1,2,3,4) con_ext con_mono finite_sub_ext freep_ext)

text \<open>\<open>Hset\<close> decides every sentence --- BKK call this @{emph \<open>saturated\<close>}, property \<open>\<^sub>~\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close>
  (BKK Definition 6.24) --- and has the Henkin witness property \<open>\<^sub>~\<nabla>\<^sub>\<exists>\<close> (BKK Definition 6.19).
  We call the former @{emph \<open>maximality\<close>} and reserve @{emph \<open>saturation\<close>} for the witness
  property; the lemma names below follow this convention.\<close>

lemma Hset_maximal: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes c: "cwff \<o> A" shows "A \<in> Hset \<Phi> \<or> \<^bold>\<not> A \<in> Hset \<Phi>"
proof -
  have "A \<in> ext \<Phi> (Suc (to_nat A)) \<or> \<^bold>\<not> A \<in> ext \<Phi> (Suc (to_nat A))"
    using c by (auto simp: step_def)
  thus ?thesis unfolding Hset_def by blast
qed
lemma Hset_saturated: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp: "freep \<Phi>"
  and cA: "cwff \<o> (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G))" and inH: "\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<in> Hset \<Phi>"
shows "\<exists>c. \<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)) \<in> Hset \<Phi>"
proof -
  note wA = cwff_wff[OF cA] and fvsA = cwff_closed[OF cA]
  let ?A = "\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)"
  let ?S = "ext \<Phi> (to_nat ?A)"
  have step: "ext \<Phi> (Suc (to_nat ?A)) = step ?S ?A"
    by simp
  have "con (insert ?A ?S)"
  proof (rule ccontr)
    assume "\<not> con (insert ?A ?S)"
    hence "\<^bold>\<not> ?A \<in> ext \<Phi> (Suc (to_nat ?A))" using cA step
        by (auto simp: step_def)
    hence "\<^bold>\<not> ?A \<in> Hset \<Phi>" unfolding Hset_def by blast
    thus False using con_not_both[OF con_Hset[OF con\<Phi> fp] inH _ wA]
        by blast
  qed
  hence "wit ?S ?A \<subseteq> ext \<Phi> (Suc (to_nat ?A))" using cA step
    by (auto simp: step_def)
  moreover have "wit ?S ?A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc ?S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}"
    by simp
  ultimately have "\<^bold>\<not> (G \<^bold>\<cdot> ((freshc ?S G)\<^sup>p\<^bsub>\<alpha>\<^esub>)) \<in> Hset \<Phi>"
    unfolding Hset_def by blast
  thus ?thesis by blast
qed

subsubsection \<open>Leibniz equality is reflexive (BKK property \<open>\<nabla>\<^sub>r\<close>, Lemma 6.25)\<close>

lemma leib_refl: assumes fp: "freep \<Phi>" and wa: "wff\<^bsub>\<alpha>\<^esub>(A)"
  shows "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A" by (simp add: EqL EqR wa)

text \<open>Leibniz substitution (the substitutivity built into BKK's Leibniz equality, Section 2.2;
cf.\ the \<open>\<nabla>\<close>-properties of BKK Lemma 6.12): equals may replace equals
in any predicate.  Instantiating \<open>P\<close> with suitable predicates yields symmetry, transitivity
and congruence.\<close>

lemma leib_subst:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B" and fp: "freep \<Phi>" and wa: "wff\<^bsub>\<alpha>\<^esub>(A)" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)"
      and wP: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(P)" and PA: "\<Phi> \<turnstile> P \<^bold>\<cdot> A"
    shows "\<Phi> \<turnstile> P \<^bold>\<cdot> B"
proof -
  let ?body = "(Bnd 0) \<^bold>\<cdot> A \<^bold>\<supset> (Bnd 0) \<^bold>\<cdot> B"
  have "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ?body"
    using Leib_beq[OF wa wb] AB by (rule bprov.Beta)
  hence "\<Phi> \<turnstile> (Pi (\<alpha> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> ?body)" by (simp add: Forall_def)
  hence P: "\<Phi> \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> ?body) \<^bold>\<cdot> P" using wP by (rule bprov.PiE)
  have wAbs: "wff\<^bsub>(\<alpha>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> ?body)"
    by (auto simp: opn_lc[OF wff_lc[OF wa]] opn_lc[OF wff_lc[OF wb]]
             intro!: wff_App wff_Fre wa wb wff_AbsI)
  have "(\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> ?body) \<^bold>\<cdot> P \<approx>\<^bsub>\<o>\<^esub> P \<^bold>\<cdot> A \<^bold>\<supset> P \<^bold>\<cdot> B"
  proof -
    have "(\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> ?body) \<^bold>\<cdot> P \<approx>\<^bsub>\<o>\<^esub> ?body\<^bold>\<langle>P\<^bold>\<rangle>"
      by (rule beq.beta[OF wAbs wP])
    thus ?thesis
      by (simp add: opn_lc[OF wff_lc[OF wa]] opn_lc[OF wff_lc[OF wb]])
  qed
  from bprov.Beta[OF this P] have "\<Phi> \<turnstile> P \<^bold>\<cdot> A \<^bold>\<supset> P \<^bold>\<cdot> B".
  moreover have "wff\<^bsub>\<o>\<^esub>(P \<^bold>\<cdot> A)" by (rule wff_App[OF wP wa])
  moreover have "wff\<^bsub>\<o>\<^esub>(P \<^bold>\<cdot> B)" by (rule wff_App[OF wP wb])
  ultimately show ?thesis using PA fp by (metis bprov_ImpE)
qed
lemma leib_sym:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B" and fp: "freep \<Phi>" and wa: "wff\<^bsub>\<alpha>\<^esub>(A)" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)"
  shows "\<Phi> \<turnstile> B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A"
proof -
  have lcA: "lc A" using wa by (rule wff_lc)
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (((Leib \<alpha>) \<^bold>\<cdot> (Bnd 0)) \<^bold>\<cdot> A)" \<comment> \<open>the predicate \<open>\<lambda>x. x \<^bold>\<doteq> A\<close>\<close>
  have wP: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)" by (auto simp: opn_lc[OF lcA] intro!: wff_Fre wa wff_AbsI)
  have PbA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)"
    using beq.beta[OF wP wa] by (simp add: opn_lc[OF lcA])
  have PbB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> (B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)"
    using beq.beta[OF wP wb] by (simp add: opn_lc[OF lcA])
  have "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A" using fp wa by (rule leib_refl)
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> A"
    using beq.sym[OF PbA] by (rule bprov.Beta[rotated])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> B" using leib_subst[OF AB fp wa wb wP] by auto
  thus ?thesis by (rule bprov.Beta[OF PbB])
qed
lemma leib_trans:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B" and BC: "\<Phi> \<turnstile> B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C" and fp: "freep \<Phi>"
      and wa: "wff\<^bsub>\<alpha>\<^esub>(A)" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)" and wc: "wff\<^bsub>\<alpha>\<^esub>(C)"
    shows "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C"
proof -
  have lcA: "lc A" using wa by (rule wff_lc)
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (((Leib \<alpha>) \<^bold>\<cdot> A) \<^bold>\<cdot> (Bnd 0))" \<comment> \<open>the predicate \<open>\<lambda>x. A \<^bold>\<doteq> x\<close>\<close>
  have wP: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)"
    by (auto simp: opn_lc[OF lcA] intro!: wff_Fre wa wff_AbsI)
  have PbB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)"
    using beq.beta[OF wP wb] by (simp add: opn_lc[OF lcA])
  have PbC: "?P \<^bold>\<cdot> C \<approx>\<^bsub>\<o>\<^esub> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C)"
    using beq.beta[OF wP wc] by (simp add: opn_lc[OF lcA])
  from AB have "\<Phi> \<turnstile> ?P \<^bold>\<cdot> B" by (rule bprov.Beta[OF beq.sym[OF PbB]])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> C" using leib_subst[OF BC fp wb wc wP] by auto
  thus ?thesis by (rule bprov.Beta[OF PbC])
qed
lemma leib_cong2:
  assumes AA: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A'" and fp: "freep \<Phi>"
  and wa: "wff\<^bsub>\<alpha>\<^esub>(A)" and wa': "wff\<^bsub>\<alpha>\<^esub>(A')" and wC: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>(C)"
  shows "\<Phi> \<turnstile> (C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C \<^bold>\<cdot> A')"
proof -
  have lcC: "lc C" using wC by (rule wff_lc)
  have lcA: "lc A" using wa by (rule wff_lc)
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> (Bnd 0))"   \<comment> \<open>\<open>\<lambda>x. (C A) \<^bold>\<doteq> (C x)\<close>\<close>
  have wP: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)"
    by (auto simp: opn_lc[OF lcC] opn_lc[OF lcA]
             intro!: wff_AbsI wff_App wff_Fre wC wa wff_App[OF wC wa])
  have PbA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> A)"
    using beq.beta[OF wP wa] by (simp add: opn_lc[OF lcC] opn_lc[OF lcA])
  have PbA': "?P \<^bold>\<cdot> A' \<approx>\<^bsub>\<o>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> A')"
    using beq.beta[OF wP wa'] by (simp add: opn_lc[OF lcC] opn_lc[OF lcA])
  have "\<Phi> \<turnstile> C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> A" using fp wff_App[OF wC wa]
      by (rule leib_refl)
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> A" by (rule bprov.Beta[OF beq.sym[OF PbA]])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> A'" using leib_subst[OF AA fp wa wa' wP] by auto
  thus ?thesis by (rule bprov.Beta[OF PbA'])
qed
lemma leib_cong1:
  assumes CC: "\<Phi> \<turnstile> C \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> C'" and fp: "freep \<Phi>"
      and wC: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>(C)" and wC': "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>(C')" and wa: "wff\<^bsub>\<alpha>\<^esub>(A)"
    shows "\<Phi> \<turnstile> (C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A)"
proof -
  have lcC: "lc C" using wC by (rule wff_lc)
  have lcA: "lc A" using wa by (rule wff_lc)
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<beta>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (Bnd 0) \<^bold>\<cdot> A)"   \<comment> \<open>\<open>\<lambda>f. (C A) \<^bold>\<doteq> (f A)\<close>\<close>
  have wP: "wff\<^bsub>(\<alpha>\<^bold>\<Rightarrow>\<beta>)\<^bold>\<Rightarrow>\<o>\<^esub>(?P)"
    by (auto simp: opn_lc[OF lcC] opn_lc[OF lcA]
             intro!: wff_AbsI wff_App wff_Fre wC wa wff_App[OF wC wa])
  have PbC: "?P \<^bold>\<cdot> C \<approx>\<^bsub>\<o>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> A)"
    using beq.beta[OF wP wC] by (simp add: opn_lc[OF lcC] opn_lc[OF lcA])
  have PbC': "?P \<^bold>\<cdot> C' \<approx>\<^bsub>\<o>\<^esub> (C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C' \<^bold>\<cdot> A)"
    using beq.beta[OF wP wC'] by (simp add: opn_lc[OF lcC] opn_lc[OF lcA])
  have "\<Phi> \<turnstile> C \<^bold>\<cdot> A \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> C \<^bold>\<cdot> A"
    using fp wff_App[OF wC wa] by (rule leib_refl)
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> C" by (rule bprov.Beta[OF beq.sym[OF PbC]])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> C'" using leib_subst[OF CC fp wC wC' wP] by auto
  thus ?thesis by (rule bprov.Beta[OF PbC'])
qed

subsubsection \<open>Deductive closure of the Hintikka set\<close>

text \<open>Since \<open>Hset\<close> is maximal and each of its finite subsets is consistent, every sentence
    provable from a finite subset already belongs to \<open>Hset\<close> (deductive closure --- a consequence
    of the maximality of the extension, BKK Lemma 6.32).\<close>

lemma Hset_deduct: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
      and finF: "finite F" and subF: "F \<subseteq> Hset \<Phi>" and FS: "F \<turnstile> S"
      and cS: "cwff \<o> S" shows "S \<in> Hset \<Phi>"
proof (rule ccontr)
  assume "S \<notin> Hset \<Phi>"
  hence negS: "\<^bold>\<not> S \<in> Hset \<Phi>" using Hset_maximal[OF cS] by blast
  have fin': "finite (insert (\<^bold>\<not> S) F)" using finF by simp
  have sub': "insert (\<^bold>\<not> S) F \<subseteq> Hset \<Phi>" using negS subF by auto
  have "insert (\<^bold>\<not> S) F \<turnstile> \<^bold>\<bottom>"
    by (meson FS Hyp NegE bprov_weaken fin' freep_finite insertCI subset_insertI wff_FalseB)
  moreover have "con (insert (\<^bold>\<not> S) F)"
      by (rule Hset_finite_con[OF con\<Phi> fp\<Phi> fin' sub'])
  ultimately show False by (simp add: con_def)
qed

text \<open>In particular, Leibniz equality is reflexive on \<open>Hset\<close> --- BKK's property \<open>\<nabla>\<^sub>r\<close>
  for saturated Hintikka sets (Lemma 6.25; Lemma 6.23 gives the negative form
  \<open>\<^sub>~\<nabla>\<^sub>=\<^sub>r\<close>); symmetry, transitivity and congruence follow below.\<close>

lemma Hset_leib_refl: fixes \<Phi> :: "'p::{countable,infinite} tm set" 
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>" and ca: "cwff \<alpha> A"
  shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{}"])
  note wa = cwff_wff[OF ca] and cA = cwff_closed[OF ca]
  show "finite {}" by simp
  show "{} \<subseteq> Hset \<Phi>" by simp
  show "{} \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A"
    by (rule leib_refl[OF freep_finite[OF finite.emptyI] wa])
  show "cwff \<o> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)"
    by (rule cwffI[OF wff_LeibE[OF wa wa]]) (simp add: Leib_def cA)
qed
lemma Hset_leib_sym: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
    and ca: "cwff \<alpha> A" and cb: "cwff \<alpha> B" and AB: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<in> Hset \<Phi>"
  shows "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wa = cwff_wff[OF ca] and cA = cwff_closed[OF ca] and
       wb = cwff_wff[OF cb] and cB = cwff_closed[OF cb]
  show "finite {A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B}" by simp
  show "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B} \<subseteq> Hset \<Phi>" using AB by simp
  show "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B} \<turnstile> B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A"
    by (simp add: Hyp freep_finite leib_sym wa wb)
  show "cwff \<o> (B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)"
    by (rule cwffI[OF wff_LeibE[OF wb wa]]) (simp add: Leib_def cA cB)
qed
lemma Hset_leib_trans: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
  and ca: "cwff \<alpha> A" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)" and cc: "cwff \<alpha> C"
  and AB: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<in> Hset \<Phi>" and BC: "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C) \<in> Hset \<Phi>"
  shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wa = cwff_wff[OF ca] and cA = cwff_closed[OF ca] and
       wc = cwff_wff[OF cc] and cC = cwff_closed[OF cc]
  let ?F = "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B, B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C}"
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using AB BC by simp
  show "?F \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C"
    by (meson Hyp \<open>finite {A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B, B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C}\<close> freep_finite insertCI
        leib_trans wa wb wc)
  show "cwff \<o> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C)"
    by (rule cwffI[OF wff_LeibE[OF wa wc]]) (simp add: Leib_def cA cC)
qed
lemma Hset_leib_cong: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
      and cc: "cwff (\<alpha>\<^bold>\<Rightarrow>\<beta>) C" and cc': "cwff (\<alpha>\<^bold>\<Rightarrow>\<beta>) C'" and ca: "cwff \<alpha> A"
      and ca': "cwff \<alpha> A'"
      and CC: "(C \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> C') \<in> Hset \<Phi>" and AA: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A') \<in> Hset \<Phi>"
    shows "((C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A')) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wC = cwff_wff[OF cc] and cC = cwff_closed[OF cc] and
       wC' = cwff_wff[OF cc'] and cC' = cwff_closed[OF cc'] and
       wA = cwff_wff[OF ca] and cA = cwff_closed[OF ca] and
       wA' = cwff_wff[OF ca'] and cA' = cwff_closed[OF ca']
  let ?F = "{C \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> C', A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A'}"
  have fp: "freep ?F" using freep_finite[of ?F] by simp
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using CC AA by simp
  show "?F \<turnstile> (C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A')"
    by (meson Hyp fp insertCI leib_cong1 leib_cong2 leib_trans wA wA' wC wC' 
              wff_App[OF wC' wA] wff_App[OF wC' wA'] wff_App[OF wC wA])
  show "cwff \<o> ((C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A'))"
    by (rule cwffI[OF wff_LeibE[OF wff_App[OF wC wA] wff_App[OF wC' wA']]])
       (simp add: Leib_def cC cA cC' cA')
qed

text \<open>Leibniz-equal propositions have the same truth (membership transfers along \<open>\<sim>\<close> at type \<open>\<o>\<close>);
proved by Leibniz substitution with the identity predicate.\<close>

lemma Hset_leib_mp: fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
      and ca: "cwff \<o> A" and cb: "cwff \<o> B" and AB: "(A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B) \<in> Hset \<Phi>"
      and A: "A \<in> Hset \<Phi>"
    shows "B \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi> _ _ _ cb])
  note wA = cwff_wff[OF ca] and cA = cwff_closed[OF ca] and
       wB = cwff_wff[OF cb] and cB = cwff_closed[OF cb]
  let ?F = "{A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B, A}"
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0)"   \<comment> \<open>the identity predicate\<close>
  have wP: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)" by (rule wff_AbsI) (simp add: wff_Fre)
  have fp: "freep ?F" using freep_finite[of ?F] by simp
  have PA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> A" using beq.beta[OF wP wA] by simp
  have PB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> B" using beq.beta[OF wP wB] by simp
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using AB A by simp
  have s1: "?F \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B" by (auto intro: bprov.Hyp)
  have s2: "?F \<turnstile> ?P \<^bold>\<cdot> A"
    by (rule bprov.Beta[OF beq.sym[OF PA]]) (auto intro: bprov.Hyp)
  have "?F \<turnstile> ?P \<^bold>\<cdot> B" by (rule leib_subst[OF s1 fp wA wB wP s2])
  thus "?F \<turnstile> B" by (rule bprov.Beta[OF PB])
qed

subsection \<open>The term model (BKK Section 6, the Hintikka lemma)\<close>

text \<open>Fix a consistent, parameter-rich set \<open>\<Phi>\<close>; its Hintikka extension \<open>H\<close> is maximal, consistent
  and saturated.  The @{emph \<open>term model\<close>} has as its domain the closed well-formed terms quotiented
  by provable Leibniz equality \<open>A \<sim> B \<equiv> (A \<^bold>\<doteq> B) \<in> H\<close>; this quotient is what forces property q.\<close>

locale hintikka_model = fixes \<Phi> :: "'p::{countable,infinite} tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "freep \<Phi>"
begin

text \<open>The \<open>\<sim>\<close>-equivalence classes of closed well-formed terms (@{const cwff} from
  Section 2): \<open>A \<sim> B \<equiv> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> H\<close> --- the Leibniz quotient of BKK's model-existence proof
  (BKK Theorem 6.33); the \<open>\<^sub>~\<nabla>\<close>-properties of Leibniz equality in \<open>H\<close> are BKK Lemma 6.23.\<close>

definition cls :: "'p tm \<Rightarrow> 'p tm set" where
  "cls A \<equiv> {B. \<exists>\<sigma>. cwff \<sigma> A \<and> cwff \<sigma> B \<and> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi>}"
lemma cls_self: "cwff \<sigma> A \<Longrightarrow> A \<in> cls A"
  using Hset_leib_refl[OF con\<Phi> fp\<Phi>] by (auto simp: cls_def cwff_def)
lemma leib_sym':
  "cwff \<sigma> A \<Longrightarrow> cwff \<sigma> B \<Longrightarrow> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi> \<Longrightarrow> (B \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> A) \<in> Hset \<Phi>" 
  using Hset_leib_sym[OF con\<Phi> fp\<Phi>] by (auto simp: cwff_def)
lemma leib_trans':
  "cwff \<sigma> A \<Longrightarrow> cwff \<sigma> B \<Longrightarrow> cwff \<sigma> C \<Longrightarrow> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi>
    \<Longrightarrow> (B \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> C) \<in> Hset \<Phi> \<Longrightarrow> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> C) \<in> Hset \<Phi>"
  using Hset_leib_trans[OF con\<Phi> fp\<Phi>] by (auto simp: cwff_def)

text \<open>The quotient is faithful: two classes coincide exactly when the terms are Leibniz-equal in
  \<open>H\<close>.  This is what will give property q in the model.\<close>

lemma cls_eq_iff:
  assumes wA: "cwff \<sigma> A" and wB: "cwff \<sigma> B"
    shows "(cls A = cls B) \<longleftrightarrow> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi>" 
  by (smt (verit, best) Collect_cong cls_def cls_self cwff_unique
      leib_sym' leib_trans' mem_Collect_eq wA wB)

lemma cls_rep:
  assumes "cwff \<sigma> A"
  shows "cwff \<sigma> (SOME B. B \<in> cls A) \<and> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> (SOME B. B \<in> cls A)) \<in> Hset \<Phi>"
proof -
  have "(SOME B. B \<in> cls A) \<in> cls A" using cls_self[OF assms]
    by (metis someI)
  then obtain \<tau> where t: "cwff \<tau> A" "cwff \<tau> (SOME B. B \<in> cls A)"
    "(A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> (SOME B. B \<in> cls A)) \<in> Hset \<Phi>" by (auto simp: cls_def)
  have "\<tau> = \<sigma>" using cwff_unique[OF t(1) assms].
  thus ?thesis using t(2,3) by simp
qed

text \<open>The applicative structure of the term model (BKK Definition 3.1): the domain of type \<open>\<sigma>\<close>
  consists of the classes of closed terms of type \<open>\<sigma>\<close>, and application is term application.\<close>

definition Dm :: "ty \<Rightarrow> 'p tm set \<Rightarrow> bool" where "Dm \<sigma> X \<equiv> \<exists>A. cwff \<sigma> A \<and> X = cls A"
definition Ap :: "'p tm set \<Rightarrow> 'p tm set \<Rightarrow> 'p tm set" where
  "Ap X Y \<equiv> cls ((SOME A. A \<in> X) \<^bold>\<cdot> (SOME B. B \<in> Y))"
lemma Ap_cls:
  assumes wA: "cwff (\<alpha> \<^bold>\<Rightarrow> \<beta>) A" and wB: "cwff \<alpha> B"
    shows "Ap (cls A) (cls B) = cls (A \<^bold>\<cdot> B)"
proof -
  have a: "cwff (\<alpha> \<^bold>\<Rightarrow> \<beta>) (SOME A'. A' \<in> cls A)" "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> (SOME A'. A' \<in> cls A)) \<in> Hset \<Phi>" 
    using cls_rep[OF wA] by auto
  have b: "cwff \<alpha> (SOME B'. B' \<in> cls B)" "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> (SOME B'. B' \<in> cls B)) \<in> Hset \<Phi>"
    using cls_rep[OF wB] by auto
  have wAB: "cwff \<beta> (A \<^bold>\<cdot> B)" using wA wB
    by (auto simp: cwff_def intro: wff_App)
  have "((A \<^bold>\<cdot> B) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))) \<in> Hset \<Phi>"
    using Hset_leib_cong[OF con\<Phi> fp\<Phi>] wA a(1) wB b(1) a(2) b(2) by (auto simp: cwff_def)
  moreover have "cwff \<beta> ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))" 
    using a(1) b(1) cwff_App by blast 
  ultimately have "cls (A \<^bold>\<cdot> B) = cls ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))"
    using cls_eq_iff wAB by blast
  thus ?thesis by (simp add: Ap_def)
qed
lemma Dm_cls: "cwff \<sigma> A \<Longrightarrow> Dm \<sigma> (cls A)" by (auto simp: Dm_def)
lemma Ap_dom: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) X \<Longrightarrow> Dm \<alpha> Y \<Longrightarrow> Dm \<beta> (Ap X Y)" 
  by (auto simp: Dm_def Ap_cls cwff_def intro: wff_App)

text \<open>Truth and falsity behave (the analogue of BKK Lemma 3.43 / property b): \<open>\<^bold>\<top> \<in> H\<close>, \<open>\<^bold>\<bottom> \<notin> H\<close>,
  so \<open>cls \<^bold>\<top> \<noteq> cls \<^bold>\<bottom>\<close>.\<close>

lemma Hset_TrueB: "\<^bold>\<top> \<in> Hset \<Phi>"
  using Hset_deduct bprov_TrueB con\<Phi> cwff_TrueB fp\<Phi> by blast 
lemma Hset_not_FalseB: "\<^bold>\<bottom> \<notin> Hset \<Phi>"
  by (metis hintikka_model_axioms Hyp con_def con_Hset hintikka_model_def)
lemma TF: "cls \<^bold>\<top> \<noteq> cls \<^bold>\<bottom>"
  using Hset_TrueB Hset_leib_mp Hset_not_FalseB cls_eq_iff con\<Phi>
        cwff_FalseB cwff_TrueB fp\<Phi> by blast

subsubsection \<open>Satisfaction bridges: membership in \<open>H\<close> as truth
  (BKK Lemma 6.21, Lemmas 6.25--6.26)\<close>

text \<open>\<open>H\<close> never contains both \<open>\<phi>\<close> and \<open>\<^bold>\<not>\<phi>\<close> (BKK's property \<open>\<^sub>~\<nabla>\<^sub>c\<close>, Definition 6.19,
  here for arbitrary sentences via Lemma 6.10).\<close>

lemma Hset_notboth: "wff\<^bsub>\<o>\<^esub>(\<phi>) \<Longrightarrow> \<phi> \<in> Hset \<Phi> \<Longrightarrow> \<^bold>\<not> \<phi> \<notin> Hset \<Phi>"
    using con\<Phi> con_Hset con_not_both fp\<Phi> by auto

text \<open>Boolean extensionality inside \<open>H\<close> (via the rule \<open>NK(b)\<close>; the saturated-sets lemma for
  property b, BKK Lemma 6.26): a member of \<open>H\<close> is Leibniz-equal to \<open>\<^bold>\<top>\<close>, a non-member
  to \<open>\<^bold>\<bottom>\<close>.\<close>

lemma Hset_eq_TrueB:
  assumes p: "\<phi> \<in> Hset \<Phi>" and w: "cwff \<o> \<phi>"
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{\<phi>}"])
  show "finite {\<phi>}" by simp
  show "{\<phi>} \<subseteq> Hset \<Phi>" using p by simp
  show "{\<phi>} \<turnstile> \<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>"
    by (metis BoolE Hyp bprov_TrueB cwff_def insertCI insert_is_Un w wff_TrueB)
  show "cwff \<o> (\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>)"
    by (metis cwff_App cwff_TrueB cwff_def fvs_defs(5) w wff_Leib)   
qed

lemma Hset_eq_FalseB: assumes np: "\<^bold>\<not> \<phi> \<in> Hset \<Phi>" and w: "cwff \<o> \<phi>"
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{\<^bold>\<not> \<phi>}"])
  show "finite {\<^bold>\<not> \<phi>}" by simp
  show "{\<^bold>\<not> \<phi>} \<subseteq> Hset \<Phi>" using np by simp
  show "{\<^bold>\<not> \<phi>} \<turnstile> \<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>" 
    by (metis BoolE Hyp NegE TrueB_def Un_empty_right
        Un_insert_right bprov_TrueB cwff_wff insertCI w wff_FalseB)
  show "cwff \<o> (\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>)" 
    by (metis w cwff_def cwff_FalseB cwff_App wff_Leib fvs_defs(5)) 
qed

text \<open>Sentences with the same truth value in \<open>H\<close> are Leibniz-equal in \<open>H\<close> (the general form
  of the \<open>NK(b)\<close> bridge, cf.\ BKK Lemma 6.26).\<close>

lemma Hset_iff_eq:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
      and iff: "\<phi> \<in> Hset \<Phi> \<longleftrightarrow> \<psi> \<in> Hset \<Phi>" 
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<psi>) \<in> Hset \<Phi>" 
  by (metis Hset_eq_FalseB Hset_eq_TrueB Hset_maximal cls_eq_iff
      cwff_FalseB cwff_TrueB iff wp wq)

text \<open>THE satisfaction bridge: a sentence's class is the class of \<open>\<^bold>\<top>\<close> exactly when it is
  in \<open>H\<close> (the \<open>\<upsilon>\<close>-valuation of the term model in the proof of BKK Theorem 6.33).\<close>

lemma cls_TrueB_iff: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<top> \<longleftrightarrow> \<phi> \<in> Hset \<Phi>" 
  by (metis Hset_eq_FalseB Hset_eq_TrueB Hset_maximal TF cls_eq_iff cwff_FalseB cwff_TrueB)

text \<open>Property b at the class level: the boolean domain has exactly the classes of \<open>\<^bold>\<top>\<close>
  and \<open>\<^bold>\<bottom>\<close> (BKK Definition 3.46).\<close>

lemma cls_bool: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<top> \<or> cls \<phi> = cls \<^bold>\<bottom>" 
  by (metis TF cls_eq_iff cwff_FalseB cls_TrueB_iff Hset_iff_eq)
lemma cls_FalseB_iff: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<bottom> \<longleftrightarrow> \<phi> \<notin> Hset \<Phi>" 
  by (metis cls_eq_iff cwff_FalseB TF Hset_iff_eq cls_TrueB_iff)

subsubsection \<open>The evaluation and logical conditions of the term model\<close>

text \<open>The \<open>\<beta>\<close>-condition (BKK Definition 3.18(4)) inside \<open>H\<close>: a \<open>\<beta>\<close>-redex is Leibniz-equal to
  its reduct, via the rule \<open>NK(\<beta>)\<close> applied to reflexivity.\<close>

lemma Hset_beta:
  assumes wAbs: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and wa: "cwff \<sigma> a"
    shows "((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> b\<^bold>\<langle>a\<^bold>\<rangle>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{}"])
  let ?A = "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a"  let ?B = "b\<^bold>\<langle>a\<^bold>\<rangle>"
  have wA: "wff\<^bsub>\<tau>\<^esub>(?A)"
    using cwff_wff[OF wAbs] cwff_wff[OF wa] by (auto intro: wff_App)
  have step: "(?B \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B) \<approx>\<^bsub>\<o>\<^esub> (?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B)" 
    by (meson appL appR beq.sym beta cwff_wff wAbs wa wff_Leib wff_opn)
  show "{} \<turnstile> ?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B"
    by (meson Beta cwff_def finite.emptyI freep_finite leib_refl local.step wAbs wa wff_opn) 
  show "finite {}" by simp
  show "{} \<subseteq> Hset \<Phi>" by simp
  show "cwff \<o> (?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B)"
    by (meson cwff_App cwff_def cwff_opn fvs_defs(5) wAbs wa wff_Leib)
qed

text \<open>The \<open>L\<^bsub>\<not>\<^esub>\<close> condition (BKK Figure 2) at the class level, from maximality
  and consistency of \<open>H\<close>.\<close>

lemma cls_neg: "cwff \<o> \<phi> \<Longrightarrow> cls (\<^bold>\<not> \<phi>) = (if cls \<phi> = cls \<^bold>\<top> then cls \<^bold>\<bottom> else cls \<^bold>\<top>)"
  by (meson Hset_maximal Hset_notboth cwff_App cwff_Neg cwff_def
            cls_FalseB_iff cls_TrueB_iff)

text \<open>The \<open>L\<^bsub>\<or>\<^esub>\<close> condition: \<open>H\<close> treats disjunction disjunctively (BKK \<open>\<nabla>\<^sub>\<or>\<close>, Definition 6.19).\<close>

lemma Hset_dis_iff:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
    shows "\<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi> \<longleftrightarrow> \<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>" 
proof
  assume d: "\<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi>"
  show "\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>"
  proof (rule ccontr)
    assume "\<not> (\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>)"
    hence np: "\<^bold>\<not> \<phi> \<in> Hset \<Phi>" and nq: "\<^bold>\<not> \<psi> \<in> Hset \<Phi>"
        using Hset_maximal[OF wp] Hset_maximal[OF wq] by blast+
    let ?F = "{\<phi> \<^bold>\<or> \<psi>, \<^bold>\<not> \<phi>, \<^bold>\<not> \<psi>}"
    have "?F \<turnstile> \<phi> \<^bold>\<or> \<psi>" by (auto intro: bprov.Hyp)
    moreover have "?F \<union> {\<phi>} \<turnstile> \<^bold>\<bottom>"
      by (metis Hyp NegE insertCI insert_is_Un sup.commute wff_FalseB)   
    moreover have "?F \<union> {\<psi>} \<turnstile> \<^bold>\<bottom>"
      by (metis Hyp NegE Un_insert_right insertCI insert_subset sup_ge1 wff_FalseB)
    ultimately have "?F \<turnstile> \<^bold>\<bottom>"
      using cwff_wff[OF wp] cwff_wff[OF wq] by (metis bprov.DisE)
    moreover have "con ?F"
      by (meson Hset_finite_con con\<Phi> d empty_subsetI finite.emptyI finite.insertI
                fp\<Phi> insert_subsetI np nq)
    ultimately show False by (simp add: con_def)
  qed
next
  show "\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi> \<Longrightarrow> \<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi>" 
    by (meson DisIL DisIR Hset_deduct Hyp bprov_finite con\<Phi> cwff_App
        cwff_Dis cwff_def fp\<Phi> wp wq)
qed

lemma cls_dis:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
  shows "cls (\<phi> \<^bold>\<or> \<psi>) = (if cls \<phi> = cls \<^bold>\<top> \<or> cls \<psi> = cls \<^bold>\<top> then cls \<^bold>\<top> else cls \<^bold>\<bottom>)"
proof -
  have wd: "cwff \<o> (\<phi> \<^bold>\<or> \<psi>)" using wp wq by (auto simp: cwff_def)
  show ?thesis by (simp add: Hset_dis_iff cls_FalseB_iff cls_TrueB_iff wd wp wq)
qed

text \<open>The \<open>L\<^sup>\<sigma>\<^bsub>\<forall>\<^esub>\<close> condition: \<open>H\<close> treats the quantifier universally --- \<open>NK(\<Pi>E)\<close> gives one
  direction, the witness property \<open>\<^sub>~\<nabla>\<^sub>\<exists>\<close> (BKK Definition 6.19) together with maximality the
  other.\<close>

lemma Hset_pi_iff:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f"
    shows "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi> \<longleftrightarrow> (\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>)"
proof
  assume pf: "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi>"
  have step: "f \<^bold>\<cdot> a \<in> Hset \<Phi>" if wa: "cwff \<sigma> a" for a
    by (meson Hset_maximal Hyp NegE PiE con\<Phi> con_Hset con_def
              cwff_App cwff_def fp\<Phi> local.wf pf wa wff_FalseB)
  thus "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>" by blast
next
  assume all: "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>"
  show "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi>"
  proof (rule ccontr)
    assume npf: "(Pi \<sigma>) \<^bold>\<cdot> f \<notin> Hset \<Phi>"
    have wPf: "wff\<^bsub>\<o>\<^esub>((Pi \<sigma>) \<^bold>\<cdot> f)"
      using cwff_wff[OF wf] by (auto intro: wff_App wff_Pi)
    have cPf: "fvs ((Pi \<sigma>) \<^bold>\<cdot> f) = {}"
      using cwff_closed[OF wf] by simp
    have n: "\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f) \<in> Hset \<Phi>"
        using Hset_maximal[OF cwffI[OF wPf cPf]] npf by blast
    have wn: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f))" using wPf by (rule wff_Not)
    have cn: "fvs (\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f)) = {}" using cPf by simp
    obtain c where nc: "\<^bold>\<not> (f \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<sigma>\<^esub>)) \<in> Hset \<Phi>"
      using Hset_saturated[OF con\<Phi> fp\<Phi> cwffI[OF wn cn] n] by blast
    have inc: "f \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<sigma>\<^esub>) \<in> Hset \<Phi>"
      using all[rule_format, of "c\<^sup>p\<^bsub>\<sigma>\<^esub>"] cwff_Par[of \<sigma> c] by simp
    show False
      using Hset_notboth[OF wff_App[OF cwff_wff[OF wf] wff_Par] inc] nc by simp
  qed
qed

lemma cls_pi:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f"
  shows "cls ((Pi \<sigma>) \<^bold>\<cdot> f) = (if (\<forall>a. cwff \<sigma> a \<longrightarrow> Ap (cls f) (cls a) = cls \<^bold>\<top>)
                             then cls \<^bold>\<top> else cls \<^bold>\<bottom>)"
proof -
  have wPf: "cwff \<o> ((Pi \<sigma>) \<^bold>\<cdot> f)"
    using wf by (auto simp: cwff_def intro: wff_App wff_Pi)
  have e: "(Ap (cls f) (cls a) = cls \<^bold>\<top>) = (f \<^bold>\<cdot> a \<in> Hset \<Phi>)" if a: "cwff \<sigma> a" for a
    using Ap_cls[OF wf a] cls_TrueB_iff[OF cwff_App[OF wf a]] by simp
  have inner: "(\<forall>a. cwff \<sigma> a \<longrightarrow> Ap (cls f) (cls a) = cls \<^bold>\<top>)
      = (\<forall>a. cwff \<sigma> a \<longrightarrow> App f a \<in> Hset \<Phi>)" using e by blast
  show ?thesis
    using cls_TrueB_iff[OF wPf] cls_FalseB_iff[OF wPf] Hset_pi_iff[OF wf] inner
    by (cases "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>") auto
qed

text \<open>The \<open>\<beta>\<close>-condition transfers membership: a redex of type \<open>\<o>\<close> is in \<open>H\<close> exactly when its
  reduct is (via the Leibniz bridge).\<close>

lemma Hset_beta_iff:
  assumes "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and "cwff \<sigma> a"
  shows "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a \<in> Hset \<Phi> \<longleftrightarrow> b\<^bold>\<langle>a\<^bold>\<rangle> \<in> Hset \<Phi>"
  by (meson Hset_beta Hset_leib_mp Hset_leib_sym con\<Phi> cwff_App cwff_opn fp\<Phi> assms)

text \<open>Type uniqueness of the classes (BKK: the domains are disjoint by type).\<close>

lemma cls_type:
  "cwff \<sigma> s \<Longrightarrow> cwff \<tau> t \<Longrightarrow> cls s = cls t \<Longrightarrow> \<sigma> = \<tau>" 
  by (smt (verit, ccfv_SIG) cls_def cls_self cwff_unique mem_Collect_eq)

text \<open>Property q (BKK Definition 3.46): the Leibniz combinator itself is the identity
  relation of the term model, by @{thm cls_eq_iff}.\<close>

lemma cwff_Leib: "cwff (\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>) (Leib \<sigma>)" by (simp add: cwff_def)

text \<open>Property f (functionality, BKK Definition 3.46) via the rule \<open>NK(f)\<close>: two functions
  that agree on every class are Leibniz-equal in \<open>H\<close>.  Saturation enters through
  @{thm Hset_pi_iff} to establish the \<open>\<Pi>\<close>-premise of \<open>NK(f)\<close>.\<close>

lemma cls_ext:
  assumes wg: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) g" and wh: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) h"
      and ag: "\<And>a. cwff \<sigma> a \<Longrightarrow> Ap (cls g) (cls a) = Ap (cls h) (cls a)"
    shows "cls g = cls h"
proof -
  have lcg: "lc g" and lch: "lc h" using wg wh
    by (auto intro: cwff_lc)
  let ?body = "g \<^bold>\<cdot> (Bnd 0) \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> h \<^bold>\<cdot> (Bnd 0)"
  have opnb: "?body\<^bold>\<langle>u\<^bold>\<rangle> = (g \<^bold>\<cdot> u \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> h \<^bold>\<cdot> u)" for u using lcg lch
    by simp
  \<comment> \<open>the abstracted body is a closed well-formed predicate\<close>
  have wB: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)"
  proof -
    have "wff\<^bsub>\<o>\<^esub>(?body\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" for x unfolding opnb
      using cwff_wff[OF wg] cwff_wff[OF wh]
      by (auto intro: wff_App wff_Fre)
    hence "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)" by (rule wff_AbsI)
    moreover have "fvs (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) = {}"
      using cwff_closed[OF wg] cwff_closed[OF wh]
      by (simp add: Leib_def)
    ultimately show ?thesis by (simp add: cwff_def)
  qed
  \<comment> \<open>pointwise agreement puts every instance of the body in \<open>H\<close>\<close>
  have inst: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<^bold>\<cdot> a \<in> Hset \<Phi>" if a: "cwff \<sigma> a" for a
    by (smt (verit, ccfv_threshold) Ap_cls Hset_beta_iff ag
        cls_eq_iff cwff_App opnb that wB wg wh)
  \<comment> \<open>hence the \<open>\<Pi>\<close>-sentence is in \<open>H\<close>, and \<open>NK(f)\<close> yields the equation\<close>
  have PiH: "(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<in> Hset \<Phi>"
      using Hset_pi_iff[OF wB] inst by blast
  have "(g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub>
      ?body)}"])
    show "finite {(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)}" by simp
    show "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)} \<subseteq> Hset \<Phi>" using PiH by simp
    have "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)} \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body"
      by (auto intro: bprov.Hyp simp: Forall_def)
    thus "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)} \<turnstile> g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h"
      using FuncE cwff_wff wg wh by blast
    show "cwff \<o> (g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h)" by (metis cwff_App wg wh cwff_Leib)
 qed
  thus ?thesis using cls_eq_iff[OF wg wh] by simp
qed

text \<open>The description condition of the term model (beyond BKK; cf.\ Andrews 1972): a class
that provably behaves as the singleton of \<open>a\<close> is mapped by \<open>Iota \<sigma>\<close> to the class of \<open>a\<close>.
Functional extensionality \<open>NK(f)\<close> reduces the pointwise hypothesis to a Leibniz equation
with the literal singleton \<open>(Leib \<sigma>) \<^bold>\<cdot> a\<close>, which the axiom \<open>NK(\<iota>)\<close> describes.\<close>

lemma cls_desc:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f" and wa: "cwff \<sigma> a"
      and sing: "\<And>b. cwff \<sigma> b \<Longrightarrow> (Ap (cls f) (cls b) = cls \<^bold>\<top>) = (cls b = cls a)"
    shows "cls ((Iota \<sigma>) \<^bold>\<cdot> f) = cls a"
proof -
  have lcf: "lc f" and lca: "lc a" using wf wa
    by (auto intro: cwff_lc)
  let ?body = "f \<^bold>\<cdot> (Bnd 0) \<^bold>\<doteq>\<^bsub>\<o>\<^esub> ((Leib \<sigma>) \<^bold>\<cdot> a) \<^bold>\<cdot> (Bnd 0)"
  have opnb: "?body\<^bold>\<langle>u\<^bold>\<rangle> = (f \<^bold>\<cdot> u \<^bold>\<doteq>\<^bsub>\<o>\<^esub> ((Leib \<sigma>) \<^bold>\<cdot> a) \<^bold>\<cdot> u)" for u
    using lcf lca by simp
  have wB: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)"
  proof -
    have "wff\<^bsub>\<o>\<^esub>(?body\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" for x unfolding opnb
      using cwff_wff[OF wf] cwff_wff[OF wa]
      by (auto intro: wff_App wff_Fre)
    hence "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)" by (rule wff_AbsI)
    moreover have "fvs (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) = {}" using cwff_def local.wf wa
      by auto
    ultimately show ?thesis by (simp add: cwff_def)
  qed
  \<comment> \<open>the pointwise singleton facts land in \<open>H\<close>\<close>
  have inst: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<^bold>\<cdot> b \<in> Hset \<Phi>" if b: "cwff \<sigma> b" for b
    by (metis (no_types, opaque_lifting) Ap_cls Hset_beta_iff Hset_iff_eq cls_TrueB_iff
              cls_eq_iff cwff_App cwff_Leib local.wf opnb sing that wB wa)
  have PiH: "(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<in> Hset \<Phi>"
    using Hset_pi_iff[OF wB] inst by blast
  \<comment> \<open>\<open>NK(f)\<close> reduces to the literal singleton, \<open>NK(\<iota>)\<close> describes it\<close>
  have "(((Iota \<sigma>) \<^bold>\<cdot> f) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)}"])
    show "finite {(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)}" by simp
    show "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)} \<subseteq> Hset \<Phi>" using PiH by simp
    let ?F = "{(Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)}"
    have fpF: "freep ?F" by (rule freep_finite) simp
    have PiD: "?F \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body"
      by (auto intro: bprov.Hyp simp: Forall_def)
    show "?F \<turnstile> (Iota \<sigma>) \<^bold>\<cdot> f \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a"
      by (rule leib_trans[OF
        leib_cong2[OF bprov.FuncE[OF PiD cwff_wff[OF wf] 
                cwff_wff[OF cwff_App[OF cwff_Leib wa]]] fpF
                    cwff_wff[OF wf] cwff_wff[OF cwff_App[OF
                    cwff_Leib wa]] 
              wff_Iota] bprov.Desc[OF cwff_wff[OF wa]] fpF
                  wff_App[OF wff_Iota cwff_wff[OF wf]] 
            wff_App[OF wff_Iota cwff_wff[OF cwff_App[OF cwff_Leib
                wa]]] cwff_wff[OF wa]])
    show "cwff \<o> ((Iota \<sigma>) \<^bold>\<cdot> f \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a)" 
      by (metis wa cwff_App local.wf cwff_Leib cwff_Iota)
  qed
  thus ?thesis
    using cls_eq_iff[OF cwff_App[OF cwff_Iota wf] wa] by simp
qed

text \<open>Primitive equality in \<open>H\<close> (BKK Remark 7.9): reflexivity is \<open>\<nabla>\<^bsub>=\<^sub>r\<^esub>\<close> via \<open>NK(=\<^sub>r)\<close>, and
primitive and Leibniz equality coincide in \<open>H\<close> --- \<open>\<rightarrow>\<close> via \<open>NK(=\<^sub>l)\<close> (\<open>\<nabla>\<^bsub>=\<^sub>\<doteq>\<^esub>\<close>), \<open>\<leftarrow>\<close> by
Leibniz substitution into \<open>\<lambda>x. a \<^bold>=\<^bsub>\<sigma>\<^esub> x\<close> from reflexivity.\<close>

lemma Hset_peq_iff:
  assumes wa: "cwff \<sigma> a" and wb: "cwff \<sigma> b"
    shows "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi> \<longleftrightarrow> (a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
proof
  assume p: "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>" show "(a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b}"])
    show "finite {a \<^bold>=\<^bsub>\<sigma>\<^esub> b}" by simp
    show "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b} \<subseteq> Hset \<Phi>" using p by simp
    show "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b} \<turnstile> a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b"
      by (auto intro: bprov.EqL bprov.Hyp)
    show "cwff \<o> (a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b)"
      using cwff_App cwff_Leib wa wb by blast
  qed
next
  assume l: "(a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>" show "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b}"])
    show "finite {a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b}" by simp
    show "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b} \<subseteq> Hset \<Phi>" using l by simp
    let ?F = "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b}"  let ?P = "\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (a \<^bold>=\<^bsub>\<sigma>\<^esub> Bnd 0)"
    have lca: "lc a" using wa by (rule cwff_lc)
    have wP: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)"
      by (rule wff_AbsI)
         (auto simp: opn_lc[OF lca] intro: cwff_wff[OF wa] wff_Fre)
    have fpF: "freep ?F" by (rule freep_finite) simp
    have hyp: "?F \<turnstile> a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b" by (auto intro: bprov.Hyp)
    have PA: "?P \<^bold>\<cdot> a \<approx>\<^bsub>\<o>\<^esub> (a \<^bold>=\<^bsub>\<sigma>\<^esub> a)"
      using beq.beta[OF wP cwff_wff[OF wa]] by (simp add: opn_lc[OF lca])
    have PB: "?P \<^bold>\<cdot> b \<approx>\<^bsub>\<o>\<^esub> (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using beq.beta[OF wP cwff_wff[OF wb]] by (simp add: opn_lc[OF lca])
    have "?F \<turnstile> a \<^bold>=\<^bsub>\<sigma>\<^esub> a" by (rule bprov.EqR[OF cwff_wff[OF wa]])
    hence "?F \<turnstile> ?P \<^bold>\<cdot> a" by (rule bprov.Beta[OF beq.sym[OF PA]])
    hence "?F \<turnstile> ?P \<^bold>\<cdot> b"
      by (rule leib_subst[OF hyp fpF cwff_wff[OF wa] cwff_wff[OF wb] wP])
    thus "?F \<turnstile> a \<^bold>=\<^bsub>\<sigma>\<^esub> b" by (rule bprov.Beta[OF PB])
    show "cwff \<o> (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using cwff_wff[OF wa] cwff_wff[OF wb] cwff_closed[OF wa] cwff_closed[OF wb] 
      by (auto simp: cwff_def)
  qed
qed

end

subsubsection \<open>Model existence (BKK Lemma 7.5 / Theorem 7.6)\<close>

text \<open>The Hintikka set induces a term evaluation: the class map \<open>cls\<close> together with the term-model
  domains and application satisfies every @{locale valuation} condition.  Via the bridge
  \<open>valuation \<subseteq> bkk_model\<close> of Section 2, every \<open>NK\<close>-consistent set of sentences therefore
  has a model in the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> --- BKK's model-existence theorem.\<close>

sublocale hintikka_model \<subseteq> V: valuation Dm Ap cls
proof
  show "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> cwff \<sigma> a \<Longrightarrow> Ap (cls (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) (cls a) = cls (b\<^bold>\<langle>a\<^bold>\<rangle>)"
    for \<sigma> \<tau> b a by (metis (no_types, lifting) Ap_cls Hset_beta cls_eq_iff cwff_App cwff_opn)
  show "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) g \<Longrightarrow> cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) h \<Longrightarrow> (\<And>a. cwff \<sigma> a
      \<Longrightarrow> Ap (cls g) (cls a) = Ap (cls h) (cls a)) \<Longrightarrow> cls g = cls h"
    for \<sigma> \<tau> g h by (rule cls_ext)
  show "cwff \<sigma> a \<Longrightarrow> cwff \<sigma> b \<Longrightarrow> (Ap (Ap (cls (Eq \<sigma>)) (cls a)) (cls b)
      = cls \<^bold>\<top>) = (cls a = cls b)" for \<sigma> a b
  proof -
    assume wa: "cwff \<sigma> a" and wb: "cwff \<sigma> b"
    have 2: "Ap (cls ((Eq \<sigma>) \<^bold>\<cdot> a)) (cls b) = cls (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using Ap_cls[OF cwff_App[OF cwff_Eq wa] wb] by simp
    have wab: "cwff \<o> (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using cwff_App[OF cwff_App[OF cwff_Eq wa] wb] by simp
    show "(Ap (Ap (cls (Eq \<sigma>)) (cls a)) (cls b) = cls \<^bold>\<top>) = (cls a = cls b)"
      using Ap_cls[OF cwff_Eq wa] 2 cls_TrueB_iff[OF wab]
            Hset_peq_iff[OF wa wb] cls_eq_iff[OF wa wb] by simp
  qed
qed(auto simp: Ap_cls Dm_def cls_type TF cls_desc cls_pi cls_dis cls_neg cls_bool)

subsubsection \<open>The truth lemma\<close>

context hintikka_model
begin

text \<open>THE TRUTH LEMMA (the satisfaction claim of BKK Theorem 6.33; the underlying Hintikka
  properties are BKK Lemma 6.21): under any domain-respecting assignment a
  sentence denotes its own class, and it denotes the truth value \<open>cls \<^bold>\<top>\<close> of the term model
  exactly when it belongs to \<open>H\<close>.\<close>

theorem truth_lemma:
  "cwff \<o> \<phi> \<Longrightarrow> V.vresp \<xi> \<Longrightarrow> V.Ev \<xi> \<phi> = cls \<^bold>\<top> \<longleftrightarrow> \<phi> \<in> Hset \<Phi>"
  using cls_TrueB_iff msub_closed cwff_closed V.Ev_def by metis

end

subsubsection \<open>Completeness (BKK Corollary 7.7)\<close>

text \<open>\<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> with \<open>NK(\<iota>)\<close> is complete for the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> of \<open>\<Sigma>\<close>-models with
  description (the description-enriched \<open>\<M>\<^sub>\<beta>\<^sub>f\<^sub>b\<close>, cf.\ Andrews 1972): a sentence that is
  valid in every such model of a sufficiently \<open>\<Sigma>\<close>-pure (\<open>freep\<close>, BKK Definition 6.3) set of
  sentences \<open>\<Phi>\<close> (it suffices to assume validity over the models carried by \<open>'p tm set\<close> --- in
  particular the term model) is derivable from \<open>\<Phi>\<close>.  Unlike BKK, who allow signatures of any
  infinite cardinality \<open>\<aleph>\<^sub>s\<close> (BKK Remark 3.16), we fix a countable type of parameter names
  (\<open>'p :: {countable, infinite}\<close>); the enumeration of sentences in the extension lemma rests
  on it.  The proof
  is by contraposition, BKK's argument: if \<open>\<Phi> \<turnstile> A\<close> fails then \<open>\<Phi> \<union> {\<^bold>\<not>A}\<close> is \<open>NK\<close>-consistent
  (\<open>NK(Contr)\<close>), extends to a maximal saturated set (BKK's abstract extension lemma 6.32),
      and its term model --- a general model by
  model existence --- satisfies \<open>\<Phi>\<close> but refutes \<open>A\<close>, contradicting validity.\<close>

lemma fp0: "freep ({} :: 'p::{countable,infinite} tm set)"
  by (rule freep_finite[OF finite.emptyI])

theorem completeness:
  fixes \<Phi> :: "'p::{countable,infinite} tm set" and A :: "'p tm" 
  assumes c: "cwff \<o> A" and fp: "freep \<Phi>"
      and valid: "\<Turnstile>('p tm set) A"
      and sen: "\<And>B. B \<in> \<Phi> \<Longrightarrow> cwff \<o> B" 
  shows "\<Phi> \<turnstile> A"
proof (rule ccontr)
  assume nd: "\<not> \<Phi> \<turnstile> A"
  note wA = cwff_wff[OF c] and cA = cwff_closed[OF c]
  let ?\<Psi> = "insert (\<^bold>\<not> A) \<Phi>"
  have con\<Psi>: "con ?\<Psi>" using bprov.simps con_def nd wA by fastforce
  have fp\<Psi>: "freep ?\<Psi>" by (rule freep_add[OF fp])
  interpret H: hintikka_model ?\<Psi> by unfold_locales (rule con\<Psi> fp\<Psi>)+
  \<comment> \<open>a domain-respecting assignment for the term model\<close>
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm set" where
    "\<xi> \<equiv> \<lambda>n \<tau>. H.cls (undefined\<^sup>p\<^bsub>\<tau>\<^esub>)"
  have r: "H.V.vresp \<xi>"
    by (auto simp: \<xi>_def H.V.vresp_def intro: H.Dm_cls cwff_Par)
  have ra: "app_struct.asg H.Dm \<xi>" using r
    by (simp add: H.V.bkkA.asg_def H.V.vresp_def)
  have bm: "bkk_model H.Dm H.Ap H.V.Ev (\<lambda>a. a = H.cls \<^bold>\<top>)"
    by intro_locales
  \<comment> \<open>the term model satisfies \<open>\<Phi>\<close> by the truth lemma\<close>
  have sat: "\<forall>B\<in>\<Phi>. H.V.Ev \<xi> B = H.cls \<^bold>\<top>"
    using H.truth_lemma[OF _ r] sen Phi_sub_Hset[of ?\<Psi>]
    by (auto simp: cwff_def)
  \<comment> \<open>validity at the term model forces \<open>A \<in> H\<close>\<close>
  have "H.V.Ev \<xi> A = H.cls \<^bold>\<top>"
    using valid unfolding bkk_valid_def rel_truth_def using bm ra sat by blast
  hence AH: "A \<in> Hset ?\<Psi>" using H.truth_lemma[OF _ r] wA cA
    by (simp add: cwff_def)
  \<comment> \<open>but \<open>\<^bold>\<not>A \<in> \<Psi> \<subseteq> H\<close> --- contradiction with consistency of \<open>H\<close>\<close>
  have "\<^bold>\<not> A \<in> Hset ?\<Psi>" using Phi_sub_Hset[of ?\<Psi>] by auto
  thus False using H.Hset_notboth[OF wA AH] by simp
qed

text \<open>Soundness (BKK Theorem 7.3) and completeness (BKK Corollary 7.7) are statements about the
  @{emph \<open>same\<close>} class of models, so together they characterise derivability semantically: a
  sentence is derivable from \<open>\<Phi>\<close> exactly when it holds in every model of \<open>\<Phi>\<close> in the class
  \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> over the term carrier.\<close>

text \<open>The semantic characterisation of derivability from the empty hypothesis set
  (BKK Corollary 7.7 at \<open>\<Phi> = {}\<close>, combined with Theorem 7.3): a sentence is derivable
  iff it is valid in every \<open>\<Sigma>\<close>-model of the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (over the carrier of the
  term model; the general hypothesis-set form is @{thm [source] completeness}).  The
  soundness direction is @{thm [source] soundness_bkk}; the completeness direction only
  shrinks the quantification to the canonical models via the sublocale bridge.\<close>

theorem derivable_iff_valid:
  fixes A :: "'p::{countable,infinite} tm"
  assumes "cwff \<o> A"
  shows "\<turnstile> A \<longleftrightarrow> \<Turnstile>('p tm set) A"
  by (metis (mono_tags, lifting) assms bkk_valid_def completeness empty_iff fp0
            rel_truth_def soundness_bkk)

subsubsection \<open>Further derived Leibniz rules\<close>

text \<open>Leibniz modus ponens: transport a theorem along a proven Leibniz equation
  (via \<open>NK(\<beta>)\<close> and Leibniz substitution into the identity predicate).\<close>

lemma leib_mp:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B" and A: "\<Phi> \<turnstile> A" and fp: "freep \<Phi>"
      and wA: "wff\<^bsub>\<o>\<^esub>(A)" and wB: "wff\<^bsub>\<o>\<^esub>(B)"
    shows "\<Phi> \<turnstile> B"
proof -
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0) :: 'p tm"
  have wP: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)" by (rule wff_AbsI) (simp add: wff_Fre)
  have bA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> A" using beq.beta[OF wP wA] by simp
  have bB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> B" using beq.beta[OF wP wB] by simp
  have "\<Phi> \<turnstile> ?P \<^bold>\<cdot> A" by (rule bprov.Beta[OF beq.sym[OF bA] A])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> B" by (rule leib_subst[OF AB fp wA wB wP])
  thus ?thesis by (rule bprov.Beta[OF bB])
qed

text \<open>From Leibniz to primitive equality (BKK Remark 7.9; by Leibniz substitution
  into \<open>\<^bold>\<Lambda>x. A \<^bold>=\<^bsub>\<alpha>\<^esub> x\<close> from \<open>NK(=\<^sub>r)\<close>-reflexivity; the converse is the rule \<open>NK(=\<^sub>l)\<close>).\<close>

lemma leib_to_peq:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B" and fp: "freep \<Phi>"
      and wA: "wff\<^bsub>\<alpha>\<^esub>(A)" and wB: "wff\<^bsub>\<alpha>\<^esub>(B)"
    shows "\<Phi> \<turnstile> A \<^bold>=\<^bsub>\<alpha>\<^esub> B"
proof -
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (A \<^bold>=\<^bsub>\<alpha>\<^esub> Bnd 0)"
  have wP: "wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>(?P)"
    by (rule wff_AbsI) (auto simp: opn_lc[OF wff_lc[OF wA]] intro!:  wA wff_Fre)
  have bA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> (A \<^bold>=\<^bsub>\<alpha>\<^esub> A)"
    using beq.beta[OF wP wA] by (simp add: opn_lc[OF wff_lc[OF wA]])
  have bB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> (A \<^bold>=\<^bsub>\<alpha>\<^esub> B)"
    using beq.beta[OF wP wB] by (simp add: opn_lc[OF wff_lc[OF wA]])
  have "\<Phi> \<turnstile> A \<^bold>=\<^bsub>\<alpha>\<^esub> A" by (rule bprov.EqR[OF wA])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> A" by (rule bprov.Beta[OF beq.sym[OF bA]])
  hence "\<Phi> \<turnstile> ?P \<^bold>\<cdot> B" by (rule leib_subst[OF AB fp wA wB wP])
  thus ?thesis by (rule bprov.Beta[OF bB])
qed

text \<open>The diagonal contradiction: a proposition Leibniz-equal to its own negation
  refutes the context (by excluded middle and Leibniz modus ponens).\<close>

lemma leib_neg_contra:
  assumes E: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (\<^bold>\<not> A)" and fp: "freep \<Phi>" and wA: "wff\<^bsub>\<o>\<^esub>(A)"
  shows "\<Phi> \<turnstile> \<^bold>\<bottom>"
proof -
  have br1: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<bottom>"
  proof -
    have fp1: "freep (\<Phi> \<union> {\<^bold>\<not> A})" using freep_add[OF fp] by simp
    have hy: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<not> A" by (auto intro: bprov.Hyp)
    have e: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (\<^bold>\<not> A)"
      by (rule bprov_weaken[OF E _ fp1]) auto
    have "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> (\<^bold>\<not> A) \<^bold>\<doteq>\<^bsub>\<o>\<^esub> A"
      by (rule leib_sym[OF e fp1 wA wff_Not[OF wA]])
    hence "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> A"
      by (rule leib_mp[OF _ hy fp1 wff_Not[OF wA] wA])
    thus ?thesis by (rule bprov.NegE[OF hy _ wff_FalseB])
  qed
  have br2: "\<Phi> \<union> {A} \<turnstile> \<^bold>\<bottom>"
  proof -
    have fp2: "freep (\<Phi> \<union> {A})" using freep_add[OF fp] by simp
    have hy: "\<Phi> \<union> {A} \<turnstile> A" by (auto intro: bprov.Hyp)
    have e: "\<Phi> \<union> {A} \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (\<^bold>\<not> A)"
      by (rule bprov_weaken[OF E _ fp2]) auto
    have "\<Phi> \<union> {A} \<turnstile> \<^bold>\<not> A"
      by (rule leib_mp[OF e hy fp2 wA wff_Not[OF wA]])
    thus ?thesis by (rule bprov.NegE[OF _ hy wff_FalseB])
  qed
  show ?thesis
    by (rule bprov.DisE[OF bprov_em[OF wA] br1 br2 wff_Not[OF wA] wA])
qed

text \<open>Application of a primitive equation, and \<open>\<beta>\<close>-reduction on the right of \<open>\<^bold>\<doteq>\<close>.\<close>

lemma peq_app: "\<Phi> \<turnstile> C \<^bold>=\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<beta>\<^esub> D \<Longrightarrow> freep \<Phi> \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<beta>\<^esub>(C) \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<beta>\<^esub>(D)
    \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> (C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (D \<^bold>\<cdot> A)"
  by (rule leib_cong1[OF bprov.EqL])
lemma leib_reduce_right: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B \<Longrightarrow> B \<approx>\<^bsub>\<o>\<^esub> B' \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B'" 
  by (metis beq.appR bprov.Beta wff_App wff_Leib)

text \<open>The same three steps for @{emph \<open>primitive\<close>} equality (via \<open>NK(=\<^sub>l)\<close> in and
  \<open>leib_to_peq\<close> out): application to an argument, \<open>\<beta>\<close>-reduction on the right, and
  the diagonal contradiction \<open>A \<^bold>= \<^bold>\<not> A \<Longrightarrow> \<^bold>\<bottom>\<close>.\<close>
subsection \<open>Completeness at every signature and carrier\<close>

text \<open>This part strengthens the completeness theorem from the term-model carrier to
  @{emph \<open>arbitrary\<close>} infinite value carriers, by an explicit model-embedding
  construction: every \<open>\<Sigma>\<close>-model of the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> whose total domain embeds
  injectively into a carrier \<open>'u\<close> has an isomorphic copy on \<open>'u\<close>, and satisfaction is
  invariant under the embedding.  Since the term model has a countable total domain
  (the language is countable), it embeds into every infinite carrier, so validity
  over any infinite carrier suffices for derivability.  Completeness is then
  extended further, to open formulas and to signatures with infinitely
  many parameters, and the development closes with the main theorems stated in
  self-contained notation.\<close>

subsubsection \<open>A countermodel for every underivable sentence\<close>

text \<open>The completeness construction, packaged as an explicit countermodel: if a
  sentence is not derivable, the Hintikka term model refutes it.  The total domain
  of the term model is countable --- the domains are \<open>\<sim>\<close>-classes of closed wffs.\<close>

lemma refuting_term_model:
  fixes A :: "'p::{countable,infinite} tm"
  assumes c: "cwff \<o> A" and nd: "\<not>\<turnstile> A"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" and vl \<xi>
  where "bkk_model Dm Ap Ee vl" "countable {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<not> vl (Ee \<xi> A)"
proof -
  note wA = cwff_wff[OF c] and cA = cwff_closed[OF c]
  have con\<Psi>: "con {\<^bold>\<not> A}" using bprov.simps con_def nd wA by fastforce
  have fp\<Psi>: "freep {\<^bold>\<not> A}" by (intro freep_finite) simp
  interpret H: hintikka_model "{\<^bold>\<not> A}"
    by unfold_locales (rule con\<Psi> fp\<Psi>)+
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm set" where
    "\<xi> \<equiv> \<lambda>n \<tau>. H.cls (undefined\<^sup>p\<^bsub>\<tau>\<^esub>)"
  have r: "H.V.vresp \<xi>"
    by (auto simp: \<xi>_def H.V.vresp_def intro: H.Dm_cls cwff_Par)
  have ra: "app_struct.asg H.Dm \<xi>"
    using r by (simp add: H.V.bkkA.asg_def H.V.vresp_def)
  have bm: "bkk_model H.Dm H.Ap H.V.Ev (\<lambda>a. a = H.cls \<^bold>\<top>)"
    by intro_locales
  \<comment> \<open>the model refutes \<open>A\<close>: \<open>\<^bold>\<not>A \<in> H\<close>, so \<open>A \<notin> H\<close>, so the truth lemma denies \<open>A\<close>\<close>
  have "\<^bold>\<not>A \<in> Hset {\<^bold>\<not> A}" using Phi_sub_Hset[of "{\<^bold>\<not> A}"] by auto
  hence "A \<notin> Hset {\<^bold>\<not> A}" using H.Hset_notboth[OF wA] by blast
  hence ref: "H.V.Ev \<xi> A \<noteq> H.cls \<^bold>\<top>" using H.truth_lemma[OF c r] by simp
  \<comment> \<open>the total domain is contained in the countable range of \<open>cls\<close>\<close>
  have "{x. \<exists>\<tau>. H.Dm \<tau> x} \<subseteq> range H.cls" by (auto simp: H.Dm_def)
  hence cnt: "countable {x. \<exists>\<tau>. H.Dm \<tau> x}"
    by (rule countable_subset) simp
  show ?thesis by (rule that[OF bm cnt ra]) (use ref in simp)
qed

subsubsection \<open>Model embedding: satisfaction is carrier-independent\<close>

text \<open>A \<open>\<Sigma>\<close>-model over a carrier \<open>'v\<close> whose total domain maps injectively into a
  carrier \<open>'u\<close> has an isomorphic copy over \<open>'u\<close>; every refutation transfers.  All
  model conditions are pointwise, so the transfer needs no induction on terms.\<close>

lemma bkk_model_embed:
  fixes Dm :: "ty \<Rightarrow> 'v \<Rightarrow> bool" and i :: "'v \<Rightarrow> 'u"
    and A :: "'p tm"
  assumes M: "bkk_model Dm Ap Ee vl"
     and inj: "inj_on i {x. \<exists>\<tau>. Dm \<tau> x}"
     and wA: "wff\<^bsub>\<o>\<^esub>(A)"
     and xi: "app_struct.asg Dm \<xi>" and nA: "\<not> vl (Ee \<xi> A)"
  obtains Dm' Ap' and Ee' :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl' \<xi>'
  where "bkk_model Dm' Ap' Ee' vl'" "app_struct.asg Dm' \<xi>'" "\<not> vl' (Ee' \<xi>' A)"
proof -
  interpret M: bkk_model Dm Ap Ee vl by (rule M)
  define D where "D = {x. \<exists>\<tau>. Dm \<tau> x}"
  have DmD: "Dm \<tau> x \<Longrightarrow> x \<in> D" for \<tau> x by (auto simp: D_def)
  have iinj: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> i x = i y \<Longrightarrow> x = y" for x y
    using inj by (auto simp: D_def inj_on_def)
  define bk where "bk = (\<lambda>u. SOME x. x \<in> D \<and> i x = u)"
  have cancel: "x \<in> D \<Longrightarrow> bk (i x) = x" for x
    unfolding bk_def by (rule some_equality) (auto intro: iinj)
  define Dm' where "Dm' = (\<lambda>\<tau> u. \<exists>x. Dm \<tau> x \<and> u = i x)"
  have Dm'I: "Dm \<tau> x \<Longrightarrow> Dm' \<tau> (i x)" for \<tau> x by (auto simp: Dm'_def)
  define pull :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 'v" where
    "pull \<equiv> \<lambda>\<xi>' n \<tau>. if \<exists>x. Dm \<tau> x \<and> i x = \<xi>' n \<tau>
                     then SOME x. Dm \<tau> x \<and> i x = \<xi>' n \<tau>
                     else SOME x. Dm \<tau> x"
  have pull_asg: "M.asg (pull \<xi>')" for \<xi>'
    unfolding M.asg_def pull_def
    by (auto intro: someI_ex M.as_nonempty someI2_ex)
  have pull_agree: "Dm' \<tau> (\<xi>' n \<tau>) \<Longrightarrow> i (pull \<xi>' n \<tau>) = \<xi>' n \<tau>"
    for \<xi>' n \<tau>
    unfolding pull_def Dm'_def by (auto intro: someI2_ex)
  have pull_push: "pull (\<lambda>n \<tau>. i (\<xi> n \<tau>)) = \<xi>"
  proof (intro ext)
    fix n \<tau>
    have d: "Dm \<tau> (\<xi> n \<tau>)" using xi by (simp add: M.asg_def)
    have "\<exists>x. Dm \<tau> x \<and> i x = i (\<xi> n \<tau>)" using d by blast
    moreover have "\<And>x. Dm \<tau> x \<Longrightarrow> i x = i (\<xi> n \<tau>) \<Longrightarrow> x = \<xi> n \<tau>"
      by (auto intro: iinj DmD d)
    ultimately show "pull (\<lambda>n \<tau>. i (\<xi> n \<tau>)) n \<tau> = \<xi> n \<tau>"
      unfolding pull_def by auto
  qed
  define Ap' where "Ap' \<equiv> \<lambda>u v. i (Ap (bk u) (bk v))"
  define Ee' where "Ee' \<equiv> \<lambda>\<xi>' B. i (Ee (pull \<xi>') B)"
  define vl' where "vl' \<equiv> \<lambda>u. vl (bk u)"
  have Ap'I: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> Ap' (i x) (i y) = i (Ap x y)" for x y
    by (simp add: Ap'_def cancel)
  have vl'I: "x \<in> D \<Longrightarrow> vl' (i x) \<longleftrightarrow> vl x" for x
    by (simp add: vl'_def cancel)
  have EeD: "wff\<^bsub>\<tau>\<^esub>(B) \<Longrightarrow> Ee (pull \<xi>') B \<in> D" for \<tau> B \<xi>'
    by (auto intro: DmD M.ev_type[OF _ pull_asg])
  have ApD: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f \<Longrightarrow> Dm \<alpha> a \<Longrightarrow> Ap f a \<in> D" for \<alpha> \<beta> f a
    by (auto intro: DmD M.as_appTy)
\<comment> \<open>the image is an applicative structure; interpreting it makes the specialised \<open>asg\<close> equation
    available\<close>
  have AS': "app_struct Dm' Ap'"
  proof (unfold_locales, goal_cases)
    case (1 \<alpha>) show ?case using M.as_nonempty Dm'I by (metis Dm'_def)
  next
    case (2 \<alpha> \<beta> f a) thus ?case
      by (auto simp: Dm'_def Ap'I DmD intro: M.as_appTy)
  qed
  interpret A': app_struct Dm' Ap' by (rule AS')
  \<comment> \<open>the image is a model: every condition transfers pointwise\<close>
  have BM: "bkk_model Dm' Ap' Ee' vl'"
  proof (unfold_locales, goal_cases)
    case 1 thus ?case
      by (auto simp: Ee'_def intro: Dm'I M.ev_type[OF _ pull_asg])
  next
    case (2 \<xi>' n \<sigma>)
    hence "Dm' \<sigma> (\<xi>' n \<sigma>)" by (simp add: A'.asg_def)
    thus ?case by (simp add: Ee'_def M.ev_var[OF pull_asg] pull_agree)
  next
    case 3 thus ?case
      by (simp add: Ee'_def M.ev_app[OF _ _ pull_asg]
          Ap'I[OF EeD EeD])
  next
    case (4 \<tau> B \<xi>' \<xi>'')
    have "pull \<xi>' n \<sigma> = pull \<xi>'' n \<sigma>" if "(n, \<sigma>) \<in> occ B" for n \<sigma>
      using 4(4)[OF that] by (auto simp: pull_def)
    thus ?case unfolding Ee'_def
      by (intro arg_cong[of _ _ i] M.ev_coin[OF 4(1) pull_asg pull_asg])
  next
    case 5 thus ?case
      by (simp add: Ee'_def M.ev_beta[OF _ pull_asg])
  next
    case (6 \<xi>' a')
    then obtain a where a: "Dm \<o> a" "a' = i a" by (auto simp: Dm'_def)
    have "vl' (Ap' (Ee' \<xi>' Neg) a') = vl (Ap (Ee (pull \<xi>') Neg) a)"
      by (simp add: a Ee'_def Ap'I[OF EeD[OF wff_Neg] DmD[OF a(1)]]
          vl'I[OF ApD[OF M.ev_type[OF wff_Neg pull_asg] a(1)]])
    thus ?case
      by (simp add: a M.vl_neg[OF pull_asg a(1)] vl'I[OF DmD[OF a(1)]])
  next
    case (7 \<xi>' a' b')
    then obtain a b where ab: "Dm \<o> a" "a' = i a" "Dm \<o> b" "b' = i b"
      by (auto simp: Dm'_def)
    have dsD: "Ap (Ee (pull \<xi>') Dis) a \<in> D"
      by (rule ApD[OF M.ev_type[OF wff_Dis pull_asg] ab(1)])
    have ds2: "Dm (\<o> \<^bold>\<Rightarrow> \<o>) (Ap (Ee (pull \<xi>') Dis) a)"
      by (rule M.as_appTy[OF M.ev_type[OF wff_Dis pull_asg] ab(1)])
    have "vl' (Ap' (Ap' (Ee' \<xi>' Dis) a') b')
            = vl (Ap (Ap (Ee (pull \<xi>') Dis) a) b)"
      by (simp add: ab Ee'_def Ap'I[OF EeD[OF wff_Dis] DmD[OF ab(1)]]
          Ap'I[OF dsD DmD[OF ab(3)]] vl'I[OF ApD[OF ds2 ab(3)]])
    thus ?case
      by (simp add: ab M.vl_dis[OF pull_asg ab(1) ab(3)]
          vl'I[OF DmD[OF ab(1)]] vl'I[OF DmD[OF ab(3)]])
  next
    case (8 \<xi>' \<sigma> f')
    then obtain f where f: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f" "f' = i f"
        by (auto simp: Dm'_def)
    have piD: "Dm ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>) (Ee (pull \<xi>') (Pi \<sigma>))"
      by (rule M.ev_type[OF wff_Pi pull_asg])
    have l: "vl' (Ap' (Ee' \<xi>' (Pi \<sigma>)) f')
               = vl (Ap (Ee (pull \<xi>') (Pi \<sigma>)) f)"
      by (simp add: f Ee'_def Ap'I[OF EeD[OF wff_Pi] DmD[OF f(1)]]
          vl'I[OF ApD[OF piD f(1)]])
    have r: "(\<forall>d'. Dm' \<sigma> d' \<longrightarrow> vl' (Ap' f' d'))
               = (\<forall>d. Dm \<sigma> d \<longrightarrow> vl (Ap f d))"
      by (auto simp: Dm'_def f Ap'I[OF DmD[OF f(1)] DmD]
          vl'I[OF ApD[OF f(1)]])
    show ?case using l r M.vl_pi[OF pull_asg f(1)] by simp
  next
    case (9 \<xi>' \<sigma> a' b')
    then obtain a b where ab: "Dm \<sigma> a" "a' = i a" "Dm \<sigma> b" "b' = i b"
      by (auto simp: Dm'_def)
    have eqD: "Ap (Ee (pull \<xi>') (Eq \<sigma>)) a \<in> D"
      by (rule ApD[OF M.ev_type[OF wff_Eq pull_asg] ab(1)])
    have eq2: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) (Ap (Ee (pull \<xi>') (Eq \<sigma>)) a)"
      by (rule M.as_appTy[OF M.ev_type[OF wff_Eq pull_asg] ab(1)])
    have "vl' (Ap' (Ap' (Ee' \<xi>' (Eq \<sigma>)) a') b')
            = vl (Ap (Ap (Ee (pull \<xi>') (Eq \<sigma>)) a) b)"
      by (simp add: ab Ee'_def Ap'I[OF EeD[OF wff_Eq] DmD[OF ab(1)]]
          Ap'I[OF eqD DmD[OF ab(3)]] vl'I[OF ApD[OF eq2 ab(3)]])
    thus ?case
      using M.vl_eq[OF pull_asg ab(1) ab(3)] iinj[OF DmD DmD] ab
      by (auto simp: DmD)
  next
    case (10 \<xi>' \<sigma> f' a')
    then obtain f a where fa: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f" "f' = i f" "Dm \<sigma> a" "a' = i a"
      by (auto simp: Dm'_def)
    have sing: "vl (Ap f b) \<longleftrightarrow> b = a" if b: "Dm \<sigma> b" for b
    proof -
      have "vl' (Ap' f' (i b)) \<longleftrightarrow> i b = a'"
        using 10(4)[OF Dm'I[OF b]] by simp
      thus ?thesis
        using b fa iinj[OF DmD DmD]
        by (auto simp: Ap'I[OF DmD[OF fa(1)] DmD[OF b]]
            vl'I[OF ApD[OF fa(1) b]] DmD)
    qed
    have "Ap (Ee (pull \<xi>') (Iota \<sigma>)) f = a"
      by (rule M.vl_iota[OF pull_asg fa(1) fa(3)]) (rule sing)
    thus ?case
      by (simp add: fa Ee'_def Ap'I[OF EeD[OF wff_Iota] DmD[OF fa(1)]])
  next
    case 11
    show ?case
      unfolding A'.functional_def
    proof (intro allI impI)
      fix \<alpha> \<beta> f' g'
      assume f': "Dm' (\<alpha> \<^bold>\<Rightarrow> \<beta>) f'" and g': "Dm' (\<alpha> \<^bold>\<Rightarrow> \<beta>) g'"
        and agree: "\<forall>a'. Dm' \<alpha> a' \<longrightarrow> Ap' f' a' = Ap' g' a'"
      obtain f g where fg: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f" "f' = i f" "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) g" "g' = i g"
        using f' g' by (auto simp: Dm'_def)
      have "Ap f a = Ap g a" if a: "Dm \<alpha> a" for a
      proof -
        have "i (Ap f a) = i (Ap g a)"
          using agree[THEN spec, of "i a"] Dm'I[OF a]
          by (simp add: fg Ap'I[OF DmD[OF fg(1)] DmD[OF a]]
              Ap'I[OF DmD[OF fg(3)] DmD[OF a]])
        thus ?thesis by (rule iinj[OF ApD ApD, OF fg(1) a fg(3) a])
      qed
      hence "f = g"
        using M.prop_f fg unfolding M.functional_def by blast
      thus "f' = g'" by (simp add: fg)
    qed
  next
    case (12 a' b')
    then obtain a b where ab: "Dm \<o> a" "a' = i a" "Dm \<o> b" "b' = i b"
      by (auto simp: Dm'_def)
    thus ?case
      using 12(3) M.prop_b[OF ab(1) ab(3)] vl'I[OF DmD[OF ab(1)]]
        vl'I[OF DmD[OF ab(3)]] by simp
  qed
  \<comment> \<open>the pushed assignment refutes \<open>A\<close> in the image model\<close>
  define \<xi>' where "\<xi>' \<equiv> \<lambda>n \<tau>. i (\<xi> n \<tau>)"
  have asg': "app_struct.asg Dm' \<xi>'"
    using xi unfolding M.asg_def \<xi>'_def A'.asg_def
    by (auto intro: Dm'I)
  have "Ee' \<xi>' A = i (Ee \<xi> A)" by (simp add: Ee'_def \<xi>'_def pull_push)
  hence "\<not> vl' (Ee' \<xi>' A)"
    using nA vl'I[OF DmD[OF M.ev_type[OF wA xi]]] by simp
  thus ?thesis using BM asg' that by simp
qed

subsubsection \<open>Completeness at every infinite carrier\<close>

text \<open>The strengthened form of BKK Corollary 7.7: validity over the models of
  \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> at @{emph \<open>any\<close>} infinite value carrier implies derivability.  The term
  carrier plays no special role: it only needs to embed into the given carrier,
  which its countability guarantees.\<close>

theorem completeness_at_any_carrier:
  fixes A :: "'p::{countable,infinite} tm"
  assumes c: "cwff \<o> A"
    and valid: "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
proof (rule ccontr)
  assume nd: "\<not>\<turnstile> A"
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" and vl \<xi>
    where M: "bkk_model Dm Ap Ee vl" and cnt: "countable {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and nA: "\<not> vl (Ee \<xi> A)"
    by (rule refuting_term_model[OF c nd])
  \<comment> \<open>embed the countable total domain into the infinite carrier \<open>'u\<close>\<close>
  obtain f :: "'p tm set \<Rightarrow> nat" where f: "inj_on f {x. \<exists>\<tau>. Dm \<tau> x}"
    using cnt by (auto simp: countable_def)
  obtain g :: "nat \<Rightarrow> 'u" where g: "inj g"
    using infinite_UNIV infinite_countable_subset by blast
  have inj: "inj_on (g \<circ> f) {x. \<exists>\<tau>. Dm \<tau> x}"
    using f g by (rule comp_inj_on[OF _ inj_on_subset]) auto
  obtain Dm' Ap' and Ee' :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl' \<xi>'
    where "bkk_model Dm' Ap' Ee' vl'" "app_struct.asg Dm' \<xi>'" "\<not> vl' (Ee' \<xi>' A)"
    using bkk_model_embed M inj cwff_wff[OF c] xi nA by blast
  thus False using valid unfolding bkk_valid_def rel_truth_def by blast
qed

subsubsection \<open>Completeness for open formulas\<close>

text \<open>Completeness does not require closed sentences: assignments interpret the free
  variables.  The bridge is a substitution-value law for @{emph \<open>abstract\<close>}
  \<open>\<Sigma>\<close>-evaluations (the abstract form of BKK Lemma 3.20, one variable at a time),
  proved without any term induction: substitution is expressed through closing,
  \<open>\<beta>\<close>-conversion and the evaluation conditions.  On the syntactic side a free
  variable is generalised through a fresh parameter by the rule chain
  \<open>NK(\<beta>)\<close>--\<open>NK(\<Pi>I)\<close>--\<open>NK(\<Pi>E)\<close>--\<open>NK(\<beta>)\<close>.\<close>

lemma opn_clos_sub: "opn k v t = t \<Longrightarrow> opn k v (clos k x \<sigma> t) = fsub x \<sigma> v t"
  by (induction t arbitrary: k) auto

lemma fsub_id: "fsub x \<sigma> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t = t"
  by (induction t) auto

lemma occ_clos: "(x, \<sigma>) \<notin> occ (clos k x \<sigma> t)"
  by (induction t arbitrary: k) auto

lemma pars_clos [simp]: "pars (clos k x \<sigma> t) = pars t"
  by (induction t arbitrary: k) auto

lemma finite_occ: "finite (occ t)"
  by (induction t) auto

lemma occ_fsub_closed: "occ u = {} \<Longrightarrow> occ (fsub x \<sigma> u t) = occ t - {(x, \<sigma>)}"
  by (induction t) auto

text \<open>The sharpened \<open>\<beta>\<close>-application law: the fresh-name condition only concerns the
  typed occurrence \<open>(x, \<sigma>)\<close>, not the bare name (a name may occur at several types).\<close>

lemma (in sigma_eval) ev_abs_app_occ:
  assumes wb: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and xi: "asg \<xi>"
    and x: "(x, \<sigma>) \<notin> occ b" and d: "Dm \<sigma> d"
  shows "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
proof -
  have xi': "asg (\<xi>(x\<^bsub>\<sigma>\<^esub> := d))" by (rule asg_upd[OF xi d])
  have "Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    by (rule ev_beta[OF beq.sym[OF beq.beta[OF wb wff_Fre]] xi'])
  also have "\<dots> = Ap (Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) (Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    by (rule ev_app[OF wb wff_Fre xi'])
  also have "\<dots> = Ap (Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d"
    using ev_var[OF xi', of x \<sigma>] by (simp add: upd_def)
  also have "\<dots> = Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d"
    using x by (intro arg_cong2[of _ _ d d Ap] refl
        ev_coin[OF wb xi' xi]) (auto simp: upd_def)
  finally show ?thesis ..
qed

text \<open>The substitution-value law for abstract \<open>\<Sigma>\<close>-evaluations (BKK Lemma 3.20 for a
  single free variable): substituting @{emph \<open>any\<close>} well-formed term equals updating
  the assignment with its value.\<close>

lemma (in sigma_eval) ev_fsub_one:
  assumes wA: "wff\<^bsub>\<tau>\<^esub>(A)" and wu: "wff\<^bsub>\<sigma>\<^esub>(u)" and xi: "asg \<xi>"
  shows "Ee \<xi> (fsub x \<sigma> u A) = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> u)) A"
proof -
  have opnA: "opn 0 v A = A" for v by (simp add: wff_lc[OF wA])
  let ?B = "clos 0 x \<sigma> A"
  have wAbs: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)"
    by (rule wff_AbsI) (simp add: opn_clos_sub[OF opnA] wff_fsub[OF wA
        wff_Fre])
  have du: "Dm \<sigma> (Ee \<xi> u)" by (rule ev_type[OF wu xi])
  have "Ee \<xi> (fsub x \<sigma> u A) = Ee \<xi> ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> u)"
    unfolding opn_clos_sub[OF opnA, symmetric]
    by (rule ev_beta[OF beq.sym[OF beq.beta[OF wAbs wu]] xi])
  also have "\<dots> = Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)) (Ee \<xi> u)"
    by (rule ev_app[OF wAbs wu xi])
  also have "\<dots> = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> u)) (?B\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    by (rule ev_abs_app_occ[OF wAbs xi occ_clos du])
  also have "?B\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> = A"
    by (simp add: opn_clos_sub[OF opnA] fsub_id)
  finally show ?thesis .
qed

text \<open>Syntactic generalisation: a fresh parameter substituted for a free variable can
  be quantified away and re-instantiated, recovering the open formula.\<close>

lemma bprov_generalize_par:
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and p: "p \<notin> pars A"
    and d: "\<turnstile> fsub x \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>) A"
  shows "\<turnstile> A"
proof -
  have opnA: "opn 0 v A = A" for v :: "'a tm"
    by (simp add: wff_lc[OF wA])
  let ?B = "clos 0 x \<sigma> A"
  have wAbs: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)"
    by (rule wff_AbsI)
       (simp add: opn_clos_sub[OF opnA] wff_fsub[OF wA wff_Fre])
  have bq1: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> (p\<^sup>p\<^bsub>\<sigma>\<^esub>) \<approx>\<^bsub>\<o>\<^esub> fsub x \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>) A"
    using beq.beta[OF wAbs wff_Par] by (simp add: opn_clos_sub[OF opnA])
  have h2: "{} \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> (p\<^sup>p\<^bsub>\<sigma>\<^esub>)"
    by (rule bprov.Beta[OF beq.sym[OF bq1] d])
  have h3: "{} \<turnstile> (Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)"
    by (rule bprov.PiI[OF h2 wAbs]) (use p in auto)
  have h4: "{} \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>)"
    by (rule bprov.PiE[OF h3 wff_Fre])
  have bq2: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) \<approx>\<^bsub>\<o>\<^esub> A"
  proof -
    have "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) \<approx>\<^bsub>\<o>\<^esub> ?B\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>"
      by (rule beq.beta[OF wAbs wff_Fre])
    thus ?thesis by (simp add: opn_clos_sub[OF opnA] fsub_id)
  qed
  show ?thesis by (rule bprov.Beta[OF bq2 h4])
qed

text \<open>Completeness for arbitrary (locally closed) well-formed formulas, by induction
  on the number of typed free occurrences: each occurrence is generalised through a
  fresh parameter, semantically justified by the substitution-value law.\<close>

lemma completeness_open_aux:
  fixes A :: "'p::{countable,infinite} tm"
  shows "card (occ A) \<le> n \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> (\<Turnstile>('p tm set) A) \<Longrightarrow> \<turnstile> A"
proof (induction n arbitrary: A)
  case (0 A)
  hence "occ A = {}" by (simp add: finite_occ card_eq_0_iff)
  hence "cwff \<o> A" using 0(2) by (simp add: cwff_def fvs_eq_fst_occ)
  thus ?case using derivable_iff_valid 0(3) by blast
next
  case (Suc n A)
  show ?case
  proof (cases "occ A = {}")
    case True
    hence "cwff \<o> A"
      using Suc.prems(2) by (simp add: cwff_def fvs_eq_fst_occ)
    thus ?thesis using derivable_iff_valid Suc.prems(3) by blast
  next
    case False
    then obtain x \<sigma> where xs: "(x, \<sigma>) \<in> occ A" by auto
    obtain p :: 'p where p: "p \<notin> pars A"
      by (meson ex_new_if_finite finite_pars infinite_UNIV)
    define A1 where "A1 = fsub x \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>) A"
    have wA1: "wff\<^bsub>\<o>\<^esub>(A1)"
      unfolding A1_def by (rule wff_fsub[OF Suc.prems(2) wff_Par])
    have occ1: "occ A1 = occ A - {(x, \<sigma>)}"
      unfolding A1_def by (rule occ_fsub_closed) simp
    have card1: "card (occ A1) \<le> n"
      using Suc.prems(1) xs finite_occ
      by (simp add: occ1 card_Diff_singleton)
    have valid1: "\<Turnstile>('p tm set) A1"
      unfolding bkk_valid_def rel_truth_def
    proof (intro allI impI)
      fix Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
        and vl :: "'p tm set \<Rightarrow> bool" and \<xi>
      assume bm: "bkk_model Dm Ap Ee vl" and xi: "app_struct.asg Dm \<xi>"
      interpret M: bkk_model Dm Ap Ee vl by (rule bm)
      have eq: "Ee \<xi> A1 = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> (p\<^sup>p\<^bsub>\<sigma>\<^esub>))) A"
        unfolding A1_def
        by (rule M.ev_fsub_one[OF Suc.prems(2) wff_Par xi])
      have asg': "app_struct.asg Dm (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> (p\<^sup>p\<^bsub>\<sigma>\<^esub>)))"
        by (rule M.asg_upd[OF xi M.ev_type[OF wff_Par xi]])
      have v: "\<forall>\<xi>. app_struct.asg Dm \<xi> \<longrightarrow> vl (Ee \<xi> A)"
        using Suc.prems(3) bm unfolding bkk_valid_def rel_truth_def by blast
      show "vl (Ee \<xi> A1)" using v[rule_format, OF asg']
          by (simp add: eq)
    qed
    have "\<turnstile> A1" by (rule Suc.IH[OF card1 wA1 valid1])
    thus ?thesis
      unfolding A1_def
      by (rule bprov_generalize_par[OF Suc.prems(2) p, of x \<sigma>])
  qed
qed

theorem completeness_open:
  fixes A :: "'p::{countable,infinite} tm"
  assumes "wff\<^bsub>\<o>\<^esub>(A)"
      and "\<Turnstile>('p tm set) A"
    shows "\<turnstile> A"
  using assms(1,2) completeness_open_aux by blast

lemma completeness_open_any_aux:
  fixes A :: "'p::{countable,infinite} tm"
  shows "card (occ A) \<le> n \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> \<Turnstile>('u::infinite) A \<Longrightarrow> \<turnstile> A"
proof (induction n arbitrary: A)
  case (0 A)
  hence "occ A = {}" by (simp add: finite_occ card_eq_0_iff)
  hence "cwff \<o> A" using 0(2) by (simp add: cwff_def fvs_eq_fst_occ)
  thus ?case using completeness_at_any_carrier 0(3) by blast
next
  case (Suc n A)
  show ?case
  proof (cases "occ A = {}")
    case True
    hence "cwff \<o> A"
      using Suc.prems(2) by (simp add: cwff_def fvs_eq_fst_occ)
    thus ?thesis using completeness_at_any_carrier Suc.prems(3) by blast
  next
    case False
    then obtain x \<sigma> where xs: "(x, \<sigma>) \<in> occ A" by auto
    obtain p :: 'p where p: "p \<notin> pars A"
      by (meson ex_new_if_finite finite_pars infinite_UNIV)
    define A1 where "A1 = fsub x \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>) A"
    have wA1: "wff\<^bsub>\<o>\<^esub>(A1)"
      unfolding A1_def by (rule wff_fsub[OF Suc.prems(2) wff_Par])
    have occ1: "occ A1 = occ A - {(x, \<sigma>)}"
      unfolding A1_def by (rule occ_fsub_closed) simp
    have card1: "card (occ A1) \<le> n"
      using Suc.prems(1) xs finite_occ
      by (simp add: occ1 card_Diff_singleton)
    have valid1: "\<Turnstile>('u) A1"
      unfolding bkk_valid_def rel_truth_def
    proof (intro allI impI)
      fix Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap
        and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl \<xi>
      assume bm: "bkk_model Dm Ap Ee vl" and xi: "app_struct.asg Dm \<xi>"
      interpret M: bkk_model Dm Ap Ee vl by (rule bm)
      have eq: "Ee \<xi> A1 = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> (p\<^sup>p\<^bsub>\<sigma>\<^esub>))) A"
        unfolding A1_def
        by (rule M.ev_fsub_one[OF Suc.prems(2) wff_Par xi])
      have asg': "app_struct.asg Dm (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> (p\<^sup>p\<^bsub>\<sigma>\<^esub>)))"
        by (rule M.asg_upd[OF xi M.ev_type[OF wff_Par xi]])
      have v: "\<forall>\<xi>. app_struct.asg Dm \<xi> \<longrightarrow> vl (Ee \<xi> A)"
        using Suc.prems(3) bm unfolding bkk_valid_def rel_truth_def by blast
      show "vl (Ee \<xi> A1)" using v[rule_format, OF asg']
        by (simp add: eq)
    qed
    have "\<turnstile> A1" by (rule Suc.IH[OF card1 wA1 valid1])
    thus ?thesis unfolding A1_def
      by (rule bprov_generalize_par[OF Suc.prems(2) p, of x \<sigma>])
  qed
qed

theorem completeness_open_at_any_carrier:
  fixes A :: "'p::{countable,infinite} tm"
  assumes "wff\<^bsub>\<o>\<^esub>(A)"
      and "\<Turnstile>('u::infinite) A"
    shows "\<turnstile> A"
  using completeness_open_any_aux assms by auto

subsubsection \<open>Signature transport\<close>

text \<open>On the semantic side, maps of parameter names need @{emph \<open>no\<close>} injectivity:
  any \<open>h :: 'p \<Rightarrow> 'q\<close> turns a model for \<open>'q\<close> into a model for \<open>'p\<close> by
  evaluating through \<open>prn h\<close> --- the value conditions \<open>vl\<^sub>\<not>, \<dots>, vl\<^sub>\<iota>\<close> only
  inspect \<open>Ee\<close> at the logical constants, which \<open>prn\<close> fixes.\<close>

lemma prn_occ [simp]: "occ (prn f t) = occ t"
  by (induction t) auto

lemma bkk_model_reduct:
  fixes Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'q tm \<Rightarrow> 'u" and h :: "'p \<Rightarrow> 'q"
  assumes "bkk_model Dm Ap Ee vl"
  shows "bkk_model Dm Ap (\<lambda>\<xi> t. Ee \<xi> (prn h t)) vl"
proof -
  interpret bkk_model Dm Ap Ee vl by (rule assms)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 3 thus ?case using ev_app by fastforce
    next case 4 thus ?case by (metis ev_coin prn_occ wff_prn)
    next case 5 thus ?case using ev_beta by blast
  qed(auto simp: vl_eq vl_pi vl_dis vl_neg vl_iota ev_var ev_type wff_prn prop_f prop_b)
qed

lemma bkk_valid_map:
  fixes h :: "'p \<Rightarrow> 'q"
  assumes v: "\<Turnstile>('u) (A :: 'p tm)"
    shows "\<Turnstile>('u) (prn h A :: 'q tm)"
  unfolding bkk_valid_def rel_truth_def
  by (metis bkk_model_reduct bkk_valid_def rel_truth_def v)

text \<open>Completeness for every signature with infinitely many parameters: the
  finitely many parameters of \<open>A\<close> are relocated into a copy of \<open>\<nat>\<close> inside \<open>'p\<close>,
  completeness over \<open>\<nat>\<close> applies, and \<open>bprov_rename\<close> transports the derivation back.
  (With only finitely many parameters this route is barred: \<open>NK(\<Pi>I)\<close> consumes fresh
  eigen-parameters, and an injection \<open>\<nat> \<Rightarrow> 'p\<close> is exactly what supplies them.)\<close>

theorem completeness_at_any_signature:
  fixes A :: "'p::infinite tm"
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and v: "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
proof -
  obtain g0 :: "nat \<Rightarrow> 'p" where g0: "inj g0"
    using infinite_UNIV infinite_countable_subset by blast
  define B where "B = pars A \<union> range g0"
  have "inj_on (inv g0) (range g0)" by (rule inj_on_inv_into) simp
  hence rc: "countable (range g0)" by (rule countableI)
  have ri: "infinite (range g0)"
    using finite_imageD[of g0 UNIV] g0 infinite_UNIV_nat by auto
  have cB: "countable B" and iB: "infinite B"
    unfolding B_def using rc ri by (auto intro: countable_finite)
  define g where "g = from_nat_into B"
  have g: "inj g" and cover: "pars A \<subseteq> range g"
    using bij_betw_from_nat_into[OF cB iB]
    unfolding g_def bij_betw_def B_def by auto
  define h :: "'p \<Rightarrow> nat" where "h = (\<lambda>p. SOME n. g n = p)"
  have gh: "g (h p) = p" if "p \<in> pars A" for p
  proof -
    from cover that obtain n where n: "g n = p" by auto
    from someI[of "\<lambda>n. g n = p", OF n] show ?thesis by (simp add: h_def)
  qed
  have wN: "wff\<^bsub>\<o>\<^esub>(prn h A)" by (rule wff_prn[OF wA])
  have dN: "\<turnstile> (prn h A :: nat tm)"
    using bkk_valid_map completeness_open_at_any_carrier v wN by blast
  have "\<turnstile> (prn g (prn h A) :: 'p tm)"
    using bprov_rename dN g by fastforce
  moreover have "prn g (prn h A) = A"
    by (simp add: gh prn_cong prn_prn)
  ultimately show ?thesis by simp
qed

end
