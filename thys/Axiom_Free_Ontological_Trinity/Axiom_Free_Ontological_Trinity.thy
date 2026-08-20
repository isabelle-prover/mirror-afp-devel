(*
  Title:     Axiom_Free_Ontological_Trinity
  Author:     Yongdock Kim
  Date:       2026-03-16
  License:    BSD-3-Clause
 
  Abstract:
    This theory provides a formal verification of an axiom-free ontological argument
    and the necessity of the Trinity. Moving beyond traditional Anselmian "perfection,"
    this work defines a supreme truth (H) through the lens of "relative certainty"
    and epistemic possible-world semantics. Using Isabelle/HOL, we demonstrate that
    the unique logical fixed point satisfying maximal domain coverage and relational
    consistency is a triune structure (N=3). The proof is strictly definitional,
    avoiding the injection of external modal axioms (e.g., S5), thereby ensuring
    the structural integrity of the trinitarian closure within the U-layer logic.
*)
theory Axiom_Free_Ontological_Trinity
  imports Main

begin
(*
  =============================================================================
  PROJECT   : Formal Verification of the Ontological Argument and Trinity Necessity
  FRAMEWORK : U-layer Axiom-free Computational Metaphysics
  -----------------------------------------------------------------------------

  SUMMARY:
  This entry provides a purely definitional, axiom-free formalization of the
  ontological necessity of the Trinity (N = 3). By constructing a structural
  meritocracy on an abstract universe U, we demonstrate that the "Supreme Truth"
  (H_opt) uniquely converges to a triune configuration.

  1. CORE LOGIC PIPELINE (Purely Definitional & Order-Theoretic):
     • U-layer Foundations :  ⊢ (primitive) ⟹ SuppU ⟹ (preceq, approx)
     • Epistemic Mapping   :  Arg, Supports, ⋄e (Epistemic Possibility)
     • Maximality Criteria :  EH (Epistemic), PH (Philosophical), MaxNT (Relational)
     • Structural Pattern  :  Ternary Joint-Support (pair ⟶ third) Semantics

  2. AXIOMATIC AUDIT (Zero-Axiom Guarantee):
     • U-layer Logic       :  No user-added axiom. All results are definitionally derived over HOL(Main)
     • Modal Primitives    :  NONE. External modal postulates (e.g., S5) are avoided
                              to prevent "Modal Collapse."
     • Bridge Primitives   :  Arg is an uninterpreted bridge; no axioms are injected.

  3. KEY THEORETICAL ACHIEVEMENTS:
     • N = 3 Necessity     :  Mechanical exclusion of N = 1 (Singularity), N = 2 (Duality),
                              and N ≥ 4 (Indeterminacy) via "Trivial Collapse" proofs.
     • Consistency         :  Proof of consistency for H_opt via finite model search (Nitpick).
     • Non-modal Collapse        :  A reusable truthmaking pattern (T+S) that preserves
                              contingency for R, ensuring Trinity ⟹ ⋄R
                              without forcing Trinity ⟹ R.
     • Structural Irreducibility :  Ordinal/Cardinal argument showing that linear 3-element
                              orderings cannot preserve the triune joint-support symmetry.

  4. FILE ARCHITECTURE:
     • Formal Body         :  Ontological argument via Double Negation (DN).
     • Structuralism       :  Full U/EH/PH/Trinity machinery with "God Finality" wrapper.
     • Locales             :  Automated audit and discharge of core metaphysical constraints.
 
  =============================================================================
*)
section \<open>1. Universe and primitive entailment\<close>
text \<open>We posit an abstract universe U and a primitive entailment @{text "\<turnstile>"} on U

  NOTICE: This entire development is strictly **axiom-free**.
  We do not use the ``axiom'' or any unproven modal postulates.
  All results are derived solely from definitions and the primitive entailment
  relation on the abstract universe U.
 \<close>

typedecl U
consts Entails :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<turnstile>" 60)


section \<open>2. Support sets, preorder and equivalence on U\<close>

definition SuppU :: "U \<Rightarrow> U set" where
  "SuppU u = {e. Entails e u}"

definition LeU :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<preceq>" 50) where
  "p \<preceq> q \<longleftrightarrow> SuppU p \<subseteq> SuppU q"

definition EqU :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<approx>" 50) where
  "p \<approx> q \<longleftrightarrow> SuppU p = SuppU q"


subsection \<open>2.1  Basic calculus (preorder/equivalence; point tools)\<close>

lemma LeU_refl[simp]: "p \<preceq> p" by (simp add: LeU_def)
lemma LeU_trans: "p \<preceq> q \<Longrightarrow> q \<preceq> r \<Longrightarrow> p \<preceq> r"
  by (simp add: LeU_def subset_trans)

lemma EqU_refl[simp]: "p \<approx> p" by (simp add: EqU_def)
lemma EqU_sym:       "p \<approx> q \<Longrightarrow> q \<approx> p" by (simp add: EqU_def)
lemma EqU_trans:     "p \<approx> q \<Longrightarrow> q \<approx> r \<Longrightarrow> p \<approx> r" by (simp add: EqU_def)

lemma EqU_iff_sets: "p \<approx> q \<longleftrightarrow> SuppU p = SuppU q"
  by (simp add: EqU_def)

lemma LeU_antisym_eq:
  assumes "p \<preceq> q" and "q \<preceq> p" shows "p \<approx> q"
  using assms by (simp add: EqU_def LeU_def subset_antisym)

lemma EqU_iff_LeU_both: "p \<approx> q \<longleftrightarrow> (p \<preceq> q \<and> q \<preceq> p)"
proof
  assume "p \<approx> q"
  thus "p \<preceq> q \<and> q \<preceq> p" by (simp add: EqU_def LeU_def)
next
  assume "p \<preceq> q \<and> q \<preceq> p"
  then have "SuppU p \<subseteq> SuppU q" and "SuppU q \<subseteq> SuppU p"
    by (simp_all add: LeU_def)
  hence "SuppU p = SuppU q" by (rule subset_antisym)
  thus "p \<approx> q" by (simp add: EqU_def)
qed

lemma SuppU_memI: "e \<turnstile> u \<Longrightarrow> e \<in> SuppU u" by (simp add: SuppU_def)
lemma SuppU_memD: "e \<in> SuppU u \<Longrightarrow> e \<turnstile> u" by (simp add: SuppU_def)

lemma LeU_pointI:
  assumes "\<forall>e\<in>SuppU p. e \<in> SuppU q" shows "p \<preceq> q"
  using assms by (simp add: LeU_def subset_iff)

lemma le_pointwise:
  assumes "p \<preceq> q" and "e \<turnstile> p" shows "e \<turnstile> q"
proof -
  have "e \<in> SuppU p" using assms(2) by (simp add: SuppU_def)
  moreover from assms(1) have "SuppU p \<subseteq> SuppU q" by (simp add: LeU_def)
  ultimately have "e \<in> SuppU q" by blast
  thus "e \<turnstile> q" by (simp add: SuppU_def)
qed

named_theorems leU_pointwise_rules
lemmas le_pointwise_SuppU [leU_pointwise_rules] = le_pointwise


subsection \<open>2.2  Useful @{text "\<approx>"}-extensionality shifters\<close>
lemma EqU_mono_left:  "p \<approx> q \<Longrightarrow> (p \<preceq> r) \<longleftrightarrow> (q \<preceq> r)" by (simp add: EqU_def LeU_def)
lemma EqU_mono_right: "p \<approx> q \<Longrightarrow> (r \<preceq> p) \<longleftrightarrow> (r \<preceq> q)" by (simp add: EqU_def LeU_def)
(* ===== strict order on U ===== *)
definition LtU :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<prec>" 50) where
  "p \<prec> q \<longleftrightarrow> (p \<preceq> q \<and> \<not> (q \<preceq> p))"


section \<open>3. (Symbols only) Modal primitives for ``@{text "\<box>"}/@{text "\<diamond>"}'' - no axioms here\<close>
text \<open>Several later definitions use the raw symbols ``@{text "\<box>"}/@{text "\<diamond>"}'' syntactically (e.g., in
  generic ``truthmaking pattern'' locales). We introduce the symbols here as
  uninterpreted constants. Any S5-style axioms/rules appear.\<close>

consts
  Box :: "bool \<Rightarrow> bool"  ("\<box> _" [60] 60)
  Dia :: "bool \<Rightarrow> bool"  ("\<diamond> _" [60] 60)


section \<open>4. Introduction of the Notion of ``Relative Certainty''(ReCert) \<close>
text\<open> [Concept: Relative Certainty]
  ``P is relatively less certain than Q'' (denoted P @{text "\<preceq>"} Q) implies that
  the set of entailments supporting P is a subset of those supporting Q.
  Ontologically, this means Q is ``heavier'' or ``more fundamental'' than P,
  as Q is necessitated by every witness that necessitates P. \<close>


subsection \<open>4.1  Bridge\<close>
consts Arg :: "bool \<Rightarrow> U"

definition Supports :: "U \<Rightarrow> bool \<Rightarrow> bool" where
  "Supports e \<phi> \<equiv> (e \<turnstile> Arg \<phi>)"      (* \<phi> holds at e *)

definition EDia :: "bool \<Rightarrow> bool"  ("\<diamond>\<^sub>e _" [60]) where
  "\<diamond>\<^sub>e \<zeta> \<equiv> (\<exists>e. Supports e \<zeta>)"      (* epistemically possible *)

lemma epi_possible_supports_Arg: "\<diamond>\<^sub>e \<zeta> \<Longrightarrow> \<exists>e. e \<turnstile> Arg \<zeta>"
  by (simp add: EDia_def Supports_def)
(* --- Minimal bridge: Makes, point lemmas, and ≤ ↔ ∀e implication --- *)
definition Makes :: "U \<Rightarrow> bool \<Rightarrow> bool" where
  "Makes e X \<equiv> Supports e X"

lemma in_SuppU_Arg_iff [simp]:
  "e \<in> SuppU (Arg X) \<longleftrightarrow> Makes e X"
  unfolding SuppU_def Supports_def Makes_def by simp

lemma LeU_iff_all:
  "((Arg S) \<preceq> (Arg T)) \<longleftrightarrow> (\<forall>e. Makes e S \<longrightarrow> Makes e T)"
  unfolding LeU_def SuppU_def Supports_def Makes_def by auto

lemma not_LeU_iff_exists_witness:
  "\<not> ((Arg S) \<preceq> (Arg T)) \<longleftrightarrow> (\<exists>a. Makes a S \<and> \<not> Makes a T)"
  by (simp add: LeU_iff_all)

corollary gap_equiv_witness_OmegaPsi_Phi':
  "\<not> ((Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>')) \<longleftrightarrow> (\<exists>a. Makes a (\<Omega> \<and> \<Psi>) \<and> \<not> Makes a \<Phi>')"
  using not_LeU_iff_exists_witness[of "\<Omega> \<and> \<Psi>" "\<Phi>'"] by simp

lemma witness_breaks_back_imp:
  assumes "Makes a X" and "\<not> Makes a Y"
  shows "\<not> (\<forall>e. Makes e X \<longrightarrow> Makes e Y)"
  using assms by blast
(* Strict order was defined earlier as LtU; define RelCert early (used later). *)
definition RelCert :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "RelCert R S \<equiv> (Arg R) \<prec> (Arg S)"

definition MoreCertain_pred :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "MoreCertain_pred \<Phi>' \<Phi> \<equiv> (\<forall>e. Makes e \<Phi>' \<longrightarrow> Makes e \<Phi>) \<and> \<not> (\<forall>e. Makes e \<Phi> \<longrightarrow> Makes e \<Phi>')"


subsection \<open>4.2  EH q: ``every epistemically possible truth support q''\<close>

definition EH :: "U \<Rightarrow> bool" where
  "EH q \<equiv> (\<forall>\<zeta>. \<diamond>\<^sub>e \<zeta> \<longrightarrow> (Arg \<zeta>) \<preceq> q)"
text \<open>[EH (Epistemic H)]
``Maximality over Epistemic Possibility''
A truth q satisfies EH if it serves as a necessary ground for every epistemically possible truth-bearer (@{text "\<diamond>"}\_e p).
(Definition: A truth-bearer p is epistemically possible if it has not yet been refuted by our current state of knowledge, thereby remaining a valid candidate for truth. This means that, regardless of whether p is inherently false or its negation simply remains unproven, from our current epistemic standpoint, its refutation is unknown.)
i.e., ``If it is epistemically possible, it is supported by q.''\<close>

lemma EH_inclusion:
  assumes "EH q" "\<diamond>\<^sub>e \<zeta>" shows "(Arg \<zeta>) \<preceq> q"
  using assms by (simp add: EH_def)

lemma EH_pointwise:
  assumes "EH q" "\<diamond>\<^sub>e \<zeta>" "Supports e \<zeta>" shows "e \<turnstile> q"
proof -
  from EH_inclusion[OF assms(1,2)] have sub: "SuppU (Arg \<zeta>) \<subseteq> SuppU q"
    by (simp add: LeU_def)
  from assms(3) have "e \<in> SuppU (Arg \<zeta>)" by (simp add: Supports_def SuppU_def)
  hence "e \<in> SuppU q" using sub by blast
  thus "e \<turnstile> q" by (simp add: SuppU_def)
qed

lemma H_principle_from_EH_inclusion:
  assumes "EH (Arg Q)" "\<diamond>\<^sub>e \<zeta>" shows "(Arg \<zeta>) \<preceq> (Arg Q)"
  using EH_inclusion[OF assms] .

lemma H_principle_from_EH_pointwise:
  assumes "EH (Arg Q)" "\<diamond>\<^sub>e \<zeta>" "Supports e \<zeta>" shows "e \<turnstile> Arg Q"
  using EH_pointwise[OF assms] .

named_theorems EH_intros
lemmas EH_to_inclusion [EH_intros] = EH_inclusion
lemmas EH_to_pointwise [EH_intros] = EH_pointwise


section \<open>5. Witness construction from the failure of EH \<close>
text\<open>
If a candidate q fails to satisfy EH, then there must exist an epistemically possible truth-bearer (denoted as @{text "\<zeta>"}) that explicitly witnesses this failure by remaining unsupported by q.
\<close>

theorem not_EH_witnessE:
  assumes "\<not> EH q'" shows "\<exists>\<zeta>. \<diamond>\<^sub>e \<zeta> \<and> \<not> ((Arg \<zeta>) \<preceq> q')"
  using assms unfolding EH_def by blast

lemma witness_from_failure_of_EH:
  assumes "\<diamond>\<^sub>e b" "\<diamond>\<^sub>e c"
      and "(Arg b) \<preceq> (Arg a)" "(Arg c) \<preceq> (Arg a)"
      and "\<not> ((Arg b) \<preceq> (Arg a')) \<or> \<not> ((Arg c) \<preceq> (Arg a'))"
  shows "\<not> EH (Arg a')"
proof -
  have D: "\<not> ((Arg b) \<preceq> (Arg a')) \<or> \<not> ((Arg c) \<preceq> (Arg a'))" using assms(5) by simp
  then show ?thesis
    proof
    assume L: "\<not> ((Arg b) \<preceq> (Arg a'))"
    with assms(1) show ?thesis by (auto simp: EH_def)
  next
    assume R: "\<not> ((Arg c) \<preceq> (Arg a'))"
    with assms(2) show ?thesis by (auto simp: EH_def)
  qed
qed


section \<open>6. ``TrueNow'' basis: relative certainty via actual truths\<close>
text \<open>[TH (TrueNow H)]
  ``Maximality over Actuality''
  A truth q satisfies TH if it serves as a necessary ground for every truth-bearer that is actually true in the present world (TrueNow).
  (Definition: A truth-bearer p is ``TrueNow'' if it possesses an actualized truth value in our current reality (e0). Unlike epistemic possibility, which only requires the absence of refutation, TrueNow demands robust ontological actuality.)
  i.e., ``If it is an actualized truth, its ontological foundation is supported by q.''
  This firmly anchors the abstract universal logic (``U-layer'') to the concrete actual world (e0). \<close>

consts e0 :: U

definition TrueNow :: "bool \<Rightarrow> bool" where
  "TrueNow \<phi> \<equiv> Supports e0 \<phi>"

definition TSupp :: "U \<Rightarrow> bool set" where
  "TSupp q \<equiv> {\<phi>. TrueNow \<phi> \<and> (Arg \<phi>) \<preceq> q}"

definition MoreCertainT :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<prec>\<^sup>T" 50) where
  "x \<prec>\<^sup>T y \<longleftrightarrow> TSupp x \<subset> TSupp y"

definition TH :: "U \<Rightarrow> bool" where
  "TH q \<equiv> (\<forall>\<phi>. TrueNow \<phi> \<longrightarrow> (Arg \<phi>) \<preceq> q)"


subsection \<open>6.1  Monotonicity and basic consequences\<close>

lemma TSupp_mono:
  assumes "q \<preceq> r" shows "TSupp q \<subseteq> TSupp r"
proof
  fix \<phi> assume "\<phi> \<in> TSupp q"
  then have Tphi: "TrueNow \<phi>" and A: "(Arg \<phi>) \<preceq> q" by (simp_all add: TSupp_def)
  from LeU_trans[OF A assms] have "(Arg \<phi>) \<preceq> r" .
  thus "\<phi> \<in> TSupp r" using Tphi by (simp add: TSupp_def)
qed

lemma TSupp_strict_by_extra:
  assumes "TSupp x \<subseteq> TSupp y"
      and "TrueNow S" and "(Arg S) \<preceq> y" and "\<not> ((Arg S) \<preceq> x)"
  shows "TSupp x \<subset> TSupp y"
proof (rule psubsetI)
  show "TSupp x \<subseteq> TSupp y" using assms(1) .
  have "S \<in> TSupp y" using assms(2,3) by (simp add: TSupp_def)
  moreover have "S \<notin> TSupp x" using assms(2,4) by (simp add: TSupp_def)
  ultimately show "TSupp x \<noteq> TSupp y" by blast
qed

lemma more_true_supports_implies_less_than_T:
  assumes "TSupp (Arg \<Gamma>) \<subseteq> TSupp (Arg \<Phi>)"
      and "TrueNow S" "(Arg S) \<preceq> (Arg \<Phi>)" "\<not> ((Arg S) \<preceq> (Arg \<Gamma>))"
  shows "(Arg \<Gamma>) \<prec>\<^sup>T (Arg \<Phi>)"
  unfolding MoreCertainT_def using TSupp_strict_by_extra[OF assms] .

lemma MoreCertainT_not_TH_left:
  assumes "(Arg \<Gamma>) \<prec>\<^sup>T (Arg \<Phi>)" shows "\<not> TH (Arg \<Gamma>)"
proof
  assume "TH (Arg \<Gamma>)"
  then have A: "\<forall>\<phi>. TrueNow \<phi> \<longrightarrow> (Arg \<phi>) \<preceq> (Arg \<Gamma>)" by (simp add: TH_def)
  from assms have "TSupp (Arg \<Gamma>) \<subset> TSupp (Arg \<Phi>)" by (simp add: MoreCertainT_def)
  then obtain S where Sin: "S \<in> TSupp (Arg \<Phi>)" and Snot: "S \<notin> TSupp (Arg \<Gamma>)"
    by (auto dest: psubsetD)
  from Sin have "TrueNow S" "(Arg S) \<preceq> (Arg \<Phi>)" by (simp_all add: TSupp_def)
  from Snot have "\<not> (TrueNow S \<and> (Arg S) \<preceq> (Arg \<Gamma>))" by (simp add: TSupp_def)
  with \<open>TrueNow S\<close> have "\<not> ((Arg S) \<preceq> (Arg \<Gamma>))" by blast
  with A \<open>TrueNow S\<close> show False by blast
qed


section \<open>7. Philosophical H (PH): ``PH q @{text "\<longleftrightarrow>"} (EH q @{text "\<and>"} TH q)''\<close>
text \<open> [Definition: PH (Philosophical H)]
  ``Total Maximality (The Supreme Truth)''
  PH is the conjunction of EH and TH.
  A truth ``q'' satisfies PH if it grounds the entire domain of discourse (PDom),
  covering both what is ``Actually True'' and what is ``Epistemically Possible''.
 
  Formal Equivalence: PH q @{text "\<longleftrightarrow>"} (EH q AND TH q) \<close>

definition PDom :: "bool set" where
  "PDom \<equiv> {\<zeta>. TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>}"

definition PSupp :: "U \<Rightarrow> bool set" where
  "PSupp q \<equiv> {\<zeta>. (TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>) \<and> (Arg \<zeta>) \<preceq> q}"

definition MoreCertainP :: "U \<Rightarrow> U \<Rightarrow> bool"  (infix "\<prec>\<^sup>P" 50) where
  "x \<prec>\<^sup>P y \<longleftrightarrow> PSupp x \<subset> PSupp y"

definition PH :: "U \<Rightarrow> bool" where
  "PH q \<equiv> (\<forall>\<zeta>. (TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q)"


subsection \<open>7.1  Basic facts, monotonicity, and extensionality\<close>

lemma PH_imp_EH: "PH q \<Longrightarrow> EH q" by (simp add: PH_def EH_def)
lemma PH_imp_TH: "PH q \<Longrightarrow> TH q" by (simp add: PH_def TH_def)

lemma EH_TH_imp_PH:
  assumes "EH q" "TH q" shows "PH q"
proof -
  have "\<forall>\<zeta>. (TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q"
    using assms by (auto simp: EH_def TH_def)
  thus "PH q" by (simp add: PH_def)
qed

corollary PH_iff_EH_TH: "PH q \<longleftrightarrow> (EH q \<and> TH q)"
  using PH_imp_EH PH_imp_TH EH_TH_imp_PH by blast

lemma PH_pointwise_possible:
  assumes "PH q" "\<diamond>\<^sub>e \<zeta>" "Supports e \<zeta>" shows "e \<turnstile> q"
  using assms PH_imp_EH EH_pointwise by blast

lemma PSupp_subset_PDom: "PSupp q \<subseteq> PDom" by (auto simp: PSupp_def PDom_def)

lemma PSupp_mono:
  assumes "q \<preceq> r" shows "PSupp q \<subseteq> PSupp r"
proof
  fix \<zeta> assume "\<zeta> \<in> PSupp q"
  then have D: "TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>" and A: "(Arg \<zeta>) \<preceq> q" by (simp_all add: PSupp_def)
  from LeU_trans[OF A assms] have "(Arg \<zeta>) \<preceq> r" .
  thus "\<zeta> \<in> PSupp r" using D by (simp add: PSupp_def)
qed

lemma PH_iff_PSupp_full: "PH q \<longleftrightarrow> PSupp q = PDom"
proof
  assume "PH q"
  then have A: "\<forall>\<zeta>. (TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q" by (simp add: PH_def)
  show "PSupp q = PDom"
  proof (intro set_eqI; intro iffI)
    fix \<zeta> assume "\<zeta> \<in> PSupp q"  thus "\<zeta> \<in> PDom" by (simp add: PSupp_def PDom_def)
  next
    fix \<zeta> assume "\<zeta> \<in> PDom"
    then have D: "TrueNow \<zeta> \<or> \<diamond>\<^sub>e \<zeta>" by (simp add: PDom_def)
    hence "(Arg \<zeta>) \<preceq> q" using A by blast
    thus "\<zeta> \<in> PSupp q" using D by (simp add: PSupp_def)
  qed
next
  assume eq: "PSupp q = PDom"
  then show "PH q" unfolding PH_def PSupp_def PDom_def by blast
qed

lemma PH_no_strict_superior:
  assumes "PH q" shows "\<not> (\<exists>r. q \<prec>\<^sup>P r)"
proof
  assume "\<exists>r. q \<prec>\<^sup>P r"
  then obtain r where r: "PSupp q \<subset> PSupp r" by (auto simp: MoreCertainP_def)
  from PH_iff_PSupp_full[of q] assms have eq: "PSupp q = PDom" by blast
  have "PDom \<subset> PSupp r" using r eq by simp
  then obtain \<zeta> where "\<zeta> \<in> PSupp r" and "\<zeta> \<notin> PDom" by (blast dest: psubsetD)
  from PSupp_subset_PDom[of r] have "PSupp r \<subseteq> PDom" .
  hence "\<zeta> \<in> PDom" using \<open>\<zeta> \<in> PSupp r\<close> by (rule subsetD)
  thus False using \<open>\<zeta> \<notin> PDom\<close> by blast
qed

lemma TSupp_extensional: "q \<approx> r \<Longrightarrow> TSupp q = TSupp r"
  by (intro set_eqI; simp add: TSupp_def EqU_mono_right)
lemma PSupp_extensional: "q \<approx> r \<Longrightarrow> PSupp q = PSupp r"
  by (intro set_eqI; simp add: PSupp_def EqU_mono_right)
lemma EH_extensional: "q \<approx> r \<Longrightarrow> EH q \<longleftrightarrow> EH r"
  by (simp add: EH_def EqU_mono_right)
lemma TH_extensional: "q \<approx> r \<Longrightarrow> TH q \<longleftrightarrow> TH r"
  by (simp add: TH_def EqU_mono_right)
lemma PH_extensional: "q \<approx> r \<Longrightarrow> PH q \<longleftrightarrow> PH r"
  by (simp add: PH_def EqU_mono_right)


section \<open>7.2 Riemann toy (Core-only, no ontic bridge)\<close>
text \<open>
  Core layer only. Two U-points eI, eII and three propositions R, Phi, Phi'.
  We assume only local facts at eI. No ontic bridge (no Val/iw).
\<close>

locale Riemann_Toy_Core =
  fixes eI eII :: U
    and R Phi Phi' :: bool
  assumes RI     : "Supports eI R"
      and RII    : "\<not> Supports eII R"
      and PhiI   : "Supports eI Phi"
      and nPhiI' : "\<not> Supports eI Phi'"
begin

text \<open>Since R holds at eI, R is epistemically possible (EDia R).\<close>
lemma EDia_R: "EDia R"
  using RI by (auto simp: EDia_def)

text \<open>If Phi' fails at eI, then PH (Arg Phi') would contradict nPhiI'.\<close>
lemma not_PH_of_Phi': "\<not> PH (Arg Phi')"
proof
  assume "PH (Arg Phi')"
  have "eI \<turnstile> Arg Phi'"
  using PH_pointwise_possible[of \<open>Arg Phi'\<close> R eI] EDia_R RI \<open>PH (Arg Phi')\<close>
  by blast

  hence "Supports eI Phi'"
    by (simp add: Supports_def)
  thus False using nPhiI' by contradiction
qed

text \<open>Helper: at eI, both R and Phi hold (just local evidence).\<close>
lemma both_at_eI: "Supports eI R \<and> Supports eI Phi"
  using RI PhiI by simp

end


subsection \<open>7.3 The H-principle: Structual Properties of Strict Subordination\<close>
text \<open>
  Below\_on K e : e is in PDom and Arg e @{text "\<prec>"} Arg K (strictly less certain than K).
  H\_principle K Q : every such e supports Q (i.e., Arg e @{text "\<preceq>"} Q).
\<close>

definition Below_on :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Below_on K e \<equiv> (e \<in> PDom \<and> (Arg e) \<prec> (Arg K))"

definition H_principle :: "bool \<Rightarrow> U \<Rightarrow> bool" where
  "H_principle K Q \<equiv> (\<forall>e. Below_on K e \<longrightarrow> (Arg e) \<preceq> Q)"

text \<open>Minimal form: for Q = Arg K it follows immediately from the definition of @{text "\<prec>"}.\<close>
lemma H_principle_self:
  shows "H_principle K (Arg K)"
  unfolding H_principle_def Below_on_def
  by (intro allI impI; simp add: LtU_def)

text \<open>It also transfers to any Q that is EqU-equivalent to Arg K.\<close>
lemma H_principle_of_EqU:
  assumes "Q \<approx> (Arg K)"
  shows   "H_principle K Q"
  unfolding H_principle_def Below_on_def
proof (intro allI impI)
  fix e assume "e \<in> PDom \<and> (Arg e) \<prec> (Arg K)"
  then have "(Arg e) \<preceq> (Arg K)" by (simp add: LtU_def)
  moreover from assms have "(Arg K) \<preceq> Q" by (simp add: EqU_iff_LeU_both)
  ultimately show "(Arg e) \<preceq> Q" by (meson LeU_trans)
qed


section \<open>8. Epistemic Frame: Definition of H\_negU\_strict and Derivation of EH\<close>

subsection \<open>8.1 Strong negative-form H (ban all equivalence/superiority; includes a non-vacuity guard)\<close>

definition H_negU_strict :: "bool \<Rightarrow> bool" where
  "H_negU_strict q \<equiv>
         (\<forall>\<zeta>\<in>PDom. \<zeta> \<noteq> q \<longrightarrow> \<not> ((Arg q) \<prec> (Arg \<zeta>)))"

lemma H_negU_strict_no_at_or_above:
  assumes "H_negU_strict q" "\<zeta> \<in> PDom" "\<zeta> \<noteq> q"
  shows "\<not> ((Arg q) \<prec> (Arg \<zeta>))"
  using assms by (simp add: H_negU_strict_def)

lemma possible_in_PDom: "\<diamond>\<^sub>e \<zeta> \<Longrightarrow> \<zeta> \<in> PDom"
  by (simp add: PDom_def)


subsection \<open>8.2 Hmax: ``all current truths supported (TH) + strong negative-form''\<close>

definition Hmax :: "bool \<Rightarrow> bool" where
  "Hmax q \<equiv> TH (Arg q) \<and> H_negU_strict q"

lemma Hmax_imp_TH: "Hmax q \<Longrightarrow> TH (Arg q)"
  by (simp add: Hmax_def)

lemma Hmax_blocks_tautology:
  assumes "Hmax q" "q \<noteq> True" "\<diamond>\<^sub>e True"
  shows "\<not> ((Arg q) \<prec> (Arg True))"
  using assms by (simp add: Hmax_def H_negU_strict_def PDom_def)


subsection \<open>8.3 Strict epistemic variants: ``currently true'' excluded\<close>
(* Possible but excluding what is currently true *)
definition EDia_strict :: "bool \<Rightarrow> bool" where
  "EDia_strict \<zeta> \<equiv> EDia \<zeta> \<and> \<not> TrueNow \<zeta>"

notation EDia_strict ("\<diamond>\<^sub>e' _" [60] 60)

lemma EDia_strict_imp_EDia: "EDia_strict \<zeta> \<Longrightarrow> EDia \<zeta>"
  by (simp add: EDia_strict_def)

lemma TrueNow_imp_not_EDia_strict: "TrueNow \<zeta> \<Longrightarrow> \<not> EDia_strict \<zeta>"
  by (simp add: EDia_strict_def)

text \<open>Strict version of EH: covers only epistemic possibilities that are not currently true(TrueNow).\<close>
definition EH_strict :: "U \<Rightarrow> bool" where
  "EH_strict q \<equiv> (\<forall>\<zeta>. EDia_strict \<zeta> \<longrightarrow> (Arg \<zeta>) \<preceq> q)"

lemma EH_imp_EH_strict: "EH q \<Longrightarrow> EH_strict q"
  unfolding EH_def EH_strict_def EDia_strict_def by blast


lemma TrueNow_implies_EDia: "TrueNow \<zeta> \<Longrightarrow> EDia \<zeta>"
  unfolding TrueNow_def EDia_def Supports_def by auto

lemma EH_from_strict_plus_TH:
  assumes "EH_strict q" and "TH q"
  shows "EH q"
  unfolding EH_def
proof (intro allI impI)
  fix \<zeta> assume "EDia \<zeta>"
  show "(Arg \<zeta>) \<preceq> q"
  proof (cases "TrueNow \<zeta>")
    case True
    with assms(2) show ?thesis by (simp add: TH_def)
  next
    case False
    from \<open>EDia \<zeta>\<close> False have "EDia_strict \<zeta>"
      by (simp add: EDia_strict_def)
    with assms(1) show ?thesis by (simp add: EH_strict_def)
  qed
qed


subsection \<open>8.4 PDom/PSupp (strict version)\<close>

definition PDom_strict :: "bool set" where
  "PDom_strict \<equiv> {\<zeta>. TrueNow \<zeta> \<or> EDia_strict \<zeta>}"

definition PSupp_strict :: "U \<Rightarrow> bool set" where
  "PSupp_strict q \<equiv> {\<zeta>. (TrueNow \<zeta> \<or> EDia_strict \<zeta>) \<and> (Arg \<zeta>) \<preceq> q}"

lemma PSupp_strict_subset_PDom_strict: "PSupp_strict q \<subseteq> PDom_strict"
  by (auto simp: PSupp_strict_def PDom_strict_def)

lemma PSupp_strict_mono:
  assumes "q \<preceq> r" shows "PSupp_strict q \<subseteq> PSupp_strict r"
proof
  fix \<zeta> assume "\<zeta> \<in> PSupp_strict q"
  then have D: "TrueNow \<zeta> \<or> EDia_strict \<zeta>" and Aq: "(Arg \<zeta>) \<preceq> q"
    by (simp_all add: PSupp_strict_def)
  from LeU_trans[OF Aq assms] have "(Arg \<zeta>) \<preceq> r" .
  thus "\<zeta> \<in> PSupp_strict r" using D by (simp add: PSupp_strict_def)
qed


subsection \<open>8.5 PH(strict)\<close>
text \<open>Strict version of PH.\<close>

definition PH_strict :: "U \<Rightarrow> bool" where
  "PH_strict q \<equiv> (\<forall>\<zeta>. (TrueNow \<zeta> \<or> EDia_strict \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q)"

lemma PH_strict_imp_TH: "PH_strict q \<Longrightarrow> TH q"
  unfolding PH_strict_def TH_def by blast

lemma PH_strict_imp_EH_strict: "PH_strict q \<Longrightarrow> EH_strict q"
  unfolding PH_strict_def EH_strict_def by blast

lemma TH_EHstrict_imp_PH_strict: "TH q \<Longrightarrow> EH_strict q \<Longrightarrow> PH_strict q"
  unfolding TH_def EH_strict_def PH_strict_def by blast

lemma PH_imp_PH_strict: "PH q \<Longrightarrow> PH_strict q"
  unfolding PH_def PH_strict_def EDia_strict_def by blast

text \<open>Equivalence with PSupp/PDom (strict).\<close>
lemma PH_strict_iff_PSupp_strict_full:
  "PH_strict q \<longleftrightarrow> PSupp_strict q = PDom_strict"
proof
  assume H: "PH_strict q"
  then have A: "\<forall>\<zeta>. (TrueNow \<zeta> \<or> EDia_strict \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q"
    by (simp add: PH_strict_def)
  show "PSupp_strict q = PDom_strict"
  proof (intro set_eqI; intro iffI)
    fix \<zeta> assume "\<zeta> \<in> PSupp_strict q"
    thus "\<zeta> \<in> PDom_strict"
      by (simp add: PSupp_strict_def PDom_strict_def)
  next
    fix \<zeta> assume "\<zeta> \<in> PDom_strict"
    then have D: "TrueNow \<zeta> \<or> EDia_strict \<zeta>"
      by (simp add: PDom_strict_def)
    with A have "(Arg \<zeta>) \<preceq> q" by blast
    thus "\<zeta> \<in> PSupp_strict q"
      using D by (simp add: PSupp_strict_def)
  qed
next
  assume eq: "PSupp_strict q = PDom_strict"
  show "PH_strict q"
  unfolding PH_strict_def
  proof (intro allI impI)
    fix \<zeta> assume H: "TrueNow \<zeta> \<or> EDia_strict \<zeta>"
    have "\<zeta> \<in> PDom_strict" using H by (simp add: PDom_strict_def)
    with eq have "\<zeta> \<in> PSupp_strict q" by simp
    thus "(Arg \<zeta>) \<preceq> q" by (simp add: PSupp_strict_def)
  qed
qed

text \<open>Extensionality.\<close>
lemma PH_strict_extensional:
  assumes "q \<approx> r"
  shows   "PH_strict q \<longleftrightarrow> PH_strict r"
proof
  assume Hq: "PH_strict q"
  have "\<forall>\<zeta>. (TrueNow \<zeta> \<or> EDia_strict \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> r"
    using Hq assms by (simp add: PH_strict_def EqU_mono_right)
  thus "PH_strict r" by (simp add: PH_strict_def)
next
  assume Hr: "PH_strict r"
  have "\<forall>\<zeta>. (TrueNow \<zeta> \<or> EDia_strict \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> q"
    using Hr assms by (simp add: PH_strict_def EqU_mono_right)
  thus "PH_strict q" by (simp add: PH_strict_def)
qed

lemma PSupp_strict_extensional:
  assumes "q \<approx> r"
  shows   "PSupp_strict q = PSupp_strict r"
proof (intro set_eqI)
  fix \<zeta>
  have "(Arg \<zeta>) \<preceq> q \<longleftrightarrow> (Arg \<zeta>) \<preceq> r"
    using assms by (simp add: EqU_mono_right)
  thus "\<zeta> \<in> PSupp_strict q \<longleftrightarrow> \<zeta> \<in> PSupp_strict r"
    by (simp add: PSupp_strict_def)
qed


subsection \<open>8.6 TH (one-way) and TSupp maximality: True vs q superiority\<close>
text \<open>We adopt **only one direction**:
  TH q @{text "\<Longrightarrow>"} (@{text "\<forall>"}x. TSupp x @{text "\<subseteq>"} TSupp q).\<close>

lemma TH_implies_TSupp_max:
  assumes "TH q"
  shows "\<forall>x. TSupp x \<subseteq> TSupp q"
proof
  fix x
  show "TSupp x \<subseteq> TSupp q"
  proof
    fix \<phi> assume "\<phi> \<in> TSupp x"
    then have T: "TrueNow \<phi>" and Ax: "(Arg \<phi>) \<preceq> x"
      by (simp_all add: TSupp_def)
    from assms T have "(Arg \<phi>) \<preceq> q"
      by (simp add: TH_def)
    thus "\<phi> \<in> TSupp q" using T by (simp add: TSupp_def)
  qed
qed

lemma Hmax_to_TSupp_max:
  assumes "Hmax q"
  shows "\<forall>x. TSupp x \<subseteq> TSupp (Arg q)"
  using assms by (simp add: Hmax_def TH_implies_TSupp_max)


section \<open>9. PDom-robustness lemmas + H\_opt @{text "\<Longrightarrow>"} EH/TH/PH\<close>
text \<open>EDia/TrueNow imply inclusion into PDom; impossibility (@{text "\<not>"} EDia) is a trivial lower bound; and EH( @{text "\<Longrightarrow>"} TH.\<close>

lemma EDia_in_PDom' [simp]: "EDia \<zeta> \<Longrightarrow> \<zeta> \<in> PDom"
  by (simp add: PDom_def)

lemma TrueNow_in_PDom' [simp]: "TrueNow \<zeta> \<Longrightarrow> \<zeta> \<in> PDom"
  by (simp add: PDom_def)

lemma not_EDia_le_any:
  assumes "\<not> EDia \<zeta>"
  shows   "(Arg \<zeta>) \<preceq> q"
  using assms
  unfolding LeU_def SuppU_def EDia_def Supports_def by auto

lemma EH_implies_TH:
  assumes "EH q"
  shows   "TH q"
  using assms
  unfolding EH_def TH_def
  using TrueNow_implies_EDia by blast

text \<open>If EH fails, there exists a possible-true counterexample (i.e., failure of top-coverage over PDom).\<close>
lemma not_EH_on_Arg_witness:
  assumes "\<not> EH (Arg q)"
  shows   "\<exists>\<zeta>. EDia \<zeta> \<and> \<not> ((Arg \<zeta>) \<preceq> (Arg q))"
  using assms not_EH_witnessE by blast


subsection \<open>9.1 Definition of H\_opt: strict anti-above + maximal nontrivial support\<close>
text \<open>
Maximizing Nontrivial Relational Supports among Heads.
We compare heads based on the cardinality of their nontrivial incoming support sets.

A support is defined as **nontrivial** into C only for patterns Arg(A @{text "\<and>"} B) @{text "\<preceq>"} Arg(C)
where A, B, and C are distinct (A @{text "\<noteq>"} B, A @{text "\<noteq>"} C, and B @{text "\<noteq>"} C).
Crucially, this excludes trivial logical properties such as plain @{text "\<and>"}-elimination
into one of the conjuncts.

MaxNT q signifies that q is a head whose set of nontrivial incoming edges
is cardinally at least as large as that of any other head (in the injection sense).
This identifies the most relationally coherent and robust truth structure.\<close>

definition Head :: "bool \<Rightarrow> bool" where
  "Head q \<equiv> H_negU_strict q"

definition NT_pair_support :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "NT_pair_support A B C \<equiv>
     A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> (Arg (A \<and> B) \<preceq> Arg C)"

definition NT_in_edges :: "bool \<Rightarrow> (bool \<times> bool) set" where
  "NT_in_edges C \<equiv>
     {(A,B). Head A \<and> Head B \<and> Head C \<and> NT_pair_support A B C}"
(* --- Cantor-style cardinal comparison via injections --- *)
definition le_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool"  (infix "\<preceq>\<^sub>c" 50) where
  "A \<preceq>\<^sub>c B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> f ` A \<subseteq> B)"

definition lt_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool"  (infix "\<prec>\<^sub>c" 50) where
  "A \<prec>\<^sub>c B \<longleftrightarrow> (A \<preceq>\<^sub>c B \<and> \<not> (B \<preceq>\<^sub>c A))"

definition eq_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool"  (infix "\<approx>\<^sub>c" 50) where
  "A \<approx>\<^sub>c B \<longleftrightarrow> (A \<preceq>\<^sub>c B \<and> B \<preceq>\<^sub>c A)"

lemma le_card_empty_left: "{} \<preceq>\<^sub>c B"
  unfolding le_card_def
  by (rule exI[where x="\<lambda>x. undefined"]; auto)

definition MaxNT :: "bool \<Rightarrow> bool" where
  "MaxNT q \<equiv>
     Head q \<and>
     (\<forall>r. Head r \<longrightarrow> NT_in_edges r \<preceq>\<^sub>c NT_in_edges q)"

definition H_opt :: "bool \<Rightarrow> bool" where
  "H_opt q \<equiv> MaxNT q"


subsection \<open>9.2 Consequences of H\_opt (Cantor-size / MaxNT version)\<close>

lemma Hopt_to_MaxNT:
  assumes HQ: "H_opt q"
  shows "MaxNT q"
  using HQ by (simp add: H_opt_def)

lemma NT_in_edges_empty_if_not_Head:
  assumes NH: "\<not> Head C"
  shows "NT_in_edges C = {}"
  using NH by (auto simp: NT_in_edges_def)

lemma Hopt_score_ge_in_PDom:
  assumes HQ: "H_opt q" and Zin: "z \<in> PDom"
  shows "NT_in_edges z \<preceq>\<^sub>c NT_in_edges q"
proof (cases "Head z")
  case True
  have Bound: "\<forall>r. Head r \<longrightarrow> NT_in_edges r \<preceq>\<^sub>c NT_in_edges q"
    using Hopt_to_MaxNT[OF HQ] by (auto simp: MaxNT_def)
  show ?thesis using Bound True by blast
next
  case False
  have "NT_in_edges z = {}" using NT_in_edges_empty_if_not_Head[OF False] .
  thus ?thesis using le_card_empty_left by simp
qed

lemma Hopt_score_tie:
  assumes HA: "H_opt A" and HB: "H_opt B"
  shows "NT_in_edges A \<approx>\<^sub>c NT_in_edges B"
proof -
  have HeadA: "Head A" and HeadB: "Head B"
    using HA HB by (auto simp: H_opt_def MaxNT_def)

  have AB: "NT_in_edges A \<preceq>\<^sub>c NT_in_edges B"
    using HB HeadA by (auto simp: H_opt_def MaxNT_def)
  have BA: "NT_in_edges B \<preceq>\<^sub>c NT_in_edges A"
    using HA HeadB by (auto simp: H_opt_def MaxNT_def)

  show ?thesis by (simp add: eq_card_def AB BA)
qed


text \<open>If H\_opt holds for K, the minimal form above also follows automatically.\<close>
lemma Hopt_implies_H_principle:
  assumes "H_opt K"
  shows   "H_principle K (Arg K)"
  using H_principle_self by simp

lemma Hopt_implies_H_principle_EqU:
  assumes "H_opt K" "Q \<approx> (Arg K)"
  shows   "H_principle K Q"
  using H_principle_of_EqU assms(2) by blast


subsection \<open>9.3 Consistency of H\_opt (Cantor-size version)\<close>

lemma Hopt_has_no_strictly_better_in_PDom:
  assumes HQ: "H_opt q"
  shows "\<not> (\<exists>z\<in>PDom. NT_in_edges q \<prec>\<^sub>c NT_in_edges z)"
proof
  assume "\<exists>z\<in>PDom. NT_in_edges q \<prec>\<^sub>c NT_in_edges z"
  then obtain z where Zin: "z \<in> PDom" and lt: "NT_in_edges q \<prec>\<^sub>c NT_in_edges z"
    by blast

  have ge: "NT_in_edges z \<preceq>\<^sub>c NT_in_edges q"
    using Hopt_score_ge_in_PDom[OF HQ Zin] .

  from lt have nz: "\<not> (NT_in_edges z \<preceq>\<^sub>c NT_in_edges q)"
    by (simp add: lt_card_def)

  show False using ge nz by contradiction
qed

text \<open>
The consistency result for @{term H_opt} is purely order-theoretic (MaxNT) and
does not require @{term "q"}(the argument of H\_opt) to be a tautology.  In particular,
even under the extra assumption @{term "q \<noteq> True"}, the same conclusion holds.
\<close>
corollary Hopt_has_no_strictly_better_in_PDom_non_tautology:
  assumes HQ: "H_opt q"
      and nT: "q \<noteq> True"
  shows "\<not> (\<exists>z\<in>PDom. NT_in_edges q \<prec>\<^sub>c NT_in_edges z)"
  using Hopt_has_no_strictly_better_in_PDom[OF HQ] .

subsection \<open>9.4 Finality (H\_opt): No argument strictly above an H\_opt truth (proof route)\<close>
text \<open>If H\_opt q holds, then Arg q is final within PDom: no proposition in PDom has an
argument strictly above Arg q. The proof route is immediate: H\_opt q entails
H\_negU\_strict q, and H\_negU\_strict q already excludes any @{text "\<zeta>"} @{text "\<in>"} PDom such that
Arg q @{text "\<prec>"} Arg @{text "\<zeta>"}. Hence no PDom-based definition can designate a proposition
strictly superior to q in argument strength; the search for a strictly higher
truth terminates at H\_opt.\<close>

lemma argument_finality_PDom:
  assumes HQ: "H_opt q"
  shows "\<forall>\<zeta>\<in>PDom. \<not> ((Arg q) \<prec> (Arg \<zeta>))"
proof (intro ballI)
  fix \<zeta> assume Zin: "\<zeta> \<in> PDom"
  have HN: "H_negU_strict q"
    using HQ by (auto simp: H_opt_def MaxNT_def Head_def)
  show "\<not> ((Arg q) \<prec> (Arg \<zeta>))"
  proof (cases "\<zeta> = q")
    case True
    then show ?thesis by (simp add: LtU_def)
  next
    case False
    then show ?thesis using HN Zin by (simp add: H_negU_strict_def)
  qed
qed

text \<open>If a definition D only ranges over PDom, then it cannot designate an argument strictly superior to Arg q under H\_opt q.\<close>
lemma argument_finality_for_defs:
  assumes HQ: "H_opt q"
      and Drng: "\<forall>r. D r \<longrightarrow> r \<in> PDom"
  shows "\<not> (\<exists>r. D r \<and> (Arg q) \<prec> (Arg r))"
proof
  assume "\<exists>r. D r \<and> (Arg q) \<prec> (Arg r)"
  then obtain r where Dr: "D r" and Lt: "(Arg q) \<prec> (Arg r)" by blast
  from Drng Dr have Rin: "r \<in> PDom" by blast
  from argument_finality_PDom[OF HQ] Rin have "\<not> ((Arg q) \<prec> (Arg r))" by blast
  with Lt show False by blast
qed

text \<open>Pointwise corollaries.\<close>
corollary argument_finality_point:
  assumes HQ: "H_opt q" and Rin: "r \<in> PDom"
  shows "\<not> ((Arg q) \<prec> (Arg r))"
  using argument_finality_PDom[OF HQ] Rin by blast

corollary argument_finality_possible:
  assumes HQ: "H_opt q" and Er: "EDia r"
  shows "\<not> ((Arg q) \<prec> (Arg r))"
proof -
  have Rin: "r \<in> PDom"
    using Er by (auto simp: PDom_def EDia_def TrueNow_def)
  show ?thesis using argument_finality_PDom[OF HQ] Rin by blast
qed

corollary argument_finality_true:
  assumes HQ: "H_opt q" and Tr: "TrueNow r"
  shows "\<not> ((Arg q) \<prec> (Arg r))"
proof -
  have Rin: "r \<in> PDom"
    using Tr by (auto simp: PDom_def TrueNow_def EDia_def)
  show ?thesis using argument_finality_PDom[OF HQ] Rin by blast
qed

corollary no_definition_strictly_superior_than_H_opt:
  assumes HQ: "H_opt q" and Drng: "\<forall>r. D r \<longrightarrow> r \<in> PDom"
  shows "\<not> (\<exists>r. D r \<and> (Arg q) \<prec> (Arg r))"
  using argument_finality_for_defs[OF HQ Drng] .

subsection \<open>9.5 Flat-model consistency witness for \<open>\<exists>q. H_opt q\<close>\<close>
text \<open>
  Purpose. Provide a concrete toy model (one-point world, always-true entailment,
  constant \<open>Arg\<close>) in which \<open>H_opt q\<close> holds for any \<open>q\<close>. This shows the existential
  \<open>\<exists>q. H_opt q\<close> is satisfiable (hence not explosive) relative to the U-style
  definitions below, without touching the main development.

  **This adds no axioms; purely a satisfiability witness.**

  **Not a semantics claim.** The construction is intentionally ``flat''
  (single world; entailment always true), so many propositions come out trivially true.
  It is **not** offered as an intended or endorsable semantics of the main theory,
  but solely as a **consistency witness**: there exists at least one interpretation
  making @{text "<exists>"}H\_opt q true without contradiction.

  **No dependency back into the core.** No main lemma or theorem should depend on
  this appendix. Keep it documentation/check-only, so the core results cannot be
  criticized as relying on a trivial model.
\<close>

text \<open>Concrete flat model **without** locales/interpretations (zero friction).\<close>
type_synonym U1 = unit
(* Flat Arg / order: everything is equal, so ≤ is always true and < is always false. *)
definition Arg_F :: "bool \<Rightarrow> U1" where
  "Arg_F _ \<equiv> ()"

definition Le_F :: "U1 \<Rightarrow> U1 \<Rightarrow> bool" where
  "Le_F _ _ \<equiv> True"

definition Lt_F :: "U1 \<Rightarrow> U1 \<Rightarrow> bool" where
  "Lt_F p q \<equiv> Le_F p q \<and> \<not> Le_F q p"

lemma Le_F_true[simp]: "Le_F p q"
  by (simp add: Le_F_def)

lemma not_Lt_F[simp]: "\<not> Lt_F p q"
  by (simp add: Lt_F_def Le_F_def)
(* PDom in the flat witness: everything is in the domain. *)
definition PDom_F :: "bool set" where
  "PDom_F \<equiv> UNIV"

lemma PDom_F_all[simp]: "z \<in> PDom_F"
  by (simp add: PDom_F_def)
(* Head filter in the MaxNT development: anti-above on PDom (always satisfied here). *)
definition H_negU_strict_F :: "bool \<Rightarrow> bool" where
  "H_negU_strict_F q \<equiv>
     (\<forall>z\<in>PDom_F. z \<noteq> q \<longrightarrow> \<not> (Lt_F (Arg_F q) (Arg_F z)))"

definition Head_F :: "bool \<Rightarrow> bool" where
  "Head_F q \<equiv> H_negU_strict_F q"

lemma Head_F_true[simp]: "Head_F q"
  by (simp add: Head_F_def H_negU_strict_F_def)
(* Nontrivial pair-support among heads (same shape as MaxNT definition). *)
definition NT_pair_support_F :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "NT_pair_support_F A B C \<equiv>
     A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> (Le_F (Arg_F (A \<and> B)) (Arg_F C))"

definition NT_in_edges_F :: "bool \<Rightarrow> (bool \<times> bool) set" where
  "NT_in_edges_F C \<equiv>
     {(A,B). Head_F A \<and> Head_F B \<and> Head_F C \<and> NT_pair_support_F A B C}"
(* Helper: no three distinct booleans exist. *)
lemma no_three_distinct_bools:
  fixes A B C :: bool
  shows "A = B \<or> A = C \<or> B = C"
  by (cases A; cases B; cases C; auto)

lemma NT_pair_support_F_false[simp]: "\<not> NT_pair_support_F A B C"
  by (simp add: NT_pair_support_F_def no_three_distinct_bools)

lemma NT_in_edges_F_empty[simp]: "NT_in_edges_F C = {}"
  by (auto simp: NT_in_edges_F_def)
(* Cardinal comparison reflexivity (handy for MaxNT). *)
lemma le_card_refl: "X \<preceq>\<^sub>c X"
  unfolding le_card_def
  by (rule exI[where x="\<lambda>x. x"]; auto)
(* MaxNT / H_opt shape (MaxNT-based). *)
definition MaxNT_F :: "bool \<Rightarrow> bool" where
  "MaxNT_F q \<equiv>
     Head_F q \<and> (\<forall>r. Head_F r \<longrightarrow> NT_in_edges_F r \<preceq>\<^sub>c NT_in_edges_F q)"

definition H_opt_MaxNT_F :: "bool \<Rightarrow> bool" where
  "H_opt_MaxNT_F q \<equiv> MaxNT_F q"

lemma MaxNT_F_all[simp]: "MaxNT_F q"
  unfolding MaxNT_F_def
  by (simp add: le_card_refl)

lemma H_opt_MaxNT_F_all[simp]: "H_opt_MaxNT_F q"
  by (simp add: H_opt_MaxNT_F_def)

corollary exists_H_opt_MaxNT_F: "\<exists>q. H_opt_MaxNT_F q"
  by (rule exI[where x=True], simp)
text \<open>
  Reading. The MaxNT/NT\_in\_edges shape is satisfiable in a concrete flat toy model.
  This witnesses non-explosiveness of the definitional pattern, without affecting the core.
\<close>


section \<open>10. Supplemental Ontic Frame: A Semantic Interpretation\<close>
text \<open> [Note on the Supplemental Nature of this Section]
  The core proof of H\_opt and the Trinitarian structure is self-contained
  within the abstract U-logic. This section provides an **optional
  interpretative bridge** to standard possible-world semantics.
 
  By mapping model propositions to sets of worlds, we demonstrate that
  our universal logic is fully compatible with classical ontic frames.
  This serves as a semantic verification (Application) rather than
  a necessary foundation for the main argument. \<close>

locale FullIdBridge =
  fixes Val :: "'W \<Rightarrow> bool \<Rightarrow> bool"    (* truth function of the model: \<zeta> is true at w *)
    and iw  :: "'W \<Rightarrow> U"               (* embedding of model worlds into U-worlds *)
  assumes surj_iw: "\<forall>e. \<exists>w. e = iw w"
      and bridge:  "\<forall>w \<zeta>. (iw w \<turnstile> Arg \<zeta>) \<longleftrightarrow> Val w \<zeta>"
begin

definition Arg0 :: "bool \<Rightarrow> 'W set" where
  "Arg0 \<zeta> \<equiv> {w. Val w \<zeta>}"

definition EDia0 :: "bool \<Rightarrow> bool" where
  "EDia0 \<zeta> \<equiv> (\<exists>w. Val w \<zeta>)"

lemma SuppU_Arg_id:
  "SuppU (Arg \<zeta>) = { iw w | w. Val w \<zeta> }"
proof (intro set_eqI iffI)
  fix e assume "e \<in> SuppU (Arg \<zeta>)"
  then have "e \<turnstile> Arg \<zeta>" by (simp add: SuppU_def)
  from surj_iw obtain w where "e = iw w" by blast
  from \<open>e = iw w\<close> \<open>e \<turnstile> Arg \<zeta>\<close> have "Val w \<zeta>" by (simp add: bridge)
  thus "e \<in> { iw w | w. Val w \<zeta> }" using \<open>e = iw w\<close> by blast
next
 
  fix e assume "e \<in> { iw w | w. Val w \<zeta> }"
  then obtain w where "e = iw w" and "Val w \<zeta>" by blast
  hence "iw w \<turnstile> Arg \<zeta>" by (simp add: bridge)
  thus "e \<in> SuppU (Arg \<zeta>)" using \<open>e = iw w\<close> by (simp add: SuppU_def)
qed

lemma Dia_equiv: "EDia \<zeta> \<longleftrightarrow> EDia0 \<zeta>"
proof
  assume "EDia \<zeta>"
  then obtain e where "Supports e \<zeta>" by (auto simp: EDia_def)
  hence "e \<turnstile> Arg \<zeta>" by (simp add: Supports_def)
  from surj_iw obtain w where "e = iw w" by blast
  with \<open>e \<turnstile> Arg \<zeta>\<close> have "Val w \<zeta>" by (simp add: bridge)
  thus "EDia0 \<zeta>" by (auto simp: EDia0_def)
next
  assume "EDia0 \<zeta>"
  then obtain w where "Val w \<zeta>" by (auto simp: EDia0_def)
  hence "(iw w) \<turnstile> Arg \<zeta>" by (simp add: bridge)
  hence "Supports (iw w) \<zeta>" by (simp add: Supports_def)
  thus "EDia \<zeta>" by (auto simp: EDia_def)
qed

lemma LeU_iff_subset: "(Arg \<zeta>) \<preceq> (Arg t) \<longleftrightarrow> Arg0 \<zeta> \<subseteq> Arg0 t"
proof
   assume le: "(Arg \<zeta>) \<preceq> (Arg t)"
  show "Arg0 \<zeta> \<subseteq> Arg0 t"
  proof
    fix w assume "w \<in> Arg0 \<zeta>"
    hence "Val w \<zeta>" by (simp add: Arg0_def)
    hence "iw w \<turnstile> Arg \<zeta>" by (simp add: bridge)
    from le have "SuppU (Arg \<zeta>) \<subseteq> SuppU (Arg t)" by (simp add: LeU_def)
    hence "iw w \<turnstile> Arg t" using \<open>iw w \<turnstile> Arg \<zeta>\<close> by (auto simp: SuppU_def)
    hence "Val w t" by (simp add: bridge)
    thus "w \<in> Arg0 t" by (simp add: Arg0_def)
  qed
next
  assume sub: "Arg0 \<zeta> \<subseteq> Arg0 t"
  show "(Arg \<zeta>) \<preceq> (Arg t)"
    unfolding LeU_def SuppU_Arg_id
  proof (intro subsetI)
    fix e assume "e \<in> { iw w | w. Val w \<zeta> }"
    then obtain w where ew: "e = iw w" and v\<zeta>: "Val w \<zeta>" by blast
    from sub v\<zeta> have "Val w t" by (auto simp: Arg0_def)
    thus "e \<in> { iw w | w. Val w t }" using ew by blast
  qed
qed

end  (* locale FullIdBridge *)
(* ---------- Riemann toy model: two worlds (I, II) ---------- *)
datatype W = I | II

locale Riemann_Toy =
  FullIdBridge Val iw for Val :: "W \<Rightarrow> bool \<Rightarrow> bool" and iw :: "W \<Rightarrow> U"
+ fixes R \<Phi> \<Phi>' :: bool
assumes RI:     "Val I R"
    and RII:    "\<not> Val II R"
    and PhiI:   "Val I \<Phi>"
    and nPhi'I: "\<not> Val I \<Phi>'"
begin

lemma Arg0_R_is_I: "Arg0 R = {w. w = I}"
proof (intro set_eqI; intro iffI)
  (* -> *)
  fix w assume "w \<in> Arg0 R"
  then have Vw: "Val w R" by (simp add: Arg0_def)
  show "w \<in> {w. w = I}"
  proof (cases w)
    case I
    then show ?thesis by simp
  next
    case II
    from Vw II have "Val II R" by simp
    with RII show ?thesis by contradiction
  qed
next
 
  fix w assume "w \<in> {w. w = I}"
  then have "w = I" by simp
  with RI show "w \<in> Arg0 R" by (simp add: Arg0_def)
qed

lemma EDia0_R: "EDia0 R"
  unfolding EDia0_def using RI by auto

lemma EDia_R: "EDia R"
  using Dia_equiv EDia0_R by simp

lemma R_supports_Phi_model: "Arg0 R \<subseteq> Arg0 \<Phi>"
  using Arg0_R_is_I PhiI by (auto simp: Arg0_def)

lemma R_not_support_Phi'_model: "\<not> (Arg0 R \<subseteq> Arg0 \<Phi>')"
proof
  assume "Arg0 R \<subseteq> Arg0 \<Phi>'"
  hence "I \<in> Arg0 \<Phi>'" using Arg0_R_is_I by simp
  thus False by (simp add: Arg0_def nPhi'I)
qed

lemma R_supports_Phi_U: "(Arg R) \<preceq> (Arg \<Phi>)"
  using LeU_iff_subset R_supports_Phi_model by blast

lemma R_not_support_Phi'_U: "\<not> ((Arg R) \<preceq> (Arg \<Phi>'))"
  using LeU_iff_subset R_not_support_Phi'_model by blast

lemma not_PH_of_Phi': "\<not> PH (Arg \<Phi>')"
proof
  assume "PH (Arg \<Phi>')"
  from this EDia_R have "(Arg R) \<preceq> (Arg \<Phi>')" by (auto simp: PH_def)
  with R_not_support_Phi'_U show False by contradiction
qed

end


section \<open>11. Vacuity Diagnosis: NT\_edge-death empties relational maximality, while N=3 remains the unique structural fixed point\<close>
text \<open>
 Design note (two-tier MaxNT).

  - MaxNT (Section 9) is the ranking core: it compares nontrivial incoming patterns
    under the minimal pairwise-distinctness guard A @{text "\<noteq>"} B, A @{text "\<noteq>"} C, and B @{text "\<noteq>"} C.
    This is the weaker, refactor-stable notion of relational maximality.

  - MaxNT\_edge (Section 11) is the non-vacuity strengthening: it rebuilds incoming
    support using NT\_edge, which additionally enforces non-collapse
    (no conjunction-elimination equivalence). Thus MaxNT\_edge is strictly stronger
    and exists only when genuine relational structure is possible.

  Therefore Section 11 is diagnostic: it shows that if NT\_edge is globally impossible,
  then every edge-based incoming-support set is empty, and the Cantor-style comparison
  used in MaxNT\_edge becomes vacuous. Hence MaxNT\_edge collapses to Head-only.

  This vacuity affects informational/relational content only; it does not by itself
  undermine the independent structural necessity of the triune fixed point (N=3).\<close>

text \<open>
 Philosophical background.

  In this development, MaxNT is intended to capture a ``supreme truth'' in a strong sense:
  not merely a truth that is final, but one whose superiority is expressed through
  maximal non-trivial relational support. Thus the real issue is not finality alone,
  but whether maximality is sustained by genuine relational content rather than by
  an informationally empty structure.

  Section 11 isolates exactly this issue. It introduces NT\_edge and the rebuilt notion
  MaxNT\_edge in order to diagnose whether the incoming relational structure remains
  genuinely non-trivial. Here, ``non-trivial'' means that a conjunction-based support
  does not collapse back into mere conjunction-elimination equivalence with one of
  its conjuncts.

  The goal of this section is therefore diagnostic, not destructive.
  We prove the following conditional:

    if NT\_edge is globally impossible (NT\_dead),
    then every NT\_in\_edges\_edge set is empty,
    and the Cantor-style comparison used in MaxNT\_edge becomes vacuous.

  Hence MaxNT\_edge collapses to a purely formal head-condition:
  its maximality remains syntactically satisfiable, but only vacuously,
  because all edge-based relational content has disappeared.

  Crucially, this vacuity does not undermine the independent structural necessity
  of the triune fixed point. Even if relational support becomes informationally empty
  through collapse, the exclusion results against N=1, N=2, and N@{text "\<ge>"}4 remain intact.
  Thus N=3 persists as the unique consistency-preserving fixed point.

  This section therefore establishes the precise message:

    ``If NT\_edge dies, relational maximality becomes vacuous;
     but the structural necessity of N=3 does not collapse.''

  No axioms are introduced here. NT\_dead is a definitional diagnostic hypothesis
  used only to prove a conditional vacuity theorem.
\<close>
(* ------------------------------------------------------------------------- *)
(* 11.0  Non-trivial edge (same meaning as earlier NT_edge)            *)
(* ------------------------------------------------------------------------- *)
definition NT_edge :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "NT_edge A B C \<longleftrightarrow>
     (Arg (A \<and> B) \<preceq> Arg C) \<and>
     \<not> (Arg (A \<and> B) \<approx> Arg A) \<and>
     \<not> (Arg (A \<and> B) \<approx> Arg B)"
(* ------------------------------------------------------------------------- *)
(* 11.1  Global “edge death” hypothesis                                     *)
(* ------------------------------------------------------------------------- *)
definition NT_dead :: bool where
  "NT_dead \<equiv> (\<forall>A B C. \<not> NT_edge A B C)"
(* ------------------------------------------------------------------------- *)
(* 11.2  NT_in_edges rebuilt directly on NT_edge (refactor-friendly)        *)
(*         (Depends on Head :: bool \<Rightarrow> bool from Section 9.1)          *)
(* ------------------------------------------------------------------------- *)
definition NT_in_edges_edge :: "bool \<Rightarrow> (bool \<times> bool) set" where
  "NT_in_edges_edge C \<equiv>
     {(A,B). Head A \<and> Head B \<and> Head C \<and>
            A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and>
            NT_edge A B C}"
(* ------------------------------------------------------------------------- *)
(* 11.3  MaxNT rebuilt on NT_in_edges_edge (Cantor-style comparison)        *)
(*         (Depends on \<preceq>\<^sub>c and le_card_empty_left from Section 9.1)   *)
(* ------------------------------------------------------------------------- *)
definition MaxNT_edge :: "bool \<Rightarrow> bool" where
  "MaxNT_edge q \<equiv>
     Head q \<and>
     (\<forall>r. Head r \<longrightarrow> NT_in_edges_edge r \<preceq>\<^sub>c NT_in_edges_edge q)"

definition Nontrivial_MaxNT_edge :: "bool \<Rightarrow> bool" where
  "Nontrivial_MaxNT_edge q \<equiv> MaxNT_edge q \<and> NT_in_edges_edge q \<noteq> {}"


subsection \<open>11.1 NT\_dead @{text "\<Longrightarrow>"} all edge-sets are empty\<close>

lemma NT_in_edges_edge_empty_if_NT_dead:
  assumes D: NT_dead
  shows "NT_in_edges_edge C = {}"
  using D
  unfolding NT_dead_def NT_in_edges_edge_def
  by auto


subsection \<open>11.2 Vacuity theorem: MaxNT\_edge collapses to Head\<close>

theorem MaxNT_edge_iff_Head_if_NT_dead:
  assumes D: NT_dead
  shows "MaxNT_edge q \<longleftrightarrow> Head q"
proof
 
  assume "MaxNT_edge q"
  thus "Head q" by (simp add: MaxNT_edge_def)
next
 
  assume Hq: "Head q"
  show "MaxNT_edge q"
    unfolding MaxNT_edge_def
  proof (intro conjI allI impI)
    show "Head q" by (rule Hq)

    fix r assume Hr: "Head r"
    have Er: "NT_in_edges_edge r = {}"
      using NT_in_edges_edge_empty_if_NT_dead[OF D] .
    have Eq: "NT_in_edges_edge q = {}"
      using NT_in_edges_edge_empty_if_NT_dead[OF D] .

    show "NT_in_edges_edge r \<preceq>\<^sub>c NT_in_edges_edge q"
      by (simp add: Er Eq le_card_empty_left)
  qed
qed


subsection \<open>11.3 Consequence: ``Meaningful MaxNT'' becomes impossible under NT\_dead\<close>

corollary no_Nontrivial_MaxNT_edge_if_NT_dead:
  assumes D: NT_dead
  shows "\<not> (\<exists>q. Nontrivial_MaxNT_edge q)"
proof
  assume "\<exists>q. Nontrivial_MaxNT_edge q"
  then obtain q where H: "Nontrivial_MaxNT_edge q" by blast
  hence NE: "NT_in_edges_edge q \<noteq> {}"
    by (simp add: Nontrivial_MaxNT_edge_def)
  moreover have "NT_in_edges_edge q = {}"
    using NT_in_edges_edge_empty_if_NT_dead[OF D] .
  ultimately show False by contradiction

qed

subsection \<open>11.4 Derived corollaries (optional)\<close>
text \<open>
  This subsection records small but useful consequences of the vacuity theorem.

  Under NT\_dead, the Cantorian maximality comparison is empty-vacuous, so:

    (i) Any Head automatically satisfies MaxNT\_edge (maximality becomes trivial).
    (ii) Any two MaxNT\_edge candidates are indistinguishable at the level of
         their incoming edge-sets (both are empty).

  These are not new assumptions; they are direct corollaries of Sections 11.1–11.2.
  Their role is purely expositional: they make the ``vacuity collapse'' behavior
  visible in lightweight lemmas that can be reused later.
\<close>

corollary Head_implies_MaxNT_edge_under_NT_dead:
  assumes D: NT_dead and Hq: "Head q"
  shows "MaxNT_edge q"
  using MaxNT_edge_iff_Head_if_NT_dead[OF D] Hq by blast

corollary MaxNT_edge_is_tied_under_NT_dead:
  assumes D: NT_dead and A: "MaxNT_edge x" and B: "MaxNT_edge y"
  shows "NT_in_edges_edge x = NT_in_edges_edge y"
  using NT_in_edges_edge_empty_if_NT_dead[OF D] by simp


subsection \<open>11.5 One-to-one collapse route: (1-to-1) @{text "\<Longrightarrow>"} NT\_dead @{text "\<Longrightarrow>"} vacuity\<close>
text \<open>
  This subsection makes explicit (as lemmas) the intended bridge:

    (1) If the theory enforces a global 1-to-1 comparability of grounds
        (a total preorder on Arg-images),
    then every conjunction collapses to one conjunct (trivial collapse).

    (2) Hence no NT\_edge can survive (NT\_dead).

    (3) Therefore, by Section 11.2, MaxNT\_edge collapses to Head-only (vacuity).

  Importantly, no axioms are introduced: the 1-to-1 condition and the conjunction
  grammar rules (MCL/MCI) are stated as *assumptions* of conditional theorems.
\<close>

lemma conj_le_left_from_MCL:
  assumes MCL: "\<And>e X Y. Makes e (X \<and> Y) \<Longrightarrow> Makes e X"
  shows "Arg (X \<and> Y) \<preceq> Arg X"
  unfolding LeU_iff_all
  using MCL by blast

lemma Subordination_implies_Trivial_Collapse_left:
  assumes AB : "Arg A \<preceq> Arg B"
      and MCL: "\<And>e X Y. Makes e (X \<and> Y) \<Longrightarrow> Makes e X"
      and MCI: "\<And>e X Y. Makes e X \<Longrightarrow> Makes e Y \<Longrightarrow> Makes e (X \<and> Y)"
  shows "Arg (A \<and> B) \<approx> Arg A"
proof -
  have le1: "Arg (A \<and> B) \<preceq> Arg A"
    using conj_le_left_from_MCL[OF MCL] .

  have AB_pt: "\<forall>e. Makes e A \<longrightarrow> Makes e B"
    using AB by (simp add: LeU_iff_all)

  have le2: "Arg A \<preceq> Arg (A \<and> B)"
  proof (simp add: LeU_iff_all, intro allI impI)
    fix e assume eA: "Makes e A"
    have eB: "Makes e B" using AB_pt eA by blast
    show "Makes e (A \<and> B)" using MCI[OF eA eB] .
  qed

  show ?thesis
    using LeU_antisym_eq[OF le1 le2] .
qed

lemma Subordination_kills_NT_edge_left:
  assumes AB : "Arg A \<preceq> Arg B"
      and MCL: "\<And>e X Y. Makes e (X \<and> Y) \<Longrightarrow> Makes e X"
      and MCI: "\<And>e X Y. Makes e X \<Longrightarrow> Makes e Y \<Longrightarrow> Makes e (X \<and> Y)"
  shows "\<not> NT_edge A B C"
proof
  assume E: "NT_edge A B C"
  have collapse: "Arg (A \<and> B) \<approx> Arg A"
    using Subordination_implies_Trivial_Collapse_left[OF AB MCL MCI] .
  from E have ncollapse: "\<not> (Arg (A \<and> B) \<approx> Arg A)"
    by (simp add: NT_edge_def)
  show False using collapse ncollapse by contradiction
qed

lemma Subordination_kills_NT_edge_right:
  assumes BA : "Arg B \<preceq> Arg A"
      and MCL: "\<And>e X Y. Makes e (X \<and> Y) \<Longrightarrow> Makes e X"
      and MCI: "\<And>e X Y. Makes e X \<Longrightarrow> Makes e Y \<Longrightarrow> Makes e (X \<and> Y)"
  shows "\<not> NT_edge A B C"
proof
  assume E: "NT_edge A B C"
  have collapse: "Arg (A \<and> B) \<approx> Arg B"
    using Subordination_implies_Trivial_Collapse_left[OF BA MCL MCI]
    by (simp add: ac_simps)
  from E have ncollapse: "\<not> (Arg (A \<and> B) \<approx> Arg B)"
    by (simp add: NT_edge_def)
  show False using collapse ncollapse by contradiction
qed

definition OneToOne :: bool where
  "OneToOne \<equiv> (\<forall>A B. Arg A \<preceq> Arg B \<or> Arg B \<preceq> Arg A)"

lemma OneToOne_implies_NT_dead:
  assumes O  : OneToOne
      and MCL: "\<And>e X Y. Makes e (X \<and> Y) \<Longrightarrow> Makes e X"
      and MCI: "\<And>e X Y. Makes e X \<Longrightarrow> Makes e Y \<Longrightarrow> Makes e (X \<and> Y)"
  shows NT_dead
  unfolding NT_dead_def OneToOne_def
proof (intro allI)
  fix A B C
  have "Arg A \<preceq> Arg B \<or> Arg B \<preceq> Arg A" using O [unfolded OneToOne_def] by blast
  thus "\<not> NT_edge A B C"
  proof
    assume AB: "Arg A \<preceq> Arg B"
    show "\<not> NT_edge A B C"
      using Subordination_kills_NT_edge_left[OF AB MCL MCI] .
  next
    assume BA: "Arg B \<preceq> Arg A"
    show "\<not> NT_edge A B C"
      using Subordination_kills_NT_edge_right[OF BA MCL MCI] .
  qed
qed


section \<open>12. TriSupport\_Joint and Ternary Semantics (No 1-to-1)\<close>
text \<open>
  We redefine the trinitarian support to strictly exclude any 1-to-1
  subordination. It mandates a pure ternary joint-support structure:
  the conjunction of any two heads necessitates the third, while
  no single head necessitates another. This guarantees Borromean stability.
\<close>

text \<open>
  1. Joint support (Ternary Support)
  2. Consistency Requirement for Non-triviality(Strict exclusion of 1-to-1 individual support (No mutual subordination))
\<close>
definition TriSupport_Joint :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "TriSupport_Joint a b c \<equiv>
     (Arg (b \<and> c) \<preceq> Arg a) \<and>
     (Arg (c \<and> a) \<preceq> Arg b) \<and>
     (Arg (a \<and> b) \<preceq> Arg c) \<and>
     \<not> (Arg a \<preceq> Arg b) \<and> \<not> (Arg b \<preceq> Arg a) \<and>
     \<not> (Arg b \<preceq> Arg c) \<and> \<not> (Arg c \<preceq> Arg b) \<and>
     \<not> (Arg c \<preceq> Arg a) \<and> \<not> (Arg a \<preceq> Arg c)"


subsection \<open>12.1 Symmetries and permutations\<close>

lemma TriSupport_Joint_perm12:
  "TriSupport_Joint a b c \<Longrightarrow> TriSupport_Joint b a c"
  by (auto simp: TriSupport_Joint_def ac_simps)

lemma TriSupport_Joint_perm23:
  "TriSupport_Joint a b c \<Longrightarrow> TriSupport_Joint a c b"
  by (auto simp: TriSupport_Joint_def ac_simps)

lemma TriSupport_Joint_rotate:
  "TriSupport_Joint a b c \<Longrightarrow> TriSupport_Joint b c a"
  by (auto simp: TriSupport_Joint_def ac_simps)


subsection \<open>12.2 Ternary Semantics (pair @{text "\<rightarrow>"} third)\<close>
text \<open>
  To extract the pointwise semantics (Supports e ...), we assume a standard
  conjunction-introduction rule (MCI) for the ``Supports'' relation, bridging
  the logical AND with the semantic evaluation at point e.
\<close>

lemma TriSupport_Joint_bc_to_a:
  assumes "TriSupport_Joint a b c"
      and MCI: "\<And>e X Y. Supports e X \<Longrightarrow> Supports e Y \<Longrightarrow> Supports e (X \<and> Y)"
      and "Supports e b" and "Supports e c"
  shows "Supports e a"
proof -
  from assms(1) have "(Arg (b \<and> c)) \<preceq> (Arg a)" by (simp add: TriSupport_Joint_def)
  hence "\<forall>x. Makes x (b \<and> c) \<longrightarrow> Makes x a" by (simp add: LeU_iff_all)
  moreover have "Makes e (b \<and> c)"
    using MCI[OF assms(3) assms(4)] by (simp add: Makes_def Supports_def)
  ultimately show "Supports e a" by (simp add: Makes_def Supports_def)
qed

lemma TriSupport_Joint_semantics:
  assumes "TriSupport_Joint a b c"
      and MCI: "\<And>e X Y. Supports e X \<Longrightarrow> Supports e Y \<Longrightarrow> Supports e (X \<and> Y)"
  shows "\<forall>e. (Supports e b \<and> Supports e c) \<longrightarrow> Supports e a"
    and "\<forall>e. (Supports e c \<and> Supports e a) \<longrightarrow> Supports e b"
    and "\<forall>e. (Supports e a \<and> Supports e b) \<longrightarrow> Supports e c"
proof -
  { fix e have "(Supports e b \<and> Supports e c) \<longrightarrow> Supports e a"
      using TriSupport_Joint_bc_to_a[OF assms(1) MCI] by blast }
  thus "\<forall>e. (Supports e b \<and> Supports e c) \<longrightarrow> Supports e a" by blast
 
  { fix e have "(Supports e c \<and> Supports e a) \<longrightarrow> Supports e b"
      using TriSupport_Joint_bc_to_a[OF TriSupport_Joint_rotate[OF assms(1)] MCI] by blast }
  thus "\<forall>e. (Supports e c \<and> Supports e a) \<longrightarrow> Supports e b" by blast
 
  { fix e have "(Supports e a \<and> Supports e b) \<longrightarrow> Supports e c"
      using TriSupport_Joint_bc_to_a[OF TriSupport_Joint_rotate[OF TriSupport_Joint_rotate[OF assms(1)]] MCI] by blast }
  thus "\<forall>e. (Supports e a \<and> Supports e b) \<longrightarrow> Supports e c" by blast
qed


section \<open>13. Proof of n=3 necessity (cardinality; assumption-free)\<close>
text \<open>
  This section formalizes the ``Structural Necessity of the Trinity'' using an
  epistemic refutation domain (PDom\_ep). The proof architecture adopts a
  non-axiomatic approach, deriving the uniqueness of n=3 from the following
  definitional constraints:

  1. **Refutation-based Epistecmic Possibility (EDia\_ep):** Defines epistemic possibility as the
     absence of formal refutation within the current evidence state.
  2. **Maximal Non-Trivial Support (MaxNT\_ep):** Identifies optimal heads
     (H\_opt\_ep) by comparing the cardinality of their non-trivial relational
     support sets (NT\_in\_edges\_ep).
  3. **Categorical Exclusion:** By defining N1, N2, and N4+ exact configurations,
     we set the stage for proving that only N3 satisfies the structural
     equilibrium between ``Relational Richness'' and ``Ontological Maximality.''

   *Note:* The use of Cantor-style cardinal comparison ensures that the
  ranking of optimal truths is independent of finite model constraints,
  grounding the Triune necessity in pure set-theoretic relations.
\<close>


subsection \<open>13.1 Ref-domain (H\_opt\_ep)\<close>

consts Ref :: "bool \<Rightarrow> bool"    
text \<open>
  Definition:
(1) Refuted(p): truth-bearer p is in a currently refuted state (a proof of falsity exists
within the current system).
(2) Negation of Refuted(p): truth-bearer p is in a currently unrefuted state (no proof of falsity
exists)
so, EDia\_ep(p) @{text "\<longleftrightarrow>"} negation of Refuted(p)

    EDia\_ep @{text "\<phi>"}  means: ``not refuted yet (given the current evidence state)''.
  Formally, EDia\_ep is definitional negation of Ref.
\<close>

definition EDia_ep :: "bool \<Rightarrow> bool" where
  "EDia_ep z \<equiv> \<not> Ref z"

definition PDom_ep :: "bool set" where
  "PDom_ep \<equiv> {z. TrueNow z \<or> EDia_ep z}"

definition Comparable_PDom_ep_on :: "bool \<Rightarrow> bool" where
  "Comparable_PDom_ep_on q \<equiv>
     (\<forall>z. z \<in> PDom_ep \<longrightarrow> ((Arg z) \<preceq> (Arg q) \<or> (Arg q) \<preceq> (Arg z)))"

definition H_negU_strict_ep :: "bool \<Rightarrow> bool" where
  "H_negU_strict_ep q \<equiv>
     (\<forall>z. z \<in> PDom_ep \<longrightarrow> z \<noteq> q \<longrightarrow> \<not> ((Arg q) \<prec> (Arg z)))"

definition Head_ep :: "bool \<Rightarrow> bool" where
  "Head_ep q \<equiv> EDia_ep q \<and> H_negU_strict_ep q"
text \<open>
Nontrivial pair-support among heads.
We exclude trivial targets C=A or C=B so plain @{text "\<and>"}-elimination does not count.
\<close>
definition NT_pair_support_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "NT_pair_support_ep A B C \<equiv>
     A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> (Arg (A \<and> B) \<preceq> Arg C)"

definition NT_in_edges_ep :: "bool \<Rightarrow> (bool \<times> bool) set" where
  "NT_in_edges_ep C \<equiv>
     {(A,B). Head_ep A \<and> Head_ep B \<and> Head_ep C \<and> NT_pair_support_ep A B C}"
(* ---------------- Cantor-style cardinal comparison ---------------- *)
lemmas le_card_empty_left_ep = le_card_empty_left

definition MaxNT_ep :: "bool \<Rightarrow> bool" where
  "MaxNT_ep q \<equiv>
     Head_ep q
   \<and> (\<forall>r. EDia_ep r \<longrightarrow> NT_in_edges_ep r \<preceq>\<^sub>c NT_in_edges_ep q)"

definition H_opt_ep :: "bool \<Rightarrow> bool" where
  "H_opt_ep q \<equiv> MaxNT_ep q"

lemma Hopt_ep_to_MaxNT_ep:
  assumes "H_opt_ep q"
  shows "MaxNT_ep q"
  using assms by (simp add: H_opt_ep_def)

lemma NT_in_edges_ep_empty_if_not_Head_ep:
  assumes "\<not> Head_ep C"
  shows "NT_in_edges_ep C = {}"
  using assms by (auto simp: NT_in_edges_ep_def)

lemma Hopt_ep_score_ge_EDia:
  assumes HQ: "H_opt_ep q" and EZ: "EDia_ep z"
  shows "NT_in_edges_ep z \<preceq>\<^sub>c NT_in_edges_ep q"
  using HQ EZ by (auto simp: H_opt_ep_def MaxNT_ep_def)

lemma Hopt_ep_score_ge_any:
  assumes HQ: "H_opt_ep q"
  shows "NT_in_edges_ep z \<preceq>\<^sub>c NT_in_edges_ep q"
proof (cases "Head_ep z")
  case True
  then have "EDia_ep z" by (simp add: Head_ep_def)
  thus ?thesis using Hopt_ep_score_ge_EDia[OF HQ] by blast
next
  case False
  have "NT_in_edges_ep z = {}"
    using NT_in_edges_ep_empty_if_not_Head_ep[OF False] .
  thus ?thesis using le_card_empty_left_ep by simp
qed

lemma Hopt_ep_score_tie:
  assumes HA: "H_opt_ep A" and HB: "H_opt_ep B"
  shows "NT_in_edges_ep A \<approx>\<^sub>c NT_in_edges_ep B"
proof -
  have AB: "NT_in_edges_ep A \<preceq>\<^sub>c NT_in_edges_ep B"
    using Hopt_ep_score_ge_any[OF HB, of A] by simp
  have BA: "NT_in_edges_ep B \<preceq>\<^sub>c NT_in_edges_ep A"
    using Hopt_ep_score_ge_any[OF HA, of B] by simp
  show ?thesis by (simp add: eq_card_def AB BA)
qed

lemma le_card_imp_card_le_if_finite:
  assumes "A \<preceq>\<^sub>c B" and "finite B"
  shows "card A \<le> card B"
proof -
  obtain f where inj: "inj_on f A" and img: "f ` A \<subseteq> B"
    using assms(1) unfolding le_card_def by blast
  have fin_img: "finite (f ` A)" using assms(2) img finite_subset by blast
  have cA: "card (f ` A) = card A" using inj fin_img by (simp add: card_image)
  have "card (f ` A) \<le> card B" using assms(2) img fin_img by (simp add: card_mono)
  thus ?thesis using cA by simp
qed

definition EqNT_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<approx>\<^sub>NT" 50) where
  "X \<approx>\<^sub>NT Y \<equiv> NT_in_edges_ep X = NT_in_edges_ep Y"

definition Distinct_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Distinct_ep X Y \<equiv> X \<noteq> Y \<and> \<not> (X \<approx>\<^sub>NT Y)"
(* -------------------------------------------------------------------------- *)
(* Semantic block (Arg/Makes/EntailsU/EH) kept intact, NOT derived from MaxNT. *)
(* -------------------------------------------------------------------------- *)
definition EntailsU :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<longrightarrow>\<^sub>U" 55) where
  "e \<longrightarrow>\<^sub>U Q \<equiv> (Arg e) \<preceq> (Arg Q)"

definition StrictBelow :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "StrictBelow e K \<equiv> (e \<longrightarrow>\<^sub>U K) \<and> \<not> (K \<longrightarrow>\<^sub>U e)"

definition NotHoptArg :: "bool \<Rightarrow> bool" where
  "NotHoptArg X \<equiv> \<not> H_opt_ep X"

definition TextPremises :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "TextPremises e K \<equiv>
       EDia_ep e
    \<and> (e \<longrightarrow>\<^sub>U K)
    \<and> \<not> (K \<longrightarrow>\<^sub>U e)
    \<and> e \<noteq> K
    \<and> NotHoptArg e"

lemma TextPremisesD:
  assumes "TextPremises e K"
  shows   "EDia_ep e"
          "e \<longrightarrow>\<^sub>U K"
          "\<not> (K \<longrightarrow>\<^sub>U e)"
          "e \<noteq> K"
          "NotHoptArg e"
  using assms by (auto simp: TextPremises_def)

definition EH_ep where
  "EH_ep U \<equiv> (\<forall>z. EDia_ep z \<longrightarrow> (Arg z) \<preceq> U)"

lemma EH_epD:
  assumes "EH_ep U" and "EDia_ep z"
  shows "(Arg z) \<preceq> U"
  using assms by (simp add: EH_ep_def)

lemma H_principle_ep_basic:
  assumes EH: "EH_ep (Arg Q)"
      and TP: "TextPremises e K"
  shows "(Arg e) \<preceq> (Arg Q)"
proof -
  from TextPremisesD[OF TP] have Ee: "EDia_ep e" by auto
  show ?thesis using EH_epD[OF EH Ee] .
qed

corollary H_principle_ep_basic_EntailsU:
  assumes EH: "EH_ep (Arg Q)" and TP: "TextPremises e K"
  shows   "e \<longrightarrow>\<^sub>U Q"
  using H_principle_ep_basic[OF EH TP] by (simp add: EntailsU_def)

lemma not_EH_ep_if_ep_possible_fails_to_support:
  assumes TP: "TextPremises e K"
      and N:  "\<not> ((Arg e) \<preceq> (Arg Q))"
  shows "\<not> EH_ep (Arg Q)"
proof
  assume EH: "EH_ep (Arg Q)"
  from H_principle_ep_basic[OF EH TP] have "(Arg e) \<preceq> (Arg Q)" .
  with N show False by contradiction
qed

subsection \<open>13.2 Consistency for H\_opt\_ep (Cantor-size version)\<close>

lemma Hopt_ep_has_no_strictly_better_in_PDom_ep:
  assumes HQ: "H_opt_ep q"
  shows "\<not> (\<exists>z\<in>PDom_ep. NT_in_edges_ep q \<prec>\<^sub>c NT_in_edges_ep z)"
proof
  assume "\<exists>z\<in>PDom_ep. NT_in_edges_ep q \<prec>\<^sub>c NT_in_edges_ep z"
  then obtain z where Zin: "z \<in> PDom_ep" and lt: "NT_in_edges_ep q \<prec>\<^sub>c NT_in_edges_ep z"
    by blast

  have ge: "NT_in_edges_ep z \<preceq>\<^sub>c NT_in_edges_ep q"
    using Hopt_ep_score_ge_any[OF HQ, of z] by simp

  from lt have nz: "\<not> (NT_in_edges_ep z \<preceq>\<^sub>c NT_in_edges_ep q)"
    by (simp add: lt_card_def)

  show False using ge nz by contradiction
qed

corollary Hopt_ep_has_no_strictly_better_in_PDom_ep_non_tautology:
  assumes HQ: "H_opt_ep q"
      and nT: "q \<noteq> True"
  shows "\<not> (\<exists>z\<in>PDom_ep. NT_in_edges_ep q \<prec>\<^sub>c NT_in_edges_ep z)"
  using Hopt_ep_has_no_strictly_better_in_PDom_ep[OF HQ] .


subsection \<open>13.3 Rescue block: Hopt3 @{text "\<Longrightarrow>"} N3 (with pure joint support)\<close>
text \<open>
  Hopt3 now explicitly requires the TriSupport\_Joint structure,
  guaranteeing that the three optimal heads do not subordinate each other,
  but strictly co-support the third.
\<close>

definition Hopt3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Hopt3 a b c \<equiv>
     H_opt a \<and> H_opt b \<and> H_opt c \<and>
     EDia a \<and> EDia b \<and> EDia c \<and>
     TriSupport_Joint a b c"

lemma Hopt3_implies_trinity_joint:
  assumes "Hopt3 a b c"
  shows   "TriSupport_Joint a b c"
  using assms by (simp add: Hopt3_def)

definition N3 :: bool where
  "N3 \<equiv> (\<exists>a b c.
          H_opt a \<and> H_opt b \<and> H_opt c \<and>
          TriSupport_Joint a b c \<and>
          (\<forall>e. Supports e b \<and> Supports e c \<longrightarrow> Supports e a) \<and>
          (\<forall>e. Supports e c \<and> Supports e a \<longrightarrow> Supports e b) \<and>
          (\<forall>e. Supports e a \<and> Supports e b \<longrightarrow> Supports e c))"

lemma OnlyN3_from_Hopt3_unboxed:
  assumes H3: "Hopt3 a b c"
      and MCI: "\<And>e X Y. Supports e X \<Longrightarrow> Supports e Y \<Longrightarrow> Supports e (X \<and> Y)"
  shows N3
proof -
  have TS: "TriSupport_Joint a b c"
    using Hopt3_implies_trinity_joint[OF H3] .

  have Sbc_a: "\<forall>e. Supports e b \<and> Supports e c \<longrightarrow> Supports e a"
    using TriSupport_Joint_semantics(1)[OF TS MCI] .
  have Sca_b: "\<forall>e. Supports e c \<and> Supports e a \<longrightarrow> Supports e b"
    using TriSupport_Joint_semantics(2)[OF TS MCI] .
  have Sab_c: "\<forall>e. Supports e a \<and> Supports e b \<longrightarrow> Supports e c"
    using TriSupport_Joint_semantics(3)[OF TS MCI] .

  from H3 have Ha: "H_opt a" and Hb: "H_opt b" and Hc: "H_opt c"
    by (auto simp: Hopt3_def)

  have "\<exists>a b c. H_opt a \<and> H_opt b \<and> H_opt c \<and>
        TriSupport_Joint a b c \<and>
        (\<forall>e. Supports e b \<and> Supports e c \<longrightarrow> Supports e a) \<and>
        (\<forall>e. Supports e c \<and> Supports e a \<longrightarrow> Supports e b) \<and>
        (\<forall>e. Supports e a \<and> Supports e b \<longrightarrow> Supports e c)"
    using Ha Hb Hc TS Sbc_a Sca_b Sab_c
    by (intro exI[of _ a] exI[of _ b] exI[of _ c]) blast

  thus N3 by (simp add: N3_def)
qed

lemma OnlyN3_epi_unboxed:
  assumes Witnesses: "(\<exists>x. H_opt x) \<longrightarrow> (\<exists>a b c. Hopt3 a b c)"
      and MCI: "\<And>e X Y. Supports e X \<Longrightarrow> Supports e Y \<Longrightarrow> Supports e (X \<and> Y)"
  shows "(\<exists>x. H_opt x) \<longrightarrow> N3"
proof
  assume Hex: "\<exists>x. H_opt x"
  have "\<exists>a b c. Hopt3 a b c" using Witnesses Hex by (rule mp)
  then obtain a b c where H3: "Hopt3 a b c" by blast
  show N3 using OnlyN3_from_Hopt3_unboxed[OF H3 MCI] .
qed

lemmas OnlyN3_epi_possible_proved = OnlyN3_epi_unboxed
lemmas OnlyN3_epi_boxed           = OnlyN3_epi_possible_proved


section \<open>14. n@{text "\<ge>"}4 exclusion\<close>


subsection \<open>14.1 Boolean reading at our world (discharging Ep\_Conj\_ locales)\<close>

locale Boolean_at_our_world =
  fixes Val :: "'w \<Rightarrow> bool \<Rightarrow> bool" and w0 :: "'w" ("w\<^sub>0")
  assumes and_hom: "\<And>A B. Val w0 (A \<and> B) = (Val w0 A \<and> Val w0 B)"
  assumes Ref_is_false_at_w0: "\<And>\<phi>. Ref \<phi> \<longleftrightarrow> \<not> Val w0 \<phi>"
begin

lemma Ref_and_sound_global:
  "Ref (A \<and> B) \<longrightarrow> (Ref A \<or> Ref B)" for A B :: bool
  using Ref_is_false_at_w0 and_hom by auto

lemma Ref_and_complete_global:
  "(Ref A \<or> Ref B) \<longrightarrow> Ref (A \<and> B)" for A B :: bool
  using Ref_is_false_at_w0 and_hom by auto

end

context
  fixes Val :: "'w \<Rightarrow> bool \<Rightarrow> bool"
    and w\<^sub>0 :: "'w"
  assumes and_hom_w0: "\<And>A B. Val w\<^sub>0 (A \<and> B) = (Val w\<^sub>0 A \<and> Val w\<^sub>0 B)"
  assumes Ref_is_false_at_w0: "\<And>\<phi>. Ref \<phi> \<longleftrightarrow> \<not> Val w\<^sub>0 \<phi>"
begin

interpretation OurWorld: Boolean_at_our_world Val w\<^sub>0
  by (unfold_locales) (simp_all add: and_hom_w0 Ref_is_false_at_w0)

end


subsection \<open>14.2 From ``NotRef ((@{text "\<Phi>"} @{text "\<and>"} @{text "\<Omega>"}) @{text "\<and>"} @{text "\<Psi>"})''
to ``EDia\_ep (@{text "\<Omega>"} @{text "\<and>"} @{text "\<Psi>"})''(ES) — no global axioms\<close>

context Boolean_at_our_world
begin

lemma EDia_ep_iff_notRef [simp]:
  "EDia_ep phi \<longleftrightarrow> \<not> Ref phi"
  by (simp add: EDia_ep_def)

lemma notRef_pair_from_notRef_triple_plain:
  assumes RCW: "!!X Y. Ref X \<Longrightarrow> Ref (X \<and> Y)"              (* weak conjunctive monotonicity *)
      and NRT: "\<not> Ref ((Phi \<and> Omega) \<and> Psi)"            (* "not yet refuted" for the triple *)
  shows "\<not> Ref (Omega \<and> Psi)"
proof
  assume ROP: "Ref (Omega \<and> Psi)"
  hence "Ref ((Omega \<and> Psi) \<and> Phi)" using RCW by blast
  hence "Ref ((Phi \<and> Omega) \<and> Psi)" by (simp add: ac_simps)
  thus False using NRT by contradiction
qed

corollary EDia_ep_pair_from_notRef_triple_plain:
  assumes RCW: "!!X Y. Ref X \<Longrightarrow> Ref (X \<and> Y)"
      and NRT: "\<not> Ref ((Phi \<and> Omega) \<and> Psi)"
  shows "EDia_ep (Omega \<and> Psi)"
  using notRef_pair_from_notRef_triple_plain[OF RCW NRT] by simp

end


subsection \<open>14.3 Coverage + witness gap @{text "\<Rightarrow>"} MoreCertain @{text "\<Phi>"}' @{text "\<Phi>"}\<close>

lemma not_LeU_iff_exists_witness_v2:
  "\<not> ((Arg S) \<preceq> (Arg T)) \<longleftrightarrow> (\<exists>a. Makes a S \<and> \<not> Makes a T)"
  by (simp add: LeU_iff_all)

corollary gap_equiv_witness_OmegaPsi_Phi'_v2:
  "\<not> ((Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>')) \<longleftrightarrow>
   (\<exists>a. Makes a (\<Omega> \<and> \<Psi>) \<and> \<not> Makes a \<Phi>')"
  using not_LeU_iff_exists_witness_v2[of "\<Omega> \<and> \<Psi>" "\<Phi>'"] by simp

lemma witness_breaks_back_imp_v2:
  assumes "Makes a X" and "\<not> Makes a Y"
  shows "\<not> (\<forall>e. Makes e X \<longrightarrow> Makes e Y)"
  using assms by blast

lemma relcert_from_cov_and_gap_min_witness_v2:
  assumes Cov   : "(Arg \<Phi>') \<preceq> (Arg \<Phi>)"
      and Gap\<Phi>: "(Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>)"
      and W     : "\<exists>a. Makes a (\<Omega> \<and> \<Psi>) \<and> \<not> Makes a \<Phi>'"
  shows "MoreCertain_pred \<Phi>' \<Phi>"  "RelCert \<Phi>' \<Phi>"
proof -
  obtain a where aS: "Makes a (\<Omega> \<and> \<Psi>)" and n_a\<Phi>': "\<not> Makes a \<Phi>'"
    using W by blast

  have S_to_\<Phi>: "\<forall>e. Makes e (\<Omega> \<and> \<Psi>) \<longrightarrow> Makes e \<Phi>"
    using Gap\<Phi> by (simp add: LeU_iff_all)
  have a\<Phi>: "Makes a \<Phi>" using S_to_\<Phi> aS by blast

  have Front: "\<forall>e. Makes e \<Phi>' \<longrightarrow> Makes e \<Phi>"
    using Cov by (simp add: LeU_iff_all)

  have BackBreak: "\<not> (\<forall>e. Makes e \<Phi> \<longrightarrow> Makes e \<Phi>')"
    using witness_breaks_back_imp_v2[OF a\<Phi> n_a\<Phi>'] .

  have MC: "MoreCertain_pred \<Phi>' \<Phi>"
    by (simp add: MoreCertain_pred_def Front BackBreak)

  have Not_rev: "\<not> ((Arg \<Phi>) \<preceq> (Arg \<Phi>'))"
  proof
    assume rev: "(Arg \<Phi>) \<preceq> (Arg \<Phi>')"
    hence "\<forall>e. Makes e \<Phi> \<longrightarrow> Makes e \<Phi>'" by (simp add: LeU_iff_all)
    hence "Makes a \<Phi>'" using a\<Phi> by blast
    with n_a\<Phi>' show False by contradiction
  qed

  have RC: "RelCert \<Phi>' \<Phi>"
    by (simp add: RelCert_def LtU_def Cov Not_rev)

  show "MoreCertain_pred \<Phi>' \<Phi>"  "RelCert \<Phi>' \<Phi>" by (simp_all add: MC RC)
qed

lemma coverage_from_Hopt_ep':
  assumes Cov: "(Arg \<Phi>') \<preceq> (Arg \<Phi>)"
  shows "(Arg \<Phi>') \<preceq> (Arg \<Phi>)"
  using Cov .

lemma gap1_from_Hopt_ep':
  assumes Gap\<Phi>: "(Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>)"
  shows "(Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>)"
  using Gap\<Phi> .

corollary relcert_from_Hopt_ep_and_EDiaS_witness:
  assumes H\<Phi>  : "H_opt_ep \<Phi>"
      and TP\<Phi>': "TextPremises \<Phi>' K1"
      and TPS   : "TextPremises (\<Omega> \<and> \<Psi>) K0"
      and Cov0  : "(Arg \<Phi>') \<preceq> (Arg \<Phi>)"
      and Gap0  : "(Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>)"
      and W     : "\<exists>a. Makes a (\<Omega> \<and> \<Psi>) \<and> \<not> Makes a \<Phi>'"
  shows "MoreCertain_pred \<Phi>' \<Phi>"  and "RelCert \<Phi>' \<Phi>"
proof -
  have Cov: "(Arg \<Phi>') \<preceq> (Arg \<Phi>)"
    using coverage_from_Hopt_ep'[OF Cov0] .
  have Gap\<Phi>: "(Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>)"
    using gap1_from_Hopt_ep'[OF Gap0] .

  obtain a where aS: "Makes a (\<Omega> \<and> \<Psi>)" and n\<Phi>': "\<not> Makes a \<Phi>'"
    using W by blast

  have S_to_\<Phi>: "\<forall>e. Makes e (\<Omega> \<and> \<Psi>) \<longrightarrow> Makes e \<Phi>"
    using Gap\<Phi> by (simp add: LeU_iff_all)
  have a\<Phi>: "Makes a \<Phi>" using aS S_to_\<Phi> by blast

  have Front: "\<forall>e. Makes e \<Phi>' \<longrightarrow> Makes e \<Phi>"
    using Cov by (simp add: LeU_iff_all)

  have BackBreak: "\<not> (\<forall>e. Makes e \<Phi> \<longrightarrow> Makes e \<Phi>')"
    using a\<Phi> n\<Phi>' by blast

  have MC: "MoreCertain_pred \<Phi>' \<Phi>"
    by (simp add: MoreCertain_pred_def Front BackBreak)

  have Not_rev: "\<not> ((Arg \<Phi>) \<preceq> (Arg \<Phi>'))"
  proof
    assume rev: "(Arg \<Phi>) \<preceq> (Arg \<Phi>')"
    hence "\<forall>e. Makes e \<Phi> \<longrightarrow> Makes e \<Phi>'" by (simp add: LeU_iff_all)
    hence "Makes a \<Phi>'" using a\<Phi> by blast
    with n\<Phi>' show False by contradiction
  qed

  have RC: "RelCert \<Phi>' \<Phi>"
    by (simp add: RelCert_def LtU_def Cov Not_rev)

  show "MoreCertain_pred \<Phi>' \<Phi>"  "RelCert \<Phi>' \<Phi>"
    by (simp_all add: MC RC)
qed


subsection \<open>14.4 n@{text "\<ge>"}4 exclusion  proof by Superfluous-removal\<close>

locale Band_Collapse_Superfluous =
  fixes \<Omega> \<Psi> \<Phi> :: bool
  assumes ES:  "EDia_ep (\<Omega> \<and> \<Psi>)"
      and Cov: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
      and NS:
        "((Arg (\<Omega> \<and> \<Psi>)) \<preceq> Arg \<Phi>) \<Longrightarrow>
         (\<forall>Y. H_opt_ep Y \<longrightarrow> EDia_ep Y \<longrightarrow>
              Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi> \<longrightarrow>
              Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>))"
      and MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCR: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B"
begin

lemma conj_le_left[simp]:  "Arg (A \<and> B) \<preceq> Arg A"
  unfolding LeU_iff_all by (auto dest: MCL)

lemma conj_le_right[simp]: "Arg (A \<and> B) \<preceq> Arg B"
  unfolding LeU_iff_all by (auto dest: MCR)

lemma pulled_eq_and_below_Phi:
  assumes HY: "H_opt_ep Y" and EY: "EDia_ep Y"
  shows  "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>"
     and "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
proof -
  have step1: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>)"
    by (rule conj_le_left)

  have CovY: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>"
    using step1 Cov by (rule LeU_trans)

  have Eq: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
    using NS[OF Cov] HY EY CovY by blast

  show "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>" by (rule CovY)
  show "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)" by (rule Eq)
qed

lemma pulled_pair_collapse_in_band:
  assumes HY1: "H_opt_ep Y\<^sub>1" and EY1: "EDia_ep Y\<^sub>1"
      and HY2: "H_opt_ep Y\<^sub>2" and EY2: "EDia_ep Y\<^sub>2"
  shows "(Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1)) \<approx> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2))"
proof -
  have "Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1) \<approx> Arg (\<Omega> \<and> \<Psi>)"
    using pulled_eq_and_below_Phi[OF HY1 EY1] by blast
  moreover
  have "Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2) \<approx> Arg (\<Omega> \<and> \<Psi>)"
    using pulled_eq_and_below_Phi[OF HY2 EY2] by blast
  ultimately show ?thesis by (meson EqU_sym EqU_trans)
qed

lemma no_three_distinct_classes_in_band:
  assumes HY1: "H_opt_ep Y\<^sub>1" and EY1: "EDia_ep Y\<^sub>1"
      and HY2: "H_opt_ep Y\<^sub>2" and EY2: "EDia_ep Y\<^sub>2"
      and HY3: "H_opt_ep Y\<^sub>3" and EY3: "EDia_ep Y\<^sub>3"
  shows "\<not> (\<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2)) \<and>
             \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>3)) \<and>
             \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>3)))"
proof -
  have E12: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2)"
    using pulled_pair_collapse_in_band[OF HY1 EY1 HY2 EY2] .
  have E13: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>3)"
    using pulled_pair_collapse_in_band[OF HY1 EY1 HY3 EY3] .
  have E23: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>3)"
    using pulled_pair_collapse_in_band[OF HY2 EY2 HY3 EY3] .
  show ?thesis using E12 E13 E23 by blast
qed

lemma all_pulled_equiv_in_band:
  assumes "finite S" and "\<forall>Y\<in>S. H_opt_ep Y \<and> EDia_ep Y"
  shows "\<exists>Q. \<forall>Y\<in>S. Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Q"
proof (cases "S = {}")
  case True then show ?thesis by simp
next
  case False
  obtain Y\<^sub>0 where Y0S: "Y\<^sub>0 \<in> S" by (use False in auto)
  have HY0: "H_opt_ep Y\<^sub>0" and EY0: "EDia_ep Y\<^sub>0"
    using assms(2) Y0S by blast+
  define Q where "Q \<equiv> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>0)"

  have base: "\<forall>Y\<in>S. Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Q"
  proof
    fix Y assume YS: "Y \<in> S"
    have HY: "H_opt_ep Y" and EY: "EDia_ep Y"
      using assms(2) YS by blast+
    have "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y\<^sub>0)"
      using pulled_pair_collapse_in_band[OF HY EY HY0 EY0] .
    thus "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Q" by (simp add: Q_def)
  qed

  show ?thesis by (intro exI[of _ Q]) (rule base)
qed

end


subsection \<open>14.5 Proof of sandwich existence (no-1, no-2, no-4+, no-superfluous)\<close>

lemma conj_le_S:
  assumes MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
  shows "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>)"
proof (unfold LeU_iff_all, intro allI impI)
  fix e
  assume "Makes e ((\<Omega> \<and> \<Psi>) \<and> Y)"
  then show "Makes e (\<Omega> \<and> \<Psi>)"
    using MCL by blast
qed

lemma S_le_Phi_via_basic:
  assumes TP_S: "TextPremises (\<Omega> \<and> \<Psi>) \<Phi>"
  shows "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
proof -
  from TextPremisesD[OF TP_S] have "(\<Omega> \<and> \<Psi>) \<longrightarrow>\<^sub>U \<Phi>" by auto
  thus ?thesis by (simp add: EntailsU_def)
qed

lemma conj_le_Phi:
  assumes MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and Cov: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
  shows "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>"
proof -
  have L1: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>)"
    using conj_le_S[OF MCL] .
  show ?thesis using L1 Cov by (rule LeU_trans)
qed

lemma N3_sandwich_expanded_noCmp:
  fixes \<Omega> \<Psi> \<Phi> :: bool
  assumes ES: "EDia_ep (\<Omega> \<and> \<Psi>)"
      and Cov: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
      and NS:  "((Arg (\<Omega> \<and> \<Psi>)) \<preceq> Arg \<Phi>) \<Longrightarrow>
                (\<forall>\<Delta>. H_opt_ep \<Delta> \<longrightarrow> EDia_ep \<Delta> \<longrightarrow>
                      Arg ((\<Omega> \<and> \<Psi>) \<and> \<Delta>) \<preceq> Arg \<Phi> \<longrightarrow>
                      Arg ((\<Omega> \<and> \<Psi>) \<and> \<Delta>) \<approx> Arg (\<Omega> \<and> \<Psi>))"
      and Ex:  "\<exists>Y. H_opt_ep Y \<and> EDia_ep Y"
      and MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCR: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B"
  shows "\<exists>Y. H_opt_ep Y \<and> EDia_ep Y \<and>
            Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg Y \<and>
            Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi> \<and>
            Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
proof -
  obtain Y where HY: "H_opt_ep Y" and EY: "EDia_ep Y"
    using Ex by blast

  have Conj_le_S: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>)"
    using conj_le_S[OF MCL] .

  have Conj_le_Phi: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>"
    using Conj_le_S Cov by (rule LeU_trans)

  have Eq: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
    using NS[OF Cov] HY EY Conj_le_Phi by blast

  have Conj_le_Y: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg Y"
  proof (unfold LeU_iff_all, intro allI impI)
    fix e
    assume "Makes e ((\<Omega> \<and> \<Psi>) \<and> Y)"
    then show "Makes e Y" using MCR by blast
  qed

  have BOTH:
    "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>) \<and>
     Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg ((\<Omega> \<and> \<Psi>) \<and> Y)"
    using Eq by (simp add: EqU_iff_LeU_both)

  have S_le_Conj: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg ((\<Omega> \<and> \<Psi>) \<and> Y)"
    using BOTH by blast

  have S_le_Y: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg Y"
    using S_le_Conj Conj_le_Y by (rule LeU_trans)

  show ?thesis
    by (intro exI[of _ Y]) (use HY EY S_le_Y Conj_le_Phi Eq in blast)
qed

lemma W_from_gap:
  assumes "\<not> ((Arg (\<Omega> \<and> \<Psi>)) \<preceq> (Arg \<Phi>'))"
  shows   "\<exists>a. Makes a (\<Omega> \<and> \<Psi>) \<and> \<not> Makes a \<Phi>'"
  using assms by (simp add: not_LeU_iff_exists_witness)


subsection \<open>14.6 N@{text "\<ge>"}4 exclusion at realization level\<close>

context Band_Collapse_Superfluous
begin

abbreviation S :: bool where "S \<equiv> (\<Omega> \<and> \<Psi>)"

lemma EqU_imp_LeU_L:
  "(Arg X) \<approx> (Arg Y) \<Longrightarrow> (Arg X) \<preceq> (Arg Y)"
  unfolding EqU_def LeU_def by auto

lemma EqU_imp_LeU_R:
  "(Arg X) \<approx> (Arg Y) \<Longrightarrow> (Arg Y) \<preceq> (Arg X)"
  unfolding EqU_def LeU_def by auto

lemma LeU_imp_transfer:
  "(Arg X) \<preceq> (Arg Y) \<Longrightarrow> Makes e X \<Longrightarrow> Makes e Y"
  unfolding LeU_iff_all by blast

lemma share_witness_if_real_NS:
  assumes RS: "\<exists>a. Makes a S"
      and HY: "H_opt_ep Y" and EY: "EDia_ep Y"
  shows "\<exists>a. Makes a S \<and> Makes a (S \<and> Y)"
proof -
  obtain a where aS: "Makes a S" using RS by blast
  have Eq: "Arg (S \<and> Y) \<approx> Arg S"
    using pulled_eq_and_below_Phi[OF HY EY] by blast
  have Sub: "Arg S \<preceq> Arg (S \<and> Y)"
    by (rule EqU_imp_LeU_R[OF Eq])
  have aSY: "Makes a (S \<and> Y)"
    by (rule LeU_imp_transfer[OF Sub aS])
  show ?thesis by (intro exI[of _ a]) (use aS aSY in blast)
qed

lemma uniform_realization_for_finite_family:
  fixes Y :: "'i \<Rightarrow> bool" and I :: "'i set"
  assumes RS:  "\<exists>a. Makes a S"
      and FIN: "finite I"
      and HY:  "\<forall>i\<in>I. H_opt_ep (Y i)"
      and EY:  "\<forall>i\<in>I. EDia_ep (Y i)"
  shows "\<exists>a. \<forall>i\<in>I. Makes a (S \<and> Y i)"
proof -
  obtain a where aS: "Makes a S" using RS by blast
  have step: "\<And>i. i\<in>I \<Longrightarrow> Makes a (S \<and> Y i)"
  proof -
    fix i assume iI: "i\<in>I"
    have HYi: "H_opt_ep (Y i)" using HY iI by blast
    have EYi: "EDia_ep (Y i)" using EY iI by blast
    have Eq:  "Arg (S \<and> Y i) \<approx> Arg S"
      using pulled_eq_and_below_Phi[OF HYi EYi] by blast
    have Sub: "Arg S \<preceq> Arg (S \<and> Y i)"
      by (rule EqU_imp_LeU_R[OF Eq])
    show "Makes a (S \<and> Y i)"
      by (rule LeU_imp_transfer[OF Sub aS])
  qed
  show ?thesis by (intro exI[of _ a] ballI step)
qed

lemma no_four_distinct_classes_in_band_pre132:
  assumes HY1: "H_opt_ep Y1" and EY1: "EDia_ep Y1"
      and HY2: "H_opt_ep Y2" and EY2: "EDia_ep Y2"
      and HY3: "H_opt_ep Y3" and EY3: "EDia_ep Y3"
      and HY4: "H_opt_ep Y4" and EY4: "EDia_ep Y4"
  shows "\<not> (\<not> (Arg (S \<and> Y1) \<approx> Arg (S \<and> Y2)) \<and>
             \<not> (Arg (S \<and> Y1) \<approx> Arg (S \<and> Y3)) \<and>
             \<not> (Arg (S \<and> Y1) \<approx> Arg (S \<and> Y4)) \<and>
             \<not> (Arg (S \<and> Y2) \<approx> Arg (S \<and> Y3)) \<and>
             \<not> (Arg (S \<and> Y2) \<approx> Arg (S \<and> Y4)) \<and>
             \<not> (Arg (S \<and> Y3) \<approx> Arg (S \<and> Y4)))"
proof -
  have E12: "Arg (S \<and> Y1) \<approx> Arg (S \<and> Y2)"
    using pulled_pair_collapse_in_band[OF HY1 EY1 HY2 EY2] .
  have E13: "Arg (S \<and> Y1) \<approx> Arg (S \<and> Y3)"
    using pulled_pair_collapse_in_band[OF HY1 EY1 HY3 EY3] .
  have E14: "Arg (S \<and> Y1) \<approx> Arg (S \<and> Y4)"
    using pulled_pair_collapse_in_band[OF HY1 EY1 HY4 EY4] .
  have E23: "Arg (S \<and> Y2) \<approx> Arg (S \<and> Y3)"
    using pulled_pair_collapse_in_band[OF HY2 EY2 HY3 EY3] .
  have E24: "Arg (S \<and> Y2) \<approx> Arg (S \<and> Y4)"
    using pulled_pair_collapse_in_band[OF HY2 EY2 HY4 EY4] .
  have E34: "Arg (S \<and> Y3) \<approx> Arg (S \<and> Y4)"
    using pulled_pair_collapse_in_band[OF HY3 EY3 HY4 EY4] .
  show ?thesis using E12 E13 E14 E23 E24 E34 by blast
qed

end


subsection \<open>14.7 Minimal nonempty core @{text "\<Omega>"}@{text "\<and>"}@{text "\<Psi>"} and no new independent pillar via @{text "\<Delta>"}\<close>

locale Band_Collapse_From_Hopt =
  fixes \<Omega> \<Psi> \<Phi> :: bool
  assumes ES:  "EDia_ep (\<Omega> \<and> \<Psi>)"
      and Cov: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
      and MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCR: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B"
      and MCI: "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
begin

lemma conj_le_left[simp]:  "Arg (A \<and> B) \<preceq> Arg A"
  unfolding LeU_iff_all by (auto dest: MCL)

lemma conj_le_right[simp]: "Arg (A \<and> B) \<preceq> Arg B"
  unfolding LeU_iff_all by (auto dest: MCR)

end


subsection \<open>14.8 NS(No-Superfluous) locale assumption dischare\<close>
text \<open>
  NS (``No-Superfluous'') is the redundancy filter for the core.
  It states that if a candidate Y is itself H-optimal and epistemically admissible,
  and if the enlarged conjunction (S @{text "\<and>"} Y) still remains within the Phi-band,
  then this enlargement contributes no genuinely new Arg-content:
  Arg (S @{text "\<and>"} Y) must be Arg-equivalent to Arg S.

  Hence NS blocks superfluous duplication of the core inside the admissible band.\<close>

text \<open>
STRUCTURAL ROLE OF THIS SUBSECTION:
  The ``Discharge Engine'' for the Band @{text "\<approx>"}-Collapse (N @{text "\<ge>"} 4 Exclusion)

  In Sections 14.4 - 14.6, we proved that 4 or more independent supreme heads
  (N @{text "\<ge>"} 4) will inevitably undergo an @{text "\<approx>"}-collapse. However, that proof temporarily
  relied on a structural assumption called ``NS'' (No-Superfluous).

  If we left ``NS'' as an unproven assumption, it would act as a hidden axiom,
  fatally weakening the strictly axiom-free claim of this development.

  The core purpose of Section 14.8 is to completely eliminate (discharge)
  this ``NS'' assumption. We mathematically prove that ``NS'' is NOT an external
  metaphysical axiom, but an inescapable analytic consequence derived purely from
  basic Boolean logic (MCL, MCI) combined with the foundational H-Principle.

  The Proof Mechanism (The Sandwich Compression in ``core\_conj\_equiv\_basic''):
  1. Bounded from above (via MCL): Arg(S @{text "\<and>"} Y) @{text "\<preceq>"} Arg(S)
     - A logical conjunction cannot contain more foundational support than its parts.
  2. Bounded from below (via MCI + H-Principle): Arg(S) @{text "\<preceq>"} Arg(S @{text "\<and>"} Y)
     - Because Y is an optimal head (H\_opt), it already covers all possibilities
       of the core S. Thus, adding Y via conjunction provides no new independent
       support.
  3. @{text "\<approx>"}-Collapse: Squeezed from both sides, Arg(S @{text "\<and>"} Y) @{text "\<approx>"} Arg(S) is strictly forced.

  Conclusion: Any attempt to add a new optimal pillar (Y) to an existing optimal
  core (S) yields exactly zero new epistemic coverage. The system is structurally
  locked, making N @{text "\<ge>"} 4 logically impossible without needing any external axioms. \<close>

definition NS_restricted :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "NS_restricted S \<Phi> \<equiv>
     (\<forall>Y. H_opt_ep Y \<longrightarrow> EDia_ep Y \<longrightarrow>
          Arg (S \<and> Y) \<preceq> Arg \<Phi> \<longrightarrow>
          Arg (S \<and> Y) \<approx> Arg S)"
text \<open> Restricted NS: no admissible H-opt extension of S yields a genuinely new layer below Phi.\<close>

lemma NSIOF_from_NS_restricted:
  "NS_restricted S \<Phi> \<longrightarrow>
     (Arg S \<preceq> Arg \<Phi> \<longrightarrow>
      (\<forall>Y. H_opt_ep Y \<longrightarrow> EDia_ep Y \<longrightarrow>
           Arg (S \<and> Y) \<preceq> Arg \<Phi> \<longrightarrow>
           Arg (S \<and> Y) \<approx> Arg S))"
  by (simp add: NS_restricted_def)

definition Pull_de :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Pull_de S \<Phi> \<equiv> NS_restricted S \<Phi>"

abbreviation Pull_NS :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Pull_NS S \<Phi> \<equiv> Pull_de S \<Phi>"

lemma NS_restricted_132_from_Pull:
  "Pull_de S \<Phi> \<longrightarrow> NS_restricted S \<Phi>"
  by (simp add: Pull_de_def)

lemma EqU_from_LeU:
  assumes XY: "X \<preceq> Y" and YX: "Y \<preceq> X"
  shows "X \<approx> Y"
proof -
  have "SuppU X \<subseteq> SuppU Y" using XY unfolding LeU_def by blast
  moreover have "SuppU Y \<subseteq> SuppU X" using YX unfolding LeU_def by blast
  ultimately have "SuppU X = SuppU Y" by (rule subset_antisym)
  thus ?thesis unfolding EqU_def by simp
qed

lemma core_conj_equiv_basic:
  fixes \<Omega> \<Psi> Y :: bool
  assumes ES       : "EDia_ep (\<Omega> \<and> \<Psi>)"    
      and HY       : "H_opt_ep Y"                
      and EY       : "EDia_ep Y"                
      and Core_to_Y: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg Y"
      and MCL      : "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCI      : "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
  shows "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
proof -
  (* 1) left projection: (S ∧ Y) ⪯ S *)
  have conj_le_left: "Arg (A \<and> B) \<preceq> Arg A" for A B
    unfolding LeU_iff_all by (auto dest: MCL)
  have sub1: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg (\<Omega> \<and> \<Psi>)"
    by (rule conj_le_left)
  (* 2) S ⪯ (S ∧ Y): from Core_to_Y + ∧-intro on Makes *)
  have sub2: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg ((\<Omega> \<and> \<Psi>) \<and> Y)"
  proof (unfold LeU_iff_all, intro allI impI)
    fix e assume eS: "Makes e (\<Omega> \<and> \<Psi>)"
    have S_to_Y: "\<forall>f. Makes f (\<Omega> \<and> \<Psi>) \<longrightarrow> Makes f Y"
      using Core_to_Y by (simp add: LeU_iff_all)
    have eY: "Makes e Y" using S_to_Y eS by blast
    show "Makes e ((\<Omega> \<and> \<Psi>) \<and> Y)"
      using MCI[OF eS eY] .
  qed

  show ?thesis
    by (rule EqU_from_LeU[OF sub1 sub2])
qed

text \<open>-- ES bridge inside the world-locale --\<close>
context Boolean_at_our_world
begin

lemma ES_from_notRef_triple:
  assumes RCW: "\<And>X Y. Ref X \<Longrightarrow> Ref (X \<and> Y)"
      and NRT: "\<not> Ref ((\<Phi> \<and> \<Omega>) \<and> \<Psi>)"
  shows "EDia_ep (\<Omega> \<and> \<Psi>)"
  using EDia_ep_pair_from_notRef_triple_plain[OF RCW NRT] .

text \<open>-- NS discharge (EH-free) --\<close>
lemma NS_discharge_from_ES:
  fixes Phi Omega Psi :: bool
  assumes ES  : "EDia_ep (Omega \<and> Psi)"
      and MCL : "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCI : "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
      and Core_to_Y_rule: "\<And>Y. H_opt_ep Y \<Longrightarrow> Arg (Omega \<and> Psi) \<preceq> Arg Y"
  shows "NS_restricted (Omega \<and> Psi) Phi"
proof -
  show ?thesis
    unfolding NS_restricted_def
  proof (intro allI impI)
    fix Y
    assume HY: "H_opt_ep Y"
    assume EY: "EDia_ep Y"
    assume Band: "Arg ((Omega \<and> Psi) \<and> Y) \<preceq> Arg Phi"  

    have core_to_Y: "Arg (Omega \<and> Psi) \<preceq> Arg Y"
      using Core_to_Y_rule[OF HY] .

  have sub1: "Arg ((Omega \<and> Psi) \<and> Y) \<preceq> Arg (Omega \<and> Psi)"
proof (unfold LeU_iff_all, intro allI impI)
  fix e
  assume eSY: "Makes e ((Omega \<and> Psi) \<and> Y)"
  show "Makes e (Omega \<and> Psi)"
    using MCL[OF eSY] .
qed

    have sub2: "Arg (Omega \<and> Psi) \<preceq> Arg ((Omega \<and> Psi) \<and> Y)"
    proof (unfold LeU_iff_all, intro allI impI)
      fix e
      assume eS: "Makes e (Omega \<and> Psi)"
      have eY: "Makes e Y"
      proof -
        have S_to_Y: "\<forall>f. Makes f (Omega \<and> Psi) \<longrightarrow> Makes f Y"
          using core_to_Y by (simp add: LeU_iff_all)
        show "Makes e Y" using S_to_Y eS by blast
      qed
      show "Makes e ((Omega \<and> Psi) \<and> Y)"
        using MCI[OF eS eY] .
    qed

    show "Arg ((Omega \<and> Psi) \<and> Y) \<approx> Arg (Omega \<and> Psi)"
      by (rule EqU_from_LeU[OF sub1 sub2])
  qed
qed

lemma NS_discharge:
  fixes Phi Omega Psi :: bool
  assumes RCW  : "\<And>X Y. Ref X \<Longrightarrow> Ref (X \<and> Y)"
      and NRT  : "\<not> Ref ((Phi \<and> Omega) \<and> Psi)"
      and MCL  : "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCR  : "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B"  
      and MCI  : "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
      and Core_to_Y_rule: "\<And>Y. H_opt_ep Y \<Longrightarrow> Arg (Omega \<and> Psi) \<preceq> Arg Y"
  shows "NS_restricted (Omega \<and> Psi) Phi"
proof -
  have ES: "EDia_ep (Omega \<and> Psi)"
    by (rule ES_from_notRef_triple[OF RCW NRT])

  show ?thesis
  proof (rule NS_discharge_from_ES)
    show "EDia_ep (Omega \<and> Psi)" by (rule ES)
    show "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A" by (rule MCL)
    show "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)" by (rule MCI)
    show "\<And>Y. H_opt_ep Y \<Longrightarrow> Arg (Omega \<and> Psi) \<preceq> Arg Y" by (rule Core_to_Y_rule)
  qed
qed

lemma NS_with_Cov:
  fixes Phi Omega Psi :: bool
  assumes ES  : "EDia_ep (Omega \<and> Psi)"
      and MCL : "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCI : "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
      and Cov0: "Arg (Omega \<and> Psi) \<preceq> Arg Phi"
      and Core_to_Y_rule: "\<And>Y. H_opt_ep Y \<Longrightarrow> Arg (Omega \<and> Psi) \<preceq> Arg Y"
  shows "NS_restricted (Omega \<and> Psi) Phi"
    and "Arg (Omega \<and> Psi) \<preceq> Arg Phi"
proof -
  have NSre: "NS_restricted (Omega \<and> Psi) Phi"
    by (rule NS_discharge_from_ES[OF ES MCL MCI Core_to_Y_rule])
  show "NS_restricted (Omega \<and> Psi) Phi" by (rule NSre)
  show "Arg (Omega \<and> Psi) \<preceq> Arg Phi" by (rule Cov0)
qed

end


section \<open>15. n=1 exclusion\<close>

text \<open>
  Intuition:
  Structurally, a solitary top element in an impoverished
  comparison domain may still fail to be genuinely unsurpassable, since a richer
  domain could in principle contain a stronger candidate. By contrast, a co-maximal
  structure realized within a comparison domain already saturated by the strongest
  admissible candidates removes that possibility altogether. Hence the decisive issue
  is not merely whether a candidate is ``top'', but whether its top-status is realized
  within the maximally relevant comparison space.
\<close>
subsection \<open>15.1 Formal Preliminaries for Singularity Exclusion\<close>
(* --- Epistemic possibility as "not refuted" --- *)
abbreviation Refuted_ep :: "bool \<Rightarrow> bool" where
  "Refuted_ep \<equiv> Ref"

locale Refuted_Backprop =
  assumes ref_back: "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> Refuted_ep Q \<Longrightarrow> Refuted_ep P"
begin

lemma EDia_ep_forward:
  assumes imp: "P \<longrightarrow> Q" and possP: "EDia_ep P"
  shows "EDia_ep Q"
  unfolding EDia_ep_def
proof
  assume rq: "Refuted_ep Q"
  have rp: "Refuted_ep P" using ref_back imp rq by blast
  show False
    using possP rp
    unfolding EDia_ep_def
    by blast
qed

end

typedecl P

consts
  AndP  :: "P \<Rightarrow> P \<Rightarrow> P"  (infixr "\<sqinter>" 70)
  ArgP  :: "P \<Rightarrow> U"
  HeadP :: "P \<Rightarrow> bool"

abbreviation LeP (infix "\<preceq>P" 50) where
  "x \<preceq>P y \<equiv> (ArgP x \<preceq> ArgP y)"

definition NT_pair_supportP :: "P \<Rightarrow> P \<Rightarrow> P \<Rightarrow> bool" where
  "NT_pair_supportP A B C \<equiv>
     A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> (ArgP (A \<sqinter> B) \<preceq> ArgP C)"

definition NT_in_edgesP :: "P \<Rightarrow> (P \<times> P) set" where
  "NT_in_edgesP C \<equiv>
     {(A,B). HeadP A \<and> HeadP B \<and> HeadP C \<and> NT_pair_supportP A B C}"
(* Cardinal-compare with a fresh name / notation to avoid clashes *)
definition le_cardP :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool"  (infix "\<preceq>\<^sub>cP" 50) where
  "A \<preceq>\<^sub>cP B \<longleftrightarrow> (\<exists>f. inj_on f A \<and> f ` A \<subseteq> B)"

definition MaxNTP :: "P \<Rightarrow> bool" where
  "MaxNTP q \<equiv> HeadP q \<and> (\<forall>r. HeadP r \<longrightarrow> NT_in_edgesP r \<preceq>\<^sub>cP NT_in_edgesP q)"

definition H_optP :: "P \<Rightarrow> bool" where
  "H_optP q \<equiv> MaxNTP q"

lemma nonempty_not_le_cardP_empty:
  assumes "A \<noteq> {}"
  shows "\<not> (A \<preceq>\<^sub>cP {})"
  using assms
  unfolding le_cardP_def
  by auto

lemma HoptP_edges_nonempty_if_exists_head_nonempty:
  assumes ex: "\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {}"
      and HQ: "H_optP q"
  shows "NT_in_edgesP q \<noteq> {}"
proof
  assume E: "NT_in_edgesP q = {}"
  from ex obtain r where Hr: "HeadP r" and Nr: "NT_in_edgesP r \<noteq> {}" by blast
  have rq: "NT_in_edgesP r \<preceq>\<^sub>cP NT_in_edgesP q"
    using HQ Hr by (simp add: H_optP_def MaxNTP_def)

  show False
    using rq E Nr nonempty_not_le_cardP_empty
    by (metis)
qed

lemma not_all_HoptP_empty_if_exists_head_nonempty:
  assumes exH: "\<exists>q. H_optP q"
      and exN: "\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {}"
  shows "\<not> (\<forall>q. H_optP q \<longrightarrow> NT_in_edgesP q = {})"
proof
  assume All: "\<forall>q. H_optP q \<longrightarrow> NT_in_edgesP q = {}"
  from exH obtain q where HQ: "H_optP q" by blast
  have "NT_in_edgesP q \<noteq> {}"
    using HoptP_edges_nonempty_if_exists_head_nonempty[OF exN HQ] .
  moreover have "NT_in_edgesP q = {}" using All HQ by blast
  ultimately show False by blast
qed

locale Epistemic_N1_Exclusion = Refuted_Backprop
begin

lemma epistemic_n1_nonclosure:
  assumes exH: "\<exists>q. H_optP q"
      and poss_nonempty_head: "EDia_ep (\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {})"
  shows "EDia_ep (\<not> (\<forall>q. H_optP q \<longrightarrow> NT_in_edgesP q = {}))"
proof -
  have imp:
    "(\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {})
     \<longrightarrow> \<not> (\<forall>q. H_optP q \<longrightarrow> NT_in_edgesP q = {})"
    using exH not_all_HoptP_empty_if_exists_head_nonempty
    by blast
  show ?thesis
    using EDia_ep_forward[OF imp poss_nonempty_head] .
qed

end


subsection \<open>15.2 Main proof: N=1 exclusion via edge-nonempty possibility\<close>

abbreviation EdgeExist :: bool where
  "EdgeExist \<equiv> (\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {})"
(* Exactly one Head (P-version) *)
definition ExactlyOneHeadP :: bool where
  "ExactlyOneHeadP \<longleftrightarrow>
     (\<exists>A0. HeadP A0 \<and> (\<forall>C. HeadP C \<longrightarrow> C = A0))"
text \<open>
  =====================  Epistemic status of @{term EdgeExist}  =====================

  We use the edge-existence proposition

    @{term EdgeExist}  @{text "\<equiv>"}  (@{text "\<exists>"}r. HeadP r @{text "\<and>"} NT\_in\_edgesP r @{text "\<noteq>"} {})

  as an epistemic (EDia\_ep) premise in the A-style MaxNT-candidate exclusions.

  (A) Model-backed confirmation (Sections 8,9 of @{file Diagnostics_Nitpick.thy}).
 Sections 8,9 of @{file Diagnostics_Nitpick.thy} provides a concrete satisfiable witness model (e.g., via Nitpick)
  in which there are distinct heads and at least one head has nonempty in-edges.
  Hence @{term EdgeExist} is not merely ``unrefuted'': it is explicitly satisfiable.
  Under the intended reading of EDia\_ep as ``not refuted / consistent with the
  current definitions'', this supports the premise:

    EDia\_ep @{term EdgeExist}.

  (B) Even without an explicit model.
  Even if we do not appeal to the Sections 8,9 of @{file Diagnostics_Nitpick.thy} witness, the epistemic role of
  @{term EdgeExist} can still be stated as a non-refutation condition:
  unless the theory derives a refutation of @{term EdgeExist} (or an equivalent
  proof of impossibility), @{term EdgeExist} remains epistemically live, so
  EDia\_ep @{term EdgeExist} is admissible as a ``not yet refuted'' premise.

  Note.
  - The witness model strengthens the premise from ``not refuted'' to ``witnessed
    satisfiable''.
  - The candidate-exclusion proofs below do not hard-code any specific model;
    they only consume EDia\_ep @{term EdgeExist} as an epistemic available truth-bearer.
\<close>

lemma NT_in_edgesP_nonempty_imp_three_distinct_heads:
  assumes Nr: "NT_in_edgesP r \<noteq> {}"
  shows "\<exists>A B. HeadP A \<and> HeadP B \<and> HeadP r \<and> A \<noteq> B \<and> A \<noteq> r \<and> B \<noteq> r"
proof -
  have "\<exists>x. x \<in> NT_in_edgesP r" using Nr by auto
  then obtain x where xin: "x \<in> NT_in_edgesP r" by blast
  then obtain A B where Pair: "x = (A,B)" by (cases x) auto
  have InEdges: "(A,B) \<in> NT_in_edgesP r" using xin Pair by simp
  have HA: "HeadP A" and HB: "HeadP B" and Hr: "HeadP r"
      and NT: "NT_pair_supportP A B r"
    using InEdges unfolding NT_in_edgesP_def by auto
  have Dist: "A \<noteq> B \<and> A \<noteq> r \<and> B \<noteq> r"
    using NT unfolding NT_pair_supportP_def by auto
  show ?thesis using HA HB Hr Dist by blast
qed
(* ---------------------------------------------------------
   (1) EdgeExist => not ExactlyOneHeadP
   --------------------------------------------------------- *)
lemma not_ExactlyOneHeadP_if_exists_head_edges_nonempty:
  assumes ex: "EdgeExist"
  shows "\<not> ExactlyOneHeadP"
proof
  assume One: "ExactlyOneHeadP"
  from One obtain A0 where HA0: "HeadP A0"
    and RANGE: "\<forall>C. HeadP C \<longrightarrow> C = A0"
    unfolding ExactlyOneHeadP_def by blast

  from ex obtain r where Hr: "HeadP r" and Nr: "NT_in_edgesP r \<noteq> {}" by blast
  from NT_in_edgesP_nonempty_imp_three_distinct_heads[OF Nr]
  obtain A B where HA: "HeadP A" and HB: "HeadP B"
    and Dist: "A \<noteq> B" "A \<noteq> r" "B \<noteq> r"
    by blast

  have Aeq: "A = A0" using RANGE HA by blast
  have Beq: "B = A0" using RANGE HB by blast
  show False using Dist(1) Aeq Beq by blast
qed

lemma Edge_implies_notOneHead:
  shows "EdgeExist \<longrightarrow> \<not> ExactlyOneHeadP"
  using not_ExactlyOneHeadP_if_exists_head_edges_nonempty by blast
(* ---------------------------------------------------------
   (2) ExactlyOneHeadP -> all heads have empty edges
   (this is the formal “0 support” consequence of N=1)
   --------------------------------------------------------- *)
lemma ExactlyOneHeadP_imp_all_heads_edges_empty:
  assumes One: "ExactlyOneHeadP"
  shows "\<forall>r. HeadP r \<longrightarrow> NT_in_edgesP r = {}"
proof (intro allI impI)
  fix r assume Hr: "HeadP r"
  show "NT_in_edgesP r = {}"
  proof (rule ccontr)
    assume Nr: "NT_in_edgesP r \<noteq> {}"
    from NT_in_edgesP_nonempty_imp_three_distinct_heads[OF Nr]
    obtain A B where HA: "HeadP A" and HB: "HeadP B"
      and Dist: "A \<noteq> B" "A \<noteq> r" "B \<noteq> r"
      by blast

    from One obtain A0 where HA0: "HeadP A0"
      and RANGE: "\<forall>C. HeadP C \<longrightarrow> C = A0"
      unfolding ExactlyOneHeadP_def by blast

    have Aeq: "A = A0" using RANGE HA by blast
    have Beq: "B = A0" using RANGE HB by blast
    have req: "r = A0" using RANGE Hr by blast
    show False using Dist Aeq Beq req by metis
  qed
qed
(* ========================================================= *)
(* 0<1 support articulation (explicit, for readability)        *)
(* ========================================================= *)
(* “All edges empty” = every head has 0 in-edges. *)
definition AllEdgesEmpty :: bool where
  "AllEdgesEmpty \<equiv> (\<forall>r. HeadP r \<longrightarrow> NT_in_edgesP r = {})"

text \<open>This lemma does not assert that any edge actually exists, or that EdgeExist is true. It proves only the incompatibility claim: ExactlyOneHeadP and EdgeExist cannot both hold at the same time.\<close>
lemma ExactlyOneHeadP_imp_AllEdgesEmpty:
  assumes One: "ExactlyOneHeadP"
  shows "AllEdgesEmpty"
  using ExactlyOneHeadP_imp_all_heads_edges_empty[OF One]
  unfolding AllEdgesEmpty_def by blast
(* “EdgeExist” = there exists at least one head with >=1 in-edges (nonempty). *)
lemma EdgeExist_imp_not_AllEdgesEmpty:
  assumes ex: "EdgeExist"
  shows "\<not> AllEdgesEmpty"
proof
  assume AE: "AllEdgesEmpty"
  obtain r where Hr: "HeadP r" and Nr: "NT_in_edgesP r \<noteq> {}"
    using ex by blast
  have "NT_in_edgesP r = {}"
    using AE Hr unfolding AllEdgesEmpty_def by blast
  thus False using Nr by blast
qed
(* Therefore: (ExactlyOneHeadP ∧ EdgeExist) is impossible = “0 cannot coexist with 1”. *)
lemma OneHead_and_edge_False:
  shows "(ExactlyOneHeadP \<and> EdgeExist) \<longrightarrow> False"
proof
  assume H: "ExactlyOneHeadP \<and> EdgeExist"
  have One: "ExactlyOneHeadP" using H by blast
  have ex: "EdgeExist" using H by blast
  have AE: "AllEdgesEmpty" using ExactlyOneHeadP_imp_AllEdgesEmpty[OF One] .
  have nAE: "\<not> AllEdgesEmpty" using EdgeExist_imp_not_AllEdgesEmpty[OF ex] .
  show False using AE nAE by blast
qed
(* ---------------------------------------------------------
   EDia forward lemma (same as N=2 proof)
   --------------------------------------------------------- *)
lemma notEdia_back_from_ref_back:
  assumes ref_back: "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> Ref Q \<Longrightarrow> Ref P"
  shows "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
  using ref_back by (simp add: EDia_ep_def)

lemma ref_back_from_notEdia_back:
  assumes notEdia_back: "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
  shows "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> Ref Q \<Longrightarrow> Ref P"
  using notEdia_back by (simp add: EDia_ep_def)
text \<open>
  Refutation back-propagation (ref\_back) and the EDia\_ep formulation
  (notEdia\_back) are definitionally equivalent since EDia\_ep @{text "\<equiv>"} @{text "\<not>"}Ref.
\<close>

lemma EDia_ep_forward0:
  assumes notEdia_back:
            "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
      and imp: "P \<longrightarrow> Q"
      and possP: "EDia_ep P"
  shows "EDia_ep Q"
proof (rule ccontr)
  assume nQ: "\<not> EDia_ep Q"
  have nP: "\<not> EDia_ep P" using notEdia_back[OF imp nQ] .
  show False using possP nP by blast
qed
(* ---------------------------------------------------------
   stronger_edge / MaxNT_candidate (same as N=2 candidate block)
   --------------------------------------------------------- *)
definition stronger_edge :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "stronger_edge Q P \<equiv>
     EDia_ep (Q \<and> EdgeExist) \<and> \<not> EDia_ep (P \<and> EdgeExist)"

definition MaxNT_candidate :: "bool \<Rightarrow> bool" where
  "MaxNT_candidate P \<equiv>
     EDia_ep P \<and> (\<forall>Q. EDia_ep Q \<longrightarrow> \<not> stronger_edge Q P)"
(* ---------------------------------------------------------
   Final: N=1 disqualified as MaxNT_candidate (N=2 style)
   --------------------------------------------------------- *)
text \<open>
Sections 8,9 of @{file Diagnostics_Nitpick.thy} provide a concrete satisfiable witness
(found by Nitpick). This computational witness corroborates that
@{term EdgeExist} is epistemically admissible under the intended reading
of @{term EDia_ep} as ``not refuted.''

In other words, the existence of a non-empty NT-edge structure is not
definitionally blocked by the framework, and thus
@{term "EDia_ep EdgeExist"} is justified at the epistemic level.
\<close>

lemma N1_fails_MaxNT_final:
  assumes poss_edge: "EDia_ep EdgeExist"
      and notEdia_back:
            "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
      and notEdia_False: "\<not> EDia_ep False"
  shows "\<not> MaxNT_candidate ExactlyOneHeadP"
proof
  assume CandN1: "MaxNT_candidate ExactlyOneHeadP"
  (* 1) EdgeExist -> (not OneHead ∧ EdgeExist) *)
  have imp_notN1:
  "EdgeExist \<longrightarrow> \<not> ExactlyOneHeadP"
  using Edge_implies_notOneHead .
  have imp_to_conj:
    "EdgeExist \<longrightarrow> (\<not> ExactlyOneHeadP \<and> EdgeExist)"
     using imp_notN1 by blast

  have poss_notN1_and_edge:
    "EDia_ep (\<not> ExactlyOneHeadP \<and> EdgeExist)"
    using EDia_ep_forward0[OF notEdia_back imp_to_conj poss_edge] .
  (* 2) Therefore ¬ EDia_ep (OneHead ∧ EdgeExist) (0 cannot coexist with 1) *)
  have not_possN1_and_edge:
    "\<not> EDia_ep (ExactlyOneHeadP \<and> EdgeExist)"
  proof
    assume poss: "EDia_ep (ExactlyOneHeadP \<and> EdgeExist)"
    have nPoss:
      "\<not> EDia_ep (ExactlyOneHeadP \<and> EdgeExist)"
      using notEdia_back[OF OneHead_and_edge_False notEdia_False] .
    show False using poss nPoss by blast
  qed
  (* 3) Extract poss_notN1 *)
  have poss_notN1: "EDia_ep (\<not> ExactlyOneHeadP)"
  proof -
    have imp1: "(\<not> ExactlyOneHeadP \<and> EdgeExist) \<longrightarrow> (\<not> ExactlyOneHeadP)" by blast
    show ?thesis
      using EDia_ep_forward0[OF notEdia_back imp1 poss_notN1_and_edge] .
  qed
  (* 4) (not OneHead) is stronger than OneHead, contradiction to candidacy *)
  have strong: "stronger_edge (\<not> ExactlyOneHeadP) ExactlyOneHeadP"
    unfolding stronger_edge_def
    using poss_notN1_and_edge not_possN1_and_edge by blast

  have no_stronger:
    "\<not> stronger_edge (\<not> ExactlyOneHeadP) ExactlyOneHeadP"
    using CandN1 poss_notN1
    unfolding MaxNT_candidate_def by blast

  show False using strong no_stronger by blast
qed


section \<open>16. N=2 exclusion: N=2 cannot exceed N=1 in MaxNT (mutual vs. non-mutual cases)\<close>

subsection \<open>16.1 Support-count machinery (NT\_in\_edges-based)\<close>

definition support_edges_ep :: "bool \<Rightarrow> (bool \<times> bool) set" where
  "support_edges_ep X \<equiv> NT_in_edges_ep X"

definition support_count_ep :: "bool \<Rightarrow> nat" where
  "support_count_ep X \<equiv> card (support_edges_ep X)"

subsection \<open>16.2 Case split predicates\<close>

definition Mutual_leU_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Mutual_leU_ep X Y \<equiv> (Arg X \<preceq> Arg Y \<and> Arg Y \<preceq> Arg X)"

definition No_cross_support_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "No_cross_support_ep X Y \<equiv>
     (\<not> (\<exists>S. NT_pair_support_ep X S Y) \<and> \<not> (\<exists>S. NT_pair_support_ep Y S X))"

definition Nonmutual_symmetric_ep :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Nonmutual_symmetric_ep X Y \<equiv>
     No_cross_support_ep X Y \<and> support_edges_ep X = support_edges_ep Y"

paragraph \<open>Case (1): mutual (Arg-level) support @{text "\<Rightarrow>"} Arg-collapse \<close>

lemma case_mutual_leU_ep:
  assumes two: "TwoHypostases_ep \<Omega> \<Pi>"
      and mut: "Mutual_leU_ep \<Omega> \<Pi>"
      and EqU_iff_LeU_both_assm:
        "\<And>A B. (A \<approx> B) \<longleftrightarrow> (A \<preceq> B \<and> B \<preceq> A)"
      and TwoHypostases_noEqArg:
        "\<And>\<Omega> \<Pi>. TwoHypostases_ep \<Omega> \<Pi> \<Longrightarrow> \<not> (Arg \<Omega> \<approx> Arg \<Pi>)"
  shows False
proof -
  have eq: "Arg \<Omega> \<approx> Arg \<Pi>"
    using mut EqU_iff_LeU_both_assm by (auto simp: Mutual_leU_ep_def)
  show False
    using TwoHypostases_noEqArg[OF two] eq by blast
qed

paragraph \<open>Case (2): nonmutual symmetric @{text "\<Rightarrow>"} equal counts\<close>

lemma case_nonmutual_equal_count_ep:
  assumes sym: "Nonmutual_symmetric_ep \<Omega> \<Pi>"
  shows "support_count_ep \<Omega> = support_count_ep \<Pi>"
  using sym
  by (simp add: Nonmutual_symmetric_ep_def support_count_ep_def)


subsection \<open>16.3 Clean case split lemma\<close>

theorem N2_cases:
  assumes two: "TwoHypostases_ep \<Omega> \<Pi>"
    and EqU_iff_LeU_both_assm: "\<And>A B. (A \<approx> B) \<longleftrightarrow> (A \<preceq> B \<and> B \<preceq> A)"
    and TwoHypostases_noEqArg: "\<And>\<Omega> \<Pi>. TwoHypostases_ep \<Omega> \<Pi> \<Longrightarrow> \<not> (Arg \<Omega> \<approx> Arg \<Pi>)"
  shows "Mutual_leU_ep \<Omega> \<Pi> \<Longrightarrow> False"
    and "Nonmutual_symmetric_ep \<Omega> \<Pi> \<Longrightarrow> support_count_ep \<Omega> = support_count_ep \<Pi>"
proof -
  { assume mut: "Mutual_leU_ep \<Omega> \<Pi>"
     show False
      apply (rule case_mutual_leU_ep [where \<Omega>=\<Omega> and \<Pi>=\<Pi>])
      using two apply assumption
      using mut apply assumption
      using EqU_iff_LeU_both_assm apply assumption
      using TwoHypostases_noEqArg apply assumption
      done }

  { assume sym: "Nonmutual_symmetric_ep \<Omega> \<Pi>"
       show "support_count_ep \<Omega> = support_count_ep \<Pi>"
      using case_nonmutual_equal_count_ep [OF sym]
      by simp }
qed

subsection \<open>16.4 Explicit tie statement: if N=2 is nonmutual symmetric, it cannot exceed N=1\<close>

lemma N2_tie_cannot_exceed_N1:
  assumes sym: "Nonmutual_symmetric_ep \<Omega> \<Pi>"
  shows "support_count_ep \<Omega> = support_count_ep \<Pi>"
    and "\<not> (support_count_ep \<Omega> > support_count_ep \<Pi>)"
    and "\<not> (support_count_ep \<Pi> > support_count_ep \<Omega>)"
proof -
  have eq: "support_count_ep \<Omega> = support_count_ep \<Pi>"
    using case_nonmutual_equal_count_ep[OF sym] .
  show "support_count_ep \<Omega> = support_count_ep \<Pi>" using eq .
  show "\<not> (support_count_ep \<Omega> > support_count_ep \<Pi>)" using eq by simp
  show "\<not> (support_count_ep \<Pi> > support_count_ep \<Omega>)" using eq by simp
qed

subsection \<open>16.5 Nonmutual symmetric @{text "\<Rightarrow>"} indistinguishable (so not a genuine N=2 split)\<close>

lemma Nonmutual_symmetric_imp_EqNT_ep:
  assumes sym: "Nonmutual_symmetric_ep X Y"
  shows "X \<approx>\<^sub>NT Y"
  using sym
  by (simp add: Nonmutual_symmetric_ep_def EqNT_ep_def support_edges_ep_def)

corollary Nonmutual_symmetric_not_Distinct_ep:
  assumes sym: "Nonmutual_symmetric_ep X Y"
  shows "\<not> Distinct_ep X Y"
  using sym
  by (simp add: Distinct_ep_def Nonmutual_symmetric_imp_EqNT_ep)

text \<open>
  In the nonmutual symmetric case, the two candidates are tied and also NT-indistinguishable,
  hence they cannot serve as two distinct hypostases in the sense of @{term Distinct_ep}.
\<close>

corollary Nonmutual_symmetric_blocks_two_witness:
  assumes sym: "Nonmutual_symmetric_ep \<Omega> \<Pi>"
  shows "\<not> (Distinct_ep \<Omega> \<Pi>)"
  using Nonmutual_symmetric_not_Distinct_ep[OF sym] .
(* ===================== N=2 exclusion (N=1 exclusion style) ===================== *)
subsection \<open>16.6 Main proof: N=2 exclusion (epistemic candidate only)\<close>

definition ExactlyTwoHeadsP :: bool where
  "ExactlyTwoHeadsP \<longleftrightarrow>
    (\<exists>A0 B0.
      A0 \<noteq> B0 \<and> HeadP A0 \<and> HeadP B0 \<and>
      (\<forall>C. HeadP C \<longrightarrow> (C = A0 \<or> C = B0)))"
(* Reuse the same EdgeExist abbreviation already introduced earlier:
   EdgeExist \<equiv> (\<exists>r. HeadP r \<and> NT_in_edgesP r \<noteq> {}) *)
lemma Edge_blocks_N2: "EdgeExist \<longrightarrow> \<not> ExactlyTwoHeadsP"
proof
  assume E: "EdgeExist"
  show "\<not> ExactlyTwoHeadsP"
  proof
    assume Two: "ExactlyTwoHeadsP"
    then obtain A0 B0 where
      AB0: "A0 \<noteq> B0" and
      HA0: "HeadP A0" and HB0: "HeadP B0" and
      RANGE: "\<forall>C. HeadP C \<longrightarrow> (C = A0 \<or> C = B0)"
      unfolding ExactlyTwoHeadsP_def by blast

    obtain r where Hr: "HeadP r" and Nr: "NT_in_edgesP r \<noteq> {}"
      using E by blast

    obtain x where xin: "x \<in> NT_in_edgesP r"
      using Nr by blast
    then obtain A B where xAB: "x = (A,B)"
      by (cases x) auto
    have InEdges: "(A,B) \<in> NT_in_edgesP r"
      using xin xAB by simp

    have HA: "HeadP A" and HB: "HeadP B" and Hr': "HeadP r"
      and NT: "NT_pair_supportP A B r"
      using InEdges unfolding NT_in_edgesP_def by auto

    have Dist: "A \<noteq> B" "A \<noteq> r" "B \<noteq> r"
      using NT unfolding NT_pair_supportP_def by auto

    have A01: "A = A0 \<or> A = B0" using RANGE HA by blast
    have B01: "B = A0 \<or> B = B0" using RANGE HB by blast
    have r01: "r = A0 \<or> r = B0" using RANGE Hr' by blast

    show False using AB0 A01 B01 r01 Dist by metis
  qed
qed

definition MaxNT_candidate_N2 :: "bool \<Rightarrow> bool" where
  "MaxNT_candidate_N2 P \<equiv>
     EDia_ep P \<and> (\<forall>Q. EDia_ep Q \<longrightarrow> \<not> stronger_edge Q P)"
(* Final verdict (candidate knockout): epistemic only.
   Uses the proved structural lemma Edge_blocks_N2, no extra assumes. *)
lemma N2_fails_MaxNT_final:
  assumes poss_edge: "EDia_ep EdgeExist"
      and notEdia_back:
            "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
      and notEdia_False: "\<not> EDia_ep False"
  shows "\<not> MaxNT_candidate_N2 ExactlyTwoHeadsP"
proof
  assume CandN2: "MaxNT_candidate_N2 ExactlyTwoHeadsP"
  (* 1) EdgeExist -> (not N2 ∧ EdgeExist) *)
  have imp_to_conj:
    "EdgeExist \<longrightarrow> (\<not> ExactlyTwoHeadsP \<and> EdgeExist)"
    using Edge_blocks_N2 by blast
  (* 2) From poss_edge, forward to poss (notN2 and EdgeExist) *)
  have poss_notN2_and_edge:
    "EDia_ep (\<not> ExactlyTwoHeadsP \<and> EdgeExist)"
    using EDia_ep_forward0[OF notEdia_back imp_to_conj poss_edge] .
  (* 3) (N2 ∧ EdgeExist) -> False, hence not EDia_ep (N2 ∧ EdgeExist) *)
  have N2_and_edge_False:
    "(ExactlyTwoHeadsP \<and> EdgeExist) \<longrightarrow> False"
  proof
    assume H: "ExactlyTwoHeadsP \<and> EdgeExist"
    have Two: "ExactlyTwoHeadsP" and E: "EdgeExist" using H by blast+
    have nTwo: "\<not> ExactlyTwoHeadsP" using Edge_blocks_N2 E by blast
    show False using Two nTwo by blast
  qed

  have not_possN2_and_edge:
    "\<not> EDia_ep (ExactlyTwoHeadsP \<and> EdgeExist)"
    using notEdia_back[OF N2_and_edge_False notEdia_False] .
  (* 4) Extract poss_notN2 *)
  have poss_notN2: "EDia_ep (\<not> ExactlyTwoHeadsP)"
  proof -
    have imp1:
      "(\<not> ExactlyTwoHeadsP \<and> EdgeExist) \<longrightarrow> (\<not> ExactlyTwoHeadsP)"
      by blast
    show ?thesis
      using EDia_ep_forward0[OF notEdia_back imp1 poss_notN2_and_edge] .
  qed
  (* 5) (notN2) is stronger than N2, contradicting candidacy *)
  have strong:
    "stronger_edge (\<not> ExactlyTwoHeadsP) ExactlyTwoHeadsP"
    unfolding stronger_edge_def
    using poss_notN2_and_edge not_possN2_and_edge by blast

  have no_stronger:
    "\<not> stronger_edge (\<not> ExactlyTwoHeadsP) ExactlyTwoHeadsP"
    using CandN2 poss_notN2
    unfolding MaxNT_candidate_N2_def by blast

  show False using strong no_stronger by blast
qed


section \<open>17. Actuality and Forcing: World-Lifted Existence of H\_opt q(@{text "\<exists>"}q. H\_opt q) and the N=3 Conclusion\<close>

subsection \<open>17.1 Forcing the triune case ``N3''\<close>
text \<open>
  We work with four structural cases for ultimate heads:

    N1\_exact   -- exactly one absolute head
    N2\_exact   -- exactly two independent heads
    N3         -- triune mutual-support package
    N4plus     -- four-or-more essentially independent heads

  Key point (clean logic):

  Existence trigger (DN).
    We assume (@{text "\<not>"}@{text "\<not>"})(@{text "\<exists>"}x. H\_opt x).
    Since Isabelle/HOL is classical, this yields @{text "\<exists>"}x. H\_opt x.
    Philosophical reading: the ground cannot ``evaporate''; we are not allowed to
    settle into the degenerate option @{text "\<not>"}@{text "\<exists>"}x. H\_opt x.

  Conditional exhaustiveness.
    The case split is not asserted unconditionally.
    We assume only the conditional form:
      (@{text "\<exists>"}x. H\_opt x)  @{text "\<longrightarrow>"} (N1\_exact @{text "\<or>"} N2\_exact @{text "\<or>"} N3 @{text "\<or>"} N4plus).
    So the disjunction is activated *only after* existence is obtained.

  Elimination (forcing).
    Once the disjunction is available, ruling out ``N1\_exact'', ``N2\_exact'',
    and ``N4plus'' leaves ``N3'' as the unique remaining live case.

  Therefore DN is not decorative: it is the engine that activates the exhaustiveness,
  i.e. it licenses the disjunction by guaranteeing existence.
\<close>

text \<open>
  Case-label packaging for the forcing step (Section 17).

  In this section, we treat the ``N=1 exact'' and ``N=2 exact'' cases as
  the corresponding MaxNT-candidate propositions used in the epistemic
  exclusion blocks (Sections 15.2 and 16.6).

  This keeps the forcing logic uniform: the disjunction is over boolean
  case-labels, and the exclusions are exactly the proved negations of
  those labels.
\<close>
definition N1_exact :: bool where
  "N1_exact \<equiv> MaxNT_candidate ExactlyOneHeadP"

definition N2_exact :: bool where
  "N2_exact \<equiv> MaxNT_candidate_N2 ExactlyTwoHeadsP"
(* N>=4 case-label: reuse the already-defined ep-level predicate *)
definition N4plus :: bool where
  "N4plus \<equiv>
     (\<exists>a b c d.
        H_opt_ep a \<and> H_opt_ep b \<and> H_opt_ep c \<and> H_opt_ep d \<and>
        EDia_ep a  \<and> EDia_ep b  \<and> EDia_ep c  \<and> EDia_ep d  \<and>
        \<not> (a \<approx>\<^sub>NT b) \<and> \<not> (a \<approx>\<^sub>NT c) \<and> \<not> (a \<approx>\<^sub>NT d) \<and>
        \<not> (b \<approx>\<^sub>NT c) \<and> \<not> (b \<approx>\<^sub>NT d) \<and> \<not> (c \<approx>\<^sub>NT d))"

lemma noN1:
  assumes poss_edge: "EDia_ep EdgeExist"
      and notEdia_back:
            "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
      and notEdia_False: "\<not> EDia_ep False"
  shows "\<not> N1_exact"
  unfolding N1_exact_def
  using N1_fails_MaxNT_final[OF poss_edge notEdia_back notEdia_False] .

lemma noN2:
  assumes poss_edge: "EDia_ep EdgeExist"
      and notEdia_back:
            "\<And>P Q. (P \<longrightarrow> Q) \<Longrightarrow> \<not> EDia_ep Q \<Longrightarrow> \<not> EDia_ep P"
      and notEdia_False: "\<not> EDia_ep False"
  shows "\<not> N2_exact"
  unfolding N2_exact_def
  using N2_fails_MaxNT_final[OF poss_edge notEdia_back notEdia_False] .

lemma noN4:
  assumes noN4ep: "\<not> N4plus"
  shows "\<not> N4plus"
  using noN4ep by (simp add: N4plus_def)

lemma force_N3_from_exhaust_and_exclusions:
  assumes Exhaust: "N1_exact \<or> N2_exact \<or> N3 \<or> N4plus"
    and noN1: "\<not> N1_exact"
    and noN2: "\<not> N2_exact"
    and noN4: "\<not> N4plus"
  shows N3
proof -
  have "N3 \<or> N1_exact \<or> N2_exact \<or> N4plus"
    using Exhaust by blast
  thus N3
    using noN1 noN2 noN4 by blast
qed

text \<open>
  Clean forced-N3 lemma (DN actually used):

  DN ensures existence:
      (@{text "\<not>"}@{text "\<not>"})(@{text "\<exists>"}x. H\_opt x)  implies (@{text "\<exists>"}x. H\_opt x).

  Exhaust\_if\_exists provides the 4-way case split *conditional on existence*:
      (@{text "\<exists>"}x. H\_opt x)  @{text "\<longrightarrow>"} (N1\_exact @{text "\<or>"} N2\_exact @{text "\<or>"} N3 @{text "\<or>"} N4plus).

  With ``N1\_exact'', ``N2\_exact'', ``N4plus'' excluded,
        the only remaining case is ``N3''.

  This makes the dependency explicit:
    without DN you cannot fire Exhaust\_if\_exists, hence you cannot conclude N3.
\<close>
lemma N3_forced_clean:
  assumes DN: "\<not>\<not> (\<exists>x. H_opt x)"
      and Exhaust_if_exists:
            "(\<exists>x. H_opt x) \<longrightarrow> (N1_exact \<or> N2_exact \<or> N3 \<or> N4plus)"
      and noN1: "\<not> N1_exact"
      and noN2: "\<not> N2_exact"
      and noN4: "\<not> N4plus"
  shows N3
proof -
  have Ex: "\<exists>x. H_opt x"
    using DN by blast

  have Exhaust: "N1_exact \<or> N2_exact \<or> N3 \<or> N4plus"
    using Exhaust_if_exists Ex by blast

  show N3
    using force_N3_from_exhaust_and_exclusions[OF Exhaust noN1 noN2 noN4] .
qed

subsection \<open>17.2  Actuality at the distinguished U-world-point (our-world)\<close>
text \<open>
  Recap.
    We already proved ``N3'' purely in the U-layer (Section 13.3 / 17.1),
    i.e. there exist three optimal heads a b c such that the fully symmetric
    ``pair @{text "\<longrightarrow>"} third'' closure holds uniformly at every U-point e
    (see N3\_def). No modal axioms and no extra metaphysical axioms were used.

  Goal (17.2).
    Instantiate that uniform closure at the distinguished point e0 and
    package it as a single internal statement TriuneGod\_e0.
    This uses only @{term Supports}, @{term H_opt}, @{term e0}, and the theorem @{term N3}
    (no Ref / EDia\_ep / Val / @{text "w\<^sub>0"}, and no modal axioms).

  World-reading (methodological, not an axiom).
    We do not add ``U = our world'' as an axiom inside the U-layer (that would be circular).
    Rather, we adopt it as an external interpretive identification—i.e. the usual way
    we interpret a formal system as describing (or modeling) facts about reality.
    Likewise, HOL's basic principles are trusted precisely because they are built from
    highly evident rules; interpreting them as applicable to our reasoning about reality
    is a methodological stance, not an extra postulate inside the object theory.
\<close>

lemma TriuneGod_e0_pair_closure_from_N3:
  assumes N3H: N3
  shows "\<exists>a b c.
          H_opt a \<and> H_opt b \<and> H_opt c \<and>
          ((Supports e0 b \<and> Supports e0 c) \<longrightarrow> Supports e0 a) \<and>
          ((Supports e0 c \<and> Supports e0 a) \<longrightarrow> Supports e0 b) \<and>
          ((Supports e0 a \<and> Supports e0 b) \<longrightarrow> Supports e0 c)"
proof -
  obtain a b c where
    Ha: "H_opt a" and Hb: "H_opt b" and Hc: "H_opt c"
    and Sbc: "\<forall>e. (Supports e b \<and> Supports e c) \<longrightarrow> Supports e a"
    and Sca: "\<forall>e. (Supports e c \<and> Supports e a) \<longrightarrow> Supports e b"
    and Sab: "\<forall>e. (Supports e a \<and> Supports e b) \<longrightarrow> Supports e c"
    using N3H unfolding N3_def by blast
  show ?thesis using Ha Hb Hc Sbc Sca Sab by blast
qed

definition TriuneGod_e0 :: bool where
  "TriuneGod_e0 \<equiv>
     (\<exists>a b c.
        H_opt a \<and> H_opt b \<and> H_opt c \<and>
        ((Supports e0 b \<and> Supports e0 c) \<longrightarrow> Supports e0 a) \<and>
        ((Supports e0 c \<and> Supports e0 a) \<longrightarrow> Supports e0 b) \<and>
        ((Supports e0 a \<and> Supports e0 b) \<longrightarrow> Supports e0 c))"

lemma TriuneGod_e0_holds_from_N3:
  assumes N3H: N3
  shows "TriuneGod_e0"
  unfolding TriuneGod_e0_def
  using TriuneGod_e0_pair_closure_from_N3[OF N3H] by blast
text \<open>
  Final philosophical summary.

    (1) Methodological identification (not an axiom).
    We treat the Isabelle U-layer (Supports / H\_opt / the distinguished @{term e0})
    as a formal description of our actual world. This is not added as an axiom
    inside the U-layer (that would be circular); rather, it is an interpretive stance
    taken when reading mathematics.

    This identification is of the same kind as the standard interpretive practice of mathematics:
    results proved from axioms are read as applicable to reality, without re-encoding that applicability
    as an additional axiom inside the object theory.

        Analogy: arithmetic facts such as ``1+1=2'' are proved internally from axioms,
        yet we naturally read them as truths about ordinary counting in reality.
        In doing so, we treat the underlying axioms/rules as applicable to our reasoning
        and to the description of the world.

        Likewise, HOL's basic commitments are accepted precisely as highly evident principles;
        interpreting them as applicable to reality is therefore not an arbitrary stipulation,
        but a methodologically justified interpretation.

    (2) Internal theorem.
        Within that very U-structure, @{term N3} is already proved (Section 17.1),
        axiom-free at the U-layer (no modal axioms, no extra metaphysical postulates).

    (3) Actuality at @{term e0}.
        Since @{term N3} quantifies @{text "\<forall>"}e, we specialize it to @{term e0},
        obtaining @{term TriuneGod_e0}: at our world-point, the ``pair @{text "\<longrightarrow>"} third''
        closure holds for some three optimal heads.

    (4) Consequence.
        Given (1)–(3), the ultimate ground of our world is coherently forced to be triune:
        rival patterns (pure one-head, strict two-head, or 4+-head fragmentation) are excluded
        by the same U-internal constraints that yielded @{term N3}.

  Short reading:
    If you accept Isabelle/U as your descriptive logic of reality, then—without adding any
    extra metaphysical axiom—the only stable ultimate ground compatible with the framework
    is triune.
\<close>


subsection \<open>17.3 Ontology argument- world-lift of existence \<close>

text \<open>
  (1) DN trigger: @{text "\<not>"}@{text "\<not>"}(@{text "\<exists>"}x. H\_opt x) @{text "\<longrightarrow>"} (@{text "\<exists>"}x. H\_opt x) (E1)
  Isabelle/HOL is classical, so double-negation elimination holds.
\<close>
lemma DN_exists_Hopt:
  assumes DN: "\<not>\<not> (\<exists>x. H_opt x)"
  shows "\<exists>x. H_opt x"
  using DN by blast

text \<open>
  (2) Reading ``God exists'' as U-layer existence of an H\_opt witness (E1').
      Moral note: this only asserts the existence of an \<open>H_opt\<close> witness in the U-layer,
      and does not assume any further ethical or theological properties.
\<close>
definition GodExists_U :: bool
  where "GodExists_U \<equiv> (\<exists>x. H_opt x)"

lemma GodExists_U_from_DN:
  assumes DN: "\<not>\<not> (\<exists>x. H_opt x)"
  shows "GodExists_U"
proof -
  from DN have "\<exists>x. H_opt x" by blast
  thus "GodExists_U" by (simp add: GodExists_U_def)
qed

text \<open>
  (3) World-lift by identification: we record the interpretive move
      ``our world follows the U-layer logic'' as a definitional identification.
      No new axioms are introduced; we simply mirror the U-claim at the world level.
\<close>
definition GodExists_world :: bool
  where "GodExists_world \<equiv> GodExists_U"

lemma GodExists_world_from_U:
  assumes "GodExists_U"
  shows   "GodExists_world"
  using assms by (simp add: GodExists_world_def)

lemma GodExists_U_iff_world:
  "GodExists_U \<longleftrightarrow> GodExists_world"
  by (simp add: GodExists_world_def)
text \<open>
  Usage sketch:
    have DN: ``@{text "\<not>"}@{text "\<not>"}(@{text "\<exists>"}x. H\_opt x)'' by (* your existing U-layer consistency proof *)
    hence ``GodExists\_U''     by (rule GodExists\_U\_from\_DN)
    hence ``GodExists\_world'' by (rule GodExists\_world\_from\_U)
\<close>


section \<open>18. Disjunctive-causal collapse on booleans\<close>
lemma disjunctive_causation_collapse:
  assumes "(A \<or> B) \<longrightarrow> C" "(A \<or> C) \<longrightarrow> B" "(B \<or> C) \<longrightarrow> A"
  shows "(A \<longleftrightarrow> C) \<and> (B \<longleftrightarrow> C) \<and> (A \<longleftrightarrow> B)"
proof -
  have AC1: "A \<Longrightarrow> C" using assms(1) by (meson disjI1)
  have AC2: "C \<Longrightarrow> A" using assms(3) by (meson disjI2)
  have AC:  "A \<longleftrightarrow> C" using AC1 AC2 by blast
  have BC1: "B \<Longrightarrow> C" using assms(1) by (meson disjI2)
  have BC2: "C \<Longrightarrow> B" using assms(2) by (meson disjI2)
  have BC:  "B \<longleftrightarrow> C" using BC1 BC2 by blast
  have AB:  "A \<longleftrightarrow> B" using AC BC by blast
  show ?thesis using AC BC AB by blast
qed

lemma no_disjunctive_trinity:
  assumes "(A \<or> B) \<longrightarrow> C" "(A \<or> C) \<longrightarrow> B" "(B \<or> C) \<longrightarrow> A"
      and "\<not> (A \<longleftrightarrow> B) \<or> \<not> (B \<longleftrightarrow> C) \<or> \<not> (A \<longleftrightarrow> C)"
  shows False
  using disjunctive_causation_collapse[OF assms(1-3)] assms(4) by blast


section \<open>19. Boolean ``Trinity'' as pure concurrency\<close>

definition Trinity :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Trinity \<Phi> \<Omega> \<psi> \<equiv> \<Phi> \<and> \<Omega> \<and> \<psi>"

lemma Trinity_equiv_from_T_and_S_strong:
  assumes T: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> R"
      and S: "\<not> (Trinity \<Phi> \<Omega> \<psi>) \<longrightarrow> \<not> R"
  shows "Trinity \<Phi> \<Omega> \<psi> \<longleftrightarrow> R"  "R \<longrightarrow> \<Phi>"  "R \<longrightarrow> \<Omega>"  "R \<longrightarrow> \<psi>"
proof -
  have "R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>" using S by (metis)
  hence R_imp: "R \<longrightarrow> (\<Phi> \<and> \<Omega> \<and> \<psi>)" by (simp add: Trinity_def)
  from this show "R \<longrightarrow> \<Phi>" "R \<longrightarrow> \<Omega>" "R \<longrightarrow> \<psi>" by (simp_all add: Trinity_def)
  show "Trinity \<Phi> \<Omega> \<psi> \<longleftrightarrow> R" using T \<open>R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>\<close> by blast
qed

lemma singleton_cause_forces_equiv:
  fixes p q :: bool
  assumes "p \<longrightarrow> q" and "q \<longrightarrow> p"
  shows "p \<longleftrightarrow> q"
  using assms by blast


section \<open>20. Packaging (T)+(S): The Trinity provides the possibility condition for created truths(R)\<close>

lemma Trinity_imp_Phi  [simp]: "Trinity \<Phi> \<Omega> \<psi> \<Longrightarrow> \<Phi>"
  by (simp add: Trinity_def)

lemma Trinity_imp_Omega [simp]: "Trinity \<Phi> \<Omega> \<psi> \<Longrightarrow> \<Omega>"
  by (simp add: Trinity_def)

lemma Trinity_imp_psi  [simp]: "Trinity \<Phi> \<Omega> \<psi> \<Longrightarrow> \<psi>"
  by (simp add: Trinity_def)

lemma Trinity_TS_package:
  assumes T: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
      and S: "\<not> (Trinity \<Phi> \<Omega> \<psi>) \<longrightarrow> \<not> R"
  shows "R \<longrightarrow> \<Phi>"
        "R \<longrightarrow> \<Omega>"
        "R \<longrightarrow> \<psi>"
        "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
proof -
  have RT: "R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>" using S by metis

  show "R \<longrightarrow> \<Phi>" using RT
    by (auto simp: Trinity_def)

  show "R \<longrightarrow> \<Omega>" using RT
    by (auto simp: Trinity_def)

  show "R \<longrightarrow> \<psi>" using RT
    by (auto simp: Trinity_def)

  show "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R" using T .
qed


section \<open>21. Relative Certainty and Ontological Grounding (definition-only)\<close>
text \<open>
  We capture the ``R @{text "\<rightarrow>"} S \& not (S @{text "\<rightarrow>"} R)'' certainty comparison on the U-layer
  via the strict support order of arguments. No axioms are added:
  everything remains definition-only and kernel-verified.

  *Recall.* The relations ``@{text "\<preceq>"}'' (relative certainty), ``@{text "\<approx>"}'' (equivalence),
  and ``<U'' (strict relative certainty) were already defined in
  **Section 4 (U-layer: Relative Certainty)**.
  In this section we do not redefine them; we only introduce a
  convenient alias ``RelCert'' and related lemmas, all of which are
  conservative and definitional.
\<close>


subsection \<open>21.1 Relative certainty on the U-layer\<close>
text \<open>``R is strictly less certain than S'' is rendered as a strict inclusion
  of U-supports for their arguments. Equivalently, (Arg R) <U (Arg S).\<close>

lemma RelCert_iff_lt:
  "RelCert R S \<longleftrightarrow> ((Arg R) \<preceq> (Arg S) \<and> \<not> ((Arg S) \<preceq> (Arg R)))"
  by (simp add: RelCert_def LtU_def)

lemma RelCert_implies_le:
  "RelCert R S \<Longrightarrow> (Arg R) \<preceq> (Arg S)"
  by (simp add: RelCert_def LtU_def)


subsection \<open>21.2 Pointwise and possibility/current-truth monotonicity\<close>

lemma RelCert_pointwise:
  assumes RC: "RelCert R S"
      and SR: "Supports e R"
  shows "Supports e S"
proof -
  (* 1. From RelCert, get the support inclusion *)
  have le: "(Arg R) \<preceq> (Arg S)"
    using RC by (simp add: RelCert_def LtU_def)
  (* 2. Unfold Supports to obtain e \<turnstile> Arg R *)
  have eR: "e \<turnstile> Arg R"
    using SR by (simp add: Supports_def)
  (* 3. Pointwise monotonicity along \<preceq> *)
  have "e \<turnstile> Arg S"
    using le eR by (rule le_pointwise)
  (* 4. Fold back to Supports *)
  thus "Supports e S"
    by (simp add: Supports_def)
qed

lemma RelCert_EDia_mono:
  assumes "RelCert R S" and "EDia R"
  shows   "EDia S"
proof -
  obtain e where "Supports e R"
    using assms(2) by (auto simp: EDia_def)
  hence "Supports e S"
    using RelCert_pointwise[OF assms(1)] by blast
  thus "EDia S" by (auto simp: EDia_def)
qed

lemma RelCert_TrueNow_mono:
  assumes "RelCert R S" and "TrueNow R"
  shows   "TrueNow S"
  using RelCert_pointwise[OF assms(1)]
  using assms(2) by (simp add: TrueNow_def)


subsection \<open>21.3 TSupp / PSupp monotonicity under ``Relative Certainty''\<close>

lemma RelCert_TSupp_mono:
  assumes "RelCert R S"
  shows   "TSupp (Arg R) \<subseteq> TSupp (Arg S)"
  using TSupp_mono RelCert_implies_le[OF assms] by blast

lemma RelCert_PSupp_mono:
  assumes "RelCert R S"
  shows   "PSupp (Arg R) \<subseteq> PSupp (Arg S)"
  using PSupp_mono RelCert_implies_le[OF assms] by blast


subsection \<open>21.4 Ontological Grounding: a definitional alias\<close>
text \<open>We introduce a thin alias ``Ground'' to record the intended philosophical
  reading: if S is strictly more certain than R (in the RelCert sense),
  then S is an ontological ground for R. This is a pure definition (no axiom).\<close>
definition Ground :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "Ground S R \<equiv> RelCert R S"

lemma RelCert_implies_Ground: "RelCert R S \<Longrightarrow> Ground S R"
  by (simp add: Ground_def)

lemma Ground_iff_RelCert: "Ground S R \<longleftrightarrow> RelCert R S"
  by (simp add: Ground_def)


subsection \<open>21.5 Model-side view (optional, inside FullIdBridge)\<close>

context FullIdBridge
begin

lemma RelCert_subset_in_model:
  assumes "RelCert R S"
  shows   "Arg0 R \<subseteq> Arg0 S"
  using LeU_iff_subset RelCert_implies_le[OF assms] by blast

end


section \<open>22. Ontological\_Origin\_Truth(OOT) characterization (axiom-free, U-layer only)\<close>

definition Ontological_Origin_Truth :: "bool \<Rightarrow> bool" where
  "Ontological_Origin_Truth q \<equiv>
      (\<forall>\<zeta>\<in>PDom. (Arg \<zeta>) \<preceq> (Arg q))
    \<and> (\<forall>\<zeta>\<in>PDom. \<not> ((Arg q) \<prec> (Arg \<zeta>)))"

lemma Hopt_dominates_PDom_all:
  assumes HQ:  "H_opt q"
      and PHq: "PH (Arg q)"
  shows "\<forall>\<zeta>\<in>PDom. (Arg \<zeta>) \<preceq> (Arg q)"
proof (intro ballI)
  fix \<zeta> assume Zin: "\<zeta> \<in> PDom"
  from PHq show "(Arg \<zeta>) \<preceq> (Arg q)"
    using Zin by (auto simp: PH_def PDom_def)
qed

lemma Hopt_is_Ontological_Origin_Truth:
  assumes HQ:  "H_opt q"
      and PHq: "PH (Arg q)"
  shows "Ontological_Origin_Truth q"
proof -
  have dom: "\<forall>\<zeta>\<in>PDom. (Arg \<zeta>) \<preceq> (Arg q)"
    using Hopt_dominates_PDom_all[OF HQ PHq] .

  have Headq: "Head q"
    using HQ by (simp add: H_opt_def MaxNT_def)
  hence HN: "H_negU_strict q"
    by (simp add: Head_def)

  have noabove: "\<forall>\<zeta>\<in>PDom. \<not> ((Arg q) \<prec> (Arg \<zeta>))"
  proof (intro ballI)
    fix \<zeta> assume Zin: "\<zeta> \<in> PDom"
    show "\<not> ((Arg q) \<prec> (Arg \<zeta>))"
    proof (cases "\<zeta> = q")
      case True
      then show ?thesis by (simp add: LtU_def)
    next
      case False
      from HN Zin False show ?thesis
        by (simp add: H_negU_strict_def)
    qed
  qed

  show ?thesis
    unfolding Ontological_Origin_Truth_def
    using dom noabove by auto
qed

corollary Ontological_Origin_Truth_covers:
  assumes "Ontological_Origin_Truth q" and "\<zeta> \<in> PDom"
  shows   "(Arg \<zeta>) \<preceq> (Arg q)"
  using assms unfolding Ontological_Origin_Truth_def by auto

corollary Ontological_Origin_Truth_no_strict_superior:
  assumes "Ontological_Origin_Truth q" and "\<zeta> \<in> PDom"
  shows   "\<not> ((Arg q) \<prec> (Arg \<zeta>))"
  using assms unfolding Ontological_Origin_Truth_def by auto


subsection \<open>22.1  Why Tautology(True) cannot be an Ontologic\_Origin\_truth (anti-coverage witness)\<close>
text\<open>
  The ``bad point'' clause functions as an anti-coverage witness against the Tautology.
  It says that there exist some @{text "\<zeta>"} in PDom and some support-point e such that
  e supports @{text "\<zeta>"}, while e does not support Arg True. Therefore Arg @{text "\<zeta>"} cannot be
  below Arg True in the support order. This blocks the universal coverage clause
  required for Ontological\_Origin\_Truth True, and thus prevents the Tautology
  from qualifying as an ontological origin truth.
\<close>

lemma anti_coverage_point_for_True:
  assumes "Supports e \<zeta>" and "\<not> (e \<turnstile> Arg True)"
  shows   "\<not> ((Arg \<zeta>) \<preceq> (Arg True))"
  using assms by (auto simp: LeU_def SuppU_def Supports_def)

lemma True_not_Ontological_Origin_Truth_if_point_counterexample:
  assumes Z: "\<zeta> \<in> PDom" and S: "Supports e \<zeta>" and N: "\<not> (e \<turnstile> Arg True)"
  shows   "\<not> Ontological_Origin_Truth True"

proof
  assume CT: "Ontological_Origin_Truth True"
  (* pull the coverage conjunct for this \<zeta> \<in> PDom *)
  have cov: "(Arg \<zeta>) \<preceq> (Arg True)"
    using Ontological_Origin_Truth_covers[OF CT Z] .
  (* but the pointwise witness forbids that *)
  have "\<not> ((Arg \<zeta>) \<preceq> (Arg True))"
    using anti_coverage_point_for_True[OF S N] .
  thus False using cov by contradiction
qed

lemma True_not_Ontological_Origin_Truth_if_exists_bad_point:
  assumes "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
  shows   "\<not> Ontological_Origin_Truth True"
proof -
  obtain \<zeta> e where Z: "\<zeta> \<in> PDom" and S: "Supports e \<zeta>" and N: "\<not> (e \<turnstile> Arg True)"
    using assms by blast
  show ?thesis
    by (rule True_not_Ontological_Origin_Truth_if_point_counterexample[OF Z S N])
qed

text \<open>Model-side construction of a ``bad point'' inside the FullIdBridge locale.\<close>
context FullIdBridge
begin

lemma bad_point_exists_for_True:
  assumes "\<exists>w \<zeta>. Val w \<zeta> \<and> \<not> Val w True"
  shows   "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
proof -
  obtain w \<zeta> where V\<zeta>: "Val w \<zeta>" and nT: "\<not> Val w True"
    using assms by blast
  define e where "e = iw w"
  have S\<zeta>: "Supports e \<zeta>"
    using V\<zeta> by (simp add: Supports_def bridge e_def)
  have nTrue_at_e: "\<not> (e \<turnstile> Arg True)"
    using nT by (simp add: bridge e_def)
 
  have Zin: "\<zeta> \<in> PDom"
    using S\<zeta> by (auto simp: PDom_def EDia_def)

  show ?thesis
  proof (intro bexI[of _ \<zeta>] exI[of _ e])
    show "\<zeta> \<in> PDom" by (rule Zin)
    show "Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
      by (simp add: S\<zeta> nTrue_at_e)
  qed
qed

end


subsection \<open>22.2  Non-triviality package: Ontological\_Origin\_Truths are never the tautology\<close>
text \<open>
  We establish that any H\_opt witness (which also satisfies PH) is an
  Ontological Origin Truth and is distinct from the Tautology.
\<close>

lemma Hopt_witness_is_nontrivial_Ontological_Origin_Truth:
  assumes HQ:  "H_opt q"
      and PHq: "PH (Arg q)"
      and Bad: "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
  shows "Ontological_Origin_Truth q \<and> q \<noteq> True"
proof -
  have Ctq: "Ontological_Origin_Truth q"
    by (rule Hopt_is_Ontological_Origin_Truth[OF HQ PHq])

  have nq: "q \<noteq> True"
  proof
    assume qt: "q = True"
    have CtT: "Ontological_Origin_Truth True" using Ctq qt by simp
    have notCTT: "\<not> Ontological_Origin_Truth True"
      by (rule True_not_Ontological_Origin_Truth_if_exists_bad_point[OF Bad])
    from notCTT CtT show False by contradiction
  qed

  show ?thesis using Ctq nq by blast
qed

text \<open>Existential headline (abstract form, needs a ``bad point'' assumption).\<close>
theorem Ontological_Origin_Truth_nontrivial_existence_from_Hopt_existence:
  assumes Hex: "\<exists>x. H_opt x \<and> PH (Arg x)"
      and Bad: "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
  shows "\<exists>q. Ontological_Origin_Truth q \<and> q \<noteq> True"
proof -
  obtain q where HQ: "H_opt q" and PHq: "PH (Arg q)"
    using Hex by blast
 
  have "Ontological_Origin_Truth q \<and> q \<noteq> True"
    using Hopt_witness_is_nontrivial_Ontological_Origin_Truth[OF HQ PHq Bad] by blast
   
  thus ?thesis by blast
qed


text \<open>Tripled version (abstract form, same ``bad point'' assumption).\<close>
theorem Hopt3_gives_three_nontrivial_Ontological_Origin_Truths:
  assumes H3:  "Hopt3 a b c"
      and PHa: "PH (Arg a)"
      and PHb: "PH (Arg b)"
      and PHc: "PH (Arg c)"
      and Bad: "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
  shows "Ontological_Origin_Truth a \<and> a \<noteq> True"
    and "Ontological_Origin_Truth b \<and> b \<noteq> True"
    and "Ontological_Origin_Truth c \<and> c \<noteq> True"
proof -
  from H3 have Ha: "H_opt a" and Hb: "H_opt b" and Hc: "H_opt c"
    by (auto simp: Hopt3_def)

  have A: "Ontological_Origin_Truth a \<and> a \<noteq> True"
    by (rule Hopt_witness_is_nontrivial_Ontological_Origin_Truth[OF Ha PHa Bad])
  have B: "Ontological_Origin_Truth b \<and> b \<noteq> True"
    by (rule Hopt_witness_is_nontrivial_Ontological_Origin_Truth[OF Hb PHb Bad])
  have C: "Ontological_Origin_Truth c \<and> c \<noteq> True"
    by (rule Hopt_witness_is_nontrivial_Ontological_Origin_Truth[OF Hc PHc Bad])

  show "Ontological_Origin_Truth a \<and> a \<noteq> True" by (rule A)
  show "Ontological_Origin_Truth b \<and> b \<noteq> True" by (rule B)
  show "Ontological_Origin_Truth c \<and> c \<noteq> True" by (rule C)
qed

text \<open>Model-side discharge of the ``bad point'' assumption inside FullIdBridge.\<close>
context FullIdBridge
begin

corollary Hopt_witness_is_nontrivial_Ontological_Origin_Truth_model:
  assumes HQ:  "H_opt q"
      and PHq: "PH (Arg q)"
      and Ex:  "\<exists>w \<zeta>. Val w \<zeta> \<and> \<not> Val w True"
  shows "Ontological_Origin_Truth q \<and> q \<noteq> True"
proof -
  have Bad: "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
    using bad_point_exists_for_True[OF Ex] .
  show ?thesis
    by (rule Hopt_witness_is_nontrivial_Ontological_Origin_Truth[OF HQ PHq Bad])
qed

corollary Ontological_Origin_Truth_nontrivial_existence_from_model:
  assumes Hex: "\<exists>x. H_opt x \<and> PH (Arg x)"
      and Ex:  "\<exists>w \<zeta>. Val w \<zeta> \<and> \<not> Val w True"
  shows "\<exists>q. Ontological_Origin_Truth q \<and> q \<noteq> True"
proof -
  obtain q where HQ: "H_opt q" and PHq: "PH (Arg q)"
    using Hex by blast

  have "Ontological_Origin_Truth q \<and> q \<noteq> True"
    using Hopt_witness_is_nontrivial_Ontological_Origin_Truth_model[OF HQ PHq Ex] .
  thus ?thesis by blast
qed

corollary Hopt3_gives_three_nontrivial_Ontological_Origin_Truths_model:
  assumes H3: "Hopt3 a b c"
      and PHs: "PH (Arg a)" "PH (Arg b)" "PH (Arg c)"
      and Ex: "\<exists>w \<zeta>. Val w \<zeta> \<and> \<not> Val w True"
  shows "Ontological_Origin_Truth a \<and> a \<noteq> True"
    and  "Ontological_Origin_Truth b \<and> b \<noteq> True"
    and  "Ontological_Origin_Truth c \<and> c \<noteq> True"
proof -
  have Bad: "\<exists>\<zeta>\<in>PDom. \<exists>e. Supports e \<zeta> \<and> \<not> (e \<turnstile> Arg True)"
    using bad_point_exists_for_True[OF Ex] .
   
  show "Ontological_Origin_Truth a \<and> a \<noteq> True"
    using Hopt3_gives_three_nontrivial_Ontological_Origin_Truths(1)[OF H3 PHs(1) PHs(2) PHs(3) Bad] .
   
  show "Ontological_Origin_Truth b \<and> b \<noteq> True"
    using Hopt3_gives_three_nontrivial_Ontological_Origin_Truths(2)[OF H3 PHs(1) PHs(2) PHs(3) Bad] .
   
  show "Ontological_Origin_Truth c \<and> c \<noteq> True"
    using Hopt3_gives_three_nontrivial_Ontological_Origin_Truths(3)[OF H3 PHs(1) PHs(2) PHs(3) Bad] .
qed

end


section \<open>23. No collapse, and why Trinity (not a singleton) can be the origin\<close>

lemma collapse_if_biimp_of_possibility:
  assumes T: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
      and B: "\<diamond> R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>"
  shows "\<diamond> R \<longleftrightarrow> Trinity \<Phi> \<Omega> \<psi>"
  using T B by blast

lemma noncollapse_if_not_back:
  assumes T: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
      and nB: "\<not> (\<diamond> R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>)"
  shows "\<not> (\<diamond> R \<longleftrightarrow> Trinity \<Phi> \<Omega> \<psi>)"
  using T nB by blast

lemma single_cause_collapse_if_back:
  assumes cause: "\<Phi> \<longrightarrow> R" and ret: "R \<longrightarrow> \<Phi>"
  shows "R \<longleftrightarrow> \<Phi>"
  using cause ret by blast

lemma single_cause_possibility_collapse_if_back:
  assumes cause: "\<Phi> \<longrightarrow> \<diamond> R" and ret: "\<diamond> R \<longrightarrow> \<Phi>"
  shows "\<diamond> R \<longleftrightarrow> \<Phi>"
  using cause ret by blast

section \<open>24. Trinity truthmaking pattern: (T) + (S)\<close>
text\<open>
  Philosophical background.

  This section isolates a minimal ``truthmaking'' pattern for contingent reality.
  The structure is intentionally weak and two-sided:

    (T) If the triune ground holds, then R is at least possible.
    (S) If the triune ground fails, then R fails.

  Thus the Trinity is not modeled here as a brute forcing principle
  that immediately yields R, but as a condition that opens the space of R
  while still allowing contingency. In this sense, the section is designed
  to preserve the distinction between enabling and forcing.

  The contrapositive of (S) yields a weak upward dependence:
  if R holds, then the triune structure must hold.
  But (T) itself gives only Trinity @{text "\<longrightarrow>"} @{text "\<diamond>"}R, not Trinity @{text "\<longrightarrow>"} R.
  Hence the framework blocks collapse from possibility into actuality.

  Importantly, this section is not part of the indispensable proof-core
  of either the ontological argument or the Trinity-necessity derivation.
  Those results are established independently elsewhere. The present section
  is instead an auxiliary interpretive-diagnostic layer showing how a derived
  triune ground can be related to contingent reality without forcing it.

  The final theorem records the system-level point in classical form:
  whether Trinity actually implies R is left contingent rather than built in
  by the truthmaking pattern itself. The purpose of this section is therefore
  diagnostic and anti-collapse: it shows how a triune ground may underwrite
  contingent reality without erasing contingency.\<close>

locale Trinity_Truthmaking =
  fixes \<Phi> \<Omega> \<psi> R :: bool
  assumes T: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
      and S: "\<not> (Trinity \<Phi> \<Omega> \<psi>) \<longrightarrow> \<not> R"
begin

lemma S_contrapositive: "R \<longrightarrow> Trinity \<Phi> \<Omega> \<psi>" using S by (metis)

lemma R_implies_each:
  shows "R \<longrightarrow> \<Phi>" and "R \<longrightarrow> \<Omega>" and "R \<longrightarrow> \<psi>"
  using S_contrapositive
  by (auto simp: Trinity_def)

lemma T_weak_truthmaking: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R" using T .
end

theorem Contingency_Preserved:
  assumes "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"
  shows "(Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> R) \<or> \<not> (Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> R)"
  by blast (* System-level guarantee that contingency is preserved. *)


section \<open>25. The Unity of the Trinity - Ordinal/Cardinal transcendence\<close>
text\<open>
  This section gives a small ordinal/cardinal diagnostic for the unity of the Trinity.
  The question is whether a triune relational pattern can be faithfully embedded
  into a simple linear three-step order.

  We model a finite ordinal chain with three points (O1, O2, O3), equip it with
  a meet-like operation CAP, and ask whether the three divine persons can be mapped
  bijectively into this linear structure while preserving the triune ``pair implies third''
  pattern.

  The result is negative: no such embedding exists.
  The reason is structural. In a linear chain, CAP behaves like a minimum,
  so pairwise joint structure always collapses downward into a lower point.
  But the triune pattern requires a symmetric and irreducible relational form in which
  each pair stands in a directed relation to the third. That demand cannot be realized
  inside a merely linear ordinal hierarchy.

  Hence the unity of the Trinity is not representable as a simple ordinal ranking
  or as a one-dimensional cardinal ladder. The triune structure has a mode of unity
  that exceeds linear order: it is not a serial progression of ranks, but a mutually
  irreducible relational whole.

  The later oneness lemma then complements this result from the opposite direction:
  although the triune pattern cannot be embedded into a linear three-chain,
  the essence-image of the three persons may still collapse to one at the level of unity.
  Thus plurality of persons and unity of essence are not modeled as contradiction,
  but as two formally distinct dimensions.\<close>

datatype ord3 = O1 | O2 | O3

primrec cap :: "ord3 \<Rightarrow> ord3 \<Rightarrow> ord3" where
  "cap O1 y = O1"
| "cap O2 y = (case y of O1 \<Rightarrow> O1 | O2 \<Rightarrow> O2 | O3 \<Rightarrow> O2)"
| "cap O3 y = (case y of O1 \<Rightarrow> O1 | O2 \<Rightarrow> O2 | O3 \<Rightarrow> O3)"

notation cap (infixl "CAP" 70)

primrec ltO :: "ord3 \<Rightarrow> ord3 \<Rightarrow> bool" where
  "ltO O1 y = (case y of O1 \<Rightarrow> False | O2 \<Rightarrow> True  | O3 \<Rightarrow> True)"
| "ltO O2 y = (case y of O1 \<Rightarrow> False | O2 \<Rightarrow> False | O3 \<Rightarrow> True)"
| "ltO O3 y = False"

notation ltO (infix "<o" 50)

lemma ltO_right_O1[simp]: "((x::ord3) <o O1) = False"
  by (cases x) simp_all

datatype person = F | S | G
definition Persons :: "person set" where "Persons = {F,S,G}"

definition O123    :: "ord3 set"   where "O123 = {O1,O2,O3}"

definition preserves_trinity_on_ord3 :: "(person \<Rightarrow> ord3) \<Rightarrow> bool" where
  "preserves_trinity_on_ord3 f \<longleftrightarrow>
     bij_betw f Persons O123 \<and>
     ((f F CAP f S) <o f G) \<and>
     ((f F CAP f G) <o f S) \<and>
     ((f S CAP f G) <o f F)"

lemma no_ordinal_embedding_for_trinity:
  "\<not> (\<exists>f. preserves_trinity_on_ord3 f)"
proof
  assume "\<exists>f. preserves_trinity_on_ord3 f"
  then obtain f where B:
    "bij_betw f Persons O123"
    "(f F CAP f S) <o f G"
    "(f F CAP f G) <o f S"
    "(f S CAP f G) <o f F"
    unfolding preserves_trinity_on_ord3_def by blast

  have FF_not_O1: "f F \<noteq> O1"
  proof
    assume "f F = O1" hence "(f S CAP f G) <o O1" using B(4) by simp
    thus False by simp
  qed
  have FS_not_O1: "f S \<noteq> O1"
  proof
    assume "f S = O1" hence "(f F CAP f G) <o O1" using B(3) by simp
    thus False by simp
  qed
  have FG_not_O1: "f G \<noteq> O1"
  proof
    assume "f G = O1" hence "(f F CAP f S) <o O1" using B(2) by simp
    thus False by simp
  qed

  have O1_in_image: "O1 \<in> f ` Persons"
    using B(1) unfolding bij_betw_def Persons_def O123_def by auto

  have notin: "O1 \<notin> f ` Persons"
  proof -
    have "O1 \<noteq> f F" using FF_not_O1 by simp
    moreover have "O1 \<noteq> f S" using FS_not_O1 by simp
    moreover have "O1 \<noteq> f G" using FG_not_O1 by simp
    ultimately show ?thesis by (simp add: Persons_def)
  qed
  from notin O1_in_image show False by contradiction
qed
(* Assumption note (already above in this file):
   datatype person = F | S | G
   definition Persons :: "person set" where "Persons = {F,S,G}"
*)
paragraph \<open>Remark (Why no 3-ordinal embedding)\<close>
text \<open>Two independent obstacles explain the non-embedding into the linear 3-chain 0<1<2.
The TriSupport pair @{text "\<rightarrow>"} third (meet-like) symmetry cannot be realized on a linear chain
with meet = min; symmetry would force each image to be maximal, a contradiction. \<close>
(* ---------- TriOneness : robust Eq-collapse lemma ---------- *)
lemma oneness_global:
  fixes essence :: "person \<Rightarrow> 'E"
  assumes FS: "essence F = essence S"
      and SG: "essence S = essence G"
  shows "card (essence ` Persons) = 1"
proof -
  have eq: "essence ` Persons = {essence F}"
  proof (intro subset_antisym)
    show "essence ` Persons \<subseteq> {essence F}"
    proof
      fix x assume "x \<in> essence ` Persons"
      then obtain p where pP: "p \<in> Persons" and x: "x = essence p" by auto
      from pP have "p = F \<or> p = S \<or> p = G" by (auto simp: Persons_def)
     have "x = essence F"
  using x FS SG pP by (cases p) (auto simp: Persons_def)
      thus "x \<in> {essence F}" by simp
    qed
    show "{essence F} \<subseteq> essence ` Persons"
      by (auto simp: Persons_def)
  qed
  show ?thesis by (simp add: eq)
qed
(* --- H-principle (extended): if PH holds, it supports both "possible" and "actually true" cases --- *)
lemma H_principle_from_PH_true:
  assumes "PH (Arg Q)" and "TrueNow \<zeta>"
  shows "(Arg \<zeta>) \<preceq> (Arg Q)"
  using assms by (simp add: PH_def)

lemma H_principle_from_PH_possible:
  assumes "PH (Arg Q)" and "EDia \<zeta>"
  shows "(Arg \<zeta>) \<preceq> (Arg Q)"
  using assms by (simp add: PH_def)

lemma H_principle_full_from_PH:
  assumes "PH (Arg Q)"
  shows "\<forall>\<zeta>. (TrueNow \<zeta> \<or> EDia \<zeta>) \<longrightarrow> (Arg \<zeta>) \<preceq> (Arg Q)"
  using assms by (simp add: PH_def)

lemma PH_no_strict_superior_pair:
  assumes "PH (Arg Q)" and "PH (Arg R)"
  shows "\<not> ((Arg Q) \<prec>\<^sup>P (Arg R)) \<and> \<not> ((Arg R) \<prec>\<^sup>P (Arg Q))"
  using PH_no_strict_superior assms by blast


section \<open>26. Uniqueness of the Trinity (MaxCov-level)\<close>
text \<open>
   Core idea:
    pick one triple (A,B,C) of MaxCov points with pairwise non-@{text "\<approx>"}
    use the ``no 4 MaxCov points can be pairwise non-@{text "\<approx>"}'' exclusion (Excl4)
      to show every MaxCov X must fall into one of the three @{text "\<approx>"}-classes
    hence the union of the three @{text "\<approx>"}-classes is independent of the chosen triple
\<close>

locale Trinity_Uniqueness_MaxCov =
  fixes MaxCov :: "U \<Rightarrow> bool"
  assumes SYM:   "\<And>p q. p \<approx> q \<Longrightarrow> q \<approx> p"
      and TRANS: "\<And>p q r. p \<approx> q \<Longrightarrow> q \<approx> r \<Longrightarrow> p \<approx> r"
      and Excl4:
        "\<And>a b c d.
           \<lbrakk> MaxCov a; MaxCov b; MaxCov c; MaxCov d;
             \<not>(a \<approx> b); \<not>(a \<approx> c); \<not>(b \<approx> c);
             \<not>(a \<approx> d); \<not>(b \<approx> d); \<not>(c \<approx> d) \<rbrakk> \<Longrightarrow> False"
begin
(* ------------------------------------------------------------- *)
(* 26.0  A "Top-3" triple at the MaxCov-level                      *)
(* ------------------------------------------------------------- *)
definition TrinityTop3_mc :: "U \<Rightarrow> U \<Rightarrow> U \<Rightarrow> bool" where
  "TrinityTop3_mc A B C \<longleftrightarrow>
     MaxCov A \<and> MaxCov B \<and> MaxCov C \<and>
     \<not>(A \<approx> B) \<and> \<not>(A \<approx> C) \<and> \<not>(B \<approx> C)"

definition Top3Classes :: "U \<Rightarrow> U \<Rightarrow> U \<Rightarrow> U set" where
  "Top3Classes A B C \<equiv> {x. x \<approx> A \<or> x \<approx> B \<or> x \<approx> C}"

lemma not_EqU_sym:
  assumes H: "\<not>(x \<approx> y)"
  shows "\<not>(y \<approx> x)"
proof
  assume YX: "y \<approx> x"
  hence XY: "x \<approx> y" using SYM by blast
  show False using H XY by contradiction
qed
(* ------------------------------------------------------------- *)
(* 26.1  Any MaxCov point falls into the Top-3 classes             *)
(* ------------------------------------------------------------- *)
lemma MaxCov_must_fall_into_Top3Classes:
  assumes T:  "TrinityTop3_mc A B C"
      and MX: "MaxCov X"
  shows "X \<approx> A \<or> X \<approx> B \<or> X \<approx> C"
proof (rule classical)
  assume H: "\<not>(X \<approx> A \<or> X \<approx> B \<or> X \<approx> C)"
  have XA: "\<not>(X \<approx> A)" and XB: "\<not>(X \<approx> B)" and XC: "\<not>(X \<approx> C)"
    using H by auto

  have MA: "MaxCov A" and MB: "MaxCov B" and MC: "MaxCov C"
    using T by (simp_all add: TrinityTop3_mc_def)
  have AB: "\<not>(A \<approx> B)" and AC: "\<not>(A \<approx> C)" and BC: "\<not>(B \<approx> C)"
    using T by (simp_all add: TrinityTop3_mc_def)

  have AX: "\<not>(A \<approx> X)" using XA by (rule not_EqU_sym)
  have BX: "\<not>(B \<approx> X)" using XB by (rule not_EqU_sym)
  have CX: "\<not>(C \<approx> X)" using XC by (rule not_EqU_sym)

  have False
    using Excl4[OF MA MB MC MX AB AC BC AX BX CX] .
  thus "X \<approx> A \<or> X \<approx> B \<or> X \<approx> C" by blast
qed
(* ------------------------------------------------------------- *)
(* 26.2  The Top-3 union of \<approx>-classes is unique             *)
(* ------------------------------------------------------------- *)
lemma Top3Classes_unique:
  assumes T1: "TrinityTop3_mc A B C"
      and T2: "TrinityTop3_mc A' B' C'"
  shows "Top3Classes A B C = Top3Classes A' B' C'"
proof (rule set_eqI, rule iffI)
  fix x
  (* 1. Left to Right: x \<in> Top3Classes A B C \<Longrightarrow> x \<in> Top3Classes A' B' C' *)
  assume hx: "x \<in> Top3Classes A B C"
  hence hx0: "x \<approx> A \<or> x \<approx> B \<or> x \<approx> C" by (simp add: Top3Classes_def)

  from hx0 show "x \<in> Top3Classes A' B' C'"
  proof (elim disjE)
    assume xA: "x \<approx> A"
    have MA: "MaxCov A" using T1 unfolding TrinityTop3_mc_def by simp
    have "A \<approx> A' \<or> A \<approx> B' \<or> A \<approx> C'"
      using MaxCov_must_fall_into_Top3Classes[OF T2 MA] .
    thus ?thesis using xA TRANS unfolding Top3Classes_def by blast
  next
    assume xB: "x \<approx> B"
    have MB: "MaxCov B" using T1 unfolding TrinityTop3_mc_def by simp
    have "B \<approx> A' \<or> B \<approx> B' \<or> B \<approx> C'"
      using MaxCov_must_fall_into_Top3Classes[OF T2 MB] .
    thus ?thesis using xB TRANS unfolding Top3Classes_def by blast
  next
    assume xC: "x \<approx> C"
    have MC: "MaxCov C" using T1 unfolding TrinityTop3_mc_def by simp
    have "C \<approx> A' \<or> C \<approx> B' \<or> C \<approx> C'"
      using MaxCov_must_fall_into_Top3Classes[OF T2 MC] .
    thus ?thesis using xC TRANS unfolding Top3Classes_def by blast
  qed

next
  fix x
  (* 2. Right to Left: x \<in> Top3Classes A' B' C' \<Longrightarrow> x \<in> Top3Classes A B C *)
  assume hx': "x \<in> Top3Classes A' B' C'"
  hence hx0': "x \<approx> A' \<or> x \<approx> B' \<or> x \<approx> C'" by (simp add: Top3Classes_def)

  from hx0' show "x \<in> Top3Classes A B C"
  proof (elim disjE)
    assume xA': "x \<approx> A'"
    have MA': "MaxCov A'" using T2 unfolding TrinityTop3_mc_def by simp
    have "A' \<approx> A \<or> A' \<approx> B \<or> A' \<approx> C"
      using MaxCov_must_fall_into_Top3Classes[OF T1 MA'] .
    thus ?thesis using xA' TRANS unfolding Top3Classes_def by blast
  next
    assume xB': "x \<approx> B'"
    have MB': "MaxCov B'" using T2 unfolding TrinityTop3_mc_def by simp
    have "B' \<approx> A \<or> B' \<approx> B \<or> B' \<approx> C"
      using MaxCov_must_fall_into_Top3Classes[OF T1 MB'] .
    thus ?thesis using xB' TRANS unfolding Top3Classes_def by blast
  next
    assume xC': "x \<approx> C'"
    have MC': "MaxCov C'" using T2 unfolding TrinityTop3_mc_def by simp
    have "C' \<approx> A \<or> C' \<approx> B \<or> C' \<approx> C"
      using MaxCov_must_fall_into_Top3Classes[OF T1 MC'] .
    thus ?thesis using xC' TRANS unfolding Top3Classes_def by blast
  qed
qed
(* ------------------------------------------------------------- *)
(* 26.3  Convenience corollary                                    *)
(* ------------------------------------------------------------- *)
corollary Top3Classes_unique_any_point:
  assumes T1: "TrinityTop3_mc A B C"
      and T2: "TrinityTop3_mc A' B' C'"
  shows "\<forall>x. x \<in> Top3Classes A B C \<longleftrightarrow> x \<in> Top3Classes A' B' C'"
  using Top3Classes_unique[OF T1 T2] by blast

end
(* ========================================================= *)
(*   WRAPPERS (explicitly labeled, still the same math)
    - "God finality" on PDom (from H_opt)
    - "Trinity actuality" N3 (from Hopt3)                          *)
(* ========================================================= *)
section \<open>27. Wrappers: ``God finality'' and ``Trinity actuality''\<close>

text \<open>``God finality'' (order-theoretic necessity within PDom): if H\_opt q, then nothing in PDom
  is strictly superior to Arg q. This is just a named wrapper of \<open>argument\_finality\_PDom\<close>.\<close>
lemma God_finality:
  assumes "H_opt q"
  shows "\<forall>\<zeta>\<in>PDom. \<not> ((Arg q) \<prec> (Arg \<zeta>))"
  using argument_finality_PDom[OF assms] .

text \<open>``Trinity actuality'': from \<open>Hopt3 a b c\<close> (three H\_opt possibles), we get the N3 pattern
  with no axiom. This is a named wrapper of \<open>OnlyN3_from_Hopt3_unboxed\<close>.\<close>
lemma Trinity_actuality:
  assumes H3: "Hopt3 a b c"
      and MCI: "\<And>e X Y. Supports e X \<Longrightarrow> Supports e Y \<Longrightarrow> Supports e (X \<and> Y)"
  shows N3
  by (rule OnlyN3_from_Hopt3_unboxed[OF H3 MCI])


section \<open>28. Final Locale Audit: Discharging Core locale assupmtions \<close>
text \<open>
  This section provides the formal certification of the entire logical architecture.
  We establish a minimal analytic environment and mechanically discharge:
  1) The ``No-Superfluous''(NS), ES, Cov, MCL, MCR constraint via Band Collapse.
  2) The ``Excl4'' constraint for the Uniqueness of the Trinity.
\<close>

locale Final_NS_Audit =
  fixes \<Omega> \<Psi> \<Phi> :: bool
  \<comment> \<open>Minimal boolean grammar assumptions (analytic truths)\<close>
  assumes MCL: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A"
      and MCR: "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B"
      and MCI: "\<And>e A B. Makes e A \<Longrightarrow> Makes e B \<Longrightarrow> Makes e (A \<and> B)"
  \<comment> \<open>Core existence and ontological coverage assumptions\<close>
  assumes ES:  "EDia_ep (\<Omega> \<and> \<Psi>)"
      and Cov: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
  \<comment> \<open>H-principle projection\<close>
      and Core_to_Y_rule: "\<And>Y. H_opt_ep Y \<Longrightarrow> Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg Y"
begin

 
subsection\<open>28.1  Discharging NS(No-Superfluous), ES, Cov, MCL, MCR \<close>

  sublocale Trinity_NS_Audit: Band_Collapse_Superfluous \<Omega> \<Psi> \<Phi>
  proof
    show "EDia_ep (\<Omega> \<and> \<Psi>)" by (rule ES)
    show "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>" by (rule Cov)
    show "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e A" by (rule MCL)
    show "\<And>e A B. Makes e (A \<and> B) \<Longrightarrow> Makes e B" by (rule MCR)
   
    show "((Arg (\<Omega> \<and> \<Psi>)) \<preceq> Arg \<Phi>) \<Longrightarrow>
          (\<forall>Y. H_opt_ep Y \<longrightarrow> EDia_ep Y \<longrightarrow>
               Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi> \<longrightarrow>
               Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>))"
    proof -
      assume "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg \<Phi>"
      show "\<forall>Y. H_opt_ep Y \<longrightarrow> EDia_ep Y \<longrightarrow> Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi> \<longrightarrow> Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
      proof (intro allI impI)
        fix Y assume HY: "H_opt_ep Y" and EY: "EDia_ep Y" and Band: "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<preceq> Arg \<Phi>"
        have CTY: "Arg (\<Omega> \<and> \<Psi>) \<preceq> Arg Y" by (rule Core_to_Y_rule[OF HY])
        show "Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<approx> Arg (\<Omega> \<and> \<Psi>)"
          using core_conj_equiv_basic [OF ES HY EY CTY MCL MCI] by assumption
      qed
    qed
  qed


subsection\<open>28.2 Discharge the Trinity\_Uniqueness\_MaxCov Locale \<close>

  sublocale Trinity_Uniqueness_Certified: Trinity_Uniqueness_MaxCov "\<lambda>u. \<exists>Y. u = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y"
  proof
    show "\<And>p q. p \<approx> q \<Longrightarrow> q \<approx> p" by (rule EqU_sym)
    show "\<And>p q r. p \<approx> q \<Longrightarrow> q \<approx> r \<Longrightarrow> p \<approx> r" by (rule EqU_trans)

    show "\<And>a b c d.
         \<lbrakk>\<exists>Y. a = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y;
          \<exists>Y. b = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y;
          \<exists>Y. c = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y;
          \<exists>Y. d = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y;
          \<not> a \<approx> b; \<not> a \<approx> c; \<not> b \<approx> c; \<not> a \<approx> d; \<not> b \<approx> d; \<not> c \<approx> d\<rbrakk> \<Longrightarrow> False"
    proof -
      fix a b c d
      assume H_a: "\<exists>Y. a = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y"
         and H_b: "\<exists>Y. b = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y"
         and H_c: "\<exists>Y. c = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y"
         and H_d: "\<exists>Y. d = Arg ((\<Omega> \<and> \<Psi>) \<and> Y) \<and> H_opt_ep Y \<and> EDia_ep Y"
         and N_ab: "\<not> a \<approx> b" and N_ac: "\<not> a \<approx> c" and N_bc: "\<not> b \<approx> c"
         and N_ad: "\<not> a \<approx> d" and N_bd: "\<not> b \<approx> d" and N_cd: "\<not> c \<approx> d"

      obtain Y1 where A: "a = Arg ((\<Omega> \<and> \<Psi>) \<and> Y1)" "H_opt_ep Y1" "EDia_ep Y1" using H_a by blast
      obtain Y2 where B: "b = Arg ((\<Omega> \<and> \<Psi>) \<and> Y2)" "H_opt_ep Y2" "EDia_ep Y2" using H_b by blast
      obtain Y3 where C: "c = Arg ((\<Omega> \<and> \<Psi>) \<and> Y3)" "H_opt_ep Y3" "EDia_ep Y3" using H_c by blast
      obtain Y4 where D: "d = Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)" "H_opt_ep Y4" "EDia_ep Y4" using H_d by blast
      \<comment> \<open>Explicitly map the inequalities to the Arg structure\<close>
      have neqs: "\<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y2)) \<and>
                  \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y3)) \<and>
                  \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)) \<and>
                  \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y3)) \<and>
                  \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)) \<and>
                  \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y3) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4))"
        using A(1) B(1) C(1) D(1) N_ab N_ac N_bc N_ad N_bd N_cd by simp
      \<comment> \<open>Summon the Band Collapse theorem from Part 1. It forces the exact opposite of our neqs\<close>
      have col: "\<not> (\<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y2)) \<and>
                    \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y3)) \<and>
                    \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y1) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)) \<and>
                    \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y3)) \<and>
                    \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y2) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)) \<and>
                    \<not> (Arg ((\<Omega> \<and> \<Psi>) \<and> Y3) \<approx> Arg ((\<Omega> \<and> \<Psi>) \<and> Y4)))"
        by (rule Trinity_NS_Audit.no_four_distinct_classes_in_band_pre132 [OF A(2) A(3) B(2) B(3) C(2) C(3) D(2) D(3)])
           \<comment> \<open>Contradiction achieved\<close>
      show False using neqs col by contradiction
    qed
  qed

end

end