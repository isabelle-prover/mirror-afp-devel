theory Calculus
  imports Syntax "HOL-Library.Infinite_Typeclass" "HOL-Eisbach.Eisbach"
begin

section \<open>The natural-deduction calculus NK\<close>

text \<open>We formalise the calculus \<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> of BKK (BKK Definition 7.1, Figures 6 and 7) --- the base
  system \<open>NK\<^sub>\<beta>\<close> together with the extensional rules \<open>NK(f)\<close> and \<open>NK(b)\<close> --- extended by BKK's
  rules \<open>NK(=\<^sub>r)\<close> and \<open>NK(=\<^sub>l)\<close> for the primitive equality of our signature (BKK Figure 9,
  Remark 7.9) and by the description rule \<open>NK(\<iota>)\<close>, a premise-free axiom scheme describing
  Leibniz singletons (beyond BKK, following Andrews 1972, their reference [3]).  BKK prove
  \<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> sound and complete for the class of \<open>\<Sigma>\<close>-Henkin models \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (BKK Theorem 7.3,
  Theorem 7.6, Corollary 7.7), and sketch the extension by primitive equality in Remark 7.9; we
  prove the fully extended calculus sound and complete for the correspondingly enriched class (with
  primitive equality and description, Section 2).  The provability judgement \<open>\<Phi> \<turnstile> A\<close> relates a set
  \<open>\<Phi>\<close> of formulas to a formula \<open>A\<close>; the rules impose well-formedness where they need it, and
  closedness is nowhere required.  Eigenvariables are @{emph \<open>parameters\<close>} (BKK's \<open>w\<^bsub>\<alpha>\<^esub>\<close>),
  which --- unlike the free variables used only during evaluation --- never occur bound.\<close>

subsection \<open>Discharging well-formedness side conditions\<close>

text \<open>Nearly every derived rule and every derivation inside the calculus carries \<open>wff\<close>
  side conditions.  The Eisbach method \<open>wffs\<close> discharges the routine ones: the composite
  introduction rules are tried first --- the applied connectives ahead of raw application,
  so that \<open>\<^bold>\<not> A\<close> is decomposed by \<open>wff_Not\<close> rather than mistyped as a bare application ---
  and the atoms close the leaves.\<close>

method wffs =
  ((intro wff_Not wff_ImpB wff_AndB wff_AllN wff_ExN wff_Forall wff_PEq wff_LeibE
          wff_Leib wff_Eq wff_TrueB wff_FalseB wff_Iota wff_App)?;
   (rule wff_Fre wff_Par)?)

subsection \<open>The inference rules of \<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> (BKK Figures 6, 7 and 9)\<close>

text \<open>Following BKK we work with the primitive constants \<open>\<^bold>\<not>\<close>, \<open>\<^bold>\<or>\<close>, \<open>\<Pi>\<^bsub>\<alpha>\<^esub>\<close>, \<open>\<^bold>=\<^bsub>\<alpha>\<^esub>\<close> and \<open>\<^bold>\<iota>\<^bsub>\<alpha>\<^esub>\<close>;
  the remaining operators (\<open>\<^bold>\<supset>\<close>, \<open>\<^bold>\<bottom>\<close>, Leibniz equality \<open>\<^bold>\<doteq>\<close>) are defined.  The rule \<open>NK(\<Pi>I)\<close>
  discharges an eigen-parameter \<open>w\<close> that must not occur in the context \<open>\<Phi>\<close> or in the
  quantified predicate.\<close>

inductive bprov :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 40) where
    Hyp:   "A \<in> \<Phi> \<Longrightarrow> \<Phi> \<turnstile> A"  \<comment> \<open>BKK \<open>NK(Hyp)\<close>\<close>
  | Beta:  "A \<approx>\<^bsub>\<o>\<^esub> B \<Longrightarrow> \<Phi> \<turnstile> A \<Longrightarrow> \<Phi> \<turnstile> B"  \<comment> \<open>BKK \<open>NK(\<beta>)\<close>\<close>
  | NegI:  "\<Phi> \<union> {A} \<turnstile> \<^bold>\<bottom> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<not> A"  \<comment> \<open>BKK \<open>NK(\<not>I)\<close>\<close>
  | NegE:  "\<Phi> \<turnstile> \<^bold>\<not> A \<Longrightarrow> \<Phi> \<turnstile> A \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(C) \<Longrightarrow> \<Phi> \<turnstile> C"  \<comment> \<open>BKK \<open>NK(\<not>E)\<close>\<close>
  | DisIL: "\<Phi> \<turnstile> A \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B) \<Longrightarrow> \<Phi> \<turnstile> A \<^bold>\<or> B"  \<comment> \<open>BKK \<open>NK(\<or>I\<^sub>L)\<close>\<close>
  | DisIR: "\<Phi> \<turnstile> B \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> A \<^bold>\<or> B"  \<comment> \<open>BKK \<open>NK(\<or>I\<^sub>R)\<close>\<close>
  | DisE:  "\<Phi> \<turnstile> A \<^bold>\<or> B \<Longrightarrow> \<Phi> \<union> {A} \<turnstile> C \<Longrightarrow> \<Phi> \<union> {B} \<turnstile> C
            \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B) \<Longrightarrow> \<Phi> \<turnstile> C"  \<comment> \<open>BKK \<open>NK(\<or>E)\<close>\<close>
  | PiI:   "\<Phi> \<turnstile> G \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>) \<Longrightarrow> wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G) \<Longrightarrow> w \<notin> pars G
            \<Longrightarrow> (\<forall>D \<in> \<Phi>. w \<notin> pars D)
            \<Longrightarrow> \<Phi> \<turnstile> (Pi \<alpha>) \<^bold>\<cdot> G"  \<comment> \<open>BKK \<open>NK(\<Pi>I)\<close>\<close>
  | PiE:   "\<Phi> \<turnstile> (Pi \<alpha>) \<^bold>\<cdot> G \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> G \<^bold>\<cdot> A"  \<comment> \<open>BKK \<open>NK(\<Pi>E)\<close>\<close>
  | Contr: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<bottom> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> A"  \<comment> \<open>BKK \<open>NK(Contr)\<close>\<close>
  | FuncE: "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> (G \<^bold>\<cdot> (Bnd 0) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> H \<^bold>\<cdot> (Bnd 0))
            \<Longrightarrow> wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>(G) \<Longrightarrow> wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>(H)
            \<Longrightarrow> \<Phi> \<turnstile> G \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> H"  \<comment> \<open>BKK \<open>NK(f)\<close>\<close>
  | BoolE: "\<Phi> \<union> {A} \<turnstile> B \<Longrightarrow> \<Phi> \<union> {B} \<turnstile> A \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)
            \<Longrightarrow> \<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B"  \<comment> \<open>BKK \<open>NK(b)\<close>\<close>
  | Desc:  "wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> (Iota \<alpha>) \<^bold>\<cdot> ((Leib \<alpha>) \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A"
      \<comment> \<open>\<open>NK(\<iota>)\<close>, beyond BKK: Leibniz-singleton description (Andrews 1972)\<close>
  | EqR:   "wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> A \<^bold>=\<^bsub>\<alpha>\<^esub> A"  \<comment> \<open>BKK \<open>NK(=\<^sub>r)\<close>, Figure 9\<close>
  | EqL:   "\<Phi> \<turnstile> C \<^bold>=\<^bsub>\<alpha>\<^esub> D \<Longrightarrow> \<Phi> \<turnstile> C \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> D"  \<comment> \<open>BKK \<open>NK(=\<^sub>l)\<close>, Figure 9\<close>

text \<open>Provability from the empty hypothesis set, with its own turnstile.\<close>

abbreviation provable :: "'p tm \<Rightarrow> bool"  (\<open>\<turnstile> _\<close> [61] 60) where
  "provable A \<equiv> {} \<turnstile> A"

text \<open>Everything derivable from a set of propositions is a proposition.\<close>

lemma bprov_wff: "\<Phi> \<turnstile> C \<Longrightarrow> (\<And> A . A \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A)) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(C)"
  by (induct rule: bprov.induct) (auto intro: wff_Pi wff_App wff_Iota simp: beq_wffR)

text \<open>Derivability is stable under injective parameter renaming --- injectivity keeps the
  eigen-parameter side-conditions of \<open>NK(\<Pi>I)\<close>.  This lets us move eigen-parameters out of the
  way, which is what makes weakening (and later, extension of consistent sets) admissible.\<close>

lemma bprov_rename: assumes \<pi>: "inj \<pi>" shows "\<Phi> \<turnstile> C \<Longrightarrow> prn \<pi> ` \<Phi> \<turnstile> prn \<pi> C"
proof (induction rule: bprov.induct)
  case PiI thus ?case
    by auto (smt (verit) assms bprov.PiI image_iff inj_image_mem_iff tm.set_map wff_prn)
qed(auto intro: bprov.intros)

subsection \<open>Weakening\<close>

text \<open>Weakening is admissible.  BKK leave this structural property implicit (their contexts
  are sets and the rules mention the context only via membership and extension); in the
  formalisation the eigen-parameter condition of \<open>NK(\<Pi>I)\<close> makes it a genuine lemma.\<close>

text \<open>Transposing two parameters --- an involutive, injective renaming --- lets us shift an
  eigen-parameter to a fresh one when weakening the context.\<close>

definition swp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "swp a b = (\<lambda>x. if x = a then b else if x = b then a else x)"
lemma swp_inj: "inj (swp a b)" by (auto simp: swp_def inj_def)
lemma swp_swp [simp]: "swp a b (swp a b x) = x" by (auto simp: swp_def)
text \<open>Statement preserved verbatim from the published version of this entry (compatibility
  export).\<close>

lemma swp_apply: "swp a b a = b" by (simp add: swp_def)
lemma prn_swp_swp [simp]: "prn (swp a b) (prn (swp a b) t) = t" by (simp add: prn_prn)
lemma image_prn_swp_swp [simp]: "prn (swp a b) ` (prn (swp a b) ` S) = S"
  by (simp add: image_image)

text \<open>\<open>freep\<close> is our rendering of BKK's @{emph \<open>sufficiently \<open>\<Sigma>\<close>-pure\<close>} (BKK Definition 6.3):
  since a parameter name may be used at every type, infinitely many unused names provide, for
  each type, a witness reservoir of the cardinality of the (countable) language.\<close>

definition usedp :: "'p tm set \<Rightarrow> 'p set" where "usedp \<Phi> \<equiv> (\<Union>D \<in> \<Phi>. pars D)"
definition freep :: "'p tm set \<Rightarrow> bool" where "freep \<Phi> \<equiv> infinite (- usedp \<Phi>)"
lemma usedp_insert: "usedp (insert A \<Phi>) = pars A \<union> usedp \<Phi>" by (auto simp: usedp_def)
lemma usedp_prn: "usedp (prn \<pi> ` \<Phi>) = \<pi> ` usedp \<Phi>" by (auto simp: usedp_def tm.set_map)
lemma bij_swp: "bij (swp a b)" by (simp add: involuntory_imp_bij)
lemma infinite_inj_image: "inj f \<Longrightarrow> infinite A \<Longrightarrow> infinite (f ` A)"
  by (metis finite_imageD inj_on_subset subset_UNIV)
lemma freep_add: "freep \<Phi> \<Longrightarrow> freep (insert A \<Phi>)"
  by (simp add: usedp_insert freep_def)
     (metis finite_pars Diff_eq Diff_infinite_finite inf.commute)
lemma freep_un_finite: "freep S \<Longrightarrow> finite T \<Longrightarrow> freep (S \<union> T)"
proof -
  assume "freep S" "finite T"
  hence "finite (usedp T)" by (auto simp: usedp_def)
  moreover have "- usedp (S \<union> T) = - usedp S - usedp T"
    by (auto simp: usedp_def)
  ultimately show ?thesis using \<open>freep S\<close>
    by (metis freep_def Diff_infinite_finite)
qed
lemma freep_fresh: "freep \<Phi> \<Longrightarrow> finite F \<Longrightarrow> \<exists>w. w \<notin> usedp \<Phi> \<and> w \<notin> F" 
  by (meson ComplD freep_def rev_finite_subset subsetI)
lemma freep_prn: "freep \<Phi> \<Longrightarrow> freep (prn (swp a b) ` \<Phi>)" 
  by (metis bij_image_Compl_eq bij_swp freep_def infinite_inj_image
      swp_inj usedp_prn)

lemma bprov_weaken: "\<Phi> \<turnstile> C \<Longrightarrow> \<Phi> \<subseteq> \<Psi> \<Longrightarrow> freep \<Psi> \<Longrightarrow> \<Psi> \<turnstile> C"
proof (induction arbitrary: \<Psi> rule: bprov.induct)
  case NegI thus ?case
    by (simp add: bprov.NegI freep_add sup.order_iff)
next
  case DisE thus ?case
    by (metis Un_insert_right bprov.DisE freep_add sup.cobounded2
              sup.order_iff sup_bot_right)
next
  case (PiI \<Phi> G w \<alpha>) 
  then obtain w' where w': "w' \<notin> usedp \<Psi>" "w' \<notin> pars G" "w' \<noteq> w"
    using freep_fresh[of _ "pars G \<union> {w}"] by force
  have wsub: "\<Phi> \<subseteq> prn (swp w w') ` \<Psi>"
  proof
    fix D assume D: "D \<in> \<Phi>"
    hence "w \<notin> pars D" and "w' \<notin> pars D"  
      by (simp add: PiI.hyps(4)) (metis D PiI.prems(1) UN_I subset_iff usedp_def w'(1)) 
    hence "prn (swp w w') D = D" by (auto simp: swp_def intro: prn_cong)
    thus "D \<in> prn (swp w w') ` \<Psi>" using D PiI.prems(1) by force
  qed
  have "prn (swp w w') ` \<Psi> \<turnstile> G \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>)"
    using PiI freep_prn wsub by meson
  hence "\<Psi> \<turnstile> (prn (swp w w') G) \<^bold>\<cdot> (w'\<^sup>p\<^bsub>\<alpha>\<^esub>)"
     by (metis bprov_rename image_prn_swp_swp swp_inj tm.simps(121,127) swp_def)
  moreover have "prn (swp w w') G = G"
    using PiI.hyps(3) w'(2)
    by (auto simp: swp_def intro: prn_cong)
  ultimately have "\<Psi> \<turnstile> G \<^bold>\<cdot> (w'\<^sup>p\<^bsub>\<alpha>\<^esub>)" by simp
  moreover have "\<forall>D \<in> \<Psi>. w' \<notin> pars D" using w'(1)
    by (auto simp: usedp_def)
  ultimately show ?case using PiI.hyps(2) w'(2)
    by (auto intro: bprov.PiI)
next case Contr thus ?case 
  by (metis Un_insert_right bprov.Contr freep_add sup.cobounded2
      sup.order_iff sup_bot.right_neutral)
next case BoolE thus ?case by (simp add: bprov.BoolE freep_add sup.absorb_iff2)
qed(auto intro: bprov.intros)

subsection \<open>Compactness\<close>

text \<open>Every derivation uses only finitely many hypotheses --- BKK: ``since every \<open>NK\<^sup>*\<close>-proof is
  finite'' (used in the proof of BKK Corollary 7.8).  With set-based contexts this is again a
  genuine lemma.\<close>

text \<open>When the parameter type is infinite, every finite context leaves infinitely many
  parameters free.\<close>

lemma freep_finite: fixes \<Phi> :: "'p::infinite tm set" assumes "finite \<Phi>"
  shows "freep \<Phi>"
by (metis assms freep_def usedp_def finite_pars infinite_UNIV
    finite_Diff2 Compl_eq_Diff_UNIV finite_UN)

lemma bprov_finite: "\<Phi> \<turnstile> (C :: 'p::infinite tm) \<Longrightarrow> \<exists>\<Phi>\<^sub>0. finite \<Phi>\<^sub>0 \<and> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<and> \<Phi>\<^sub>0 \<turnstile> C"
proof (induction rule: bprov.induct)
  case (NegI \<Phi> A) thus ?case
    by (smt (verit) Un_infinite Un_insert_right bprov.NegI
        bprov_weaken freep_add freep_finite subset_UnE
        subset_insertI subset_singleton_iff)
next
  case (NegE \<Phi> A C) thus ?case
    by (smt (verit) bprov.NegE bprov_weaken finite_UnI freep_finite le_sup_iff
        sup_ge1 sup_ge2)
next
  case (DisE \<Phi> A B C)
  then obtain \<Phi>\<^sub>1 \<Phi>\<^sub>2 \<Phi>\<^sub>3 where
    Q1: "finite \<Phi>\<^sub>1" "\<Phi>\<^sub>1 \<subseteq> \<Phi>" "\<Phi>\<^sub>1 \<turnstile> A \<^bold>\<or> B" and
    Q2: "finite \<Phi>\<^sub>2" "\<Phi>\<^sub>2 \<subseteq> \<Phi> \<union> {A}" "\<Phi>\<^sub>2 \<turnstile> C" and
    Q3: "finite \<Phi>\<^sub>3" "\<Phi>\<^sub>3 \<subseteq> \<Phi> \<union> {B}" "\<Phi>\<^sub>3 \<turnstile> C"
    by blast
  moreover define \<Phi>\<^sub>0 where "\<Phi>\<^sub>0 = \<Phi>\<^sub>1 \<union> (\<Phi>\<^sub>2 - {A}) \<union> (\<Phi>\<^sub>3 - {B})"
  ultimately have "finite \<Phi>\<^sub>0" and "\<Phi>\<^sub>0 \<subseteq> \<Phi>" by auto
  moreover {
    have "\<Phi>\<^sub>0 \<turnstile> A \<^bold>\<or> B"
      by (metis Q1(3) \<Phi>\<^sub>0_def bprov_weaken dual_order.refl calculation(1)
          freep_finite le_sup_iff)
    moreover have "\<Phi>\<^sub>0 \<union> {A} \<turnstile> C" and "\<Phi>\<^sub>0 \<union> {B} \<turnstile> C"
      by (auto intro: bprov_weaken[OF Q2(3)] bprov_weaken[OF Q3(3)]
               simp: \<Phi>\<^sub>0_def Q1(1) Q2(1) Q3(1) freep_finite)
    ultimately have "\<Phi>\<^sub>0 \<turnstile> C" by (auto intro: DisE bprov.DisE)
  }
  ultimately show ?case by blast
next case (Contr \<Phi> A) show ?case by (smt (verit, del_insts) Contr.IH
    Contr.hyps(2) Un_infinite Un_insert_right
          bprov.Contr bprov_weaken freep_add freep_finite subset_UnE
              subset_insertI subset_singleton_iff)
next case (BoolE \<Phi> A B)
  then obtain \<Phi>\<^sub>1 \<Phi>\<^sub>2 where
    Q1: "finite \<Phi>\<^sub>1" "\<Phi>\<^sub>1 \<subseteq> \<Phi> \<union> {A}" "\<Phi>\<^sub>1 \<turnstile> B" and
    Q2: "finite \<Phi>\<^sub>2" "\<Phi>\<^sub>2 \<subseteq> \<Phi> \<union> {B}" "\<Phi>\<^sub>2 \<turnstile> A" 
    by blast
  moreover define \<Phi>\<^sub>0 where "\<Phi>\<^sub>0 = (\<Phi>\<^sub>1 - {A}) \<union> (\<Phi>\<^sub>2 - {B})"
  ultimately have "finite \<Phi>\<^sub>0" and "\<Phi>\<^sub>0 \<subseteq> \<Phi>" by auto
  moreover {
    have "\<Phi>\<^sub>0 \<union> {A} \<turnstile> B" and "\<Phi>\<^sub>0 \<union> {B} \<turnstile> A"
      by (auto intro: bprov_weaken[OF Q1(3)] bprov_weaken[OF Q2(3)]
               simp: calculation Q1(1,2) Q2(1) \<Phi>\<^sub>0_def freep_finite)
    hence "\<Phi>\<^sub>0 \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B" using BoolE by (auto intro: bprov.intros)
  }
  ultimately show ?case by blast
qed(auto intro: bprov.intros)

subsection \<open>Derivability from hypotheses\<close>

text \<open>The calculus \<open>\<turnstile>\<close> manipulates its context as a set, and \<open>NK(\<Pi>I)\<close> consumes fresh
  eigen-parameters; over a context that uses @{emph \<open>every\<close>} parameter, generalisation ---
  and with it weakening --- becomes unavailable (hence the proviso \<open>freep \<Psi>\<close> in
  @{thm [source] bprov_weaken}).  Derivability from a set of @{emph \<open>hypotheses\<close>} is
  therefore defined through finite sub-contexts, in the style of Andrews (2002): \<open>\<Phi> \<tturnstile> A\<close>
  holds when some finite part of \<open>\<Phi>\<close> derives \<open>A\<close>.  This relation is monotone without any
  proviso and of finite character by construction, and on \<open>freep\<close> contexts --- in
  particular on all finite ones --- it coincides with \<open>\<turnstile>\<close>.\<close>

definition fprov :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> bool"  (infix \<open>\<tturnstile>\<close> 40) where
  "\<Phi> \<tturnstile> A \<longleftrightarrow> (\<exists>\<Phi>\<^sub>0. finite \<Phi>\<^sub>0 \<and> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<and> \<Phi>\<^sub>0 \<turnstile> A)"

lemma fprovI: "finite \<Phi>\<^sub>0 \<Longrightarrow> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<Longrightarrow> \<Phi>\<^sub>0 \<turnstile> A \<Longrightarrow> \<Phi> \<tturnstile> A"
  by (auto simp: fprov_def)

lemma bprov_fprov: "\<Phi> \<turnstile> (A :: 'p::infinite tm) \<Longrightarrow> \<Phi> \<tturnstile> A"
  using bprov_finite by (auto simp: fprov_def)

lemma fprov_bprov: "\<Phi> \<tturnstile> A \<Longrightarrow> freep \<Phi> \<Longrightarrow> \<Phi> \<turnstile> A"
  using bprov_weaken by (auto simp: fprov_def)

lemma fprov_eq_bprov: "freep \<Phi> \<Longrightarrow> (\<Phi> \<tturnstile> (A :: 'p::infinite tm)) \<longleftrightarrow> (\<Phi> \<turnstile> A)"
  using bprov_fprov fprov_bprov by blast

lemma fprov_finite_eq_bprov:
  "finite \<Phi> \<Longrightarrow> (\<Phi> \<tturnstile> (A :: 'p::infinite tm)) \<longleftrightarrow> (\<Phi> \<turnstile> A)"
  by (simp add: fprov_eq_bprov freep_finite)

lemma fprov_mono: "\<Phi> \<tturnstile> A \<Longrightarrow> \<Phi> \<subseteq> \<Psi> \<Longrightarrow> \<Psi> \<tturnstile> A"
  by (auto simp: fprov_def)

lemma fprov_compact: "\<Phi> \<tturnstile> A \<longleftrightarrow> (\<exists>\<Phi>\<^sub>0. finite \<Phi>\<^sub>0 \<and> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<and> \<Phi>\<^sub>0 \<tturnstile> A)"
  by (auto simp: fprov_def)

subsection \<open>Consistency\<close>

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
  "(\<And>\<Phi>\<^sub>0::'p::infinite tm set. finite \<Phi>\<^sub>0 \<Longrightarrow> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<Longrightarrow> con \<Phi>\<^sub>0) \<Longrightarrow> con \<Phi>"
  using bprov_finite unfolding con_def by blast

text \<open>For the hypothesis relation, consistency of finite character is a definitional
  unfolding.\<close>

lemma fprov_con:
  "(\<not> (\<Phi> \<tturnstile> (\<^bold>\<bottom> :: 'p tm))) \<longleftrightarrow> (\<forall>\<Phi>\<^sub>0. finite \<Phi>\<^sub>0 \<longrightarrow> \<Phi>\<^sub>0 \<subseteq> \<Phi> \<longrightarrow> con \<Phi>\<^sub>0)"
  by (auto simp: fprov_def con_def)

text \<open>The central step of a maximal-consistent extension (the \<open>\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close> case of BKK Lemma 7.5;
  property \<open>\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close> is BKK Definition 6.5): from a consistent set, adding a proposition or its
  negation keeps it consistent.\<close>

lemma con_split: assumes "con \<Phi>" and "wff\<^bsub>\<o>\<^esub>(A)"
  shows "con (insert A \<Phi>) \<or> con (insert (\<^bold>\<not> A) \<Phi>)"
proof (rule ccontr)
  assume "\<not>?thesis"
  hence "\<Phi> \<union> {A} \<turnstile> \<^bold>\<bottom>" and 0: "\<Phi> \<union> {\<^bold>\<not> A} \<turnstile> \<^bold>\<bottom>" by (auto simp: con_def)
  hence "\<Phi> \<turnstile> \<^bold>\<not> A" using assms(2) by (auto intro: bprov.NegI)
  moreover have "\<Phi> \<turnstile> A" using assms(2) 0 by (auto intro: bprov.Contr)
  ultimately have "\<Phi> \<turnstile> \<^bold>\<bottom>" using wff_FalseB by (auto intro: bprov.NegE)
  thus False using assms(1) by (simp add: con_def)
qed

text \<open>A consistent set does not contain both a proposition and its negation.\<close>

lemma con_not_both: "con \<Phi> \<Longrightarrow> A \<in> \<Phi> \<Longrightarrow> \<^bold>\<not> A \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> False"
  by (metis con_def wff_FalseB NegE Hyp)

subsection \<open>Admissible rules\<close>

lemma freep_un: "freep \<Phi> \<Longrightarrow> freep (\<Phi> \<union> {A})"
  by (metis freep_add Un_insert_right sup_bot.right_neutral)

text \<open>Double-negation elimination (derivable from the classical rule \<open>NK(Contr)\<close>).\<close>

lemma dneg: "\<Phi> \<turnstile> \<^bold>\<not> (Neg \<^bold>\<cdot> X) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(X) \<Longrightarrow> freep \<Phi> \<Longrightarrow> \<Phi> \<turnstile> X"
  by (metis (no_types, lifting) Contr Hyp NegE Un_insert_right bprov_weaken
            freep_add insertI1 subset_insertI sup_bot.right_neutral wff_FalseB)

text \<open>Excluded middle and implication elimination (derivable in the classical calculus).\<close>

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

subsection \<open>Derived rules for the defined quantifiers\<close>

text \<open>\<open>NK(\<Pi>E)\<close> and \<open>NK(\<Pi>I)\<close> for the folded quantifier \<open>\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub>\<close>.\<close>

lemma PiE_Forall: "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<^bold>\<cdot> A"
  unfolding Forall_def by (rule bprov.PiE)
lemma PiI_Forall: "\<Phi> \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>) \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<Longrightarrow> w \<notin> pars (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b)
                   \<Longrightarrow> (\<forall>D \<in> \<Phi>. w \<notin> pars D)  \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b"
  unfolding Forall_def by (rule bprov.PiI)

text \<open>Existential elimination at a fresh eigen-parameter, for the defined quantifier
  \<open>\<^bold>\<exists> = \<^bold>\<not>\<^bold>\<Pi>\<^bold>\<not>\<close>: the derived counterpart of the paper-style step ``obtain a witness''.\<close>

lemma ExE: assumes ex: "\<Phi> \<turnstile> \<^bold>\<exists>\<^bsub>\<sigma>\<^esub> b" and step: "\<Phi> \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> C"
    and wb: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
  and wC: "wff\<^bsub>\<o>\<^esub>(C)" and wpb: "w \<notin> pars b" and wpC: "w \<notin> pars C"
      and wp\<Phi>: "\<forall>D \<in> \<Phi>. w \<notin> pars D" and fp: "freep \<Phi>"
  shows "\<Phi> \<turnstile> C"
proof -
  have wNb: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))"
    by (auto intro!: wff_opn[OF wb] wff_Fre wff_AbsI)
  have fp1: "freep (\<Phi> \<union> {\<^bold>\<not> C})" using freep_add[OF fp] by simp
  have fp2: "freep (\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>})"
      using freep_add[OF freep_add[OF fp]] by simp
  have s1: "\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> C"
    by (rule bprov_weaken[OF step _ fp2]) auto
  have s2: "\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> \<^bold>\<not> C" by (auto intro: bprov.Hyp)
  have bq: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b)) \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<sigma>\<^esub>) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<not> (b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    using beq.beta[OF wNb wff_Par] by simp
  have s5: "\<Phi> \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b)"
    using wpb wpC wp\<Phi>
    by (safe intro!:
        PiI_Forall[OF bprov.Beta[OF beq.sym[OF bq] bprov.NegI[OF
              bprov.NegE[OF s2 s1 wff_FalseB] wff_opn[OF wb wff_Par]]] wNb]) auto
  have s6: "\<Phi> \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<not> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))" by (rule bprov_weaken[OF ex _ fp1]) auto
  show ?thesis by (rule bprov.Contr[OF bprov.NegE[OF s6 s5 wff_FalseB] wC])
qed

text \<open>Universal instantiation directly at the \<open>\<beta>\<close>-reduced instance.\<close>

lemma PiE_open: "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> b\<^bold>\<langle>A\<^bold>\<rangle>"
  by (metis PiE_Forall beq.beta bprov.Beta)

text \<open>Syntactic generalisation: a fresh parameter substituted for a free variable can
  be quantified away and re-instantiated, recovering the open formula (the rule chain
  \<open>NK(\<beta>)\<close>--\<open>NK(\<Pi>I)\<close>--\<open>NK(\<Pi>E)\<close>--\<open>NK(\<beta>)\<close>).  Statement preserved verbatim from the
  published version of this entry (compatibility export, relocated from \<open>Completeness\<close>);
  the completeness proof now uses the simultaneous variable-for-parameter substitution of
  \<open>Completeness\<close> instead.\<close>

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

subsection \<open>Parameter-to-variable substitution in derivations\<close>

text \<open>Derivability is stable under replacing a parameter by a @{emph \<open>free variable\<close>}, as it
  is under injective renamings (@{thm [source] bprov_rename}).  No eigen-parameter need be
  renamed: the substitution only ever removes parameters, so the side conditions of \<open>NK(\<Pi>I)\<close>
  survive; and where the eigen-parameter @{emph \<open>is\<close>} the substituted one, \<open>pvar\<close> is the
  identity on context and quantified predicate, so the original rule instance already applies.\<close>

lemma bprov_pvar: "\<Phi> \<turnstile> C \<Longrightarrow> pvar w \<sigma> x ` \<Phi> \<turnstile> pvar w \<sigma> x C"
proof (induction rule: bprov.induct)
  case Beta thus ?case by (meson beq_pvar bprov.Beta)
next
  case DisE thus ?case by (simp add: bprov.DisE wff_pvar)
next
  case (PiI \<Phi> G v \<alpha>)
  show ?case
  proof (cases "v = w \<and> \<alpha> = \<sigma>")
    case True
    have "pvar w \<sigma> x G = G" using PiI.hyps(3) True by simp
    moreover have "pvar w \<sigma> x ` \<Phi> = \<Phi>"
      using PiI.hyps(4) True by (simp add: pvar_image_id)
    ultimately show ?thesis
      using bprov.PiI[OF PiI.hyps(1) PiI.hyps(2) PiI.hyps(3) PiI.hyps(4)] by simp
  next
    case False
    hence pv: "pvar w \<sigma> x (v\<^sup>p\<^bsub>\<alpha>\<^esub>) = v\<^sup>p\<^bsub>\<alpha>\<^esub>" by simp
    have h1: "pvar w \<sigma> x ` \<Phi> \<turnstile> (pvar w \<sigma> x G) \<^bold>\<cdot> (v\<^sup>p\<^bsub>\<alpha>\<^esub>)" using PiI.IH pv by simp
    have h2: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(pvar w \<sigma> x G)" by (rule wff_pvar[OF PiI.hyps(2)])
    have h3: "v \<notin> pars (pvar w \<sigma> x G)"
      using PiI.hyps(3) pars_pvar[of w \<sigma> x G] by blast
    have h4: "\<forall>D \<in> pvar w \<sigma> x ` \<Phi>. v \<notin> pars D"
    proof
      fix D' assume "D' \<in> pvar w \<sigma> x ` \<Phi>"
      then obtain D where D: "D \<in> \<Phi>" "D' = pvar w \<sigma> x D" by auto
      have "v \<notin> pars D" using PiI.hyps(4) D(1) by blast
      thus "v \<notin> pars D'" using D(2) pars_pvar[of w \<sigma> x D] by blast
    qed
    show ?thesis using bprov.PiI[OF h1 h2 h3 h4] by simp
  qed
next
  case Contr thus ?case by (simp add: bprov.Contr wff_pvar)
next
  case NegE thus ?case by (metis bprov.NegE pvar.simps(4) pvar.simps(9) wff_pvar)
next
  case PiE thus ?case by (metis bprov.PiE pvar.simps(6) pvar.simps(9) wff_pvar)
qed(auto simp: bprov.EqL bprov.EqR bprov.Desc bprov.FuncE bprov.DisIL bprov.DisIR bprov.Hyp
               bprov.BoolE bprov.NegI wff_pvar)

subsection \<open>Leibniz equality in the calculus\<close>

lemma leib_refl: assumes wa: "wff\<^bsub>\<alpha>\<^esub>(A)"
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

text \<open>The one transport step behind symmetry, transitivity, congruence and modus ponens:
  a proven \<open>\<beta>\<close>-reduct \<open>X\<close> of \<open>P \<^bold>\<cdot> A\<close> transports along \<open>\<Phi> \<turnstile> A \<^bold>\<doteq> B\<close> to the \<open>\<beta>\<close>-reduct
  \<open>Y\<close> of \<open>P \<^bold>\<cdot> B\<close>.  Each rule below just picks its predicate \<open>P\<close> and its base fact.\<close>

lemma leib_transport:
  assumes AB: "\<Phi> \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B" and fp: "freep \<Phi>"
      and wa: "wff\<^bsub>\<alpha>\<^esub>(A)" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)" and wP: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(P)"
      and bX: "P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> X" and bY: "P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> Y"
      and X: "\<Phi> \<turnstile> X"
    shows "\<Phi> \<turnstile> Y"
proof -
  have "\<Phi> \<turnstile> P \<^bold>\<cdot> A" by (rule bprov.Beta[OF beq.sym[OF bX] X])
  hence "\<Phi> \<turnstile> P \<^bold>\<cdot> B" by (rule leib_subst[OF AB fp wa wb wP])
  thus ?thesis by (rule bprov.Beta[OF bY])
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
  show ?thesis
    by (rule leib_transport[OF AB fp wa wb wP PbA PbB leib_refl[OF wa]])
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
  show ?thesis by (rule leib_transport[OF BC fp wb wc wP PbB PbC AB])
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
  show ?thesis
    by (rule leib_transport[OF AA fp wa wa' wP PbA PbA' leib_refl[OF wff_App[OF wC wa]]])
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
  show ?thesis
    by (rule leib_transport[OF CC fp wC wC' wP PbC PbC' leib_refl[OF wff_App[OF wC wa]]])
qed

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
  show ?thesis by (rule leib_transport[OF AB fp wA wB wP bA bB A])
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
  show ?thesis
    by (rule leib_transport[OF AB fp wA wB wP bA bB bprov.EqR[OF wA]])
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

text \<open>For @{emph \<open>primitive\<close>} equality the same facts are available through the translation
  (\<open>NK(=\<^sub>l)\<close> in, \<open>leib_to_peq\<close> out).\<close>

end
