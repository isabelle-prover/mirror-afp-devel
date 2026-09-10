theory Calculus
  imports Semantics "HOL-Library.Infinite_Typeclass"
begin

section \<open>The natural-deduction calculus NK\<close>

text \<open>We formalise the calculus \<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> of BKK (BKK Definition 7.1, Figures 6 and 7) --- the base
  system \<open>NK\<^sub>\<beta>\<close> together with the extensional rules \<open>NK(f)\<close> and \<open>NK(b)\<close> --- extended by BKK's
  rules \<open>NK(=\<^sub>r)\<close> and \<open>NK(=\<^sub>l)\<close> for the primitive equality of our signature (BKK Figure 9,
  Remark 7.9) and by the description rule \<open>NK(\<iota>)\<close>, a premise-free axiom scheme describing
  Leibniz singletons (beyond BKK, following Andrews 1972, their reference [3]).  BKK prove
  \<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> sound and complete for the class of \<open>\<Sigma>\<close>-Henkin models \<open>\<M>\<^sub>\<beta>\<^sub>f\<^sub>b\<close> (BKK Theorem 7.3,
  Theorem 7.6, Corollary 7.7), and sketch the extension by primitive equality in Remark 7.9; we
  prove the fully extended calculus sound and complete for the correspondingly enriched class (with
      primitive 
  equality and description, Section 2).  The provability judgement \<open>\<Phi> \<turnstile> A\<close> relates a set
      of sentences
  \<open>\<Phi>\<close> to a sentence \<open>A\<close>.  Eigenvariables are @{emph \<open>parameters\<close>} (BKK's \<open>w\<^bsub>\<alpha>\<^esub>\<close>), which --- unlike
  the free variables used only during evaluation --- never occur bound.\<close>

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
proof (induct rule: bprov.induct)
  case PiI thus ?case by (meson wff_App wff_Pi)
next
  case Desc thus ?case by (metis wff_Leib wff_App wff_Iota)
qed(auto simp: beq_wff wff_App)


text \<open>Derivability is stable under injective parameter renaming --- injectivity keeps the
  eigen-parameter side-conditions of \<open>NK(\<Pi>I)\<close>.  This lets us move eigen-parameters out of the
  way, which is what makes weakening (and later, extension of consistent sets) admissible.\<close>

lemma bprov_rename: assumes \<pi>: "inj \<pi>" shows "\<Phi> \<turnstile> C \<Longrightarrow> prn \<pi> ` \<Phi> \<turnstile> prn \<pi> C"
proof (induction rule: bprov.induct)
  case DisE thus ?case using DisE bprov.DisE by auto
next
  case PiI thus ?case
    by auto (smt (verit) assms bprov.PiI image_iff inj_image_mem_iff tm.set_map wff_prn)
qed(auto intro: bprov.intros)

subsection \<open>Weakening\<close>

text \<open>Weakening is admissible.  BKK leave this structural property implicit (their contexts
  are sets and the rules mention the context only via membership and extension); in the
  formalisation the eigen-parameter condition of \<open>NK(\<Pi>I)\<close> makes it a genuine lemma, proved
      by transposing the 
  eigen-parameter out of the way of the enlarged context.\<close>

text \<open>Transposing two parameters --- an involutive, injective renaming --- lets us shift an
  eigen-parameter to a fresh one when weakening the context.\<close>

definition swp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "swp a b = (\<lambda>x. if x = a then b else if x = b then a else x)"
lemma swp_inj: "inj (swp a b)" by (auto simp: swp_def inj_def)
lemma swp_swp [simp]: "swp a b (swp a b x) = x" by (auto simp: swp_def)
lemma swp_apply: "swp a b a = b" by (simp add: swp_def)
lemma prn_swp_swp [simp]: "prn (swp a b) (prn (swp a b) t) = t" by (simp add: prn_prn)
lemma image_prn_swp_swp [simp]: "prn (swp a b) ` (prn (swp a b) ` S) = S"
  by (simp add: image_image)

text \<open>The parameters used by a context, and the property of leaving infinitely many free.
  \<open>freep\<close> is our rendering of BKK's @{emph \<open>sufficiently \<open>\<Sigma>\<close>-pure\<close>} (BKK Definition 6.3): since a
  parameter name may be used at every type, infinitely many unused names provide,
      for each type, a witness
   reservoir of the cardinality of the (countable) language.\<close>

definition usedp :: "'p tm set \<Rightarrow> 'p set" where "usedp \<Phi> \<equiv> (\<Union>D \<in> \<Phi>. pars D)"
definition freep :: "'p tm set \<Rightarrow> bool" where "freep \<Phi> \<equiv> infinite (- usedp \<Phi>)"
lemma usedp_insert: "usedp (insert A \<Phi>) = pars A \<union> usedp \<Phi>" by (auto simp: usedp_def)
lemma usedp_prn: "usedp (prn \<pi> ` \<Phi>) = \<pi> ` usedp \<Phi>" by (auto simp: usedp_def pars_prn)
lemma bij_swp: "bij (swp a b)" by (simp add: involuntory_imp_bij)
lemma infinite_inj_image: "inj f \<Longrightarrow> infinite A \<Longrightarrow> infinite (f ` A)"
  by (metis finite_imageD inj_on_subset subset_UNIV)
lemma freep_add: "freep \<Phi> \<Longrightarrow> freep (insert A \<Phi>)"
  by (simp add: usedp_insert freep_def)
     (metis finite_pars Diff_eq Diff_infinite_finite inf.commute)
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
  parameters free, and every derivation uses only a finite part of its context.\<close>

lemma freep_finite: fixes \<Phi> :: "'p::infinite tm set" assumes "finite \<Phi>"
  shows "freep \<Phi>"
by (metis assms freep_def usedp_def finite_pars infinite_UNIV
    finite_Diff2 Compl_eq_Diff_UNIV finite_UN)

lemma bprov_finite: "\<Phi> \<turnstile> (C :: 'p::infinite tm) \<Longrightarrow> \<exists>\<Phi>0. finite \<Phi>0 \<and> \<Phi>0 \<subseteq> \<Phi> \<and> \<Phi>0 \<turnstile> C"
proof (induction rule: bprov.induct)
  case (NegI \<Phi> A) thus ?case
    by (smt (verit) Un_infinite Un_insert_right bprov.NegI
        bprov_weaken freep_add freep_finite subset_UnE
        subset_insertI subset_singleton_iff)
next
  case (NegE \<Phi> A C) thus ?case
    by (smt (verit) bprov.NegE bprov_weaken finite_UnI freep_finite le_sup_iff sup_ge1 sup_ge2)
next
  case (DisE \<Phi> A B C)
  then obtain \<Phi>1 \<Phi>2 \<Phi>3 where
    Q1: "finite \<Phi>1" "\<Phi>1 \<subseteq> \<Phi>" "\<Phi>1 \<turnstile> A \<^bold>\<or> B" and
    Q2: "finite \<Phi>2" "\<Phi>2 \<subseteq> \<Phi> \<union> {A}" "\<Phi>2 \<turnstile> C" and
    Q3: "finite \<Phi>3" "\<Phi>3 \<subseteq> \<Phi> \<union> {B}" "\<Phi>3 \<turnstile> C"
    by blast
  moreover define \<Phi>0 where "\<Phi>0 = \<Phi>1 \<union> (\<Phi>2 - {A}) \<union> (\<Phi>3 - {B})"
  ultimately have "finite \<Phi>0" and "\<Phi>0 \<subseteq> \<Phi>" by auto
  moreover {
    have "\<Phi>0 \<turnstile> A \<^bold>\<or> B"
      by (metis Q1(3) \<Phi>0_def bprov_weaken dual_order.refl calculation(1) freep_finite le_sup_iff)
    moreover have "\<Phi>0 \<union> {A} \<turnstile> C" and "\<Phi>0 \<union> {B} \<turnstile> C"
      by (auto intro: bprov_weaken[OF Q2(3)] bprov_weaken[OF Q3(3)]
               simp: \<Phi>0_def Q1(1) Q2(1) Q3(1) freep_finite)
    ultimately have "\<Phi>0 \<turnstile> C" by (auto intro: DisE bprov.DisE)
  }
  ultimately show ?case by blast
next case (Contr \<Phi> A) show ?case by (smt (verit, del_insts) Contr.IH
    Contr.hyps(2) Un_infinite Un_insert_right
          bprov.Contr bprov_weaken freep_add freep_finite subset_UnE
              subset_insertI subset_singleton_iff)
next case (BoolE \<Phi> A B)
  then obtain \<Phi>1 \<Phi>2 where
    Q1: "finite \<Phi>1" "\<Phi>1 \<subseteq> \<Phi> \<union> {A}" "\<Phi>1 \<turnstile> B" and
    Q2: "finite \<Phi>2" "\<Phi>2 \<subseteq> \<Phi> \<union> {B}" "\<Phi>2 \<turnstile> A" 
    by blast
  moreover define \<Phi>0 where "\<Phi>0 = (\<Phi>1 - {A}) \<union> (\<Phi>2 - {B})"
  ultimately have "finite \<Phi>0" and "\<Phi>0 \<subseteq> \<Phi>" by auto
  moreover {
    have "\<Phi>0 \<union> {A} \<turnstile> B" and "\<Phi>0 \<union> {B} \<turnstile> A"
      by (auto intro: bprov_weaken[OF Q1(3)] bprov_weaken[OF Q2(3)]
               simp: calculation Q1(1,2) Q2(1) \<Phi>0_def freep_finite)
    hence "\<Phi>0 \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B" using BoolE by (auto intro: bprov.intros)
  }
  ultimately show ?case by blast
qed(auto intro: bprov.intros)

end
