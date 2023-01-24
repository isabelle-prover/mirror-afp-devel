chapter \<open> Classical Soundness and Completeness \label{sec:classical-propositional-calculus} \<close>

theory Classical_Logic_Completeness
  imports Classical_Logic
begin

text \<open> The following presents soundness completeness of the classical propositional
       calculus for propositional semantics. The classical propositional calculus
       is sometimes referred to as the \<^emph>\<open>sentential calculus\<close>.
       We give a concrete algebraic data type for propositional
       formulae in \S\ref{sec:classical-calculus-syntax}. We inductively
       define a logical judgement \<open>\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p\<close> for these formulae.
       We also define the Tarski truth relation \<open>\<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p\<close> inductively,
       which we present in \S\ref{sec:propositional-semantics}.\<close>

text \<open> The most significant results here are the \<^emph>\<open>embedding theorems\<close>.
       These theorems show that the propositional calculus
       can be embedded in any logic extending @{class classical_logic}.
       These theorems are proved in \S\ref{sec:propositional-embedding}. \<close>

section \<open> Syntax \label{sec:classical-calculus-syntax} \<close>

text \<open> Here we provide the usual language for formulae in the propositional
       calculus. It contains  \<^emph>\<open>falsum\<close> \<open>\<^bold>\<bottom>\<close>, implication \<open>(\<^bold>\<rightarrow>)\<close>, and a way of
       constructing \<^emph>\<open>atomic\<close> propositions \<open>\<lambda> \<phi> . \<^bold>\<langle> \<phi> \<^bold>\<rangle>\<close>. Defining the
       language is straight-forward using an algebraic data type. \<close>

datatype 'a classical_propositional_formula =
      Falsum ("\<^bold>\<bottom>")
    | Proposition 'a ("\<^bold>\<langle> _ \<^bold>\<rangle>" [45])
    | Implication
        "'a classical_propositional_formula"
        "'a classical_propositional_formula" (infixr "\<^bold>\<rightarrow>" 70)

section \<open> Propositional Calculus \<close>

text \<open> In this section we recursively define what a proof is in the classical
       propositional calculus. We provide the familiar \<^emph>\<open>K\<close> and \<^emph>\<open>S\<close> axioms,
       as well as \<^emph>\<open>double negation\<close> and \<^emph>\<open>modus ponens\<close>. \<close>

named_theorems classical_propositional_calculus
  "Rules for the Propositional Calculus"

inductive classical_propositional_calculus ::
  "'a classical_propositional_formula \<Rightarrow> bool" ("\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p _" [60] 55)
  where
     axiom_k [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<phi>"
   | axiom_s [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi> \<^bold>\<rightarrow> \<chi>"
   | double_negation [classical_propositional_calculus]:
       "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<phi> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<phi>"
   | modus_ponens [classical_propositional_calculus]:
        "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>"

text \<open> Our proof system for our propositional calculus is trivially
       an instance of @{class classical_logic}. The introduction rules
       for \<open>\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p\<close> naturally reflect the axioms of the classical logic
       axiom class. \<close>

instantiation classical_propositional_formula
  :: (type) classical_logic
begin
definition [simp]: "\<bottom> = \<^bold>\<bottom>"
definition [simp]: "\<turnstile> \<phi> = \<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
definition [simp]: "\<phi> \<rightarrow> \<psi> = \<phi> \<^bold>\<rightarrow> \<psi>"
instance by standard (simp add: classical_propositional_calculus)+
end

section \<open> Propositional Semantics \label{sec:propositional-semantics} \<close>

text \<open> Below we give the typical definition of the Tarski truth relation
       \<open> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p\<close>. \<close>

primrec classical_propositional_semantics ::
  "'a set \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
       "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle> p \<^bold>\<rangle> = (p \<in> \<MM>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<^bold>\<rightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
    |  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<bottom> = False"

text \<open> Soundness of our calculus for these semantics is trivial. \<close>

theorem classical_propositional_calculus_soundness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  by (induct rule: classical_propositional_calculus.induct, simp+)

section \<open> Soundness and Completeness Proofs \label{sec:classical-logic-completeness}\<close>

definition strong_classical_propositional_deduction ::
  "'a classical_propositional_formula set
    \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<Gamma> \<tturnstile> \<phi>"

definition strong_classical_propositional_tarski_truth ::
  "'a classical_propositional_formula set
    \<Rightarrow> 'a classical_propositional_formula \<Rightarrow> bool"
  (infix "\<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p" 65)
  where
    [simp]: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<forall> \<MM>.(\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"

definition theory_propositions ::
  "'a classical_propositional_formula set \<Rightarrow> 'a set" ("\<^bold>\<lbrace> _ \<^bold>\<rbrace>" [50])
  where
    [simp]: "\<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> = {p . \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle> p \<^bold>\<rangle>}"

text \<open> Below we give the main lemma for completeness: the \<^emph>\<open>truth lemma\<close>.
       This proof connects the maximally consistent sets developed in \S\ref{sec:implicational-maximally-consistent-sets}
       and \S\ref{sec:mcs} with the semantics given in
       \S\ref{sec:propositional-semantics}. \<close>

text \<open> All together, the technique we are using essentially follows the
       approach by Blackburn et al. @{cite \<open>\S 4.2, pgs. 196-201\<close> blackburnSectionCanonicalModels2001}. \<close>

lemma truth_lemma:
  assumes "MCS \<Gamma>"
  shows "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<equiv> \<^bold>\<lbrace> \<Gamma> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof (induct \<phi>)
  case Falsum
  then show ?case using assms by auto
next
  case (Proposition x)
  then show ?case by simp
next
  case (Implication \<psi> \<chi>)
  thus ?case
    unfolding strong_classical_propositional_deduction_def
    by (metis
          assms
          maximally_consistent_set_def
          formula_maximally_consistent_set_def_implication
          classical_propositional_semantics.simps(2)
          implication_classical_propositional_formula_def
          set_deduction_modus_ponens
          set_deduction_reflection)
qed

text \<open> Here the truth lemma above is combined with @{thm formula_maximally_consistent_extension [no_vars]}
 proven in \S\ref{sec:propositional-semantics}.  These theorems together
  give rise to strong completeness for the propositional calculus. \<close>

theorem classical_propositional_calculus_strong_soundness_and_completeness:
  "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
proof -
  have soundness: "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof -
    assume "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    from this obtain \<Gamma>' where \<Gamma>': "set \<Gamma>' \<subseteq> \<Gamma>" "\<Gamma>' :\<turnstile> \<phi>"
    by (simp add: set_deduction_def, blast)
    {
      fix \<MM>
      assume "\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
      hence "\<forall> \<gamma> \<in> set \<Gamma>'. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>" using \<Gamma>'(1) by auto
      hence "\<forall> \<phi>. \<Gamma>' :\<turnstile> \<phi> \<longrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      proof (induct \<Gamma>')
        case Nil
        then show ?case
          by (simp add:
                classical_propositional_calculus_soundness
                list_deduction_def)
      next
        case (Cons \<psi> \<Gamma>')
        thus ?case using list_deduction_theorem by fastforce
      qed
      with \<Gamma>'(2) have "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>" by blast
    }
    thus "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      using strong_classical_propositional_tarski_truth_def by blast
  qed
  have completeness: "\<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
  proof (erule contrapos_pp)
    assume "\<not> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    hence "\<exists> \<MM>. (\<forall> \<gamma> \<in> \<Gamma>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>) \<and> \<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    proof -
      from \<open>\<not> \<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>\<close> obtain \<Omega> where \<Omega>: "\<Gamma> \<subseteq> \<Omega>" "\<phi>-MCS \<Omega>"
        by (meson
              formula_consistent_def
              formula_maximally_consistent_extension
              strong_classical_propositional_deduction_def)
      hence "(\<phi> \<rightarrow> \<bottom>) \<in> \<Omega>"
        using formula_maximally_consistent_set_def_negation by blast
      hence "\<not> \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
        using \<Omega>
              formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_set_def_def
              truth_lemma
        unfolding strong_classical_propositional_deduction_def
        by blast
      moreover have "\<forall> \<gamma> \<in> \<Gamma>. \<^bold>\<lbrace> \<Omega> \<^bold>\<rbrace> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<gamma>"
        using
          formula_maximal_consistency
          truth_lemma
          \<Omega>
          set_deduction_reflection
        unfolding strong_classical_propositional_deduction_def
        by blast
      ultimately show ?thesis by auto
    qed
    thus "\<not> \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
      unfolding strong_classical_propositional_tarski_truth_def
      by simp
  qed
  from soundness completeness show "\<Gamma> \<tturnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = \<Gamma> \<TTurnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>"
    by linarith
qed

text \<open> For our applications in \S{sec:propositional-embedding},
       we will only need a weaker form of soundness and completeness
       rather than the stronger form proved above.\<close>

theorem classical_propositional_calculus_soundness_and_completeness:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> = (\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  using classical_propositional_calculus_soundness [where \<phi>="\<phi>"]
        classical_propositional_calculus_strong_soundness_and_completeness
            [where \<phi>="\<phi>" and \<Gamma>="{}"]
        strong_classical_propositional_deduction_def
            [where \<phi>="\<phi>" and \<Gamma>="{}"]
        strong_classical_propositional_tarski_truth_def
            [where \<phi>="\<phi>" and \<Gamma>="{}"]
        deduction_classical_propositional_formula_def [where \<phi>="\<phi>"]
        set_deduction_base_theory [where \<phi>="\<phi>"]
  by metis

instantiation classical_propositional_formula
  :: (type) consistent_classical_logic
begin
instance by standard
  (simp add: classical_propositional_calculus_soundness_and_completeness)
end

section \<open> Embedding Theorem For the Propositional Calculus \label{sec:propositional-embedding} \<close>

text \<open> A recurring technique to prove theorems in logic moving forward is
       \<^emph>\<open>embed\<close> our theorem into the classical propositional calculus. \<close>

text \<open> Using our embedding, we can leverage completeness to turn our
       problem into semantics and dispatch to Isabelle/HOL's classical
       theorem provers.\<close>

text \<open> In future work we may make a tactic for this, but for now we just
       manually leverage the technique throughout our subsequent proofs. \<close>

primrec (in classical_logic)
   classical_propositional_formula_embedding
   :: "'a classical_propositional_formula \<Rightarrow> 'a" ("\<^bold>\<lparr> _ \<^bold>\<rparr>" [50]) where
     "\<^bold>\<lparr> \<^bold>\<langle> p \<^bold>\<rangle> \<^bold>\<rparr> = p"
   | "\<^bold>\<lparr> \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<rightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
   | "\<^bold>\<lparr> \<^bold>\<bottom> \<^bold>\<rparr> = \<bottom>"

theorem (in classical_logic) propositional_calculus:
  "\<turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (induct rule: classical_propositional_calculus.induct,
      (simp add: axiom_k axiom_s double_negation modus_ponens)+)

text \<open> The following theorem in particular shows that it suffices to
       prove theorems using classical semantics to prove theorems about
       the logic under investigation. \<close>

theorem (in classical_logic) propositional_semantics:
  "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<Longrightarrow> \<turnstile> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (simp add:
        classical_propositional_calculus_soundness_and_completeness
        propositional_calculus)

end
