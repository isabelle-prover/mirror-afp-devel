chapter \<open> Classical Propositional Logic \label{sec:classical-propositional-logic}\<close>

theory Classical_Logic
  imports Implication_Logic
begin

text \<open> This theory presents \<^emph>\<open>classical propositional logic\<close>, which is
       classical logic without quantifiers. \<close>

section \<open> Axiomatization \<close>

text \<open> Classical propositional logic can be given by the following
       Hilbert-style axiom system.  It is @{class implication_logic}
       extended with \<^emph>\<open>falsum\<close> and double negation. \<close>

class classical_logic = implication_logic +
  fixes falsum :: "'a" ("\<bottom>")
  assumes double_negation: "\<turnstile> (((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> \<phi>)"

text \<open> In some cases it is useful to assume consistency as an axiom: \<close>

class consistent_classical_logic = classical_logic +
  assumes consistency: "\<not> \<turnstile> \<bottom>"

section \<open> Common Rules \<close>

text \<open> There are many common tautologies in classical logic.  Once we have
       established \<^emph>\<open>completeness\<close> in \S\ref{sec:classical-propositional-calculus},
       we will be able to leverage Isabelle/HOL's automation for proving
       these elementary results. \<close>

text \<open> In order to bootstrap completeness, we develop some common lemmas
       using classical deduction alone. \<close>

lemma (in classical_logic)
  ex_falso_quodlibet: "\<turnstile> \<bottom> \<rightarrow> \<phi>"
  using axiom_k double_negation modus_ponens hypothetical_syllogism
  by blast

lemma (in classical_logic)
  Contraposition: "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)) \<rightarrow> \<psi> \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<bottom>"
    using flip_implication list_deduction_theorem list_implication.simps(1)
    unfolding list_deduction_def
    by presburger
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[\<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)] :\<turnstile> \<phi>"
    using double_negation list_deduction_weaken list_deduction_modus_ponens
    by blast
  thus ?thesis
    using list_deduction_base_theory list_deduction_theorem by blast
qed

lemma (in classical_logic)
  double_negation_converse: "\<turnstile> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
  by (meson axiom_k modus_ponens flip_implication)

text \<open>The following lemma is sometimes referred to as
      \<^emph>\<open>The Principle of Pseudo-Scotus\<close>@{cite bobenriethOriginsUseArgument2010}.\<close>

lemma (in classical_logic)
  pseudo_scotus: "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  using ex_falso_quodlibet modus_ponens hypothetical_syllogism by blast

text \<open>Another popular lemma is attributed to Charles Sanders Peirce,
      and has come to be known as \<^emph>\<open>Peirces Law\<close>@{cite peirceAlgebraLogicContribution1885}.\<close>

lemma (in classical_logic) Peirces_law:
  "\<turnstile> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>) \<rightarrow> \<phi>"
proof -
  have "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi> \<rightarrow> \<psi>"
    using
      pseudo_scotus
      list_deduction_theorem
      list_deduction_weaken
    by blast
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    by (meson
          list.set_intros(1)
          list_deduction_reflection
          list_deduction_modus_ponens
          set_subset_Cons
          subsetCE)
  hence "[\<phi> \<rightarrow> \<bottom>, (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<bottom>"
    by (meson
          list.set_intros(1)
          list_deduction_modus_ponens
          list_deduction_reflection)
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    using list_deduction_theorem by blast
  hence "[(\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>] :\<turnstile> \<phi>"
    using double_negation
          list_deduction_modus_ponens
          list_deduction_weaken
    by blast
  thus ?thesis
    using list_deduction_def
    by auto
qed

lemma (in classical_logic) excluded_middle_elimination:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) \<rightarrow> \<psi>"
proof -
  let ?\<Gamma> = "[\<psi> \<rightarrow> \<bottom>, \<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>]"
  have "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"
       "?\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<bottom>"
    by (simp add: list_deduction_reflection)+
  hence "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
    by (meson
          flip_hypothetical_syllogism
          list_deduction_base_theory
          list_deduction_monotonic
          list_deduction_theorem
          set_subset_Cons)
  hence "?\<Gamma> :\<turnstile> \<phi>"
    using
      double_negation
      list_deduction_modus_ponens
      list_deduction_weaken
    by blast
  hence "?\<Gamma> :\<turnstile> \<psi>"
    by (meson
          list.set_intros(1)
          list_deduction_modus_ponens
          list_deduction_reflection
          set_subset_Cons subsetCE)
  hence "[\<phi> \<rightarrow> \<psi>, (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>] :\<turnstile> \<psi>"
    using
      Peirces_law
      list_deduction_modus_ponens
      list_deduction_theorem
      list_deduction_weaken
    by blast
  thus ?thesis
    unfolding list_deduction_def
    by simp
qed

section \<open> Maximally Consistent Sets For Classical Logic \label{sec:mcs}\<close>

text \<open> \<^emph>\<open>Relativized\<close> maximally consistent sets were introduced in
       \S\ref{sec:implicational-maximally-consistent-sets}.
       Often this is exactly what we want in a proof.
       A completeness theorem typically starts by assuming \<^term>\<open>\<phi>\<close> is
       not provable, then finding a \<^term>\<open>\<phi>-MCS \<Gamma>\<close> which gives rise to a model
       which does not make \<^term>\<open>\<phi>\<close> true. \<close>

text \<open> A more conventional presentation says that \<^term>\<open>\<Gamma>\<close> is maximally
       consistent if and only if  \<^term>\<open>\<not> (\<Gamma> \<tturnstile> \<bottom>)\<close> and
       \<^term>\<open>\<forall> \<psi>. \<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>\<close>. This conventional presentation
       will come up when formulating \textsc{MaxSAT} in
       \S\ref{sec:abstract-maxsat}. This in turn allows us to formulate
       \textsc{MaxSAT} completeness for probability inequalities in
       \S\ref{subsec:maxsat-completeness}, and reduce checking if a strategy
       will always lose money or if it will always make money if matched to
       bounded \textsc{MaxSAT} as part of our proof of the \<^emph>\<open>Dutch Book Theorem\<close>
       in \S\ref{subsec:guardian-dutch-book-maxsat-reduction} and \S\ref{subsec:market-depth-dutch-book-maxsat-reduction}
       respectively. \<close>

definition (in classical_logic)
  consistent :: "'a set \<Rightarrow> bool" where
    [simp]: "consistent \<Gamma> \<equiv> \<bottom>-consistent \<Gamma>"

definition (in classical_logic)
  maximally_consistent_set :: "'a set \<Rightarrow> bool" ("MCS") where
    [simp]: "MCS \<Gamma> \<equiv> \<bottom>-MCS \<Gamma>"

lemma (in classical_logic)
  formula_maximally_consistent_set_def_negation: "\<phi>-MCS \<Gamma> \<Longrightarrow> \<phi> \<rightarrow> \<bottom> \<in> \<Gamma>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<phi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
    hence "(\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding formula_maximally_consistent_set_def_def
      by blast
    hence "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
      using set_deduction_reflection
      by simp
    hence "\<Gamma> \<tturnstile> \<phi>"
      using
        Peirces_law
        set_deduction_modus_ponens
        set_deduction_weaken
      by metis
    hence "False"
      using \<open>\<phi>-MCS \<Gamma>\<close>
      unfolding
        formula_maximally_consistent_set_def_def
        formula_consistent_def
      by simp
  }
  thus ?thesis by blast
qed

text \<open> Relative maximal consistency and conventional maximal consistency in
       fact coincide in classical logic. \<close>

lemma (in classical_logic)
  formula_maximal_consistency: "(\<exists>\<phi>. \<phi>-MCS \<Gamma>) = MCS \<Gamma>"
proof -
  {
    fix \<phi>
    have "\<phi>-MCS \<Gamma> \<Longrightarrow> MCS \<Gamma>"
    proof -
      assume "\<phi>-MCS \<Gamma>"
      have "consistent \<Gamma>"
        using
          \<open>\<phi>-MCS \<Gamma>\<close>
          ex_falso_quodlibet [where \<phi>="\<phi>"]
          set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          set_deduction_modus_ponens
        unfolding
          formula_maximally_consistent_set_def_def
          consistent_def
          formula_consistent_def
        by metis
      moreover {
        fix \<psi>
        have "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma>"
        proof -
          assume "\<psi> \<rightarrow> \<bottom> \<notin> \<Gamma>"
          hence "(\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi> \<in> \<Gamma>"
            using \<open>\<phi>-MCS \<Gamma>\<close>
            unfolding formula_maximally_consistent_set_def_def
            by blast
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<phi>"
            using set_deduction_reflection
            by simp
          also have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<bottom>"
            using \<open>\<phi>-MCS \<Gamma>\<close>
                  formula_maximally_consistent_set_def_negation
                  set_deduction_reflection
            by simp
          hence "\<Gamma> \<tturnstile> (\<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
            using calculation
                  hypothetical_syllogism
                    [where \<phi>="\<psi> \<rightarrow> \<bottom>" and \<psi>="\<phi>" and \<chi>="\<bottom>"]
                  set_deduction_weaken
                    [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by metis
          hence "\<Gamma> \<tturnstile> \<psi>"
            using double_negation
                    [where \<phi>="\<psi>"]
                  set_deduction_weaken
                    [where \<Gamma>="\<Gamma>"]
                  set_deduction_modus_ponens
            by metis
          thus ?thesis
            using \<open>\<phi>-MCS \<Gamma>\<close>
                  formula_maximally_consistent_set_def_reflection
            by blast
       qed
      }
      ultimately show ?thesis
        unfolding maximally_consistent_set_def
                  formula_maximally_consistent_set_def_def
                  formula_consistent_def
                  consistent_def
        by blast
    qed
  }
  thus ?thesis
    unfolding maximally_consistent_set_def
    by metis
qed

text \<open> Finally, classical logic allows us to strengthen
       @{thm formula_maximally_consistent_set_def_implication_elimination [no_vars]} to a
       biconditional. \<close>

lemma (in classical_logic)
  formula_maximally_consistent_set_def_implication:
  assumes "\<phi>-MCS \<Gamma>"
  shows "\<psi> \<rightarrow> \<chi> \<in> \<Gamma> = (\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>)"
proof -
  {
    assume hypothesis: "\<psi> \<in> \<Gamma> \<longrightarrow> \<chi> \<in> \<Gamma>"
    {
      assume "\<psi> \<notin> \<Gamma>"
      have "\<forall>\<psi>. \<phi> \<rightarrow> \<psi> \<in> \<Gamma>"
        by (meson assms
                  formula_maximally_consistent_set_def_negation
                  formula_maximally_consistent_set_def_implication_elimination
                  formula_maximally_consistent_set_def_reflection
                  pseudo_scotus set_deduction_weaken)
      then have "\<forall>\<chi> \<psi>. insert \<chi> \<Gamma> \<tturnstile> \<psi> \<or> \<chi> \<rightarrow> \<phi> \<notin> \<Gamma>"
        by (meson assms
                  axiom_k
                  formula_maximally_consistent_set_def_reflection
                  set_deduction_modus_ponens
                  set_deduction_theorem
                  set_deduction_weaken)
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (meson \<open>\<psi> \<notin> \<Gamma>\<close>
                  assms
                  formula_maximally_consistent_set_def_def
                  formula_maximally_consistent_set_def_reflection
                  set_deduction_theorem)
    }
    moreover {
      assume "\<chi> \<in> \<Gamma>"
      hence "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>"
        by (metis assms
                  calculation
                  insert_absorb
                  formula_maximally_consistent_set_def_reflection
                  set_deduction_theorem)
    }
    ultimately have  "\<psi> \<rightarrow> \<chi> \<in> \<Gamma>" using hypothesis by blast
  }
  thus ?thesis
    using assms
          formula_maximally_consistent_set_def_implication_elimination
    by metis
qed

end
