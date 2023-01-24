chapter \<open> Classical Logic Connectives \label{sec:logical-connectives}\<close>

theory Classical_Connectives
  imports
    Classical_Logic_Completeness
    List_Utilities
begin

text \<open> Here we define the usual connectives for classical logic. \<close>

no_notation FuncSet.funcset (infixr "\<rightarrow>" 60)

section \<open> Verum \<close>

definition (in classical_logic) verum :: "'a" ("\<top>")
  where
    "\<top> = \<bottom> \<rightarrow> \<bottom>"

lemma (in classical_logic) verum_tautology [simp]: "\<turnstile> \<top>"
  by (metis list_implication.simps(1) list_implication_axiom_k verum_def)

lemma verum_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<top>"
  unfolding verum_def by simp

lemma (in classical_logic) verum_embedding [simp]:
  "\<^bold>\<lparr> \<top> \<^bold>\<rparr> = \<top>"
  by (simp add: classical_logic_class.verum_def verum_def)

section \<open> Conjunction \<close>

definition (in classical_logic)
  conjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<sqinter>" 67)
  where
    "\<phi> \<sqinter> \<psi> = (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"

primrec (in classical_logic)
  arbitrary_conjunction :: "'a list \<Rightarrow> 'a" ("\<Sqinter>")
  where
     "\<Sqinter> [] = \<top>"
  |  "\<Sqinter> (\<phi> # \<Phi>) = \<phi> \<sqinter> \<Sqinter> \<Phi>"

lemma (in classical_logic) conjunction_introduction:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis
        modus_ponens
        conjunction_def
        list_flip_implication1
        list_implication.simps(1)
        list_implication.simps(2))

lemma (in classical_logic) conjunction_left_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<phi>"
  by (metis (full_types)
        Peirces_law
        pseudo_scotus
        conjunction_def
        list_deduction_base_theory
        list_deduction_modus_ponens
        list_deduction_theorem
        list_deduction_weaken)

lemma (in classical_logic) conjunction_right_elimination:
  "\<turnstile> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<psi>"
  by (metis (full_types)
        axiom_k
        Contraposition
        modus_ponens
        conjunction_def
        flip_hypothetical_syllogism
        flip_implication)

lemma (in classical_logic) conjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<sqinter> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<sqinter> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding conjunction_def classical_logic_class.conjunction_def
  by simp

lemma conjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<sqinter> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<and> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding conjunction_def by simp

section \<open> Biconditional \<close>

definition (in classical_logic) biconditional :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<leftrightarrow>" 75)
  where
    "\<phi> \<leftrightarrow> \<psi> = (\<phi> \<rightarrow> \<psi>) \<sqinter> (\<psi> \<rightarrow> \<phi>)"

lemma (in classical_logic) biconditional_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)"
  by (simp add: biconditional_def conjunction_introduction)

lemma (in classical_logic) biconditional_left_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (simp add: biconditional_def conjunction_left_elimination)

lemma (in classical_logic) biconditional_right_elimination:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>"
  by (simp add: biconditional_def conjunction_right_elimination)

lemma (in classical_logic) biconditional_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<leftrightarrow> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<leftrightarrow> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding biconditional_def classical_logic_class.biconditional_def
  by simp

lemma biconditional_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<leftrightarrow> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<longleftrightarrow> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding biconditional_def
  by (simp, blast)

section \<open> Negation \<close>

definition (in classical_logic) negation :: "'a \<Rightarrow> 'a"  ("\<sim>")
  where
    "\<sim> \<phi> = \<phi> \<rightarrow> \<bottom>"

lemma (in classical_logic) negation_introduction:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<sim> \<phi>"
  unfolding negation_def
  by (metis axiom_k modus_ponens implication_absorption)

lemma (in classical_logic) negation_elimination:
  "\<turnstile> \<sim> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>)"
  unfolding negation_def
  by (metis axiom_k modus_ponens implication_absorption)

lemma (in classical_logic) negation_embedding [simp]:
  "\<^bold>\<lparr> \<sim> \<phi> \<^bold>\<rparr> = \<sim> \<^bold>\<lparr> \<phi> \<^bold>\<rparr>"
  by (simp add:
        classical_logic_class.negation_def
        negation_def)

lemma negation_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<phi> = (\<not> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi>)"
  unfolding negation_def
  by simp

section \<open> Disjunction \<close>

definition (in classical_logic) disjunction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<squnion>" 67)
  where
    "\<phi> \<squnion> \<psi> = (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>"

primrec (in classical_logic) arbitrary_disjunction :: "'a list \<Rightarrow> 'a" ("\<Squnion>")
  where
     "\<Squnion> [] = \<bottom>"
  |  "\<Squnion> (\<phi> # \<Phi>) = \<phi> \<squnion> \<Squnion> \<Phi>"

lemma (in classical_logic) disjunction_elimination:
  "\<turnstile> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<squnion> \<psi>) \<rightarrow> \<chi>"
proof -
  let ?\<Gamma> = "[\<phi> \<rightarrow> \<chi>, \<psi> \<rightarrow> \<chi>, \<phi> \<squnion> \<psi>]"
  have "?\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<chi>"
    unfolding disjunction_def
    by (metis hypothetical_syllogism
              list_deduction_def
              list_implication.simps(1)
              list_implication.simps(2)
              set_deduction_base_theory
              set_deduction_theorem
              set_deduction_weaken)
  hence "?\<Gamma> :\<turnstile> \<chi>"
    using excluded_middle_elimination
          list_deduction_modus_ponens
          list_deduction_theorem
          list_deduction_weaken
    by blast
  thus ?thesis
    unfolding list_deduction_def
    by simp
qed

lemma (in classical_logic) disjunction_left_introduction:
  "\<turnstile> \<phi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  by (metis modus_ponens
            pseudo_scotus
            flip_implication)

lemma (in classical_logic) disjunction_right_introduction:
  "\<turnstile> \<psi> \<rightarrow> (\<phi> \<squnion> \<psi>)"
  unfolding disjunction_def
  using axiom_k
  by simp

lemma (in classical_logic) disjunction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<squnion> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<squnion> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding disjunction_def classical_logic_class.disjunction_def
  by simp

lemma disjunction_semantics [simp]:
  "\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<squnion> \<psi> = (\<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<phi> \<or> \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<psi>)"
  unfolding disjunction_def
  by (simp, blast)

section \<open> Mutual Exclusion \<close>

primrec (in classical_logic) exclusive :: "'a list \<Rightarrow> 'a" ("\<Coprod>")
  where
      "\<Coprod> [] = \<top>"
    | "\<Coprod> (\<phi> # \<Phi>) = \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>) \<sqinter> \<Coprod> \<Phi>"

section \<open> Subtraction \<close>

definition (in classical_logic) subtraction :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<setminus>" 69)
  where "\<phi> \<setminus> \<psi> = \<phi> \<sqinter> \<sim> \<psi>"

lemma (in classical_logic) subtraction_embedding [simp]:
  "\<^bold>\<lparr> \<phi> \<setminus> \<psi> \<^bold>\<rparr> = \<^bold>\<lparr> \<phi> \<^bold>\<rparr> \<setminus> \<^bold>\<lparr> \<psi> \<^bold>\<rparr>"
  unfolding subtraction_def classical_logic_class.subtraction_def
  by simp

section \<open> Negated Lists \<close>

definition (in classical_logic) map_negation :: "'a list \<Rightarrow> 'a list" ("\<^bold>\<sim>")
  where [simp]: "\<^bold>\<sim> \<Phi> \<equiv> map \<sim> \<Phi>"

section \<open> Common (\& Uncommon) Identities \<close>

subsection \<open> Biconditional Equivalence Relation \<close>

lemma (in classical_logic) biconditional_reflection:
  "\<turnstile> \<phi> \<leftrightarrow> \<phi>"
  by (meson
        axiom_k
        modus_ponens
        biconditional_introduction
        implication_absorption)

lemma (in classical_logic) biconditional_symmetry:
  "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<leftrightarrow> (\<psi> \<leftrightarrow> \<phi>)"
  by (metis (full_types) modus_ponens
                         biconditional_def
                         conjunction_def
                         flip_hypothetical_syllogism
                         flip_implication)

lemma (in classical_logic) biconditional_symmetry_rule:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<phi>"
  by (meson modus_ponens
            biconditional_introduction
            biconditional_left_elimination
            biconditional_right_elimination)

lemma (in classical_logic) biconditional_transitivity:
    "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<chi>) \<rightarrow> (\<phi> \<leftrightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<rightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
 thus ?thesis by simp
qed

lemma (in classical_logic) biconditional_transitivity_rule:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<chi> \<Longrightarrow> \<turnstile> \<phi> \<leftrightarrow> \<chi>"
  using modus_ponens biconditional_transitivity by blast

subsection \<open> Biconditional Weakening \<close>

lemma (in classical_logic) biconditional_weaken:
  assumes "\<Gamma> \<tturnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> \<tturnstile> \<phi> = \<Gamma> \<tturnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            set_deduction_modus_ponens
            set_deduction_weaken)

lemma (in classical_logic) list_biconditional_weaken:
  assumes "\<Gamma> :\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<Gamma> :\<turnstile> \<phi> = \<Gamma> :\<turnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            list_deduction_modus_ponens
            list_deduction_weaken)

lemma (in classical_logic) weak_biconditional_weaken:
  assumes "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  shows "\<turnstile> \<phi> = \<turnstile> \<psi>"
  by (metis assms
            biconditional_left_elimination
            biconditional_right_elimination
            modus_ponens)

subsection \<open> Conjunction Identities \<close>

lemma (in classical_logic) conjunction_negation_identity:
  "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>)"
  by (metis Contraposition
            double_negation_converse
            modus_ponens
            biconditional_introduction
            conjunction_def
            negation_def)

lemma (in classical_logic) conjunction_set_deduction_equivalence [simp]:
  "\<Gamma> \<tturnstile> \<phi> \<sqinter> \<psi> = (\<Gamma> \<tturnstile> \<phi> \<and> \<Gamma> \<tturnstile> \<psi>)"
  by (metis set_deduction_weaken [where \<Gamma>="\<Gamma>"]
            set_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
            conjunction_introduction
            conjunction_left_elimination
            conjunction_right_elimination)

lemma (in classical_logic) conjunction_list_deduction_equivalence [simp]:
  "\<Gamma> :\<turnstile> \<phi> \<sqinter> \<psi> = (\<Gamma> :\<turnstile> \<phi> \<and> \<Gamma> :\<turnstile> \<psi>)"
  by (metis list_deduction_weaken [where \<Gamma>="\<Gamma>"]
            list_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
            conjunction_introduction
            conjunction_left_elimination
            conjunction_right_elimination)

lemma (in classical_logic) weak_conjunction_deduction_equivalence [simp]:
  "\<turnstile> \<phi> \<sqinter> \<psi> = (\<turnstile> \<phi> \<and> \<turnstile> \<psi>)"
  by (metis conjunction_set_deduction_equivalence set_deduction_base_theory)

lemma (in classical_logic) conjunction_set_deduction_arbitrary_equivalence [simp]:
  "\<Gamma> \<tturnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<phi>)"
  by (induct \<Phi>, simp add: set_deduction_weaken, simp)

lemma (in classical_logic) conjunction_list_deduction_arbitrary_equivalence [simp]:
  "\<Gamma> :\<turnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<Gamma> :\<turnstile> \<phi>)"
  by (induct \<Phi>, simp add: list_deduction_weaken, simp)

lemma (in classical_logic) weak_conjunction_deduction_arbitrary_equivalence [simp]:
  "\<turnstile> \<Sqinter> \<Phi> = (\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<phi>)"
  by (induct \<Phi>, simp+)

lemma (in classical_logic) conjunction_commutativity:
  "\<turnstile> (\<psi> \<sqinter> \<phi>) \<leftrightarrow> (\<phi> \<sqinter> \<psi>)"
  by (metis
        (full_types)
        modus_ponens
        biconditional_introduction
        conjunction_def
        flip_hypothetical_syllogism
        flip_implication)

lemma (in classical_logic) conjunction_associativity:
  "\<turnstile> ((\<phi> \<sqinter> \<psi>) \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<sqinter> (\<psi> \<sqinter> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) arbitrary_conjunction_antitone:
  "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
proof -
  have "\<forall> \<Phi>. set \<Phi> \<subseteq> set \<Psi> \<longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case
      by (simp add: pseudo_scotus verum_def)
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
      have "\<turnstile> \<Sqinter> (\<psi> # \<Psi>) \<rightarrow> \<Sqinter> \<Phi>"
      proof (cases "\<psi> \<in> set \<Phi>")
        assume "\<psi> \<in> set \<Phi>"
                have "\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<chi> \<Phi>)
          {
            fix \<phi>
            assume "\<phi> \<in> set (\<chi> # \<Phi>)"
            have "\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> (\<chi> # \<Phi>)))"
            proof cases
              assume "\<phi> \<in> set \<Phi>"
              hence "\<turnstile> \<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
                using Cons.hyps \<open>\<phi> \<in> set \<Phi>\<close>
                by auto
              moreover
              have "\<turnstile> (\<Sqinter> \<Phi> \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))) \<rightarrow>
                      (\<chi> \<sqinter> \<Sqinter> \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p
                        (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>))
                            \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>)
                                   \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)"
                    by auto
                hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>))
                               \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>)
                                      \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
              ultimately have "\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))"
                using modus_ponens by auto
              show ?thesis
              proof cases
                assume "\<phi> = \<chi>"
                moreover
                {
                  fix \<phi>
                  have "\<turnstile> (\<chi> \<sqinter> \<phi>) \<rightarrow> (\<chi> \<sqinter> \<chi> \<sqinter> \<phi>)"
                    unfolding conjunction_def
                    by (meson
                          axiom_s
                          double_negation
                          modus_ponens
                          flip_hypothetical_syllogism
                          flip_implication)
                } note tautology = this
                from \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                     \<open>\<phi> = \<chi>\<close>
                have "\<turnstile> (\<chi> \<sqinter> \<Sqinter> (removeAll \<chi> \<Phi>)) \<rightarrow> (\<chi> \<sqinter> \<Sqinter> \<Phi>)"
                  unfolding biconditional_def
                  by (simp, metis tautology hypothetical_syllogism modus_ponens)
                moreover
                from \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                     \<open>\<phi> = \<chi>\<close>
                have "\<turnstile> (\<chi> \<sqinter> \<Sqinter> \<Phi>) \<rightarrow> (\<chi> \<sqinter> \<Sqinter> (removeAll \<chi> \<Phi>))"
                  unfolding biconditional_def
                  by (simp,
                      metis conjunction_right_elimination
                            hypothetical_syllogism
                            modus_ponens)
                ultimately show ?thesis
                  unfolding biconditional_def
                  by simp
              next
                assume "\<phi> \<noteq> \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Sqinter> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<sqinter> \<chi> \<sqinter> \<Sqinter> (removeAll \<phi> \<Phi>))\<close>
                  by simp
              qed
            next
              assume "\<phi> \<notin> set \<Phi>"
              hence "\<phi> = \<chi>" "\<chi> \<notin> set \<Phi>"
                using \<open>\<phi> \<in> set (\<chi> # \<Phi>)\<close> by auto
              then show ?thesis
                using biconditional_reflection
                by simp
            qed
          }
          thus ?case by blast
        qed
        hence "\<turnstile> (\<psi> \<sqinter> \<Sqinter> (removeAll \<psi> \<Phi>)) \<rightarrow> \<Sqinter> \<Phi>"
          using modus_ponens biconditional_right_elimination \<open>\<psi> \<in> set \<Phi>\<close>
          by blast
        moreover
        from \<open>\<psi> \<in> set \<Phi>\<close> \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> Cons.hyps
        have "\<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> (removeAll \<psi> \<Phi>)"
          by (simp add: subset_insert_iff insert_absorb)
        hence "\<turnstile> (\<psi> \<sqinter> \<Sqinter> \<Psi>) \<rightarrow> (\<psi> \<sqinter> \<Sqinter> (removeAll \<psi> \<Phi>))"
          unfolding conjunction_def
          using
            modus_ponens
            hypothetical_syllogism
            flip_hypothetical_syllogism
          by meson
        ultimately have "\<turnstile> (\<psi> \<sqinter> \<Sqinter> \<Psi>) \<rightarrow> \<Sqinter> \<Phi>"
          using modus_ponens hypothetical_syllogism
          by blast
        thus ?thesis
          by simp
      next
        assume "\<psi> \<notin> set \<Phi>"
        hence "\<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>"
          using Cons.hyps \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close>
          by auto
        hence "\<turnstile> (\<psi> \<sqinter> \<Sqinter> \<Psi>) \<rightarrow> \<Sqinter> \<Phi>"
          unfolding conjunction_def
          by (metis
                modus_ponens
                conjunction_def
                conjunction_right_elimination
                hypothetical_syllogism)
        thus ?thesis
          by simp
      qed
    }
    thus ?case by blast
  qed
  thus "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Sqinter> \<Psi> \<rightarrow> \<Sqinter> \<Phi>" by blast
qed

lemma (in classical_logic) arbitrary_conjunction_remdups:
  "\<turnstile> (\<Sqinter> \<Phi>) \<leftrightarrow> \<Sqinter> (remdups \<Phi>)"
  by (simp add: arbitrary_conjunction_antitone biconditional_def)

lemma (in classical_logic) curry_uncurry:
  "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<leftrightarrow> ((\<phi> \<sqinter> \<psi>) \<rightarrow> \<chi>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) list_curry_uncurry:
  "\<turnstile> (\<Phi> :\<rightarrow> \<chi>) \<leftrightarrow> (\<Sqinter> \<Phi> \<rightarrow> \<chi>)"
proof (induct \<Phi>)
  case Nil
  have "\<turnstile> \<chi> \<leftrightarrow> (\<top> \<rightarrow> \<chi>)"
    unfolding biconditional_def
              conjunction_def
              verum_def
    using
      axiom_k
      ex_falso_quodlibet
      modus_ponens
      conjunction_def
      excluded_middle_elimination
      set_deduction_base_theory
      conjunction_set_deduction_equivalence
    by metis
  with Nil show ?case
    by simp
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<chi>))"
    by (simp add: biconditional_reflection)
  with Cons have "\<turnstile> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> \<Sqinter> \<Phi> \<rightarrow> \<chi>)"
    by (metis modus_ponens
              biconditional_def
              hypothetical_syllogism
              list_implication.simps(2)
              weak_conjunction_deduction_equivalence)
  with curry_uncurry [where ?\<phi>="\<phi>"  and ?\<psi>="\<Sqinter> \<Phi>" and ?\<chi>="\<chi>"]
  show ?case
    unfolding biconditional_def
    by (simp, metis modus_ponens hypothetical_syllogism)
qed

subsection \<open> Disjunction Identities \<close>

lemma (in classical_logic) bivalence:
  "\<turnstile> \<sim> \<phi> \<squnion> \<phi>"
  by (simp add: double_negation disjunction_def negation_def)

lemma (in classical_logic) implication_equivalence:
  "\<turnstile> (\<sim> \<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<rightarrow> \<psi>)"
  by (metis double_negation_converse
            modus_ponens
            biconditional_introduction
            bivalence
            disjunction_def
            flip_hypothetical_syllogism
            negation_def)

lemma (in classical_logic) disjunction_commutativity:
  "\<turnstile> (\<psi> \<squnion> \<phi>) \<leftrightarrow> (\<phi> \<squnion> \<psi>)"
  by (meson modus_ponens
            biconditional_introduction
            disjunction_elimination
            disjunction_left_introduction
            disjunction_right_introduction)

lemma (in classical_logic) disjunction_associativity:
  "\<turnstile> ((\<phi> \<squnion> \<psi>) \<squnion> \<chi>) \<leftrightarrow> (\<phi> \<squnion> (\<psi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
    by simp
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) arbitrary_disjunction_monotone:
  "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
proof -
  have "\<forall> \<Phi>. set \<Phi> \<subseteq> set \<Psi> \<longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
  proof (induct \<Psi>)
    case Nil
    then show ?case using verum_def verum_tautology by auto
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
      have "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> (\<psi> # \<Psi>)"
      proof cases
        assume "\<psi> \<in> set \<Phi>"
        have "\<forall> \<phi> \<in> set \<Phi>. \<turnstile> \<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<chi> \<Phi>)
          {
            fix \<phi>
            assume "\<phi> \<in> set (\<chi> # \<Phi>)"
            have "\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> (\<chi> # \<Phi>)))"
            proof cases
              assume "\<phi> \<in> set \<Phi>"
              hence "\<turnstile> \<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
                using Cons.hyps \<open>\<phi> \<in> set \<Phi>\<close>
                by auto
              moreover
              have "\<turnstile> (\<Squnion> \<Phi> \<leftrightarrow> (\<phi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))) \<rightarrow>
                      (\<chi> \<squnion> \<Squnion> \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p
                        (\<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>))
                         \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)
                              \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>)"
                    by auto
                  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>))
                             \<rightarrow> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)
                                 \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (removeAll \<phi> \<Phi>)\<^bold>\<rangle>) \<^bold>\<rparr>"
                    using propositional_semantics by blast
                  thus ?thesis by simp
              qed
              ultimately have "\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))"
                using modus_ponens by auto
              show ?thesis
              proof cases
                assume "\<phi> = \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))\<close>
                  unfolding biconditional_def
                  by (simp add: disjunction_def,
                      meson
                        axiom_k
                        modus_ponens
                        flip_hypothetical_syllogism
                        implication_absorption)
              next
                assume "\<phi> \<noteq> \<chi>"
                then show ?thesis
                  using \<open>\<turnstile> \<Squnion> (\<chi> # \<Phi>) \<leftrightarrow> (\<phi> \<squnion> \<chi> \<squnion> \<Squnion> (removeAll \<phi> \<Phi>))\<close>
                  by simp
              qed
            next
              assume "\<phi> \<notin> set \<Phi>"
              hence "\<phi> = \<chi>" "\<chi> \<notin> set \<Phi>"
                using \<open>\<phi> \<in> set (\<chi> # \<Phi>)\<close> by auto
              then show ?thesis
                using biconditional_reflection
                by simp
            qed
          }
          thus ?case by blast
        qed
        hence "\<turnstile> \<Squnion> \<Phi> \<rightarrow> (\<psi> \<squnion> \<Squnion> (removeAll \<psi> \<Phi>))"
          using modus_ponens biconditional_left_elimination \<open>\<psi> \<in> set \<Phi>\<close>
          by blast
        moreover
        from \<open>\<psi> \<in> set \<Phi>\<close> \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> Cons.hyps
        have "\<turnstile> \<Squnion> (removeAll \<psi> \<Phi>) \<rightarrow> \<Squnion> \<Psi>"
          by (simp add: subset_insert_iff insert_absorb)
        hence "\<turnstile> (\<psi> \<squnion> \<Squnion> (removeAll \<psi> \<Phi>)) \<rightarrow> \<Squnion> (\<psi> # \<Psi>)"
          using
            modus_ponens
            disjunction_def
            hypothetical_syllogism
          by fastforce
        ultimately show ?thesis
          by (simp, metis modus_ponens hypothetical_syllogism)
      next
        assume "\<psi> \<notin> set \<Phi>"
        hence "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>"
          using Cons.hyps \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close>
          by auto
        then show ?thesis
          by (metis
                arbitrary_disjunction.simps(2)
                disjunction_def
                list_deduction_def
                list_deduction_theorem
                list_deduction_weaken
                list_implication.simps(1)
                list_implication.simps(2))
      qed
    }
    then show ?case by blast
  qed
  thus "set \<Phi> \<subseteq> set \<Psi> \<Longrightarrow> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<Squnion> \<Psi>" by blast
qed

lemma (in classical_logic) arbitrary_disjunction_remdups:
  "\<turnstile> (\<Squnion> \<Phi>) \<leftrightarrow> \<Squnion> (remdups \<Phi>)"
  by (simp add: arbitrary_disjunction_monotone biconditional_def)

lemma (in classical_logic) arbitrary_disjunction_exclusion_MCS:
  assumes "MCS \<Omega>"
  shows "\<Squnion> \<Psi> \<notin> \<Omega> \<equiv> \<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>"
proof (induct \<Psi>)
  case Nil
  then show ?case
    using
      assms
      formula_consistent_def
      formula_maximally_consistent_set_def_def
      maximally_consistent_set_def
      set_deduction_reflection
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<Squnion> (\<psi> # \<Psi>) \<notin> \<Omega> = (\<psi> \<notin> \<Omega> \<and> \<Squnion> \<Psi> \<notin> \<Omega>)"
    by (simp add: disjunction_def,
        meson
          assms
          formula_consistent_def
          formula_maximally_consistent_set_def_def
          formula_maximally_consistent_set_def_implication
          maximally_consistent_set_def
          set_deduction_reflection)
  thus ?case using Cons.hyps by simp
qed

lemma (in classical_logic) contra_list_curry_uncurry:
  "\<turnstile> (\<Phi> :\<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> \<Squnion> (\<^bold>\<sim> \<Phi>))"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp,
          metis
            biconditional_introduction
            bivalence
            disjunction_def
            double_negation_converse
            modus_ponens
            negation_def)
next
  case (Cons \<phi> \<Phi>)
  hence "\<turnstile> (\<Sqinter> \<Phi> \<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> \<Squnion> (\<^bold>\<sim> \<Phi>))"
    by (metis
          biconditional_symmetry_rule
          biconditional_transitivity_rule
          list_curry_uncurry)
  have "\<turnstile> (\<Sqinter> (\<phi> # \<Phi>) \<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> \<Squnion> (\<^bold>\<sim> (\<phi> # \<Phi>)))"
  proof -
    have "\<turnstile> (\<Sqinter> \<Phi> \<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> \<Squnion> (\<^bold>\<sim> \<Phi>))
             \<rightarrow> ((\<phi> \<sqinter> \<Sqinter> \<Phi>) \<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> (\<sim> \<phi> \<squnion> \<Squnion> (\<^bold>\<sim> \<Phi>)))"
    proof -
      have
       "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p
         (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<sim> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> (\<^bold>\<sim> \<Phi>)\<^bold>\<rangle>)
             \<rightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<sim> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (\<^bold>\<sim> \<Phi>)\<^bold>\<rangle>))"
        by auto
      hence
        "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<sim> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> (\<^bold>\<sim> \<Phi>)\<^bold>\<rangle>)
             \<rightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Phi>\<^bold>\<rangle>) \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<leftrightarrow> (\<sim> \<^bold>\<langle>\<chi>\<^bold>\<rangle> \<rightarrow> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> (\<^bold>\<sim> \<Phi>)\<^bold>\<rangle>)) \<^bold>\<rparr>"
        using propositional_semantics by blast
      thus ?thesis by simp
    qed
    thus ?thesis
      using \<open>\<turnstile> (\<Sqinter> \<Phi> \<rightarrow> \<chi>) \<leftrightarrow> (\<sim> \<chi> \<rightarrow> \<Squnion> (\<^bold>\<sim> \<Phi>))\<close> modus_ponens by auto
  qed
  then show ?case
    using biconditional_transitivity_rule list_curry_uncurry by blast
qed

subsection \<open> Monotony of Conjunction and Disjunction \<close>

lemma (in classical_logic) conjunction_monotonic_identity:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<sqinter> \<chi>) \<rightarrow> (\<psi> \<sqinter> \<chi>)"
  unfolding conjunction_def
  using modus_ponens
        flip_hypothetical_syllogism
  by blast

lemma (in classical_logic) conjunction_monotonic:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi>"
  shows "\<turnstile> (\<phi> \<sqinter> \<chi>) \<rightarrow> (\<psi> \<sqinter> \<chi>)"
  using assms
        modus_ponens
        conjunction_monotonic_identity
  by blast

lemma (in classical_logic) disjunction_monotonic_identity:
  "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<squnion> \<chi>) \<rightarrow> (\<psi> \<squnion> \<chi>)"
  unfolding disjunction_def
  using modus_ponens
        flip_hypothetical_syllogism
  by blast

lemma (in classical_logic) disjunction_monotonic:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi>"
  shows "\<turnstile> (\<phi> \<squnion> \<chi>) \<rightarrow> (\<psi> \<squnion> \<chi>)"
  using assms
        modus_ponens
        disjunction_monotonic_identity
  by blast

subsection \<open> Distribution Identities \<close>

lemma (in classical_logic) conjunction_distribution:
  "\<turnstile> ((\<psi> \<squnion> \<chi>) \<sqinter> \<phi>) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> (\<chi> \<sqinter> \<phi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> ((\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<chi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) subtraction_distribution:
  "\<turnstile> ((\<psi> \<squnion> \<chi>) \<setminus> \<phi>) \<leftrightarrow> ((\<psi> \<setminus> \<phi>) \<squnion> (\<chi> \<setminus> \<phi>))"
  by (simp add: conjunction_distribution subtraction_def)

lemma (in classical_logic) conjunction_arbitrary_distribution:
  "\<turnstile> (\<Squnion> \<Psi> \<sqinter> \<phi>) \<leftrightarrow> \<Squnion> [\<psi> \<sqinter> \<phi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    by (simp add: ex_falso_quodlibet
                  biconditional_def
                  conjunction_left_elimination)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> (\<Squnion> (\<psi> # \<Psi>) \<sqinter> \<phi>) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> ((\<Squnion> \<Psi>) \<sqinter> \<phi>))"
    using conjunction_distribution by auto
  moreover
  from Cons have
    "\<turnstile> ((\<psi> \<sqinter> \<phi>) \<squnion> ((\<Squnion> \<Psi>) \<sqinter> \<phi>)) \<leftrightarrow> ((\<psi> \<sqinter> \<phi>) \<squnion> (\<Squnion> [\<psi> \<sqinter> \<phi>. \<psi> \<leftarrow> \<Psi>]))"
    unfolding disjunction_def biconditional_def
    by (simp, meson modus_ponens hypothetical_syllogism)
  ultimately show ?case
    by (simp, metis biconditional_transitivity_rule)
qed

lemma (in classical_logic) subtraction_arbitrary_distribution:
  "\<turnstile> (\<Squnion> \<Psi> \<setminus> \<phi>) \<leftrightarrow> \<Squnion> [\<psi> \<setminus> \<phi>. \<psi> \<leftarrow> \<Psi>]"
  by (simp add: conjunction_arbitrary_distribution subtraction_def)

lemma (in classical_logic) disjunction_distribution:
  "\<turnstile> (\<phi> \<squnion> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) implication_distribution:
  "\<turnstile> (\<phi> \<rightarrow> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<phi> \<rightarrow> \<psi>) \<sqinter> (\<phi> \<rightarrow> \<chi>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) list_implication_distribution:
  "\<turnstile> (\<Phi> :\<rightarrow> (\<psi> \<sqinter> \<chi>)) \<leftrightarrow> ((\<Phi> :\<rightarrow> \<psi>) \<sqinter> (\<Phi> :\<rightarrow> \<chi>))"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp add: biconditional_reflection)
next
  case (Cons \<phi> \<Phi>)
  hence " \<turnstile> (\<phi> # \<Phi>) :\<rightarrow> (\<psi> \<sqinter> \<chi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<chi>))"
    by (metis
          modus_ponens
          biconditional_def
          hypothetical_syllogism
          list_implication.simps(2)
          weak_conjunction_deduction_equivalence)
  moreover
  have "\<turnstile> (\<phi> \<rightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<chi>)) \<leftrightarrow> (((\<phi> # \<Phi>) :\<rightarrow> \<psi>) \<sqinter> ((\<phi> # \<Phi>) :\<rightarrow> \<chi>))"
    using implication_distribution by auto
  ultimately show ?case
    by (simp, metis biconditional_transitivity_rule)
qed

lemma (in classical_logic) biconditional_conjunction_weaken:
  "\<turnstile> (\<alpha> \<leftrightarrow> \<beta>) \<rightarrow> ((\<gamma> \<sqinter> \<alpha>) \<leftrightarrow> (\<gamma> \<sqinter> \<beta>))"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>))"
      by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<alpha>\<^bold>\<rangle> \<leftrightarrow> \<^bold>\<langle>\<beta>\<^bold>\<rangle>) \<rightarrow> ((\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<alpha>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<gamma>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<beta>\<^bold>\<rangle>)) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) biconditional_conjunction_weaken_rule:
  "\<turnstile> (\<alpha> \<leftrightarrow> \<beta>) \<Longrightarrow> \<turnstile> (\<gamma> \<sqinter> \<alpha>) \<leftrightarrow> (\<gamma> \<sqinter> \<beta>)"
  using modus_ponens biconditional_conjunction_weaken by blast

lemma (in classical_logic) disjunction_arbitrary_distribution:
  "\<turnstile> (\<phi> \<squnion> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<phi> \<squnion> \<psi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    unfolding disjunction_def biconditional_def
    using axiom_k modus_ponens verum_tautology
    by (simp, blast)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> (\<phi> \<squnion> \<Sqinter> (\<psi> # \<Psi>)) \<leftrightarrow> ((\<phi> \<squnion> \<psi>) \<sqinter> (\<phi> \<squnion> \<Sqinter> \<Psi>))"
    by (simp add: disjunction_distribution)
  moreover
  from biconditional_conjunction_weaken_rule
       Cons
  have " \<turnstile> ((\<phi> \<squnion> \<psi>) \<sqinter> \<phi> \<squnion> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> (map (\<lambda> \<chi> . \<phi> \<squnion> \<chi>) (\<psi> # \<Psi>))"
    by simp
  ultimately show ?case
    by (metis biconditional_transitivity_rule)
qed

lemma (in classical_logic) list_implication_arbitrary_distribution:
  "\<turnstile> (\<Phi> :\<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<Phi> :\<rightarrow> \<psi>. \<psi> \<leftarrow> \<Psi>]"
proof (induct \<Psi>)
  case Nil
  then show ?case
    by (simp add: biconditional_def,
        meson
          axiom_k
          modus_ponens
          list_implication_axiom_k
          verum_tautology)
next
  case (Cons \<psi> \<Psi>)
  have "\<turnstile> \<Phi> :\<rightarrow> \<Sqinter> (\<psi> # \<Psi>) \<leftrightarrow> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<Sqinter> \<Psi>)"
    using list_implication_distribution
    by fastforce
  moreover
  from biconditional_conjunction_weaken_rule
       Cons
  have "\<turnstile> (\<Phi> :\<rightarrow> \<psi> \<sqinter> \<Phi> :\<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<Phi> :\<rightarrow> \<psi>. \<psi> \<leftarrow> (\<psi> # \<Psi>)]"
    by simp
  ultimately show ?case
    by (metis biconditional_transitivity_rule)
qed

lemma (in classical_logic) implication_arbitrary_distribution:
  "\<turnstile> (\<phi> \<rightarrow> \<Sqinter> \<Psi>) \<leftrightarrow> \<Sqinter> [\<phi> \<rightarrow> \<psi>. \<psi> \<leftarrow> \<Psi>]"
  using list_implication_arbitrary_distribution [where ?\<Phi>="[\<phi>]"]
  by simp

subsection \<open> Negation \<close>

lemma (in classical_logic) double_negation_biconditional:
  "\<turnstile> \<sim> (\<sim> \<phi>) \<leftrightarrow> \<phi>"
  unfolding biconditional_def negation_def
  by (simp add: double_negation double_negation_converse)

lemma (in classical_logic) double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> \<sim> (\<sim> \<phi>) = \<Gamma> \<tturnstile> \<phi>"
  using
    set_deduction_weaken
    biconditional_weaken
    double_negation_biconditional
  by metis

lemma (in classical_logic) alt_double_negation_elimination [simp]:
  "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<Gamma> \<tturnstile> \<phi>"
  using double_negation_elimination
  unfolding negation_def
  by auto

lemma (in classical_logic) base_double_negation_elimination [simp]:
  "\<turnstile> \<sim> (\<sim> \<phi>) = \<turnstile> \<phi>"
  by (metis double_negation_elimination set_deduction_base_theory)

lemma (in classical_logic) alt_base_double_negation_elimination [simp]:
  "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom> \<equiv> \<turnstile> \<phi>"
  using base_double_negation_elimination
  unfolding negation_def
  by auto

subsection \<open> Mutual Exclusion Identities \<close>

lemma (in classical_logic) exclusion_contrapositive_equivalence:
  "\<turnstile> (\<phi> \<rightarrow> \<gamma>) \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<sim> \<gamma>)"
proof -
  have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>)"
    by auto
  hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<sim> \<^bold>\<langle>\<gamma>\<^bold>\<rangle>) \<^bold>\<rparr>"
    using propositional_semantics by blast
  thus ?thesis by simp
qed

lemma (in classical_logic) disjuction_exclusion_equivalence:
  "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>) \<equiv> \<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp add:
          conjunction_right_elimination
          negation_def
          set_deduction_weaken)
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) \<leftrightarrow> \<sim> (\<psi> \<sqinter> (\<phi> \<squnion> \<Squnion> \<Phi>))"
    by (simp add: biconditional_reflection)
  moreover have "\<turnstile> \<sim> (\<psi> \<sqinter> (\<phi> \<squnion> \<Squnion> \<Phi>)) \<leftrightarrow> (\<sim> (\<psi> \<sqinter> \<phi>) \<sqinter> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))
                         \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
      by auto
    hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))
               \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately
  have "\<turnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) \<leftrightarrow> (\<sim> (\<psi> \<sqinter> \<phi>) \<sqinter> \<sim> (\<psi> \<sqinter> \<Squnion> \<Phi>))"
    by simp
  hence "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) = (\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>)
           \<and> (\<forall>\<phi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>)))"
    using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          conjunction_set_deduction_equivalence [where \<Gamma>="\<Gamma>"]
          Cons.hyps
          biconditional_def
          set_deduction_modus_ponens
    by metis
  thus "\<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<Squnion> (\<phi> # \<Phi>)) = (\<forall>\<phi>\<in>set (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> (\<psi> \<sqinter> \<phi>))"
    by simp
qed

lemma (in classical_logic) exclusive_elimination1:
  assumes "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
  shows "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  thus ?case by auto
next
  case (Cons \<chi> \<Phi>)
  assume "\<Gamma> \<tturnstile> \<Coprod> (\<chi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" by simp
  hence "\<forall>\<phi>\<in>set \<Phi>. \<forall>\<psi>\<in>set \<Phi>. \<phi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    using Cons.hyps by blast
  moreover have "\<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<Squnion> \<Phi>)"
    using \<open>\<Gamma> \<tturnstile> \<Coprod> (\<chi> # \<Phi>)\<close> conjunction_set_deduction_equivalence by auto
  hence "\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<phi>)"
    using disjuction_exclusion_equivalence by auto
  moreover {
    fix \<phi>
    have "\<turnstile> \<sim> (\<chi> \<sqinter> \<phi>) \<rightarrow> \<sim> (\<phi> \<sqinter> \<chi>)"
      unfolding negation_def
                conjunction_def
      using modus_ponens flip_hypothetical_syllogism flip_implication by blast
  }
  with \<open>\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<phi>)\<close> have "\<forall> \<phi> \<in> set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
    using set_deduction_weaken [where \<Gamma>="\<Gamma>"]
          set_deduction_modus_ponens [where \<Gamma>="\<Gamma>"]
    by blast
  ultimately
  show "\<forall>\<phi> \<in> set (\<chi> # \<Phi>). \<forall>\<psi> \<in> set (\<chi> # \<Phi>). \<phi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    by simp
qed

lemma (in classical_logic) exclusive_elimination2:
  assumes "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
  shows "\<forall> \<phi> \<in> duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  assume "\<Gamma> \<tturnstile> \<Coprod> (\<phi> # \<Phi>)"
  hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" by simp
  hence "\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>" using Cons.hyps by auto
  show ?case
  proof cases
    assume "\<phi> \<in> set \<Phi>"
    moreover {
      fix \<phi> \<psi> \<chi>
      have "\<turnstile> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<chi>)) \<leftrightarrow> (\<sim> (\<phi> \<sqinter> \<psi>) \<sqinter> \<sim> (\<phi> \<sqinter> \<chi>))"
      proof -
        have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))
                       \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>))"
          by auto
        hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<leftrightarrow> (\<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<chi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
          using propositional_semantics by blast
        thus ?thesis by simp
      qed
      hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<chi>)) \<equiv> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>) \<sqinter> \<sim> (\<phi> \<sqinter> \<chi>)"
        using set_deduction_weaken
              biconditional_weaken by presburger
    }
    moreover
    have "\<turnstile> \<sim> (\<phi> \<sqinter> \<phi>) \<leftrightarrow> \<sim> \<phi>"
    proof -
      have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle>"
        by auto
      hence "\<turnstile> \<^bold>\<lparr> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<phi>\<^bold>\<rangle>) \<leftrightarrow> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<rparr>"
        using propositional_semantics by blast
      thus ?thesis by simp
    qed
    hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<phi>) \<equiv> \<Gamma> \<tturnstile> \<sim> \<phi>"
      using set_deduction_weaken
            biconditional_weaken by presburger
    moreover have "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" using \<open>\<Gamma> \<tturnstile> \<Coprod> (\<phi> # \<Phi>)\<close> by simp
    ultimately have "\<Gamma> \<tturnstile> \<sim> \<phi>" by (induct \<Phi>, simp, simp, blast)
    thus ?thesis using \<open>\<phi> \<in> set \<Phi>\<close> \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close> by simp
  next
    assume "\<phi> \<notin> set \<Phi>"
    hence "duplicates (\<phi> # \<Phi>) = duplicates \<Phi>" by simp
    then show ?thesis using \<open>\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>\<close>
      by auto
  qed
qed

lemma (in classical_logic) exclusive_equivalence:
   "\<Gamma> \<tturnstile> \<Coprod> \<Phi> =
      ((\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>) \<and>
         (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)))"
proof -
  {
    assume "\<forall>\<phi>\<in>duplicates \<Phi>. \<Gamma> \<tturnstile> \<sim> \<phi>"
           "\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    hence "\<Gamma> \<tturnstile> \<Coprod> \<Phi>"
    proof (induct \<Phi>)
      case Nil
      then show ?case
        by (simp add: set_deduction_weaken)
    next
      case (Cons \<phi> \<Phi>)
      assume A: "\<forall>\<phi>\<in>duplicates (\<phi> # \<Phi>). \<Gamma> \<tturnstile> \<sim> \<phi>"
         and B: "\<forall>\<chi>\<in>set (\<phi> # \<Phi>). \<forall>\<psi>\<in>set (\<phi> # \<Phi>). \<chi> \<noteq> \<psi> \<longrightarrow> \<Gamma> \<tturnstile> \<sim> (\<chi> \<sqinter> \<psi>)"
      hence C: "\<Gamma> \<tturnstile> \<Coprod> \<Phi>" using Cons.hyps by simp
      then show ?case
      proof cases
        assume "\<phi> \<in> duplicates (\<phi> # \<Phi>)"
        moreover from this have "\<Gamma> \<tturnstile> \<sim> \<phi>" using A by auto
        moreover have "duplicates \<Phi> \<subseteq> set \<Phi>" by (induct \<Phi>, simp, auto)
        ultimately have "\<phi> \<in> set \<Phi>" by (metis duplicates.simps(2) subsetCE)
        hence "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim>(\<phi> \<sqinter> \<Squnion> \<Phi>)"
        proof (induct \<Phi>)
          case Nil
          then show ?case by simp
        next
          case (Cons \<psi> \<Phi>)
          assume "\<phi> \<in> set (\<psi> # \<Phi>)"
          then show "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> (\<psi> # \<Phi>))"
          proof -
            {
              assume "\<phi> = \<psi>"
              hence ?thesis
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
                  using \<open>\<phi> = \<psi>\<close> by auto
                hence "\<turnstile> \<^bold>\<lparr> \<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
            }
            moreover
            {
              assume "\<phi> \<noteq> \<psi>"
              hence "\<phi> \<in> set \<Phi>" using \<open>\<phi> \<in> set (\<psi> # \<Phi>)\<close> by auto
              hence "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" using Cons.hyps by auto
              moreover have "\<turnstile> (\<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>))
                                   \<rightarrow> (\<sim> \<phi> \<leftrightarrow> \<sim> (\<phi> \<sqinter> (\<psi> \<squnion> \<Squnion> \<Phi>)))"
              proof -
                have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow>
                                     (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)))"
                  by auto
                hence "\<turnstile> \<^bold>\<lparr> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))
                           \<rightarrow> (\<sim> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> \<sim> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))) \<^bold>\<rparr>"
                  using propositional_semantics by blast
                thus ?thesis by simp
              qed
              ultimately have ?thesis using modus_ponens by simp
            }
            ultimately show ?thesis by auto
          qed
        qed
        with \<open>\<Gamma> \<tturnstile> \<sim> \<phi>\<close> have "\<Gamma> \<tturnstile> \<sim>(\<phi> \<sqinter> \<Squnion> \<Phi>)"
          using biconditional_weaken set_deduction_weaken by blast
        with \<open>\<Gamma> \<tturnstile> \<Coprod> \<Phi>\<close> show ?thesis by simp
      next
        assume "\<phi> \<notin> duplicates (\<phi> # \<Phi>)"
        hence "\<phi> \<notin> set \<Phi>" by auto
        with B have "\<forall>\<psi>\<in>set \<Phi>. \<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<psi>)" by (simp, metis)
        hence "\<Gamma> \<tturnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)"
          by (simp add: disjuction_exclusion_equivalence)
        with \<open>\<Gamma> \<tturnstile> \<Coprod> \<Phi>\<close> show ?thesis by simp
      qed
    qed
  }
  thus ?thesis
    by (metis exclusive_elimination1 exclusive_elimination2)
qed

subsection \<open> Miscellaneous Disjunctive Normal Form Identities \<close>

lemma (in classical_logic) map_negation_list_implication:
  "\<turnstile> ((\<^bold>\<sim> \<Phi>) :\<rightarrow> (\<sim> \<phi>)) \<leftrightarrow> (\<phi> \<rightarrow> \<Squnion> \<Phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case
    unfolding
      biconditional_def
      map_negation_def
      negation_def
    using
      conjunction_introduction
      modus_ponens
      trivial_implication
    by simp
next
  case (Cons \<psi> \<Phi>)
  have "\<turnstile> (\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi> \<leftrightarrow> (\<phi> \<rightarrow> \<Squnion> \<Phi>))
          \<rightarrow> (\<sim> \<psi> \<rightarrow> \<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>) \<leftrightarrow> (\<phi> \<rightarrow> (\<psi> \<squnion> \<Squnion> \<Phi>))"
  proof -
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow>
                        (\<sim> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>))"
      by fastforce
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<rightarrow>
               (\<sim> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<rightarrow> \<^bold>\<langle>\<^bold>\<sim> \<Phi> :\<rightarrow> \<sim> \<phi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<Squnion> \<Phi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  with Cons show ?case
    by (metis
          map_negation_def
          list.simps(9)
          arbitrary_disjunction.simps(2)
          modus_ponens
          list_implication.simps(2))
qed


lemma (in classical_logic) conj_dnf_distribute:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
proof(induct \<Lambda>)
  case Nil
  have "\<turnstile> \<bottom> \<leftrightarrow> (\<phi> \<sqinter> \<bottom>)"
  proof -
    let ?\<phi> = "\<bottom> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<bottom>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis by simp
  qed
  then show ?case by simp
next
  case (Cons \<Psi> \<Lambda>)
  assume "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda>) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> ?A \<leftrightarrow> (\<phi> \<sqinter> ?B)")
  moreover
  have "\<turnstile> (?A \<leftrightarrow> (\<phi> \<sqinter> ?B)) \<rightarrow> (((\<phi> \<sqinter> \<Sqinter> \<Psi>) \<squnion> ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> \<Psi> \<squnion> ?B))"
  proof -
    let ?\<phi> = "(\<^bold>\<langle>?A\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?B\<^bold>\<rangle>)) \<rightarrow>
               (((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle>) \<squnion> \<^bold>\<langle>?A\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Sqinter> \<Psi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>?B\<^bold>\<rangle>))"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by fastforce
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  ultimately have "\<turnstile> ((\<phi> \<sqinter> \<Sqinter> \<Psi>) \<squnion> ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Sqinter> \<Psi> \<squnion> ?B)"
    using modus_ponens
    by blast
  moreover
  have "map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) \<Lambda> = map (\<lambda>\<Psi>. \<phi> \<sqinter> \<Sqinter> \<Psi>) \<Lambda>" by simp
  ultimately show ?case by simp
qed

lemma (in classical_logic) append_dnf_distribute:
  "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<Psi>. \<Phi> @ \<Psi>)) \<Lambda>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
proof(induct \<Phi>)
  case Nil
  have "\<turnstile> \<Squnion> (map \<Sqinter> \<Lambda>) \<leftrightarrow> (\<top> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> ?A \<leftrightarrow> (\<top> \<sqinter> ?A)")
  proof -
    let ?\<phi> = "\<^bold>\<langle>?A\<^bold>\<rangle> \<leftrightarrow> ((\<bottom> \<rightarrow> \<bottom>) \<sqinter> \<^bold>\<langle>?A\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by simp
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      unfolding verum_def
      by simp
  qed
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>)
  have "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (@) \<Phi>) \<Lambda>) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))
       = \<turnstile> \<Squnion> (map \<Sqinter> (map ((@) \<Phi>) \<Lambda>)) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    by simp
  with Cons have
    "\<turnstile> \<Squnion> (map \<Sqinter> (map (\<lambda> \<Psi>. \<Phi> @ \<Psi>) \<Lambda>)) \<leftrightarrow> (\<Sqinter> \<Phi> \<sqinter> \<Squnion> (map \<Sqinter> \<Lambda>))"
    (is "\<turnstile> \<Squnion> (map \<Sqinter> ?A) \<leftrightarrow> (?B \<sqinter> ?C)")
    by meson
  moreover have "\<turnstile> \<Squnion> (map \<Sqinter> ?A) \<leftrightarrow> (?B \<sqinter> ?C)
                \<rightarrow> (\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> (\<phi> \<sqinter> \<Squnion> (map \<Sqinter> ?A)))
                \<rightarrow> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
  proof -
    let ?\<phi> = "\<^bold>\<langle>\<Squnion> (map \<Sqinter> ?A)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>?B\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?C\<^bold>\<rangle>)
           \<rightarrow> (\<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A)\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<Squnion> (map \<Sqinter> ?A)\<^bold>\<rangle>))
           \<rightarrow> \<^bold>\<langle>\<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A)\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>?B\<^bold>\<rangle>) \<sqinter> \<^bold>\<langle>?C\<^bold>\<rangle>)"
    have "\<forall>\<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p ?\<phi>" by simp
    hence "\<turnstile> \<^bold>\<lparr> ?\<phi> \<^bold>\<rparr>" using propositional_semantics by blast
    thus ?thesis
      by simp
  qed
  ultimately have "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (\<lambda> \<phi>s. \<phi> # \<phi>s)) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
    using modus_ponens conj_dnf_distribute
    by blast
  moreover
  have "\<Sqinter> \<circ> (@) (\<phi> # \<Phi>) = \<Sqinter> \<circ> (#) \<phi> \<circ> (@) \<Phi>" by auto
  hence
    "\<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (@) (\<phi> # \<Phi>)) \<Lambda>) \<leftrightarrow> (\<Sqinter> (\<phi> # \<Phi>) \<sqinter> ?C)
   = \<turnstile> \<Squnion> (map (\<Sqinter> \<circ> (#) \<phi>) ?A) \<leftrightarrow> ((\<phi> \<sqinter> ?B) \<sqinter> ?C)"
    by simp
  ultimately show ?case by meson
qed

notation FuncSet.funcset (infixr "\<rightarrow>" 60)

end
