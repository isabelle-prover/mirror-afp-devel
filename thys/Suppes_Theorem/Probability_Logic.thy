chapter \<open> Probability Logic \label{chapter:probability} \<close>

theory Probability_Logic
  imports
    "Propositional_Logic_Class.Classical_Connectives"
    HOL.Real
    "HOL-Library.Countable"
begin

no_notation FuncSet.funcset (infixr "\<rightarrow>" 60)

section \<open> Definition of Probability Logic \label{sec:definition-of-probability-logic} \<close>

text \<open> Probability logic is defined in terms of an operator over
       classical logic obeying certain postulates. Scholars often credit
       George Boole for first conceiving this kind of formulation @{cite booleChapterXVITheory1853}.
       Theodore Hailperin in particular has written extensively on this subject
       @{cite hailperinProbabilityLogic1984
         and hailperinBooleLogicProbability1986
         and hailperinSententialProbabilityLogic1996}. \<close>

text \<open> The presentation below roughly follows Kolmogorov's axiomatization
       @{cite kolmogoroffChapterElementareWahrscheinlichkeitsrechnung1933}.
       A key difference is that we only require \<^emph>\<open>finite additivity\<close>, rather
       than \<^emph>\<open>countable additivity\<close>. Finite additivity is also defined in
       terms of implication \<^term>\<open>(\<rightarrow>)\<close>. \<close>

class probability_logic = classical_logic +
  fixes \<P> :: "'a \<Rightarrow> real"
  assumes probability_non_negative: "\<P> \<phi> \<ge> 0"
  assumes probability_unity: "\<turnstile> \<phi> \<Longrightarrow> \<P> \<phi> = 1"
  assumes probability_implicational_additivity:
    "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> \<P> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = \<P> \<phi> + \<P> \<psi>"

text \<open> A similar axiomatization may be credited to
       Rescher @{cite \<open>pg. 185\<close> rescherManyvaluedLogic1969}.
       However, our formulation has fewer axioms.
       While Rescher assumes \<^term>\<open>\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<P> \<phi> = \<P> \<psi>\<close>, we
       show this is a lemma in \S\ref{sec:prob-logic-alt-def}. \<close>

section \<open> Why Finite Additivity? \label{section:why-finite-additivity} \<close>

text \<open> In this section we touch on why we have chosen to
       employ finite additivity in our axiomatization of
       @{class probability_logic} and deviate from conventional
       probability theory. \<close>

text \<open> Conventional probability obeys an axiom known as \<^emph>\<open>countable additivity\<close>.
       Traditionally it states if \<open>S\<close> is a countable set of sets which are
       pairwise disjoint, then the limit \<open>\<Sum> s \<in> S. \<P> s\<close> exists and
       \<open>\<P> (\<Union> S) = (\<Sum> s \<in> S. \<P> s)\<close>. This is more powerful than our
       finite additivity axiom
       @{lemma \<open>\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom> \<Longrightarrow> \<P> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = \<P> \<phi> + \<P> \<psi>\<close>
          by (metis probability_implicational_additivity) }. \<close>

text \<open> However, we argue that demanding countable additivity is not practical. \<close>

text \<open> Historically, the statisticians Bruno de Finetti and Leonard Savage
       gave the most well known critiques.  In @{cite definettiSuiPassaggiLimite1930}
       de Finetti shows various properties which are true for countably additive
       probability measures may not hold for finitely additive measures.
       Savage @{cite savageDifficultiesTheoryPersonal1967}, on the other hand,
       develops probability based on choices prizes in lotteries. \<close>

text \<open> We instead argue that if we demand countable additivity, then certain
       properties of real world software would no longer be formally verifiable 
       as we demonstrate here. In particular, it prohibits conventional recursive
       data structures for defining propositions. Our argument is derivative of 
       one given by Giangiacomo Gerla @{cite \<open>Section 3\<close> gerlaInferencesProbabilityLogic1994}. \<close>

text \<open> By taking equivalence classes modulo \<^term>\<open>\<lambda> \<phi> \<psi> . \<turnstile> \<phi> \<leftrightarrow> \<psi>\<close>,
       any classical logic instance gives rise to a Boolean algebra known as
       a \<^emph>\<open>Lindenbaum Algebra\<close>. In the case of @{typ "'a classical_propositional_formula"}
       this Boolean algebra algebra is both countable and \<^emph>\<open>atomless\<close>.
       A theorem of Horn and Tarski @{cite \<open>Theorem 3.2\<close> hornMeasuresBooleanAlgebras1948}
       asserts there can be no countably additive \<^term>\<open>Pr\<close> for a countable
       atomless Boolean algebra. \<close>

text \<open> The above argument is not intended as a blanket refutation of conventional
       probability theory. It is simply an impossibility result with respect
       to software implementations of probability logic. Plenty of classic results 
       in probability rely on countable additivity. A nice example, formalized in 
       Isabelle/HOL, is Bouffon's needle @{cite eberlBuffonNeedleProblem2017}. \<close>

section \<open> Basic Properties of Probability Logic \<close>

lemma (in probability_logic) probability_additivity:
  assumes "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
  shows "\<P> (\<phi> \<squnion> \<psi>) = \<P> \<phi> + \<P> \<psi>"
  using
    assms
  unfolding
    conjunction_def
    disjunction_def
    negation_def
  by (simp add: probability_implicational_additivity)

lemma (in probability_logic) probability_alternate_additivity:
  assumes "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  shows "\<P> (\<phi> \<squnion> \<psi>) = \<P> \<phi> + \<P> \<psi>"
  using assms
  by (metis
        probability_additivity
        double_negation_converse
        modus_ponens
        conjunction_def
        negation_def)

lemma (in probability_logic) complementation:
  "\<P> (\<sim> \<phi>) = 1 - \<P> \<phi>"
  by (metis
        probability_alternate_additivity
        probability_unity
        bivalence
        negation_elimination
        add.commute
        add_diff_cancel_left')

lemma (in probability_logic) unity_upper_bound:
  "\<P> \<phi> \<le> 1"
  by (metis
        (no_types)
        diff_ge_0_iff_ge
        probability_non_negative
        complementation)

section \<open> Alternate Definition of Probability Logic \label{sec:prob-logic-alt-def} \<close>

text \<open> There is an alternate axiomatization of probability logic,
       due to Brian Gaines @{cite \<open>pg. 159, postulates P7, P8, and P8\<close> gainesFuzzyProbabilityUncertainty1978}
       and independently formulated by Brian Weatherson @{cite weathersonClassicalIntuitionisticProbability2003}.
       As Weatherson notes, this axiomatization is suited to formulating
       \<^emph>\<open>intuitionistic\<close> probability logic. In the case where the underlying
       logic is classical the Gaines/Weatherson axiomatization is equivalent
       to the traditional Kolmogorov axiomatization from
       \S\ref{sec:definition-of-probability-logic}. \<close>

class gaines_weatherson_probability = classical_logic +
  fixes \<P> :: "'a \<Rightarrow> real"
  assumes gaines_weatherson_thesis:
    "\<P> \<top> = 1"
  assumes gaines_weatherson_antithesis:
    "\<P> \<bottom> = 0"
  assumes gaines_weatherson_monotonicity:
    "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<P> \<phi> \<le> \<P> \<psi>"
  assumes gaines_weatherson_sum_rule:
    "\<P> \<phi> + \<P> \<psi> = \<P> (\<phi> \<sqinter> \<psi>) + \<P> (\<phi> \<squnion> \<psi>)"

sublocale gaines_weatherson_probability \<subseteq> probability_logic
proof
  fix \<phi>
  have "\<turnstile> \<bottom> \<rightarrow> \<phi>"
    by (simp add: ex_falso_quodlibet)
  thus "0 \<le> \<P> \<phi>"
    using
      gaines_weatherson_antithesis
      gaines_weatherson_monotonicity
    by fastforce
next
  fix \<phi>
  assume "\<turnstile> \<phi>"
  thus "\<P> \<phi> = 1"
    by (metis
          gaines_weatherson_thesis
          gaines_weatherson_monotonicity
          eq_iff
          axiom_k
          ex_falso_quodlibet
          modus_ponens
          verum_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)"
    by (simp add: conjunction_def negation_def)
  thus "\<P> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = \<P> \<phi> + \<P> \<psi>"
    by (metis
          add.commute
          add.right_neutral
          eq_iff
          disjunction_def
          ex_falso_quodlibet
          negation_def
          gaines_weatherson_antithesis
          gaines_weatherson_monotonicity
          gaines_weatherson_sum_rule)
qed

lemma (in probability_logic) monotonicity:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<P> \<phi> \<le> \<P> \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<sim> \<psi>)"
    unfolding negation_def conjunction_def
    by (metis
          conjunction_def
          exclusion_contrapositive_equivalence
          negation_def
          weak_biconditional_weaken)
  hence "\<P> (\<phi> \<squnion> \<sim> \<psi>) = \<P> \<phi> + \<P> (\<sim> \<psi>)"
    by (simp add: probability_additivity)
  hence "\<P> \<phi> + \<P> (\<sim> \<psi>) \<le> 1"
    by (metis unity_upper_bound)
  hence "\<P> \<phi> + 1 - \<P> \<psi> \<le> 1"
    by (simp add: complementation)
  thus ?thesis by linarith
qed

lemma (in probability_logic) biconditional_equivalence:
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<P> \<phi> = \<P> \<psi>"
  by (meson
        eq_iff
        modus_ponens
        biconditional_left_elimination
        biconditional_right_elimination
        monotonicity)

lemma (in probability_logic) sum_rule:
  "\<P> (\<phi> \<squnion> \<psi>) + \<P> (\<phi> \<sqinter> \<psi>) = \<P> \<phi> + \<P> \<psi>"
proof -
  have "\<turnstile> (\<phi> \<squnion> \<psi>) \<leftrightarrow> (\<phi> \<squnion> \<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<leftrightarrow> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<squnion> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> \<phi> \<rightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> \<bottom>"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom>"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<rightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<rightarrow> \<bottom> \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "\<P> (\<phi> \<squnion> \<psi>) = \<P> \<phi> + \<P> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>))"
    using
      probability_alternate_additivity
      biconditional_equivalence
      calculation
    by auto
  moreover have "\<turnstile> \<psi> \<leftrightarrow> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by auto
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<psi>\<^bold>\<rangle> \<leftrightarrow> (\<^bold>\<langle>\<psi>\<^bold>\<rangle> \<setminus> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by
      blast
    thus ?thesis by simp
  qed
  moreover have "\<turnstile> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) \<rightarrow> (\<phi> \<sqinter> \<psi>) \<rightarrow> \<bottom>"
    unfolding
      subtraction_def
      negation_def
      conjunction_def
    using
      conjunction_def
      conjunction_right_elimination
    by auto
  hence "\<P> \<psi> = \<P> (\<psi> \<setminus> (\<phi> \<sqinter> \<psi>)) + \<P> (\<phi> \<sqinter> \<psi>)"
    using
      probability_alternate_additivity
      biconditional_equivalence
      calculation
    by auto
  ultimately show ?thesis
    by simp
qed

sublocale probability_logic \<subseteq> gaines_weatherson_probability
proof
  show "\<P> \<top> = 1"
    by (simp add: probability_unity)
next
  show "\<P> \<bottom> = 0"
    by (metis
          add_cancel_left_right
          probability_additivity
          ex_falso_quodlibet
          probability_unity
          bivalence
          conjunction_right_elimination
          negation_def)
next
  fix \<phi> \<psi>
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  thus "\<P> \<phi> \<le> \<P> \<psi>"
    using monotonicity
    by auto
next
  fix \<phi> \<psi>
  show "\<P> \<phi> + \<P> \<psi> = \<P> (\<phi> \<sqinter> \<psi>) + \<P> (\<phi> \<squnion> \<psi>)"
    by (metis sum_rule add.commute)
qed

sublocale probability_logic \<subseteq> consistent_classical_logic
proof
  show "\<not> \<turnstile> \<bottom>" using probability_unity gaines_weatherson_antithesis by auto
qed

lemma (in probability_logic) subtraction_identity:
  "\<P> (\<phi> \<setminus> \<psi>) = \<P> \<phi> - \<P> (\<phi> \<sqinter> \<psi>)"
proof -
  have "\<turnstile> \<phi> \<leftrightarrow> ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.biconditional_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by (simp, blast)
    hence "\<turnstile> \<^bold>\<lparr> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<leftrightarrow> ((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<squnion> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  hence "\<P> \<phi>  = \<P> ((\<phi> \<setminus> \<psi>) \<squnion> (\<phi> \<sqinter> \<psi>))"
    using biconditional_equivalence
    by simp
  moreover have "\<turnstile> \<sim>((\<phi> \<setminus> \<psi>) \<sqinter> (\<phi> \<sqinter> \<psi>))"
  proof -
    have "\<forall> \<MM>. \<MM> \<Turnstile>\<^sub>p\<^sub>r\<^sub>o\<^sub>p \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>))"
      unfolding
        classical_logic_class.subtraction_def
        classical_logic_class.negation_def
        classical_logic_class.conjunction_def
        classical_logic_class.disjunction_def
      by simp
    hence "\<turnstile> \<^bold>\<lparr> \<sim>((\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<setminus> \<^bold>\<langle>\<psi>\<^bold>\<rangle>) \<sqinter> (\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<sqinter> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)) \<^bold>\<rparr>"
      using propositional_semantics by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    using probability_additivity
    by auto
qed

section \<open> Basic Probability Logic Inequality Results \label{sec:basic-probability-inequality-results}\<close>

lemma (in probability_logic) disjunction_sum_inequality:
  "\<P> (\<phi> \<squnion> \<psi>) \<le> \<P> \<phi> + \<P> \<psi>"
proof -
  have "\<P> (\<phi> \<squnion> \<psi>) + \<P> (\<phi> \<sqinter> \<psi>) = \<P> \<phi> + \<P> \<psi>"
       "0 \<le> \<P> (\<phi> \<sqinter> \<psi>)"
    by (simp add: sum_rule, simp add: probability_non_negative)
  thus ?thesis by linarith
qed

lemma (in probability_logic)
  arbitrary_disjunction_list_summation_inequality:
  "\<P> (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)"
proof (induct \<Phi>)
  case Nil
  then show ?case by (simp add: gaines_weatherson_antithesis)
next
  case (Cons \<phi> \<Phi>)
  have "\<P> (\<Squnion> (\<phi> # \<Phi>)) \<le> \<P> \<phi> + \<P> (\<Squnion> \<Phi>)"
    using disjunction_sum_inequality
    by simp
  with Cons have "\<P> (\<Squnion> (\<phi> # \<Phi>)) \<le> \<P> \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)" by linarith
  then show ?case by simp
qed

lemma (in probability_logic) implication_list_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "\<P> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<P> \<psi>)"
  using
    assms
    arbitrary_disjunction_list_summation_inequality
    monotonicity
    order_trans
  by blast

lemma (in probability_logic) arbitrary_disjunction_set_summation_inequality:
  "\<P> (\<Squnion> \<Phi>) \<le> (\<Sum>\<phi> \<in> set \<Phi>. \<P> \<phi>)"
  by (metis
        arbitrary_disjunction_list_summation_inequality
        arbitrary_disjunction_remdups
        biconditional_equivalence
        sum.set_conv_list)

lemma (in probability_logic) implication_set_summation_inequality:
  assumes "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  shows "\<P> \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. \<P> \<psi>)"
  using
    assms
    arbitrary_disjunction_set_summation_inequality
    monotonicity
    order_trans
  by blast

section \<open> Dirac Measures \label{sec:dirac-measures}\<close>

text \<open> Before presenting \<^emph>\<open>Dirac measures\<close> in probability logic, we first
       give the set of all functions satisfying probability logic.\<close>

definition (in classical_logic) probabilities :: "('a \<Rightarrow> real) set"
  where "probabilities =
         {\<P>. class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> \<P> }"

text \<open> Traditionally, a Dirac measure is a function \<^term>\<open>\<delta>\<^sub>x\<close> where
       \<^term>\<open>\<delta>\<^sub>x(S) = (1::real)\<close> if \<^term>\<open>x \<in> S\<close> and \<^term>\<open>\<delta>\<^sub>x(S) = (0::real)\<close>
       otherwise.  This means that Dirac measures correspond to special
       ultrafilters on their underlying \<^term>\<open>\<sigma>\<close>-algebra which are
       closed under countable unions. \<close>

text \<open> Probability logic, as discussed in \S\ref{section:why-finite-additivity},
       may not have countable joins in its underlying logic. In the setting
       of probability logic, Dirac measures are simple probability functions
       that are either 0 or 1. \<close>

definition (in classical_logic) dirac_measures :: "('a \<Rightarrow> real) set"
  where "dirac_measures =
         { \<P>. class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> \<P>
               \<and> (\<forall>x. \<P> x = 0 \<or> \<P> x = 1) }"

lemma (in classical_logic) dirac_measures_subset:
  "dirac_measures \<subseteq> probabilities"
  unfolding
    probabilities_def
    dirac_measures_def
  by fastforce

text \<open> Maximally consistent sets correspond to Dirac measures. One direction
       of this correspondence is established below. \<close>

lemma (in classical_logic) MCS_dirac_measure:
  assumes "MCS \<Omega>"
    shows "(\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0) \<in> dirac_measures"
      (is "?\<P> \<in> dirac_measures")
proof -
  have "class.probability_logic (\<lambda> \<phi>. \<turnstile> \<phi>) (\<rightarrow>) \<bottom> ?\<P>"
  proof (standard, simp,
         meson
           assms
           formula_maximally_consistent_set_def_reflection
           maximally_consistent_set_def
           set_deduction_weaken)
    fix \<phi> \<psi>
    assume "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<bottom>"
    hence "\<phi> \<sqinter> \<psi> \<notin> \<Omega>"
      by (metis
            assms
            formula_consistent_def
            formula_maximally_consistent_set_def_def
            maximally_consistent_set_def
            conjunction_def
            set_deduction_modus_ponens
            set_deduction_reflection
            set_deduction_weaken)
    hence "\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>"
      using
        assms
        formula_maximally_consistent_set_def_reflection
        maximally_consistent_set_def
        conjunction_set_deduction_equivalence
      by meson
    have "\<phi> \<squnion> \<psi> \<in> \<Omega> = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)"
      by (metis
            \<open>\<phi> \<sqinter> \<psi> \<notin> \<Omega>\<close>
            assms
            formula_maximally_consistent_set_def_implication
            maximally_consistent_set_def
            conjunction_def
            disjunction_def)
    have "?\<P> (\<phi> \<squnion> \<psi>) = ?\<P> \<phi> + ?\<P> \<psi>"
    proof (cases "\<phi> \<squnion> \<psi> \<in> \<Omega>")
      case True
      hence \<diamondsuit>: "1 = ?\<P> (\<phi> \<squnion> \<psi>)" by simp
      show ?thesis
      proof (cases "\<phi> \<in> \<Omega>")
        case True
        hence "\<psi> \<notin> \<Omega>"
          using \<open>\<phi> \<notin> \<Omega> \<or> \<psi> \<notin> \<Omega>\<close>
          by blast
        have "?\<P> (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
        also have "... = 1 + (0::real)" by linarith
        also have "... = ?\<P> \<phi> + ?\<P> \<psi>"
          using \<open>\<psi> \<notin> \<Omega>\<close> \<open>\<phi> \<in> \<Omega>\<close> by simp
        finally show ?thesis .
      next
        case False
        hence "\<psi> \<in> \<Omega>"
          using \<open>\<phi> \<squnion> \<psi> \<in> \<Omega>\<close> \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close>
          by blast
        have "?\<P> (\<phi> \<squnion> \<psi>) = (1::real)" using \<diamondsuit> by simp
        also have "... = (0::real) + 1" by linarith
        also have "... = ?\<P> \<phi> + ?\<P> \<psi>"
          using \<open>\<psi> \<in> \<Omega>\<close> \<open>\<phi> \<notin> \<Omega>\<close> by simp
        finally show ?thesis .
      qed
    next
      case False
      moreover from this have "\<phi> \<notin> \<Omega>" "\<psi> \<notin> \<Omega>"
        using \<open>(\<phi> \<squnion> \<psi> \<in> \<Omega>) = (\<phi> \<in> \<Omega> \<or> \<psi> \<in> \<Omega>)\<close> by blast+
      ultimately show ?thesis by simp
    qed
    thus "?\<P> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi>) = ?\<P> \<phi> + ?\<P> \<psi>"
      unfolding disjunction_def .
  qed
  thus ?thesis
    unfolding dirac_measures_def
    by simp
qed

notation FuncSet.funcset (infixr "\<rightarrow>" 60)

end
