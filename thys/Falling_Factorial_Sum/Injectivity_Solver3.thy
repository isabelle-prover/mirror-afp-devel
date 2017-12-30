(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Combinatorial Basics\<close>

theory Injectivity_Solver3
imports
  "Card_Equiv_Relations.Card_Partial_Equiv_Relations"
begin

subsection \<open>Third Version of Injectivity Solver\<close>

text \<open>
Here, we provide a third version of the injectivity solver. The original first version was provided
in the AFP entry `Spivey's Generalized Recurrence for Bell Numbers`. From that method, I derived a
second version in the AFP entry `Cardinality of Equivalence Relations`. At roughly the same time,
Makarius improved the injectivity solver in the development version of the first AFP entry. This
third version now includes the improvements of the second version and Makarius improvements
to the first, and it further extends the method to handle the new cases in the cardinality proof
of this AFP entry.

As the implementation of the injectivity solver only evolves in the development branch of the AFP,
the submissions of the three AFP entries that employ the injectivity solver, have to create clones
of the injectivity solver for the identified and needed method adjustments. Ultimately, these three
clones should only remain in the stable branches of the AFP from Isabelle2016 to Isabelle2017
to work with their corresponding release versions.
In the development versions, I will move the consolidated version of the injectivity solver in
the @{theory Disjoint_Sets} and it will hopefully only evolve further there.
\<close>

lemmas injectivity_solver_prep_assms_Collect = injectivity_solver_prep_assms

lemma injectivity_solver_prep_assms: "x \<in> A \<Longrightarrow> x \<in> A \<and> x \<in> A"
  by simp

lemmas disjoint_terminal_singleton = disjoint_singleton

lemmas disjoint_terminal_Collect = disjoint_terminal

lemma disjoint_terminal:
  "s \<noteq> t \<Longrightarrow> (\<And>x x'. x \<in> S \<and> x' \<in> T \<Longrightarrow> x = x' \<Longrightarrow> s = t) \<Longrightarrow> S \<inter> T = {}"
by blast

lemma elim_singleton:
  assumes "x \<in> {s} \<and> x' \<in> {t}"
  obtains "x = s \<and> x' = t"
using assms by blast

method injectivity_solver uses rule =
  insert method_facts,
  use nothing in \<open>
    ((drule injectivity_solver_prep_assms_Collect | drule injectivity_solver_prep_assms)+)?;
    rule disjoint_family_onI;
    ((rule disjoint_bind | rule disjoint_bind')+)?;
    (erule elim_singleton)?;
    (erule disjoint_terminal_singleton | erule disjoint_terminal_Collect | erule disjoint_terminal);
    (elim injectivity_solver_CollectE)?;
    rule rule;
    assumption+
  \<close>

end