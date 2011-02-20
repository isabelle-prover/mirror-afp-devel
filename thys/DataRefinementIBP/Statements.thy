header {*Program Statements as Predicate Transformers*}

theory Statements
imports Preliminaries
begin

text {*
  Program statements are modeled as predicate transformers, functions from predicates to predicates.
  If $\mathit{State}$ is the type of program states, then a program $S$ is a a function from 
  $\mathit{State}\ \mathit{set}$ to
  $\mathit{State}\ \mathit{set}$. If $q \in \mathit{State}\ \mathit{set}$, then the elements of 
  $S\ q$ are the initial states from which
  $S$ is guarantied to terminate in a state from $q$.

  However, most of the time we will work with an arbitrary compleate lattice, or an arbitrary boolean algebra
  instead of the complete boolean algebra of predicate transformers. 

  We will introduce in this section assert, assume, demonic choice, angelic choice, demonic update, and 
  angelic update statements. We will prove also that these statements are monotonic.
*}



lemma mono_top[simp]: "mono top"
  by (simp add: mono_def top_fun_def)



lemma mono_choice[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S \<sqinter> T)"
  apply (simp add: mono_def inf_fun_def)
  apply safe
  apply (rule_tac y = "S x" in order_trans)
  apply simp_all
  apply (rule_tac y = "T x" in order_trans)
  by simp_all

subsection "Assert statement"

text {*
The assert statement of a predicate $p$ when executed from a state $s$ fails
if $s\not\in p$ and behaves as skip otherwise.
*}

definition
  "assert p q = p \<sqinter> q"

subsection "Assume statement"

text {*
The assume statement of a predicate $p$ when executed from a state $s$ is not enabled
if $s\not\in p$ and behaves as skip otherwise.
*}

definition
  "assume (P::'a::boolean_algebra) Q = -P \<squnion> Q"

lemma mono_assume [simp]: "mono (assume P)"
  apply (simp add: assume_def mono_def)
  apply safe
  apply (rule_tac y = "y" in order_trans)
  by simp_all

subsection "Demonic update statement"

text {*
The demonic update statement of a relation $Q: \mathit{State} \to \mathit{Sate} \to bool$,
when executed in a state $s$ computes nondeterministically a new state $s'$ such 
$Q\ s \ s'$ is true. In order for this statement to be correct all
possible choices of $s'$ should be correct. If there is no state $s'$
such that $Q\ s \ s'$, then the demonic update of $Q$ is not enabled
in $s$.
*}

definition
  "demonic Q p = {s . Q s \<le> p}"

lemma mono_demonic [simp]: "mono (demonic Q)"
  apply (simp add: mono_def demonic_def le_bool_def)
  by auto

theorem demonic_bottom:
  "demonic R (\<bottom>::('a::{order, bot})) = {s . (R s) = \<bottom>}"
  apply (unfold demonic_def)
  apply auto
  apply (rule antisym)
  by auto

theorem demonic_bottom_top [simp]:
  "demonic \<bottom>  = \<top>"
  by (simp add: fun_eq_iff inf_fun_def sup_fun_def demonic_def simp_set_function inf_bool_def top_fun_def bot_fun_def)

theorem demonic_sup_inf:
  "demonic (Q \<squnion> Q') = demonic Q \<sqinter> demonic Q'"
  by (simp add: fun_eq_iff inf_fun_def sup_fun_def demonic_def simp_set_function inf_bool_def)



subsection "Angelic update statement"

text {*
The angelic update statement of a relation $Q: \mathit{State} \to \mathit{State} \to \mathit{bool}$ is similar
to the demonic version, except that it is enough that at least for one choice $s'$, $Q \ s \ s'$
is correct. If there is no state $s'$
such that $Q\ s \ s'$, then the angelic update of $Q$ fails in $s$.
*}

definition
  "angelic Q p = {s . (Q s) \<sqinter> p \<noteq> \<bottom>}"

lemma mono_angelic[simp]:
  "mono (angelic R)" 
  apply (unfold mono_def)
  apply (unfold angelic_def)
  apply auto
  apply (erule notE)
  apply (rule antisym)
  apply auto
  apply (case_tac "R xa \<sqinter> x \<le> R xa \<sqinter> y")
  apply simp
  apply (erule notE)
  apply (rule_tac inf_greatest)
  apply auto
  apply (rule_tac y = x in order_trans)
  by auto

theorem angelic_bottom [simp]:
  "angelic R \<bottom>  = {}"
  by (simp add: angelic_def)

theorem angelic_disjunctive:
  "angelic R ((p::'a::boolean_algebra) \<squnion> q) = angelic R p \<squnion> angelic R q"
by (simp add: fun_eq_iff inf_fun_def sup_fun_def angelic_def simp_set_function inf_bool_def sup_bool_def inf_sup_distrib1)

theorem angelic_udisjunctive1:
  "angelic R ((Sup P)::'a::distributive_complete_lattice) = (SUP p:P . (angelic R p))"
  apply (simp add: angelic_def)
  apply (unfold SUPR_def)
  apply (simp add: inf_sup_distributivity)
  apply (unfold SUPR_def)
  apply auto
  apply (unfold Sup_bottom)
  by auto

theorem angelic_udisjunctive:
  "angelic R ((SUP P)::'a::distributive_complete_lattice) = SUP (\<lambda> w . angelic R (P w))"
  apply (simp add: angelic_def)
  apply (unfold SUPR_def)
  apply (simp add: inf_sup_distributivity)
  apply (unfold SUPR_def)
  apply auto
  apply (unfold Sup_bottom)
  by auto


subsection "The guard of a statement"

text {*
The guard of a statement $S$ is the set of iniatial states from which $S$
is enabled or fails.
*}

definition
  "((grd S)::'a::boolean_algebra) = - (S bot)"

lemma grd_choice[simp]: "grd (S \<sqinter> T) = (grd S) \<squnion> (grd T)"
  by (simp add: grd_def compl_inf inf_fun_def)

lemma grd_demonic: "grd (demonic Q) = {s . \<exists> s' . s' \<in> (Q s) }" 
  apply (simp add: grd_def demonic_def)
  by blast

lemma grd_demonic_2[simp]: "(s \<notin> grd (demonic Q)) = (\<forall> s' . s' \<notin>  (Q s))" 
  by (simp add: grd_demonic)


theorem grd_angelic:
  "grd (angelic R) = UNIV"
  by (simp add: grd_def)


end