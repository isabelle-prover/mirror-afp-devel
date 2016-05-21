theory PLTL
  imports Main "../LTL/LTL" Samplers StutterEquivalence
begin

section {* Stuttering Invariant PLTL Formulas *}

text {*
  We define the syntax and semantics of propositional linear-time
  temporal logic PLTL and show that its next-free fragment is
  invariant to finite stuttering.
*}

notation False_ltlp ("false")
  and Implies_ltlp ("implies")
  and Atom_ltlp ("atom")
  and Until_ltlp ("until")
  and Next_ltlp ("next")
  and atoms_pltl ("atoms")

subsection {* Finite Conjunctions and Disjunctions *}

(* It would be tempting to define these operators as follows:

definition OR where "OR \<Phi> = Finite_Set.fold or false \<Phi>"
definition AND where "AND \<Phi> = Finite_Set.fold and true \<Phi>"

However, this would only work if "or" and "and" were left-commutative,
which they are not (syntactically). We must therefore resort to
the more general fold_graph predicate, effectively picking a
conjunction (or disjunction) in arbitrary order. 

An alternative would be to define these generalized operators
over lists of formulas, but working with sets is more natural
in the following.
*)

definition OR where "OR \<Phi> \<equiv> SOME \<phi>. fold_graph Or_ltlp False_ltlp \<Phi> \<phi>"

definition AND where "AND \<Phi> \<equiv> SOME \<phi>. fold_graph And_ltlp True_ltlp \<Phi> \<phi>"

lemma fold_graph_OR: "finite \<Phi> \<Longrightarrow> fold_graph Or_ltlp False_ltlp \<Phi> (OR \<Phi>)"
  unfolding OR_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma fold_graph_AND: "finite \<Phi> \<Longrightarrow> fold_graph And_ltlp True_ltlp \<Phi> (AND \<Phi>)"
  unfolding AND_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma holds_of_OR [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "(\<sigma> \<Turnstile>\<^sub>p OR \<Phi>) = (\<exists>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<exists>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma holds_of_AND [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "(\<sigma> \<Turnstile>\<^sub>p AND \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<forall>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed

subsection {* Next-Free PLTL Formulas *}

text {*
  A PLTL formula is called \emph{next-free} if it does not contain any
  subformula.
*}

fun next_free :: "'a pltl \<Rightarrow> bool"
where
  "next_free false\<^sub>p = True"
| "next_free (atom\<^sub>p p) = True"
| "next_free (\<phi> implies\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
| "next_free (X\<^sub>p \<phi>) = False"
| "next_free (\<phi> U\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"

lemma next_free_not [simp]: 
  "next_free (not\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Not_ltlp_def)

lemma next_free_true [simp]: 
  "next_free true\<^sub>p"
  by (simp add: True_ltlp_def)

lemma next_free_or [simp]: 
  "next_free (\<phi> or\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (simp add: Or_ltlp_def)

lemma next_free_and [simp]: "next_free (\<phi> and\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (simp add: And_ltlp_def)

lemma next_free_eventually [simp]: 
  "next_free (F\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Eventually_ltlp_def)

lemma next_free_always [simp]: 
  "next_free (G\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Always_ltlp_def)

lemma next_free_OR [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "next_free (OR \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "next_free \<psi> = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma next_free_AND [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "next_free (AND \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "next_free \<psi> = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed


subsection {* Stuttering Invariance of PLTL Without ``Next'' *}

text {*
  A PLTL formula is \emph{stuttering invariant} if for any stuttering equivalent
  state sequences @{text "\<sigma> \<approx> \<tau>"}, the formula holds of @{text "\<sigma>"} iff it
  holds of @{text "\<tau>"}.
*}

definition stutter_invariant where
  "stutter_invariant \<phi> = (\<forall>\<sigma> \<tau>. (\<sigma> \<approx> \<tau>) \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>))"

text {*
  Since stuttering equivalence is symmetric, it is enough to show an
  implication in the above definition instead of an equivalence.
*}

lemma stutter_invariantI [intro!]:
  assumes "\<And>\<sigma> \<tau>. \<lbrakk>\<sigma> \<approx> \<tau>; \<sigma> \<Turnstile>\<^sub>p \<phi>\<rbrakk> \<Longrightarrow> \<tau> \<Turnstile>\<^sub>p \<phi>"
  shows "stutter_invariant \<phi>"
proof -
  {
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and f: "\<sigma> \<Turnstile>\<^sub>p \<phi>"
    hence "\<tau> \<Turnstile>\<^sub>p \<phi>" by (rule assms)
  }
moreover
  {
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and f: "\<tau> \<Turnstile>\<^sub>p \<phi>"
    from st have "\<tau> \<approx> \<sigma>" by (rule stutter_equiv_sym)
    from this f have "\<sigma> \<Turnstile>\<^sub>p \<phi>" by (rule assms)
  }
ultimately show ?thesis by (auto simp: stutter_invariant_def)
qed

lemma stutter_invariantD [dest]:
  assumes "stutter_invariant \<phi>" and "\<sigma> \<approx> \<tau>"
  shows "(\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)"
  using assms by (auto simp: stutter_invariant_def)

text {*
  We first show that next-free PLTL formulas are indeed stuttering invariant.
  The proof proceeds by straightforward induction on the syntax of PLTL formulas.
*}
theorem next_free_stutter_invariant:
  "next_free \<phi> \<Longrightarrow> stutter_invariant (\<phi>::'a pltl)"
proof (induct "\<phi>")
    show "stutter_invariant false" by auto
next
  fix p :: "'a \<Rightarrow> bool"
  show "stutter_invariant (atom p)"
  proof
    fix \<sigma> \<tau>
    assume "\<sigma> \<approx> \<tau>" "\<sigma> \<Turnstile>\<^sub>p atom p"
    thus "\<tau> \<Turnstile>\<^sub>p atom p" by (simp add: stutter_equiv_0)
  qed
next
  fix \<phi> \<psi> :: "'a pltl"
  assume ih: "next_free \<phi> \<Longrightarrow> stutter_invariant \<phi>"
             "next_free \<psi> \<Longrightarrow> stutter_invariant \<psi>"
  assume "next_free (implies \<phi> \<psi>)"
  with ih show "stutter_invariant (implies \<phi> \<psi>)" by auto
next
  fix \<phi> :: "'a pltl"
  assume "next_free (next \<phi>)"  -- {* hence contradiction *}
  thus "stutter_invariant (next \<phi>)" by simp
next
  fix \<phi> \<psi> :: "'a pltl"
  assume ih: "next_free \<phi> \<Longrightarrow> stutter_invariant \<phi>"
             "next_free \<psi> \<Longrightarrow> stutter_invariant \<psi>"
  assume "next_free (until \<phi> \<psi>)"
  with ih have stinv: "stutter_invariant \<phi>" "stutter_invariant \<psi>" by auto
  show "stutter_invariant (until \<phi> \<psi>)"
  proof
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and unt: "\<sigma> \<Turnstile>\<^sub>p until \<phi> \<psi>"
    from unt obtain m
      where 1: "\<sigma>[m..] \<Turnstile>\<^sub>p \<psi>" and 2: "\<forall>j<m. \<sigma>[j..] \<Turnstile>\<^sub>p \<phi>" by auto
    from st obtain n
      where 3: "\<sigma>[m..] \<approx> \<tau>[n..]" and 4: "\<forall>i<n. \<exists>j<m. \<sigma>[j..] \<approx> \<tau>[i..]"
      by (rule stutter_equiv_suffixes_right)
    from 1 3 stinv have "\<tau>[n..] \<Turnstile>\<^sub>p \<psi>" by auto
    moreover
    from 2 4 stinv have "\<forall>i<n. \<tau>[i..] \<Turnstile>\<^sub>p \<phi>" by force
    ultimately show "\<tau> \<Turnstile>\<^sub>p until \<phi> \<psi>" by auto
  qed
qed


subsection {* Atoms, Canonical State Sequences, and Characteristic Formulas *}

text {*
  We now address the converse implication: any stutter invariant PLTL
  formula @{text "\<phi>"} can be equivalently expressed by a next-free formula.
  The construction of that formula requires attention to the atomic
  formulas that appear in @{text "\<phi>"}. We will also prove that the
  next-free formula does not need any new atoms beyond those present
  in @{text "\<phi>"}.

  The following function collects the atoms (of type @{text "'a \<Rightarrow> bool"})
  of a PLTL formula.
*}


lemma atoms_OR [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "atoms (OR \<Phi>) = (\<Union>\<phi>\<in>\<Phi>. atoms \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "atoms \<psi> = (\<Union>\<phi>\<in>\<Phi>. atoms \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma atoms_AND [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "atoms (AND \<Phi>) = (\<Union>\<phi>\<in>\<Phi>. atoms \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "atoms \<psi> = (\<Union>\<phi>\<in>\<Phi>. atoms \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed

text {*
  Given a set of atoms @{text A} as above, we say that two states
  are @{text A}-similar if they agree on all atoms in @{text A}.
  Two state sequences @{text "\<sigma>"} and @{text "\<tau>"} are @{text A}-similar
  if corresponding states are @{text A}-equal.
*}

definition state_sim :: "['a, ('a \<Rightarrow> bool) set, 'a] \<Rightarrow> bool" 
  ("_ ~_~ _" [70,100,70] 50) where
  "s ~A~ t = (\<forall>p\<in>A. p s \<longleftrightarrow> p t)"

definition seq_sim :: "[nat \<Rightarrow> 'a, ('a \<Rightarrow> bool) set, nat \<Rightarrow> 'a] \<Rightarrow> bool"
  ("_ \<simeq>_\<simeq> _" [70,100,70] 50)  where
  "\<sigma> \<simeq>A\<simeq> \<tau> = (\<forall>n. (\<sigma> n) ~A~ (\<tau> n))"

text {*
  These relations are (indexed) equivalence relations. Moreover
  @{text "s ~A~ t"} implies @{text "s ~B~ t"} for @{text "B \<subseteq> A"},
  and similar for @{text "\<sigma> \<simeq>A\<simeq> \<tau>"} and @{text "\<sigma> \<simeq>B\<simeq> \<tau>"}.
*}

lemma state_sim_refl [simp]: "s ~A~ s"
  by (simp add: state_sim_def)

lemma state_sim_sym: "s ~A~ t \<Longrightarrow> t ~A~ s"
  by (auto simp: state_sim_def)

lemma state_sim_trans[trans]: "s ~A~ t \<Longrightarrow> t ~A~ u \<Longrightarrow> s ~A~ u"
  unfolding state_sim_def by blast

lemma state_sim_mono:
  assumes "s ~A~ t" and "B \<subseteq> A"
  shows "s ~B~ t"
  using assms unfolding state_sim_def by auto

lemma seq_sim_refl [simp]: "\<sigma> \<simeq>A\<simeq> \<sigma>"
  by (simp add: seq_sim_def)

lemma seq_sim_sym: "\<sigma> \<simeq>A\<simeq> \<tau> \<Longrightarrow> \<tau> \<simeq>A\<simeq> \<sigma>"
  by (auto simp: seq_sim_def state_sim_sym)

lemma seq_sim_trans[trans]: "\<rho> \<simeq>A\<simeq> \<sigma> \<Longrightarrow> \<sigma> \<simeq>A\<simeq> \<tau> \<Longrightarrow> \<rho> \<simeq>A\<simeq> \<tau>"
  unfolding seq_sim_def by (blast intro: state_sim_trans)

lemma seq_sim_mono:
  assumes "\<sigma> \<simeq>A\<simeq> \<tau>" and "B \<subseteq> A"
  shows "\<sigma> \<simeq>B\<simeq> \<tau>"
  using assms unfolding seq_sim_def by (blast intro: state_sim_mono)

text {*
  State sequences that are similar w.r.t. the atoms of a PLTL formula
  evaluate that formula to the same value.  
*}

lemma pltl_seq_sim: "\<sigma> \<simeq>(atoms \<phi>)\<simeq> \<tau> \<Longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)"
  (is "?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>")
proof (induct \<phi> arbitrary: \<sigma> \<tau>)
  fix \<sigma> \<tau>
  show "?P \<sigma> false \<tau>" by simp
next
  fix p \<sigma> \<tau>
  assume "?sim \<sigma> (atom p) \<tau>" thus "?P \<sigma> (atom p) \<tau>"
    by (auto simp: seq_sim_def state_sim_def)
next
  fix \<phi> \<psi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>" 
             "\<And>\<sigma> \<tau>. ?sim \<sigma> \<psi> \<tau> \<Longrightarrow> ?P \<sigma> \<psi> \<tau>"
     and sim: "?sim \<sigma> (implies \<phi> \<psi>) \<tau>"
  from sim have "?sim \<sigma> \<phi> \<tau>" "?sim \<sigma> \<psi> \<tau>"
    by (auto elim: seq_sim_mono)
  with ih show "?P \<sigma> (implies \<phi> \<psi>) \<tau>" by simp
next
  fix \<phi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>"
     and sim: "\<sigma> \<simeq>atoms (next \<phi>)\<simeq> \<tau>"
  from sim have "\<sigma>[1..] \<simeq>atoms \<phi>\<simeq> \<tau>[1..]"
    by (auto simp: seq_sim_def)
  with ih show "?P \<sigma> (next \<phi>) \<tau>" by auto
next
  fix \<phi> \<psi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>" 
             "\<And>\<sigma> \<tau>. ?sim \<sigma> \<psi> \<tau> \<Longrightarrow> ?P \<sigma> \<psi> \<tau>"
     and sim: "?sim \<sigma> (until \<phi> \<psi>) \<tau>"
  from sim have "\<forall>i. \<sigma>[i..] \<simeq>atoms \<phi>\<simeq> \<tau>[i..]" "\<forall>j. \<sigma>[j..] \<simeq> atoms \<psi> \<simeq> \<tau>[j..]"
    by (auto simp: seq_sim_def state_sim_def)
  with ih have "\<forall>i. ?P (\<sigma>[i..]) \<phi> (\<tau>[i..])" "\<forall>j. ?P (\<sigma>[j..]) \<psi> (\<tau>[j..])"
    by blast+
  thus "?P \<sigma> (until \<phi> \<psi>) \<tau>" 
    by (meson semantics_pltl.simps(5))
qed

text {*
  The following function picks an arbitrary representative among
  @{text A}-similar states. Because the choice is functional,
  any two @{text A}-similar states are mapped to the same state.
*}

definition canonize where
  "canonize A s \<equiv> SOME t. t ~A~ s"

lemma canonize_state_sim: "canonize A s ~A~ s"
  unfolding canonize_def by (rule someI, rule state_sim_refl)

lemma canonize_canonical:
  assumes st: "s ~A~ t"
  shows "canonize A s = canonize A t"
proof -
  from st have "\<forall>u. (u ~A~s) = (u ~A~ t)"
    by (auto elim: state_sim_sym state_sim_trans)
  thus ?thesis unfolding canonize_def by simp
qed

lemma canonize_idempotent:
  "canonize A (canonize A s) = canonize A s"
  by (rule canonize_canonical[OF canonize_state_sim])

text {*
  In a canonical state sequence, any two @{text A}-similar states
  are in fact equal.
*}

definition canonical_sequence where
  "canonical_sequence A \<sigma> \<equiv> \<forall>m (n::nat). \<sigma> m ~A~ \<sigma> n \<longrightarrow> \<sigma> m = \<sigma> n"

text {*
  Every suffix of a canonical sequence is canonical, as is any
  (sampled) subsequence, in particular any stutter-sampling.
*}

lemma canonical_suffix:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<sigma>[k..])"
  by (auto simp: canonical_sequence_def)

lemma canonical_sampled:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<sigma> \<circ> f)"
  by (auto simp: canonical_sequence_def)

lemma canonical_reduced:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<natural>\<sigma>)"
  unfolding stutter_reduced_def by (rule canonical_sampled)

text {*
  For any sequence @{text "\<sigma>"} there exists a canonical
  @{text A}-similar sequence @{text "\<tau>"}. Such a @{text "\<tau>"}
  can be obtained by canonizing all states of @{text "\<sigma>"}.
*}

lemma canonical_exists:
  obtains \<tau> where "\<tau> \<simeq>A\<simeq> \<sigma>" "canonical_sequence A \<tau>"
proof -
  have "(canonize A \<circ> \<sigma>) \<simeq>A\<simeq> \<sigma>"
    by (simp add: seq_sim_def canonize_state_sim)
  moreover
  have "canonical_sequence A (canonize A \<circ> \<sigma>)"
    by (auto simp: canonical_sequence_def canonize_idempotent
             dest: canonize_canonical)
  ultimately
  show ?thesis using that by blast
qed

text {*
  Given a state @{text s} and a set @{text A} of atoms, we define
  the characteristic formula of @{text s} as the conjunction of
  all atoms in @{text A} that hold of @{text s} and the negation of
  the atoms in @{text A} that do not hold of @{text s}.
*}

definition characteristic_formula where
  "characteristic_formula A s \<equiv>
   ((AND { atom p | p . p \<in> A \<and> p s }) and\<^sub>p (AND { not\<^sub>p (atom p) | p . p \<in> A \<and> \<not>(p s) }))"

lemma characteristic_holds: 
  "finite A \<Longrightarrow> \<sigma> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
  by (auto simp: characteristic_formula_def)

lemma characteristic_state_sim:
  assumes fin: "finite A"
  shows "(\<sigma> 0 ~A~ \<tau> 0) = (\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> (0::nat)))"
proof
  assume sim: "\<sigma> 0 ~A~ \<tau> 0"
  {
    fix p
    assume "p \<in> A"
    with sim have "p (\<tau> 0) = p (\<sigma> 0)" by (auto simp: state_sim_def)
  }
  with fin show "\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
    by (auto simp: characteristic_formula_def) (blast+)
next
  assume "\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
  with fin show "\<sigma> 0 ~A~ \<tau> 0"
    by (auto simp: characteristic_formula_def state_sim_def)
qed


subsection {* Stuttering Invariant PLTL Formulas Don't Need Next *}

text {*
  The following is the main lemma used in the proof of the
  completeness theorem: for any PLTL formula @{text "\<phi>"} there
  exists a next-free formula @{text "\<psi>"} such that the two
  formulas evaluate to the same value over stutter-free and
  canonical sequences (w.r.t. some @{text "A \<supseteq> atoms \<phi>"}).
*}

lemma ex_next_free_stutter_free_canonical:
  assumes A: "atoms \<phi> \<subseteq> A" and fin: "finite A"
  shows "\<exists>\<psi>. next_free \<psi> \<and> atoms \<psi> \<subseteq> A \<and>
             (\<forall>\<sigma>. stutter_free \<sigma> \<and> canonical_sequence A \<sigma> \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>))"
    (is "\<exists>\<psi>. ?P \<phi> \<psi>")
using A proof (induct \<phi>)
  txt {* The cases of @{text "false"} and atomic formulas are trivial. *}
  have "?P false false" by auto
  thus "\<exists>\<psi>. ?P false \<psi>" ..
next
  fix p
  assume "atoms (atom p) \<subseteq> A"
  hence "?P (atom p) (atom p)" by auto
  thus "\<exists>\<psi>. ?P (atom p) \<psi>" ..
next
  txt {* Implication is easy, using the induction hypothesis. *}
  fix \<phi> \<psi>
  assume "atoms \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<phi>'. ?P \<phi> \<phi>'"
     and "atoms \<psi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>'. ?P \<psi> \<psi>'"
     and "atoms (implies \<phi> \<psi>) \<subseteq> A"
  then obtain \<phi>' \<psi>' where "?P \<phi> \<phi>'" "?P \<psi> \<psi>'" by auto
  hence "?P (implies \<phi> \<psi>) (implies \<phi>' \<psi>')" by auto
  thus "\<exists>\<chi>. ?P (implies \<phi> \<psi>) \<chi>" ..
next
  txt {* The case of @{text "until"} follows similarly. *}
  fix \<phi> \<psi>
  assume "atoms \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<phi>'. ?P \<phi> \<phi>'"
     and "atoms \<psi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>'. ?P \<psi> \<psi>'"
     and "atoms (until \<phi> \<psi>) \<subseteq> A"
  then obtain \<phi>' \<psi>' where 1: "?P \<phi> \<phi>'" and 2: "?P \<psi> \<psi>'" by auto
  {
    fix \<sigma>
    assume sigma: "stutter_free \<sigma>" "canonical_sequence A \<sigma>"
    hence "\<And>k. stutter_free (\<sigma>[k..])" "\<And>k. canonical_sequence A (\<sigma>[k..])"
      by (auto simp: stutter_free_suffix canonical_suffix)
    with 1 2 
    have "\<And>k. (\<sigma>[k..] \<Turnstile>\<^sub>p \<phi>') = (\<sigma>[k..] \<Turnstile>\<^sub>p \<phi>)"
     and "\<And>k. (\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>') = (\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>)"
      by (blast+)
    hence "(\<sigma> \<Turnstile>\<^sub>p until \<phi>' \<psi>') = (\<sigma> \<Turnstile>\<^sub>p until \<phi> \<psi>)"
      by auto
  }
  with 1 2 have "?P (until \<phi> \<psi>) (until \<phi>' \<psi>')" by auto
  thus "\<exists>\<chi>. ?P (until \<phi> \<psi>) \<chi>" ..
next
  txt {* The interesting case is the one of the @{text "next"}-operator. *}
  fix \<phi>
  assume ih: "atoms \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>. ?P \<phi> \<psi>" and at: "atoms (next \<phi>) \<subseteq> A"
  then obtain \<psi> where psi: "?P \<phi> \<psi>" by auto
  txt {* A valuation (over @{text A}) is a set @{text "val \<subseteq> A"} of atoms. We
    define some auxiliary notions: the valuation corresponding to a state and
    the characteristic formula for a valuation. Finally, we define the formula
    @{text "psi'"} that we will prove to be equivalent to @{text "next \<phi>"} over
    the stutter-free and canonical sequence @{text "\<sigma>"}. *}
  def stval \<equiv> "\<lambda>s. { p \<in> A . p s }"
  def chi \<equiv> "\<lambda>val. ((AND {atom p | p . p \<in> val}) and\<^sub>p
                        (AND {not\<^sub>p (atom p) | p . p \<in> A - val}))"
  def psi' \<equiv> "(Or_ltlp (\<psi> and\<^sub>p (OR {G\<^sub>p (chi val) | val . val \<subseteq> A }))
                  (OR {(chi val) and\<^sub>p (until (chi val) ( \<psi> and\<^sub>p (chi val'))) | val val'.
                        val \<subseteq> A \<and> val' \<subseteq> A \<and> val' \<noteq> val }))"
        (is "(Or_ltlp ( _ and\<^sub>p (OR ?ALW)) (OR ?UNT))")

  have "\<And>s. {not\<^sub>p (atom p) | p . p \<in> A - stval s}
           = {not\<^sub>p (atom p) | p . p \<in> A \<and> \<not>(p s)}"
    by (auto simp: stval_def)
  hence chi1: "\<And>s. chi (stval s) = characteristic_formula A s"
    by (auto simp: chi_def stval_def characteristic_formula_def)
  {
    fix val \<tau>
    assume val: "val \<subseteq> A" and tau: "\<tau> \<Turnstile>\<^sub>p chi val"
    with fin have "val = stval (\<tau> 0)"
      by (auto simp: stval_def chi_def finite_subset)
  }
  note chi2 = this

  have "?UNT \<subseteq> (\<lambda>(val,val'). (chi val) and\<^sub>p (until (chi val) (\<psi> and\<^sub>p (chi val'))))
               ` (Pow A \<times> Pow A)"
    (is "_ \<subseteq> ?S")
    by auto
  with fin have fin_UNT: "finite ?UNT"
    by (auto simp: finite_subset)

  have nf: "next_free psi'"
  proof -
    from fin have "\<And>val. val \<subseteq> A \<Longrightarrow> next_free (chi val)"
      by (auto simp: chi_def finite_subset)
    with fin fin_UNT psi show ?thesis
      by (force simp: psi'_def finite_subset)
  qed

  have atoms: "atoms psi' \<subseteq> A"
  proof -
    from fin have at_chi: "\<And>val. val \<subseteq> A \<Longrightarrow> atoms (chi val) \<subseteq> A"
      by (auto simp: chi_def finite_subset)
    with fin psi have at_alw: "atoms (\<psi> and\<^sub>p (OR ?ALW)) \<subseteq> A"
      by auto blast?    (** FRAGILE: auto leaves trivial goal about subset **)
    from fin fin_UNT psi at_chi have "atoms (OR ?UNT) \<subseteq> A"
      by auto (blast+)? (** FRAGILE: even more left-over goals here **)
    with at_alw show ?thesis by (auto simp: psi'_def)
  qed

  {
    fix \<sigma>
    assume st: "stutter_free \<sigma>" and can: "canonical_sequence A \<sigma>"
    have "(\<sigma> \<Turnstile>\<^sub>p next \<phi>) = (\<sigma> \<Turnstile>\<^sub>p psi')"
    proof (cases "\<sigma> (Suc 0) = \<sigma> 0")
      case True
      txt {* In the case of a stuttering transition at the beginning, we must have
        infinite stuttering, and the first disjunct of @{text "psi'"} holds,
        whereas the second does not. *}
      {
        fix n
        have "\<sigma> n = \<sigma> 0"
        proof (cases n)
          case 0 thus ?thesis by simp
        next
          case Suc
          hence "n > 0" by simp
          with True st show ?thesis unfolding stutter_free_def by blast
        qed
      }
      note alleq = this
      have suffix: "\<And>n. \<sigma>[n..] = \<sigma>"
      proof (rule ext)
        fix n i
        have "(\<sigma>[n..]) i = \<sigma> 0" by (auto intro: alleq)
        moreover have "\<sigma> i = \<sigma> 0" by (rule alleq)
        ultimately show "(\<sigma>[n..]) i = \<sigma> i" by simp
      qed
      with st can psi have 1: "(\<sigma> \<Turnstile>\<^sub>p next \<phi>) = (\<sigma> \<Turnstile>\<^sub>p \<psi>)" by simp

      from fin have "\<sigma> \<Turnstile>\<^sub>p chi (stval (\<sigma> 0))" by (simp add: chi1 characteristic_holds)
      with suffix have "\<sigma> \<Turnstile>\<^sub>p G\<^sub>p (chi (stval (\<sigma> 0)))" (is "_ \<Turnstile>\<^sub>p ?alw") by simp
      moreover have "?alw \<in> ?ALW" by (auto simp: stval_def)
      ultimately have 2: "\<sigma> \<Turnstile>\<^sub>p OR ?ALW"
        using fin by (auto simp: finite_subset simp del: semantics_pltl_sugar)

      have 3: "\<not>(\<sigma> \<Turnstile>\<^sub>p OR ?UNT)"
      proof
        assume unt: "\<sigma> \<Turnstile>\<^sub>p OR ?UNT"
        with fin_UNT obtain val val' k where
          val: "val \<subseteq> A" "val' \<subseteq> A" "val' \<noteq> val" and
          now: "\<sigma> \<Turnstile>\<^sub>p chi val" and k: "\<sigma>[k..] \<Turnstile>\<^sub>p chi val'"
          by auto (blast+)?  (* FRAGILE: similar as above *)
        from `val \<subseteq> A` now have "val = stval (\<sigma> 0)" by (rule chi2)
        moreover
        from `val' \<subseteq> A` k suffix have "val' = stval (\<sigma> 0)" by (simp add: chi2)
        moreover note `val' \<noteq> val`
        ultimately show "False" by simp
      qed

      from 1 2 3 show ?thesis by (simp add: psi'_def)

    next
      case False
      txt {* Otherwise, @{text "\<sigma> \<Turnstile>\<^sub>p next \<phi>"} is equivalent to @{text "\<sigma>"} satisfying
        the second disjunct of @{text "psi'"}. We show both implications separately. *}
      let ?val = "stval (\<sigma> 0)"
      let ?val' = "stval (\<sigma> 1)"
      from False can have vals: "?val' \<noteq> ?val"
        by (auto simp: canonical_sequence_def state_sim_def stval_def)
        
      show ?thesis
      proof
        assume phi: "\<sigma> \<Turnstile>\<^sub>p next \<phi>"
        from fin have 1: "\<sigma> \<Turnstile>\<^sub>p chi ?val" by (simp add: chi1 characteristic_holds)

        from st can have "stutter_free (\<sigma>[1..])" "canonical_sequence A (\<sigma>[1..])"
          by (auto simp: stutter_free_suffix canonical_suffix)
        with phi psi have 2: "\<sigma>[1..] \<Turnstile>\<^sub>p \<psi>" by auto

        from fin have "\<sigma>[1..] \<Turnstile>\<^sub>p characteristic_formula A ((\<sigma>[1..]) 0)"
          by (rule characteristic_holds)
        hence 3: "\<sigma>[1..] \<Turnstile>\<^sub>p chi ?val'" by (simp add: chi1)

        from 1 2 3 have "\<sigma> \<Turnstile>\<^sub>p And_ltlp (chi ?val) (until (chi ?val) (And_ltlp \<psi> (chi ?val')))"
          (is "_ \<Turnstile>\<^sub>p ?unt")
          by auto
        moreover from vals have "?unt \<in> ?UNT"
          by (auto simp: stval_def)
        ultimately have "\<sigma> \<Turnstile>\<^sub>p OR ?UNT"
          using fin_UNT[THEN holds_of_OR] by blast
        thus "\<sigma> \<Turnstile>\<^sub>p psi'" by (simp add: psi'_def)

      next
        assume psi': "\<sigma> \<Turnstile>\<^sub>p psi'"
        have "\<not>(\<sigma> \<Turnstile>\<^sub>p OR ?ALW)"
        proof
          assume "\<sigma> \<Turnstile>\<^sub>p OR ?ALW"
          with fin obtain val where 1: "val \<subseteq> A" and 2: "\<forall>n. \<sigma>[n..] \<Turnstile>\<^sub>p chi val"
            by (force simp: finite_subset)
          from 2 have "\<sigma>[0..] \<Turnstile>\<^sub>p chi val" ..
          with 1 have "val = ?val" by (simp add: chi2)
          moreover
          from 2 have "\<sigma>[1..] \<Turnstile>\<^sub>p chi val" ..
          with 1 have "val = ?val'" by (force dest: chi2)
          ultimately
          show "False" using vals by simp
        qed
        with psi' have "\<sigma> \<Turnstile>\<^sub>p OR ?UNT" by (simp add: psi'_def)
        with fin_UNT obtain val val' k where
          val: "val \<subseteq> A" "val' \<subseteq> A" "val' \<noteq> val" and
          now: "\<sigma> \<Turnstile>\<^sub>p chi val" and
          k: "\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>" "\<sigma>[k..] \<Turnstile>\<^sub>p chi val'" and
          i: "\<forall>i<k. \<sigma>[i..] \<Turnstile>\<^sub>p chi val"
          by auto (blast+)?  (* FRAGILE: similar as above *)

        from val now have 1: "val = ?val" by (simp add: chi2)

        have 2: "k \<noteq> 0"
        proof
          assume "k=0"
          with val k have "val' = ?val" by (simp add: chi2)
          with 1 `val' \<noteq> val` show "False" by simp
        qed

        have 3: "k \<le> 1"
        proof (rule ccontr)
          assume "\<not>(k \<le> 1)"
          with i have "\<sigma>[1..] \<Turnstile>\<^sub>p chi val" by simp
          with 1 have "\<sigma>[1..] \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)" 
            by (simp add: chi1)
          hence "(\<sigma> 0) ~A~ ((\<sigma>[1..]) 0)"
            using characteristic_state_sim[OF fin] by blast
          with can have "\<sigma> 0 = \<sigma> 1"
            by (simp add: canonical_sequence_def)
          with `\<sigma> (Suc 0) \<noteq> \<sigma> 0` show "False" by simp
        qed

        from 2 3 have "k=1" by simp
        moreover
        from st can have "stutter_free (\<sigma>[1..])" "canonical_sequence A (\<sigma>[1..])"
          by (auto simp: stutter_free_suffix canonical_suffix)
        ultimately show "\<sigma> \<Turnstile>\<^sub>p next \<phi>" using `\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>` psi by auto
      qed
    qed
  }
  with nf atoms show "\<exists>\<psi>'. ?P (next \<phi>) \<psi>'" by blast
qed

text {*
  Comparing the definition of the next-free formula in the case of
  formulas @{text "next \<phi>"} with the one that appears in~\cite{peled:ltl-x},
  there is a subtle difference. Peled and Wilke define the second disjunct as
  a disjunction of formulas
%
  \begin{center}\(
    @{text "until (chi val) (and \<psi> (chi val'))"}
  \)\end{center}
%
  for subsets @{text "val, val' \<subseteq> A"} whereas we conjoin the formula
  @{text "chi val"} to the ``until'' formula. This conjunct is indeed
  necessary in order to rule out the case of the ``until'' formula
  being true because of @{text "chi val'"} being true immediately.
  The subtle error in the definition of the formula was acknowledged 
  by Peled and Wilke and apparently had not been noticed since the 
  publication of~\cite{peled:ltl-x} in 1996 (which has been cited more
  than a hundred times according to Google Scholar). Although the error
  was corrected easily, the fact that authors, reviewers, and readers
  appear to have missed it for so long underscores the usefulness of
  formal proofs.

  We now show that any stuttering invariant PLTL formula
  can be expressed without the @{text "next"} operator.
*}

theorem stutter_invariant_next_free:
  assumes phi: "stutter_invariant \<phi>"
  obtains \<psi> where "next_free \<psi>" "atoms \<psi> \<subseteq> atoms \<phi>"
                  "\<forall>\<sigma>. (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  have "atoms \<phi> \<subseteq> atoms \<phi>" "finite (atoms \<phi>)" by simp_all
  then obtain \<psi> where
    psi: "next_free \<psi>" "atoms \<psi> \<subseteq> atoms \<phi>" and
    equiv: "\<forall>\<sigma>. stutter_free \<sigma> \<and> canonical_sequence (atoms \<phi>) \<sigma> \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)"
    by (blast dest: ex_next_free_stutter_free_canonical)
  from `next_free \<psi>` have sinv: "stutter_invariant \<psi>"
    by (rule next_free_stutter_invariant)
  {
    fix \<sigma>
    obtain \<tau> where 1: "\<tau> \<simeq> atoms \<phi> \<simeq> \<sigma>" and 2: "canonical_sequence (atoms \<phi>) \<tau>"
      by (rule canonical_exists)
    from 1 `atoms \<psi> \<subseteq> atoms \<phi>` have 3: "\<tau> \<simeq> atoms \<psi> \<simeq> \<sigma>"
      by (rule seq_sim_mono)

    from 1 have "(\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)" by (simp add: pltl_seq_sim)
    also from phi stutter_reduced_equivalent have "... = (\<natural>\<tau> \<Turnstile>\<^sub>p \<phi>)" by auto
    also from 2[THEN canonical_reduced] equiv stutter_reduced_stutter_free 
    have "... = (\<natural>\<tau> \<Turnstile>\<^sub>p \<psi>)" by auto
    also from sinv stutter_reduced_equivalent have "... = (\<tau> \<Turnstile>\<^sub>p \<psi>)" by auto
    also from 3 have "... = (\<sigma> \<Turnstile>\<^sub>p \<psi>)" by (simp add: pltl_seq_sim)
    finally have "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)" by (rule sym)
  }
  with psi that show ?thesis by blast
qed

text {*
  Combining theorems @{text "next_free_stutter_invariant"} and
  @{text "stutter_invariant_next_free"}, it follows that a PLTL
  formula is stuttering invariant iff it is equivalent to a next-free
  formula.
*}

theorem pltl_stutter_invariant:
  "stutter_invariant \<phi> \<longleftrightarrow> 
   (\<exists>\<psi>. next_free \<psi> \<and> atoms \<psi> \<subseteq> atoms \<phi> \<and> (\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>))"
proof -
  {
    assume "stutter_invariant \<phi>"
    hence "\<exists>\<psi>. next_free \<psi> \<and> atoms \<psi> \<subseteq> atoms \<phi> \<and> (\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule stutter_invariant_next_free) blast
  }
moreover
  {
    fix \<psi>
    assume 1: "next_free \<psi>" and 2: "\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>"
    from 1 have "stutter_invariant \<psi>" by (rule next_free_stutter_invariant)
    with 2 have "stutter_invariant \<phi>" by blast
  }
ultimately show ?thesis by blast
qed


end

