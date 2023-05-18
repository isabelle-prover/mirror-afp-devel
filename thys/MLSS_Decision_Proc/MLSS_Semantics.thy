theory MLSS_Semantics
  imports MLSS_Logic HereditarilyFinite.Finitary "HOL-Library.Adhoc_Overloading"
begin

section \<open>Definition of MLSS\<close>
text \<open>
  Here, we define the syntax and semantics of multi-level syllogistic
  with singleton (MLSS). Additionally, we define a number of functions
  working on the syntax such as a function that collects all the subterms
  of a term.
\<close>

subsection \<open>Syntax and Semantics\<close>

datatype (vars_term: 'a) pset_term = 
  Empty nat | is_Var: Var 'a |
  Union "'a pset_term" "'a pset_term" |
  Inter "'a pset_term" "'a pset_term" |
  Diff "'a pset_term" "'a pset_term" |
  Single "'a pset_term"

datatype (vars_atom: 'a) pset_atom =
  Elem "'a pset_term" "'a pset_term" | 
  Equal "'a pset_term" "'a pset_term"

bundle mlss_notation
begin

notation Empty (\<open>\<emptyset> _\<close>)
notation Union (infixr \<open>\<squnion>\<^sub>s\<close> 165)
notation Inter (infixr \<open>\<sqinter>\<^sub>s\<close> 170)
notation Diff (infixl \<open>-\<^sub>s\<close> 180)

notation Elem (infix \<open>\<in>\<^sub>s\<close> 150)
notation Equal (infix \<open>=\<^sub>s\<close> 150)

end

bundle mlss_no_notation
begin

no_notation Empty (\<open>\<emptyset> _\<close>)
no_notation Union (infixr \<open>\<squnion>\<^sub>s\<close> 165)
no_notation Inter (infixr \<open>\<sqinter>\<^sub>s\<close> 170)
no_notation Diff (infixl \<open>-\<^sub>s\<close> 180)

no_notation Elem (infix \<open>\<in>\<^sub>s\<close> 150)
no_notation Equal (infix \<open>=\<^sub>s\<close> 150)

end

unbundle mlss_notation


abbreviation "AT a \<equiv> Atom a"
abbreviation "AF a \<equiv> Neg (Atom a)"

type_synonym 'a pset_fm = "'a pset_atom fm"
type_synonym 'a branch = "'a pset_fm list"

fun I\<^sub>s\<^sub>t :: "('a \<Rightarrow> hf) \<Rightarrow> 'a pset_term \<Rightarrow> hf" where
  "I\<^sub>s\<^sub>t v (\<emptyset> n) = 0"
| "I\<^sub>s\<^sub>t v (Var x) = v x"
| "I\<^sub>s\<^sub>t v (s1 \<squnion>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<squnion> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 \<sqinter>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<sqinter> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 -\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 - I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (Single s) = HF {I\<^sub>s\<^sub>t v s}"

fun I\<^sub>s\<^sub>a :: "('a \<Rightarrow> hf) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>a v (t1 \<in>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<^bold>\<in> I\<^sub>s\<^sub>t v t2"
| "I\<^sub>s\<^sub>a v (t1 =\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 = I\<^sub>s\<^sub>t v t2"


subsection \<open>Variables\<close>

definition vars_fm :: "'a pset_fm \<Rightarrow> 'a set" where
  "vars_fm \<phi> \<equiv> \<Union>(vars_atom ` atoms \<phi>)"

definition vars_branch :: "'a branch \<Rightarrow> 'a set" where
  "vars_branch b \<equiv> \<Union>(vars_fm ` set b)"

consts vars :: "'b \<Rightarrow> 'a set"
adhoc_overloading
  vars vars_term and
  vars vars_atom and
  vars vars_fm and
  vars vars_branch

lemma vars_fm_simps[simp]:
  "vars (Atom a) = vars a"
  "vars (And p q) = vars p \<union> vars q"
  "vars (Or p q) = vars p \<union> vars q"
  "vars (Neg p) = vars p"
  unfolding vars_fm_def
     apply(auto)
  done

lemma vars_fmI:
  "x \<in> vars p \<Longrightarrow> x \<in> vars (And p q)"
  "x \<in> vars q \<Longrightarrow> x \<in> vars (And p q)"
  "x \<in> vars p \<Longrightarrow> x \<in> vars (Or p q)"
  "x \<in> vars q \<Longrightarrow> x \<in> vars (Or p q)"
  "x \<in> vars p \<Longrightarrow> x \<in> vars (Neg p)"
  by auto

lemma vars_branch_simps:
  "vars [] = {}"
  "vars (x # xs) = vars x \<union> vars xs"
  unfolding vars_branch_def by auto

lemma vars_branch_append:
  "vars (b1 @ b2) = vars b1 \<union> vars b2"
  unfolding vars_branch_def by simp

lemma vars_fm_vars_branchI:
  "\<phi> \<in> set b \<Longrightarrow> x \<in> vars_fm \<phi> \<Longrightarrow> x \<in> vars_branch b"
  unfolding vars_branch_def by blast


subsection \<open>Subformulae and Subterms\<close>

subsubsection \<open>Subformulae\<close>

fun subfms :: "'a fm \<Rightarrow> 'a fm set"  where
  "subfms (Atom a) = {Atom a}"
| "subfms (And p q) = {And p q} \<union> subfms p \<union> subfms q"
| "subfms (Or p q) = {Or p q} \<union> subfms p \<union> subfms q"
| "subfms (Neg q) = {Neg q} \<union> subfms q"

definition subfms_branch :: "'a fm list \<Rightarrow> 'a fm set" where
  "subfms_branch b \<equiv> \<Union>(subfms ` set b)"

lemma subfms_branch_simps:
  "subfms_branch [] = {}"
  "subfms_branch (x # xs) = subfms x \<union> subfms_branch xs"
  unfolding subfms_branch_def by auto

lemma subfms_refl[simp]: "p \<in> subfms p"
  by (cases p) auto

lemma subfmsI:
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (And p q)"
  "a \<in> subfms q \<Longrightarrow> a \<in> subfms (And p q)"
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (Or p q)"
  "a \<in> subfms q \<Longrightarrow> a \<in> subfms (Or p q)"
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (Neg p)"
  by auto

lemma subfms_trans: "q \<in> subfms p \<Longrightarrow> p \<in> subfms r \<Longrightarrow> q \<in> subfms r"
  by (induction r) auto

lemma subfmsD:
  "And p q \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  "And p q \<in> subfms \<phi> \<Longrightarrow> q \<in> subfms \<phi>"
  "Or p q \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  "Or p q \<in> subfms \<phi> \<Longrightarrow> q \<in> subfms \<phi>"
  "Neg p \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  using subfmsI subfms_refl subfms_trans by metis+


subsubsection \<open>Subterms\<close>

fun subterms_term :: "'a pset_term \<Rightarrow> 'a pset_term set"  where
  "subterms_term (\<emptyset> n) = {\<emptyset> n}"
| "subterms_term (Var i) = {Var i}"
| "subterms_term (t1 \<squnion>\<^sub>s t2) = {t1 \<squnion>\<^sub>s t2} \<union> subterms_term t1 \<union> subterms_term t2"
| "subterms_term (t1 \<sqinter>\<^sub>s t2) = {t1 \<sqinter>\<^sub>s t2} \<union> subterms_term t1 \<union> subterms_term t2"
| "subterms_term (t1 -\<^sub>s t2) = {t1 -\<^sub>s t2} \<union> subterms_term t1 \<union> subterms_term t2"
| "subterms_term (Single t) = {Single t} \<union> subterms_term t"

fun subterms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set"  where
  "subterms_atom (t1 \<in>\<^sub>s t2) = subterms_term t1 \<union> subterms_term t2"
| "subterms_atom (t1 =\<^sub>s t2) = subterms_term t1 \<union> subterms_term t2"

definition subterms_fm :: "'a pset_fm \<Rightarrow> 'a pset_term set" where
 "subterms_fm \<phi> \<equiv> \<Union>(subterms_atom ` atoms \<phi>)"

definition subterms_branch :: "'a branch \<Rightarrow> 'a pset_term set" where
  "subterms_branch b \<equiv> \<Union>(subterms_fm ` set b)"

consts subterms :: "'a \<Rightarrow> 'b set"
adhoc_overloading 
  subterms subterms_term and
  subterms subterms_atom and
  subterms subterms_fm and
  subterms subterms_branch

lemma subterms_fm_simps[simp]:
  "subterms (Atom a) = subterms a"
  "subterms (And p q) = subterms p \<union> subterms q"
  "subterms (Or p q) = subterms p \<union> subterms q"
  "subterms (Neg p) = subterms p"
  unfolding subterms_fm_def by auto

lemma subterms_branch_simps:
  "subterms [] = {}"
  "subterms (x # xs) = subterms x \<union> subterms xs"
  unfolding subterms_branch_def by auto

lemma subterms_refl[simp]:
  "t \<in> subterms t"
  by (induction t) auto

lemma subterms_term_subterms_term_trans:
  "s \<in> subterms_term t \<Longrightarrow> t \<in> subterms_term v \<Longrightarrow> s \<in> subterms_term v"
  apply(induction v)
       apply(auto)
  done

lemma subterms_term_subterms_atom_trans:
  "s \<in> subterms_term t \<Longrightarrow> t \<in> subterms_atom v \<Longrightarrow> s \<in> subterms_atom v"
  apply(cases v rule: subterms_atom.cases)
  using subterms_term_subterms_term_trans by auto

lemma subterms_term_subterms_fm_trans:
  "s \<in> subterms_term t \<Longrightarrow> t \<in> subterms_fm \<phi> \<Longrightarrow> s \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
     apply(auto simp: subterms_term_subterms_atom_trans)
  done

lemma subterms_fmD:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "Single t \<in> subterms_fm \<phi> \<Longrightarrow> t \<in> subterms_fm \<phi>"
  by (metis UnCI subterms_term.simps subterms_refl subterms_term_subterms_fm_trans)+

lemma subterms_branchD:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "Single t \<in> subterms_branch b \<Longrightarrow> t \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_fmD by fast+

lemma subterms_term_subterms_branch_trans:
  "s \<in> subterms_term t \<Longrightarrow> t \<in> subterms_branch b \<Longrightarrow> s \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_term_subterms_fm_trans by blast

lemma AT_mem_subterms_branchD:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms b" "t \<in> subterms b"
  using assms unfolding subterms_branch_def by force+

lemma AF_mem_subterms_branchD:
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms b" "t \<in> subterms b"
  using assms unfolding subterms_branch_def by force+

lemma AT_eq_subterms_branchD:
  assumes "AT (s =\<^sub>s t) \<in> set b"
  shows "s \<in> subterms b" "t \<in> subterms b"
  using assms unfolding subterms_branch_def by force+

lemma AF_eq_subterms_branchD:
  assumes "AF (s =\<^sub>s t) \<in> set b"
  shows "s \<in> subterms b" "t \<in> subterms b"
  using assms unfolding subterms_branch_def by force+


subsubsection \<open>Interactions between Subterms and Subformulae\<close>

lemma Un_vars_term_subterms_term_eq_vars_term:
  "\<Union>(vars_term ` subterms t) = vars_term t"
  by (induction t) auto

lemma Un_vars_term_subterms_fm_eq_vars_fm:
  "\<Union>(vars_term ` subterms_fm \<phi>) = vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom a)
  then show ?case
    by (cases a) (auto simp: Un_vars_term_subterms_term_eq_vars_term)
qed (fastforce)+

lemma Un_vars_term_subterms_branch_eq_vars_branch:
  "\<Union>(vars_term ` subterms_branch b) = vars_branch b"
  using Un_vars_term_subterms_fm_eq_vars_fm
  unfolding vars_branch_def subterms_branch_def
  by force

lemma subs_vars_branch_if_subs_subterms_branch:
  "subterms_branch b1 \<subseteq> subterms_branch b2 \<Longrightarrow> vars_branch b1 \<subseteq> vars_branch b2"
  using Un_vars_term_subterms_branch_eq_vars_branch
  by (metis complete_lattice_class.Sup_subset_mono subset_image_iff)

lemma subterms_branch_eq_if_vars_branch_eq:
  "subterms_branch b1 = subterms_branch b2 \<Longrightarrow> vars_branch b1 = vars_branch b2"
  using subs_vars_branch_if_subs_subterms_branch by blast

lemma mem_vars_term_if_mem_subterms_term:
  "x \<in> vars_term s \<Longrightarrow> s \<in> subterms_term t \<Longrightarrow> x \<in> vars_term t"
  apply(induction t)
       apply(auto intro: pset_term.set_intros)
  done

lemma mem_vars_fm_if_mem_subterms_fm:
  "x \<in> vars_term s \<Longrightarrow> s \<in> subterms_fm \<phi> \<Longrightarrow> x \<in> vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom a)
  then show ?case
    by (cases a) (auto simp: mem_vars_term_if_mem_subterms_term)
qed (auto simp: vars_fm_def)


lemma vars_term_subs_subterms_term:
  "v \<in> vars_term t \<Longrightarrow> Var v \<in> subterms_term t"
  apply(induction t)
       apply(auto)
  done

lemma vars_atom_subs_subterms_atom:
  "v \<in> vars_atom a \<Longrightarrow> Var v \<in> subterms_atom a"
  apply(cases a)
   apply(auto simp: vars_term_subs_subterms_term)
  done

lemma vars_fm_subs_subterms_fm:
  "v \<in> vars_fm \<phi> \<Longrightarrow> Var v \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
     apply(auto simp: vars_atom_subs_subterms_atom)
  done

lemma vars_branch_subs_subterms_branch:
  "Var ` vars_branch b \<subseteq> subterms_branch b"
  unfolding vars_branch_def subterms_branch_def
  apply(auto simp: vars_fm_subs_subterms_fm)
  done

lemma subterms_term_subterms_atom_Atom_trans:
  "Atom a \<in> set b \<Longrightarrow> x \<in> subterms_term s \<Longrightarrow> s \<in> subterms_atom a \<Longrightarrow> x \<in> subterms_branch b"
  unfolding subterms_branch_def
  by (metis UN_I subterms_fm_simps(1) subterms_term_subterms_atom_trans)

lemma subterms_branch_subterms_subterms_fm_trans:
  "b \<noteq> [] \<Longrightarrow> x \<in> subterms_term t \<Longrightarrow> t \<in> subterms_fm (last b) \<Longrightarrow> x \<in> subterms_branch b"
  using subterms_branch_def subterms_term_subterms_fm_trans by fastforce


subsubsection \<open>Set Atoms in a Branch\<close>

abbreviation pset_atoms_branch :: "'a fm list \<Rightarrow> 'a set" where
  "pset_atoms_branch b \<equiv> \<Union>(atoms ` set b)"

section \<open>Finiteness\<close>

lemma finite_vars_term: "finite (vars_term t)"
  apply(induction t)
       apply(auto)
  done

lemma finite_vars_atom: "finite (vars_atom a)"
  apply(cases a)
   apply(auto simp: finite_vars_term)
  done

lemma finite_vars_fm: "finite (vars_fm \<phi>)"
  apply(induction \<phi>)
     apply(auto simp: finite_vars_atom)
  done

lemma finite_vars_branch: "finite (vars_branch b)"
  apply(induction b)
   apply(auto simp: vars_branch_def finite_vars_fm)
  done

lemma finite_subterms_term: "finite (subterms_term l)"
  apply(induction l)
       apply(auto)
  done

lemma finite_subterms_atom: "finite (subterms_atom l)"
  apply(cases l rule: subterms_atom.cases)
   apply(auto simp: finite_subterms_term)
  done

lemma finite_subterms_fm: "finite (subterms_fm \<phi>)"
  apply(induction \<phi>)
     apply(auto simp: finite_subterms_atom)
  done

lemma finite_subterms_branch: "finite (subterms_branch b)"
  apply(induction b)
   apply(auto simp: subterms_branch_def finite_subterms_fm)
  done

lemma finite_subfms: "finite (subfms \<phi>)"
  apply(induction \<phi>)
     apply(auto)
  done

lemma finite_subfms_branch: "finite (subfms_branch b)"
  by (induction b) (auto simp: subfms_branch_simps finite_subfms)

lemma finite_atoms: "finite (atoms \<phi>)"
  by (induction \<phi>) auto

lemma finite_pset_atoms_branch: "finite (pset_atoms_branch b)"
  by (auto simp: finite_atoms)

subsection \<open>Non-Emptiness\<close>

lemma subterms_term_nonempty[simp]: "subterms_term t \<noteq> {}"
  by (induction t) auto

lemma subterms_atom_nonempty[simp]: "subterms_atom l \<noteq> {}"
  by (cases l rule: subterms_atom.cases) auto

lemma subterms_fm_nonempty[simp]: "subterms_fm \<phi> \<noteq> {}"
  by (induction \<phi>) auto

end