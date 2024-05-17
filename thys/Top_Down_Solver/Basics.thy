section \<open>Preliminaries\<close>

text \<open>\label{sec:preliminaries}\<close>

text \<open>Before we define the \td in Isabelle/HOL and start with its partial correctness proof, we define
all required data structures, formalize definitions and prove auxiliary lemmas.\<close>

theory Basics
  imports Main "HOL-Library.Finite_Map"
begin

unbundle lattice_syntax

subsection \<open>Strategy Trees\<close>

text \<open>The constraint system is a function mapping each unknown to a right-hand side to compute its
  value. We require the right-hand sides to be pure functionals
  \<^cite>\<open>hofmannWhatPureFunctional2010\<close>. This means that they may query the values of other unknowns
  and perform additional computations based on those, but they may, e.g., not spy on the solver's
  data structures. Such pure functions can be expressed as strategy trees.\<close>

datatype ('a, 'b) strategy_tree = Answer 'b |
  Query 'a "'b \<Rightarrow> ('a , 'b) strategy_tree"


text \<open>The solver is defined based on a black-box function T describing the constraint system and
  under the assumption that the special element @{term \<bottom>} exists among the values.\<close>

locale Solver =
  fixes D :: "'d :: bot"
    and T :: "'x \<Rightarrow> ('x , 'd) strategy_tree"
begin

subsection \<open>Auxiliary Lemmas for Default Maps\<close>

text\<open>The solver maintains a solver state to implement optimizations based on self-observation.
  Among the data structures for the solver state are maps that return a default value for
  non-existing keys. In the following, we define some helper functions and lemmas for these.\<close>

definition fmlookup_default where
  "fmlookup_default m d x = (case fmlookup m x of Some v \<Rightarrow> v | None \<Rightarrow> d)"

abbreviation slookup where
  "slookup infl x \<equiv> set (fmlookup_default infl [] x)"

definition mlup where
  "mlup \<sigma> x \<equiv> case \<sigma> x of Some v \<Rightarrow> v | None \<Rightarrow> \<bottom>"

definition fminsert where
  "fminsert infl x y = fmupd x (y # (fmlookup_default infl [] x)) infl"

lemma set_fmlookup_default_cases:
  assumes "y \<in> slookup infl x"
  obtains (1) xs where "fmlookup infl x = Some xs" and "y \<in> set xs"
  using assms that unfolding fmlookup_default_def
  by (cases "fmlookup infl x"; auto)

lemma notin_fmlookup_default_cases:
  assumes "y \<notin> slookup infl x"
  obtains (1) xs where "fmlookup infl x = Some xs" and "y \<notin> set xs"
  | (2) "fmlookup infl x = None"
  using assms that unfolding fmlookup_default_def
  by (cases "fmlookup infl x"; auto)

lemma slookup_helper[simp]:
  assumes "fmlookup m x = Some ys"
    and "y \<in> set ys"
  shows "y \<in> slookup m x"
  using assms(1,2) notin_fmlookup_default_cases by force

lemma lookup_implies_mlup:
  assumes "\<sigma> x = \<sigma>' x'"
  shows "mlup \<sigma> x = mlup \<sigma>' x'"
  using assms
  unfolding mlup_def fmlookup_default_def
  by auto

lemma fmlookup_fminsert:
  assumes "fmlookup_default infl [] x = xs"
  shows "fmlookup (fminsert infl x y) x = Some (y # xs)"
proof(cases "fmlookup infl x")
  case None
  then show ?thesis using assms unfolding fmlookup_default_def fminsert_def by auto
next
  case (Some a)
  then show ?thesis using assms unfolding fmlookup_default_def fminsert_def by auto
qed

lemma fmlookup_fminsert':
  obtains xs ys
  where "fmlookup (fminsert infl x y) x = Some xs"
    and "fmlookup_default infl [] x = ys" and "xs = y # ys"
  using that fmlookup_fminsert
  by fastforce

lemma fmlookup_default_drop_set:
  "fmlookup_default (fmdrop_set A m) [] x = (if x \<notin> A then fmlookup_default m [] x else [])"
  by (simp add: fmlookup_default_def)

lemma mlup_eq_mupd_set:
  assumes "x \<notin> s"
    and "\<forall>y\<in>s. mlup \<sigma> y = mlup \<sigma>' y"
  shows "\<forall>y\<in>s. mlup \<sigma> y = mlup (\<sigma>'(x \<mapsto> xd)) y"
  using assms
  by (simp add: mlup_def)

subsection \<open>Functions on the Constraint System\<close>

text \<open>The function @{term rhs_length} computes the length of a specific path in the strategy tree
  defined by a value assignment for unknowns @{term \<sigma>}.\<close>
function (domintros) rhs_length where
  "rhs_length (Answer d) _ = 0" |
  "rhs_length (Query x f) \<sigma> = 1 + rhs_length (f (mlup \<sigma> x)) \<sigma>"
  by pat_completeness auto

termination rhs_length
proof (rule allI, safe)
  fix t :: "('a, 'b) strategy_tree" and \<sigma> :: "('a, 'b) map"
  show "rhs_length_dom (t, \<sigma>)"
    by (induction t, auto simp add: rhs_length.domintros)
qed

text \<open>The function @{term traverse_rhs} traverses a strategy tree and determines the answer when
  choosing the path through the strategy tree based on a given unknown-value mapping @{term \<sigma>}\<close>
function (domintros) traverse_rhs where
  "traverse_rhs (Answer d) _ = d" |
  "traverse_rhs (Query x f) \<sigma> = traverse_rhs (f (mlup \<sigma> x)) \<sigma>"
  by pat_completeness auto

termination traverse_rhs
  by (relation "measure (\<lambda>(t,\<sigma>). rhs_length t \<sigma>)") auto

text \<open>The function @{term eq} evaluates the right-hand side of an unknown x with an unknown-value
  mapping @{term \<sigma>}.\<close>
definition eq :: "'x \<Rightarrow> ('x, 'd) map \<Rightarrow> 'd" where
  "eq x \<sigma> = traverse_rhs (T x) \<sigma>"
declare eq_def[simp]


subsection \<open>Subtrees of Strategy Trees\<close>

text\<open>We define the set of subtrees of a strategy tree for a specific path (defined through
  @{term \<sigma>}).\<close>
inductive_set subt_aux ::
    "('x, 'd) map \<Rightarrow> ('x, 'd) strategy_tree \<Rightarrow> ('x, 'd) strategy_tree set" for \<sigma> t where
  base: "t \<in> subt_aux \<sigma> t"
| step: "t' \<in> subt_aux \<sigma> t \<Longrightarrow> t' = Query y g \<Longrightarrow> (g (mlup \<sigma> y)) \<in> subt_aux \<sigma> t"

definition subt where
  "subt \<sigma> x = subt_aux \<sigma> (T x)"

lemma subt_of_answer_singleton:
  shows "subt_aux \<sigma> (Answer d) = {Answer d}"
proof (intro set_eqI iffI, goal_cases)
  case (1 x)
  then show ?case by (induction rule: subt_aux.induct; simp)
next
  case (2 x)
  then show ?case by (simp add: subt_aux.base)
qed

lemma subt_transitive:
  assumes "t' \<in> subt_aux \<sigma> t"
  shows "subt_aux \<sigma> t' \<subseteq> subt_aux \<sigma> t"
proof
  fix \<tau>
  assume "\<tau> \<in> subt_aux \<sigma> t'"
  then show "\<tau> \<in> subt_aux \<sigma> t"
    using assms
    by (induction rule: subt_aux.induct; simp add: subt_aux.step)
qed

lemma subt_unfold:
  shows "subt_aux \<sigma> (Query x f) = insert (Query x f) (subt_aux \<sigma> (f (mlup \<sigma> x)))"
proof(intro set_eqI iffI, goal_cases)
  case (1 \<tau>)
  then show ?case
    using subt_aux.simps
    by (induction rule: subt_aux.induct; blast)
next
  case (2 \<tau>)
  then show ?case
  proof (elim insertE, goal_cases)
    case 1
    then show ?case
      using subt_aux.base
      by simp
  next
    case 2
    then show ?case
      using subt_transitive[of "f (mlup \<sigma> x)" \<sigma> "Query x f"] subt_aux.base subt_aux.step
      by auto
  qed
qed

subsection \<open>Dependencies between Unknowns\<close>

text\<open>The set @{term "dep \<sigma> x"} collects all unknowns occuring in the right-hand side of @{term x}
  when traversing it with @{term \<sigma>}.\<close>
function dep_aux where
  "dep_aux \<sigma> (Answer d) = {}"
| "dep_aux \<sigma> (Query y g) = insert y (dep_aux \<sigma> (g (mlup \<sigma> y)))"
  by pat_completeness auto

termination dep_aux
  by (relation "measure (\<lambda>(\<sigma>, t). rhs_length t \<sigma>)") auto

definition dep where
  "dep \<sigma> x = dep_aux \<sigma> (T x)"

lemma dep_aux_eq:
  assumes "\<forall>y \<in> dep_aux \<sigma> t. mlup \<sigma> y = mlup \<sigma>' y"
  shows "dep_aux \<sigma> t = dep_aux \<sigma>' t"
  using assms
  by (induction t rule: strategy_tree.induct) auto

lemmas dep_eq = dep_aux_eq[of \<sigma> "T x" \<sigma>' for \<sigma> x \<sigma>', folded dep_def]

lemma subt_implies_dep:
  assumes "Query y g \<in> subt_aux \<sigma> t"
  shows "y \<in> dep_aux \<sigma> t"
  using assms subt_of_answer_singleton subt_unfold
  by (induction t) auto

lemma solution_sufficient:
  assumes "\<forall>y \<in> dep \<sigma> x. mlup \<sigma> y = mlup \<sigma>' y"
  shows "eq x \<sigma> = eq x \<sigma>'"
proof -
  obtain xd where xd_def: "eq x \<sigma> = xd" by simp
  have "traverse_rhs t \<sigma>' = xd"
    if "t \<in> subt \<sigma> x"
      and "traverse_rhs t \<sigma> = xd"
    for t
    using that
  proof(induction t rule: strategy_tree.induct)
    case (Query y g)
    define t where [simp]: "t = g (mlup \<sigma> y)"
    have "traverse_rhs t \<sigma>' = xd"
      using subt_aux.step Query.prems Query.IH
      by (simp add: subt_def)
    then show ?case
      using subt_implies_dep[where ?t="T x", folded subt_def dep_def] Query.prems(1) assms(1)
      by simp
  qed simp
  then show ?thesis
    using assms subt_aux.base xd_def
    unfolding eq_def subt_def
    by simp
qed

corollary eq_mupd_no_dep:
  assumes "x \<notin> dep \<sigma> y"
  shows "eq y \<sigma> = eq y (\<sigma> (x \<mapsto> xd))"
  using assms solution_sufficient fmupd_lookup
  unfolding fmlookup_default_def mlup_def
  by simp

subsection \<open>Set \<open>Reach\<close>\<close>

text\<open>Let @{term reach} be the set of all unknowns contributing to @{term x} (for a given @{term \<sigma>}).
  This corresponds to the set of all unknowns on which @{term x} transitively depends on when
  evaluating the necessary right-hand sides with @{term \<sigma>}.\<close>

inductive_set reach for \<sigma> x where
  base: "x \<in> reach \<sigma> x"
| step: "y \<in> reach \<sigma> x \<Longrightarrow> z \<in> dep \<sigma> y \<Longrightarrow> z \<in> reach \<sigma> x"

text\<open>The solver stops descending when it encounters an unknown whose evaluation it has already
  started (i.e. an unknown in @{term c}). Therefore, @{term reach} might collect contributing
  unknowns which the solver did not descend into. For a predicate, that relates more closely to the
  solver's history, we define the set @{term [source = true] reach_cap}. Similarly to
  @{term reach} it collects the unknowns on which an unknown transitively depends, but only until an
  unknown in @{term c} is reached.\<close>

inductive_set reach_cap_tree for \<sigma> c t where
  base: "x \<in> dep_aux \<sigma> t \<Longrightarrow> x \<in> reach_cap_tree \<sigma> c t"
| step: "y \<in> reach_cap_tree \<sigma> c t \<Longrightarrow> y \<notin> c \<Longrightarrow> z \<in> dep \<sigma> y \<Longrightarrow> z \<in> reach_cap_tree \<sigma> c t"

abbreviation "reach_cap \<sigma> c x
  \<equiv> insert x (if x \<in> c then {} else reach_cap_tree \<sigma> (insert x c) (T x))"

lemma reach_cap_tree_answer_empty[simp]:
  "reach_cap_tree \<sigma> c (Answer d) = {}"
proof (intro equals0I, goal_cases)
  case (1 y)
  then show ?case by (induction rule: reach_cap_tree.induct; simp)
qed

lemma dep_subset_reach_cap_tree:
  "dep_aux \<sigma>' t \<subseteq> reach_cap_tree \<sigma>' c t"
proof(intro subsetI, goal_cases)
  case (1 x)
  then show ?case using reach_cap_tree.base
    by (induction rule: dep_aux.induct; auto)
qed

lemma reach_cap_tree_subset:
  shows "reach_cap_tree \<sigma> c t \<subseteq> reach_cap_tree \<sigma> (c - {x}) t"
proof
  fix xa
  show "xa \<in> reach_cap_tree \<sigma> c t \<Longrightarrow> xa \<in> reach_cap_tree \<sigma> (c - {x}) t"
  proof(induction rule: reach_cap_tree.induct)
    case base
    then show ?case
      using reach_cap_tree.base
      by simp
  next
    case (step y' z)
    then show ?case
      using reach_cap_tree.step
      by simp
  qed
qed

lemma reach_empty_capped:
  shows "reach \<sigma> x = insert x (reach_cap_tree \<sigma> {x} (T x))"
proof(intro equalityI subsetI, goal_cases)
  case (1 y)
  then show ?case
  proof(induction rule: reach.induct)
    case (step y z)
    then show ?case using reach_cap_tree.base[of z \<sigma> "T x"] reach_cap_tree.step[of y \<sigma> "{x}"]
      unfolding dep_def by blast
  qed simp
next
  case (2 y)
  then show ?case
    using reach.base
  proof(cases "y = x")
    case False
    then have "y \<in> reach_cap_tree \<sigma> {x} (T x)"
      using 2
      by simp
    then show ?thesis
    proof(induction rule: reach_cap_tree.induct)
      case (base y)
      then show ?case
        using reach.base reach.step[of x]
        unfolding dep_def
        by auto
    next
      case (step y z)
      then show ?case
        using reach.step
        by blast
    qed
  qed simp
qed

lemma dep_aux_implies_reach_cap_tree:
  assumes "y \<notin> c"
    and "y \<in> dep_aux \<sigma> t"
  shows "reach_cap_tree \<sigma> c (T y) \<subseteq> reach_cap_tree \<sigma> c t"
proof
  fix xa
  assume "xa \<in> reach_cap_tree \<sigma> c (T y)"
  then show "xa \<in> reach_cap_tree \<sigma> c t"
  proof(induction rule: reach_cap_tree.induct)
    case (base x)
    then show ?case
      using assms reach_cap_tree.base reach_cap_tree.step[unfolded dep_def, of y]
      by simp
  next
    case (step y z)
    then show ?case
      using reach_cap_tree.step
      by simp
  qed
qed

lemma reach_cap_tree_simp:
  shows "reach_cap_tree \<sigma> c t
    = dep_aux \<sigma> t \<union> (\<Union>\<xi>\<in>dep_aux \<sigma> t - c. reach_cap_tree \<sigma> (insert \<xi> c) (T \<xi>))"
proof (intro set_eqI iffI, goal_cases)
  case (1 x)
  then show ?case
  proof (induction rule: reach_cap_tree.induct)
    case (base x)
    then show ?case using reach_cap_tree.step by auto
  next
    case (step y z)
    then show ?case using reach_cap_tree.step[of y \<sigma>] reach_cap_tree.base[of z \<sigma> "T y"]
      unfolding dep_def
      by blast
  qed
next
  case (2 x)
  then show ?case
  proof (elim UnE, goal_cases)
    case 1
    then show ?case using reach_cap_tree.base by simp
  next
    case 2
    then obtain y where "x \<in> reach_cap_tree \<sigma> (insert y c) (T y)" and "y \<in> dep_aux \<sigma> t - c" by auto
    then show ?case
    using dep_aux_implies_reach_cap_tree[of y c] reach_cap_tree_subset[of \<sigma> "insert y c" "T y" y]
    by auto
  qed
qed

lemma reach_cap_tree_step:
  assumes "mlup \<sigma> y = yd"
  shows "reach_cap_tree \<sigma> c (Query y g) = insert y (if y \<in> c then {}
    else reach_cap_tree \<sigma> (insert y c) (T y)) \<union> reach_cap_tree \<sigma> c (g yd)"
  using assms reach_cap_tree_simp[of \<sigma> c]
  by auto

lemma reach_cap_tree_eq:
  assumes "\<forall>x\<in>reach_cap_tree \<sigma> c t. mlup \<sigma> x = mlup \<sigma>' x"
  shows "reach_cap_tree \<sigma> c t = reach_cap_tree \<sigma>' c t"
proof(intro equalityI subsetI, goal_cases)
  case (1 x)
  then show ?case
  proof(induction rule: reach_cap_tree.induct)
    case (base x)
    then show ?case
      using assms reach_cap_tree.base[of _ \<sigma> t c] dep_aux_eq reach_cap_tree.base[of x \<sigma>' t c]
      by metis
  next
    case (step y z)
    then show ?case
      using assms reach_cap_tree.step[of y \<sigma> c t] dep_eq reach_cap_tree.step[of y \<sigma>' c t z]
      by blast
  qed
next
  case (2 x)
  then show ?case
  proof(induction rule: reach_cap_tree.induct)
    case (base x)
    then show ?case
      using assms reach_cap_tree.base[of _ \<sigma> t c] dep_aux_eq reach_cap_tree.base[of x \<sigma>' t c]
      by metis
  next
    case (step y z)
    then show ?case
      using assms reach_cap_tree.step[of y \<sigma> c t] dep_eq reach_cap_tree.step[of y \<sigma>' c t z]
      by blast
  qed
qed

lemma reach_cap_tree_simp2:
  shows "insert x (if x \<in> c then {} else reach_cap_tree \<sigma> c (T x)) =
         insert x (if x \<in> c then {} else reach_cap_tree \<sigma> (insert x c) (T x))"
proof(cases "x \<in> c" rule: case_split[case_names called not_called])
  case not_called
  moreover have "insert x (reach_cap_tree \<sigma> (insert x c) (T x))
    = insert x (reach_cap_tree \<sigma> c (T x))"
  proof(intro equalityI subsetI, goal_cases)
    case (1 y)
    then show ?case
    proof(cases "x = y")
      case False
      then show ?thesis
        by (metis "1" Diff_insert_absorb in_mono insert_mono not_called reach_cap_tree_subset)
    qed auto
  next
    case (2 y)
    then show ?case
    proof(cases "x = y")
      case False
      then show ?thesis
      proof(cases "y \<in> dep \<sigma> x" rule: case_split[case_names xdep no_xdep])
        case xdep
        then show ?thesis using 2 reach_cap_tree.base[of y \<sigma> "T x" "insert x c", folded dep_def]
          by auto
      next
        case no_xdep
        have "y \<in> reach_cap_tree \<sigma> c (T x)" using 2 False by auto
        then show ?thesis
        proof (induction rule: reach_cap_tree.induct)
          case (base x)
          then show ?case by (simp add: reach_cap_tree.base)
        next
          case (step y z)
          then show ?case using reach_cap_tree.step reach_cap_tree.base dep_def by blast
        qed
      qed
    qed auto
  qed
  then show ?thesis by auto
qed auto

lemma dep_closed_implies_reach_cap_tree_closed:
  assumes "x \<in> s"
    and "\<forall>\<xi>\<in>s - (c - {x}). dep \<sigma>' \<xi> \<subseteq> s"
  shows "reach_cap \<sigma>' (c - {x}) x \<subseteq> s"
proof (intro subsetI, goal_cases)
  case (1 y)
  then show ?case using assms
  proof(cases "x = y")
    case False
    then have "y \<in> reach_cap_tree \<sigma>' (c - {x}) (T x)"
      using 1 reach_cap_tree_simp2[of x "c - {x}" \<sigma>'] by auto
    then show ?thesis using assms
    proof(induction)
      case (base y)
      then show ?case using base.hyps dep_def by auto
    next
      case (step y z)
      then show ?case by (metis (no_types, lifting) Diff_iff insert_subset mk_disjoint_insert)
    qed
  qed simp
qed

lemma reach_cap_tree_subset2:
  assumes "mlup \<sigma> y = yd"
  shows "reach_cap_tree \<sigma> c (g yd) \<subseteq> reach_cap_tree \<sigma> c (Query y g)"
  using reach_cap_tree_step[OF assms] by blast

lemma reach_cap_tree_subset_subt:
  assumes "t' \<in> subt_aux \<sigma> t"
  shows "reach_cap_tree \<sigma> c t' \<subseteq> reach_cap_tree \<sigma> c t"
  using assms
proof(induction rule: subt_aux.induct)
  case (step t' y g)
  then show ?case using reach_cap_tree_step by simp
qed simp

lemma reach_cap_tree_singleton:
  assumes "reach_cap_tree \<sigma> (insert x c) t \<subseteq> {x}"
  obtains (Answer) d where "t = Answer d"
  | (Query) f where "t = Query x f"
    and "dep_aux \<sigma> t = {x}"
  using assms that(1)
proof(cases t)
  case (Query x' f)
  then have "x' \<in> reach_cap_tree \<sigma> (insert x c) t"
    using reach_cap_tree.base dep_aux.simps(2) by simp
  then have [simp]: "x' = x" using assms by auto
  then show ?thesis
    using assms that(2) reach_cap_tree.base Query dep_subset_reach_cap_tree subset_antisym
    by fastforce
qed simp

subsection \<open>Partial solution\<close>

text\<open>Finally, we define an unknown-to-value mapping @{term \<sigma>} to be a partial solution over a set of
  unknowns @{term vars} if for every unknown in @{term vars}, the value obtained from an evaluation
  of its right-hand side function @{term "eq x"} with @{term \<sigma>} matches the value stored in
  @{term \<sigma>}.\<close>
abbreviation part_solution where
  "part_solution \<sigma> vars \<equiv> (\<forall>x \<in> vars. eq x \<sigma> = mlup \<sigma> x)"

lemma part_solution_coinciding_sigma_called:
  assumes "part_solution \<sigma> (s - c)"
    and "\<forall>x \<in> s. mlup \<sigma> x = mlup \<sigma>' x"
    and "\<forall>x \<in> s - c. dep \<sigma> x \<subseteq> s"
  shows "part_solution \<sigma>' (s - c)"
  using assms
proof(intro ballI, goal_cases)
  case (1 x)
  then have "\<forall>y\<in>dep \<sigma> x. mlup \<sigma> y = mlup \<sigma>' y" by blast
  then show ?case using 1 solution_sufficient[of \<sigma> x \<sigma>'] by simp
qed

end

end
