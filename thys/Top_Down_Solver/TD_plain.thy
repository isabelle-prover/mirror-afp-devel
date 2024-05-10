section \<open>The plain Top-Down Solver\<close>
text \<open>\label{sec:td_plain}\<close>

text\<open>TD\_plain is a simplified version of the original TD which only keeps track of already called
  unknowns to avoid infinite descend in case of recursive dependencies. In contrast to the TD, it
  does, however, not track stable unknowns and the dependencies between unknowns. Instead, it
  re-iterates every unknown when queried again.
\<close>

theory TD_plain
  imports Basics
begin

locale TD_plain = Solver D T
  for D :: "'d :: bot"
    and T :: "'x \<Rightarrow> ('x, 'd) strategy_tree"
begin

subsection \<open>Definition of the Solver Algorithm\<close>

text \<open>The recursively descending solver algorithm is defined with three mutual recursive functions.
  Initially, the function @{term iterate} is called from the top-level @{term solve} function for
  the requested unknown. @{term iterate} keeps evaluating the right-hand side by calling the
  function @{term eval} and updates the value mapping @{term \<sigma>} until the value stabilizes. The
  function @{term eval} walks through a strategy tree and chooses the path based on the result for
  queried unknowns. These queries are delegated to the third mutual recursive function @{term query}
  which checks that the unknown is not already being evaluated and iterates it otherwise. The
  function keyword is used for the definition, since, without further assumptions, the solver may
  not terminate.\<close>

function (domintros)
    query :: "'x \<Rightarrow> 'x \<Rightarrow> 'x set \<Rightarrow> ('x, 'd) map \<Rightarrow> 'd \<times> ('x, 'd) map" and
  iterate :: "'x \<Rightarrow> 'x set \<Rightarrow> ('x, 'd) map \<Rightarrow> 'd \<times> ('x, 'd) map" and
     eval :: "'x \<Rightarrow> ('x, 'd) strategy_tree \<Rightarrow> 'x set \<Rightarrow> ('x, 'd) map \<Rightarrow> 'd \<times> ('x, 'd) map" where
  "query x y c \<sigma> = (
    if y \<in> c then
      (mlup \<sigma> y, \<sigma>)
    else
      iterate y (insert y c) \<sigma>)"
| "iterate x c \<sigma> = (
    let (d_new, \<sigma>) = eval x (T x) c \<sigma> in
    if d_new = mlup \<sigma> x then
      (d_new, \<sigma>)
    else
      iterate x c (\<sigma>(x \<mapsto> d_new)))"
| "eval x t c \<sigma> = (case t of
      Answer d \<Rightarrow> (d, \<sigma>)
    | Query y g \<Rightarrow> (let (yd, \<sigma>) = query x y c \<sigma> in eval x (g yd) c \<sigma>))"
  by pat_completeness auto

definition solve :: "'x \<Rightarrow> ('x, 'd) map" where
  "solve x = (let (_, \<sigma>) = iterate x {x} Map.empty in \<sigma>)"

definition query_dom where
  "query_dom x y c \<sigma> = query_iterate_eval_dom (Inl (x, y, c, \<sigma>))"
declare query_dom_def [simp]
definition iterate_dom where
  "iterate_dom x c \<sigma> = query_iterate_eval_dom (Inr (Inl (x, c, \<sigma>)))"
declare iterate_dom_def [simp]
definition eval_dom where
  "eval_dom x t c \<sigma> = query_iterate_eval_dom (Inr (Inr (x, t, c, \<sigma>)))"
declare eval_dom_def [simp]

definition solve_dom where
  "solve_dom x = iterate_dom x {x} Map.empty"

lemmas dom_defs = query_dom_def iterate_dom_def eval_dom_def


subsection \<open>Refinement of Auto-Generated Rules\<close>

text \<open>The auto-generated \texttt{pinduct} rule contains a redundant assumption. This lemma removes
  this redundant assumption for easier instantiation and assigns each case a comprehensible name.\<close>

lemmas query_iterate_eval_pinduct[consumes 1, case_names Query Iterate Eval]
  = query_iterate_eval.pinduct(1)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x y c \<sigma> for x y c \<sigma>
    ]
    query_iterate_eval.pinduct(2)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x c \<sigma> for x c \<sigma>
    ]
    query_iterate_eval.pinduct(3)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x t c \<sigma> for x t c \<sigma>
    ]

lemmas iterate_pinduct[consumes 1, case_names Iterate]
  = query_iterate_eval_pinduct(2)[where ?P="\<lambda>x y c \<sigma>. True" and ?R="\<lambda>x t c \<sigma>. True",
    simplified (no_asm_use), folded query_dom_def iterate_dom_def eval_dom_def]

declare query.psimps [simp]
declare iterate.psimps [simp]
declare eval.psimps [simp]

subsection \<open>Domain Lemmas\<close>

lemma dom_backwards_pinduct:
  shows "query_dom x y c \<sigma>
    \<Longrightarrow> y \<notin> c \<Longrightarrow> iterate_dom y (insert y c) \<sigma>"
  and "iterate_dom x c \<sigma>
    \<Longrightarrow> (eval_dom x (T x) c \<sigma> \<and>
        (eval x (T x) c \<sigma> = (xd_new, \<sigma>')
          \<longrightarrow> mlup \<sigma>' x = xd_old \<longrightarrow> xd_new \<noteq> xd_old \<longrightarrow>
          iterate_dom x c (\<sigma>'(x \<mapsto> xd_new))))"
  and "eval_dom x (Query y g) c \<sigma>
    \<Longrightarrow> (query_dom x y c \<sigma> \<and> (query x y c \<sigma> = (yd, \<sigma>') \<longrightarrow> eval_dom x (g yd) c \<sigma>'))"
proof (induction x y c \<sigma> and x c \<sigma> and x "Query y g" c \<sigma>
    arbitrary: and xd_new xd_old \<sigma>' and y g yd \<sigma>'
    rule: query_iterate_eval_pinduct)
  case (Query x c \<sigma>)
  then show ?case
    using query_iterate_eval.domintros(2) by fastforce
next
  case (Iterate x c \<sigma>)
  then show ?case
    using query_iterate_eval.domintros(2,3)[folded eval_dom_def iterate_dom_def query_dom_def]
    by metis
next
  case (Eval c \<sigma>)
  then show ?case
    using query_iterate_eval.domintros(1,3) by simp
qed

subsection \<open>Case Rules\<close>

lemma iterate_continue_fixpoint_cases[consumes 3]:
  assumes "iterate_dom x c \<sigma>"
    and "iterate x c \<sigma> = (xd, \<sigma>')"
    and "x \<in> c"
  obtains (Fixpoint) "eval_dom x (T x) c \<sigma>"
    and "eval x (T x) c \<sigma> = (xd, \<sigma>')"
    and "mlup \<sigma>' x = xd"
  | (Continue) \<sigma>1 xd_new
  where "eval_dom x (T x) c \<sigma>"
    and "eval x (T x) c \<sigma> = (xd_new, \<sigma>1)"
    and "mlup \<sigma>1 x \<noteq> xd_new"
    and "iterate_dom x c (\<sigma>1(x \<mapsto> xd_new))"
    and "iterate x c (\<sigma>1(x \<mapsto> xd_new)) = (xd, \<sigma>')"
proof -
 obtain xd_new \<sigma>1
    where "eval x (T x) c \<sigma> = (xd_new, \<sigma>1)"
    by (cases "eval x (T x) c \<sigma>")
  then show ?thesis
    using assms that dom_backwards_pinduct(2)
    by (cases "mlup \<sigma>1 x = xd_new"; simp)
qed

lemma iterate_fmlookup:
  assumes "iterate_dom x c \<sigma>"
    and "iterate x c \<sigma> = (xd, \<sigma>')"
    and "x \<in> c"
  shows "mlup \<sigma>' x = xd"
  using assms
proof(induction rule: iterate_pinduct)
  case (Iterate x c \<sigma>)
  show ?case
    using Iterate.hyps Iterate.prems
  proof (cases rule: iterate_continue_fixpoint_cases)
    case (Continue \<sigma>1 xd_new)
    then show ?thesis
      using Iterate.prems(2) Iterate.IH
      by fastforce
  qed simp
qed

corollary query_fmlookup:
  assumes "query_dom x y c \<sigma>"
    and "query x y c \<sigma> = (yd, \<sigma>')"
  shows "mlup \<sigma>' y = yd"
  using assms iterate_fmlookup dom_backwards_pinduct(1)[of x y c \<sigma>]
  by (auto split: if_splits)

lemma query_iterate_lookup_cases [consumes 2]:
  assumes "query_dom x y c \<sigma>"
    and "query x y c \<sigma> = (yd, \<sigma>')"
  obtains (Iterate)
        "iterate_dom y (insert y c) \<sigma>"
    and "iterate y (insert y c) \<sigma> = (yd, \<sigma>')"
    and "mlup \<sigma>' y = yd"
    and "y \<notin> c"
  | (Lookup) "mlup \<sigma> y = yd"
    and "\<sigma> = \<sigma>'"
    and "y \<in> c"
  using assms that dom_backwards_pinduct(1) query_fmlookup[of x y c \<sigma> yd \<sigma>']
  by (cases "y \<in> c"; auto)

lemma eval_query_answer_cases [consumes 2]:
  assumes "eval_dom x t c \<sigma>"
    and "eval x t c \<sigma> = (d, \<sigma>')"
  obtains (Query) y g yd \<sigma>1
  where "t = Query y g"
    and "query_dom x y c \<sigma>"
    and "query x y c \<sigma> = (yd, \<sigma>1)"
    and "eval_dom x (g yd) c \<sigma>1"
    and "eval x (g yd) c \<sigma>1 = (d, \<sigma>')"
    and "mlup \<sigma>1 y = yd"
  | (Answer) "t = Answer d"
    and "\<sigma> = \<sigma>'"
  using assms dom_backwards_pinduct(3) that query_fmlookup
  by (cases t; auto split: prod.splits)

subsection \<open>Predicate for Valid Input States\<close>

text\<open>We define a predicate for valid input solver states. @{term c} is the set of called unknowns,
  i.e., the unknowns currently being evaluated and @{term \<sigma>} is an unknown-to-value mapping. Both
  are data structures maintained by the solver. In contrast, the parameter @{term s} describing a
  set of unknowns, for which a partial solution has already been computed or which are currently
  being evaluated, is introduced for the proof. Although it is similar to the set @{term stabl}
  maintained by the original TD, it is only an under-approximation of it.
  A valid solver state is one, where @{term \<sigma>} is a partial solution for all truly stable unknowns,
  i.e., unknowns in @{term "s - c"}, and where these truly stable unknowns only depend on unknowns
  which are also truly stable or currently being evaluated.
  A substantial part of the partial correctness proof is to show that this property about the
  solver's state is preserved during a solver's run.\<close>

definition invariant where
  "invariant s c \<sigma> \<equiv> (\<forall>\<xi>\<in>s - c. dep \<sigma> \<xi> \<subseteq> s) \<and> part_solution \<sigma> (s - c)"

lemma invariant_simp:
  assumes "x \<in> c"
    and "invariant s (c - {x}) \<sigma>"
  shows "invariant (insert x s) c \<sigma>"
  using assms
proof -
  have "c - {x} \<subseteq> s \<equiv> c \<subseteq> insert x s"
    using assms(1)
    by (simp add: subset_insert_iff)
  moreover have "s - (c - {x}) \<supseteq> insert x s - c"
    using assms(1)
    by auto
  ultimately show ?thesis
    using assms(2)
    unfolding invariant_def
    by fastforce
qed

lemma invariant_continue:
  assumes "x \<notin> s"
    and "invariant s c \<sigma>"
    and "\<forall>y\<in>s. mlup \<sigma> y = mlup \<sigma>1 y"
  shows "invariant s c (\<sigma>1(x \<mapsto> xd))"
proof -
  show ?thesis
  using assms mlup_eq_mupd_set[OF assms(1,3)] unfolding invariant_def
  proof(intro conjI, goal_cases)
    case 1 then show ?case using dep_eq by blast
  next
    case 2 then show ?case using part_solution_coinciding_sigma_called
      by (metis DiffD1 solution_sufficient subsetD)
  qed
qed

subsection \<open>Partial Correctness Proofs\<close>

lemma x_not_stable:
  assumes "eq x \<sigma> \<noteq> mlup \<sigma> x"
    and "part_solution \<sigma> s"
  shows "x \<notin> s"
  using assms by auto

text\<open>With the following lemma we establish, that whenever the solver is called for an unknown
  in @{term s} and where the solver state and @{term s} fulfill the invariant, the output value
  mapping is unchanged compared to the input value mapping.\<close>

lemma already_solution:
  shows "query_dom x y c \<sigma>
    \<Longrightarrow> query x y c \<sigma> = (yd, \<sigma>')
    \<Longrightarrow> y \<in> s
    \<Longrightarrow> invariant s c \<sigma>
    \<Longrightarrow> \<sigma> = \<sigma>'"
    and "iterate_dom x c \<sigma>
    \<Longrightarrow> iterate x c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> x \<in> c
    \<Longrightarrow> x \<in> s
    \<Longrightarrow> invariant s (c - {x}) \<sigma>
    \<Longrightarrow> \<sigma> = \<sigma>'"
    and "eval_dom x t c \<sigma>
    \<Longrightarrow> eval x t c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> dep_aux \<sigma> t \<subseteq> s
    \<Longrightarrow> invariant s c \<sigma>
    \<Longrightarrow> traverse_rhs t \<sigma>' = xd \<and> \<sigma> = \<sigma>'"
proof(induction arbitrary: yd s \<sigma>' and xd s \<sigma>' and xd s \<sigma>' rule: query_iterate_eval_pinduct)
  case (Query x y c \<sigma>)
  show ?case using Query.IH(1) Query.prems Query.IH(2)
    by (cases rule: query_iterate_lookup_cases; simp)
next
  case (Iterate x c \<sigma>)
  show ?case using Iterate.IH(1) Iterate.prems(1,2)
  proof(cases rule: iterate_continue_fixpoint_cases)
    case Fixpoint
    then show ?thesis
      using Iterate.prems(3,4) Iterate.IH(2)[of _ _ "insert x s"]
        invariant_simp[OF Iterate.prems(2,4)]
      unfolding dep_def invariant_def by auto
  next
    case (Continue \<sigma>1 xd')
    show ?thesis
    proof(rule ccontr)
      have IH: "eq x \<sigma>1 = xd' \<and> \<sigma> = \<sigma>1"
        using Iterate.prems(2-4) Iterate.IH(2)[OF Continue(2), of s]
          invariant_simp[OF Iterate.prems(2,4)] unfolding dep_def invariant_def by auto
      then show False
        using Iterate.prems(2-4) Continue(3) unfolding invariant_def by simp
    qed
  qed
next
  case (Eval x t c \<sigma>)
  show ?case using Eval.IH(1) Eval.prems(1)
  proof(cases rule: eval_query_answer_cases)
    case (Query y g yd \<sigma>1)
    then show ?thesis using Eval.prems(1-3) Eval.IH(1) Eval.IH(2)[OF Query(1,3)]
        Eval.IH(3)[OF Query(1) Query(3)[symmetric] _ Query(5)]
      by auto
  qed simp
qed

text\<open>Furthermore, we show that whenever the solver is called with a valid solver state, the valid
  solver state invariant also holds for its output state and the set of stable unknowns increases by
  the set @{term [source = true] reach_cap} of the current unknown.\<close>

lemma partial_correctness_ind:
  shows "query_dom x y c \<sigma>
    \<Longrightarrow> query x y c \<sigma> = (yd, \<sigma>')
    \<Longrightarrow> invariant s c \<sigma>
    \<Longrightarrow> invariant (s \<union> reach_cap \<sigma>' c y) c \<sigma>'
      \<and> (\<forall>\<xi> \<in> s. mlup \<sigma> \<xi> = mlup \<sigma>' \<xi>)"
    and "iterate_dom x c \<sigma>
    \<Longrightarrow> iterate x c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> x \<in> c
    \<Longrightarrow> invariant s (c - {x}) \<sigma>
    \<Longrightarrow> invariant (s \<union> (reach_cap \<sigma>' (c - {x}) x)) (c - {x}) \<sigma>'
      \<and> (\<forall>\<xi> \<in> s. mlup \<sigma> \<xi> = mlup \<sigma>' \<xi>)"
    and "eval_dom x t c \<sigma>
    \<Longrightarrow> eval x t c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> invariant s c \<sigma>
    \<Longrightarrow> invariant (s \<union> reach_cap_tree \<sigma>' c t) c \<sigma>'
      \<and> (\<forall>\<xi> \<in> s. mlup \<sigma> \<xi> = mlup \<sigma>' \<xi>)
      \<and> traverse_rhs t \<sigma>' = xd"
proof(induction arbitrary: yd s \<sigma>' and xd s \<sigma>' and xd s \<sigma>' rule: query_iterate_eval_pinduct)
  case (Query x y c \<sigma>)
  show ?case
    using Query.IH(1) Query.prems(1)
  proof (cases rule: query_iterate_lookup_cases)
    case Iterate
    note IH = Query.IH(2)[simplified, OF Iterate(4,2) Query.prems(2)]
    then show ?thesis
      using Iterate(4) by simp
  next
    case Lookup
    then show ?thesis
      using Query.prems(2) unfolding invariant_def by auto
  qed
next
  case (Iterate x c \<sigma>)
  show ?case
    using Iterate.IH(1) Iterate.prems(1,2)
  proof(cases rule: iterate_continue_fixpoint_cases)
    case Fixpoint
    note IH = Iterate.IH(2)[OF Fixpoint(2) invariant_simp[OF Iterate.prems(2,3)], folded eq_def]
    then show ?thesis
      using Fixpoint(3) Iterate.prems(2) reach_cap_tree_simp2[of x "c - {x}"]
        dep_subset_reach_cap_tree[of \<sigma>' "T x", folded dep_def]
      unfolding invariant_def
      by (auto simp add: insert_absorb)
  next
    case (Continue \<sigma>1 xd')
    note IH = Iterate.IH(2)[OF Continue(2) invariant_simp[OF Iterate.prems(2,3)]]

    have "part_solution \<sigma>1 (s - (c - {x}))"
      using part_solution_coinciding_sigma_called[of s "c - {x}" \<sigma> \<sigma>1] IH Iterate.prems(3)
      unfolding invariant_def
      by simp
    then have x_not_stable: "x \<notin> s"
      using x_not_stable[of x \<sigma>1 s] IH Continue(3)
      by auto
    then have inv: "invariant s (c - {x}) (\<sigma>1(x \<mapsto> xd'))"
      using IH invariant_continue[OF x_not_stable Iterate.prems(3)] by blast

    note ih = Iterate.IH(3)[OF Continue(2)[symmetric] _ Continue(3)[symmetric] Continue(5)
        Iterate.prems(2) inv, simplified]
    then show ?thesis
      using IH mlup_eq_mupd_set[OF x_not_stable, of \<sigma>]
      unfolding mlup_def
      by auto
  qed
next
  case (Eval x t c \<sigma>)
  show ?case using Eval.IH(1) Eval.prems(1)
  proof(cases rule: eval_query_answer_cases)
    case (Query y g yd \<sigma>1)
    note IH = Eval.IH(2)[OF Query(1,3) Eval.prems(2)]
    note ih = Eval.IH(3)[OF Query(1) Query(3)[symmetric] _ Query(5) conjunct1[OF IH], simplified]
    show ?thesis
      using Query IH ih reach_cap_tree_step reach_cap_tree_eq[of \<sigma>1 "insert y c" "T y" \<sigma>']
      by (auto simp add: Un_assoc)
  next
    case Answer
    then show ?thesis
      using Eval.prems(2) by simp
  qed
qed

text\<open>Since the initial solver state fulfills the valid solver state predicate, we can conclude from
  the above lemma, that the solve function returns a partial solution for the queried unknown
  @{term x} and all unknowns on which it transitively depends.\<close>

corollary partial_correctness:
  assumes "solve_dom x"
    and "solve x = \<sigma>"
  shows "part_solution \<sigma> (reach \<sigma> x)"
proof -
  obtain xd where "iterate x {x} Map.empty = (xd, \<sigma>)"
    using assms(2) unfolding solve_def by (auto split: prod.splits)
  then show ?thesis
  using assms(1) partial_correctness_ind(2)[of x "{x}" Map.empty xd \<sigma> "{}"] reach_empty_capped
  unfolding solve_dom_def invariant_def by simp
qed


subsection \<open>Termination of TD\_plain for Stable Unknowns\<close>

text\<open>In the equivalence proof of the TD and the TD\_plain, we need to show that when the TD
  trivially terminates because the queried unknown is already stable and its value is only looked
  up, the evaluation of this unknown @{term x} with TD\_plain also terminates. For this, we exploit
  that the set of stable unknowns is always finite during a terminating solver's run and provide the
  following lemma:\<close>

lemma td1_terminates_for_stabl:
  assumes "x \<in> s"
    and "invariant s (c - {x}) \<sigma>"
    and "mlup \<sigma> x = xd"
    and "finite s"
    and "x \<in> c"
  shows "iterate_dom x c \<sigma>" and "iterate x c \<sigma> = (xd, \<sigma>)"
proof(goal_cases)
  have "reach_cap \<sigma> (c - {x}) x \<subseteq> s"
    using assms(1,2) dep_closed_implies_reach_cap_tree_closed unfolding invariant_def by simp
  from finite_subset[OF this] have "finite (reach_cap \<sigma> (c - {x}) x - (c - {x}))"
    using assms(4) by simp+
  then have goal: "iterate_dom x c \<sigma> \<and> iterate x c \<sigma> = (xd, \<sigma>)" using assms(1-3,5)
  proof(induction "reach_cap \<sigma> (c - {x}) x - (c - {x})"
      arbitrary: x c xd rule: finite_psubset_induct)
    case psubset
    have "eval_dom x t c \<sigma> \<and> (traverse_rhs t \<sigma>, \<sigma>) = eval x t c \<sigma>" if "t \<in> subt \<sigma> x" for t
      using that
    proof(induction t)
      case (Answer _)
      then show ?case
        using query_iterate_eval.domintros(3)[folded query_dom_def iterate_dom_def eval_dom_def]
        by fastforce
    next
      case (Query y g)
      have "reach_cap_tree \<sigma> (insert x (c - {x})) (T x) \<subseteq> s"
        using dep_closed_implies_reach_cap_tree_closed[OF psubset.prems(1), of c \<sigma>]
          psubset.prems(2)[unfolded invariant_def]
        by auto
      then have y_stable: "y \<in> s"
        using dep_subset_reach_cap_tree subt_implies_dep[OF Query(2)[unfolded subt_def]]
        by blast
      show ?case
      proof(cases "y \<in> c" rule: case_split[case_names called not_called])
        case called
        then have dom: "query_dom x y c \<sigma>"
          using query_iterate_eval.domintros(1)[folded query_dom_def] by auto
        moreover have query_val: "(mlup \<sigma> y, \<sigma>) = query x y c \<sigma>"
          using called already_solution(1) partial_correctness_ind(1)
          by (metis query.psimps query_iterate_eval.domintros(1))
        ultimately have "eval_dom x (Query y g) c \<sigma>"
          using Query.IH[of "g (mlup \<sigma> y)"]
            query_iterate_eval.domintros(3)[folded dom_defs, of "Query y g" x c \<sigma>] Query.prems
            subt_aux.step subt_def
          by fastforce
        have "g (mlup \<sigma> y) \<in> subt_aux \<sigma> (T x)"
          using Query.prems subt_aux.step subt_def by blast
        then have "eval_dom x (g (mlup \<sigma> y)) c \<sigma>"
            and "(traverse_rhs (g (mlup \<sigma> y)) \<sigma>, \<sigma>) = eval x (g (mlup \<sigma> y)) c \<sigma>"
          using Query.IH unfolding subt_def by auto
        then show ?thesis
          using \<open>eval_dom x (Query y g) c \<sigma>\<close> query_val
          by (auto split: strategy_tree.split prod.split)
      next
        case not_called
        then obtain yd where lupy: "mlup \<sigma> y = yd" and eqy: "eq y \<sigma> = yd"
          using y_stable psubset.prems(2) unfolding invariant_def by auto
        have ih: "eval_dom x (g (mlup \<sigma> y)) c \<sigma>"
            and "(traverse_rhs (g (mlup \<sigma> y)) \<sigma>, \<sigma>) = eval x (g (mlup \<sigma> y)) c \<sigma>"
          using Query.IH[of "g (mlup \<sigma> y)"] Query.prems subt_aux.step subt_def by auto
        moreover have "reach_cap \<sigma> c y \<subseteq> reach_cap \<sigma> (c - {x}) x"
          using not_called psubset.prems(4) reach_cap_tree_step[of \<sigma> y yd c g, OF lupy]
            reach_cap_tree_subset_subt[of "Query y g" \<sigma> "T x" c, folded subt_def, OF Query.prems]
          by (simp add: insert_absorb subset_insertI2)
        then have f_def: "reach_cap \<sigma> c y - c \<subset> reach_cap \<sigma> (c - {x}) x - (c - {x})"
          using psubset.prems(4)
          by blast
        have "invariant s (c - {y}) \<sigma>"
          using psubset.prems(2) not_called psubset.prems(1) invariant_simp
          by (metis Diff_empty Diff_insert0 insert_absorb)
        then have IH: "iterate_dom y (insert y c) \<sigma> \<and> iterate y (insert y c) \<sigma> = (yd, \<sigma>)"
          using f_def y_stable not_called lupy psubset.hyps(2)[of y "c - {y}" yd] psubset.hyps(2)
          by (metis Diff_idemp Diff_insert_absorb insertCI )
        then have "query_dom x y c \<sigma> \<and> (mlup \<sigma> y, \<sigma>) = query x y c \<sigma>"
          using not_called lupy query_iterate_eval.domintros(1)[folded dom_defs, of y c \<sigma>]
          by simp
        ultimately show ?thesis
          using query_iterate_eval.domintros(3)[folded dom_defs, of "Query y g" x c \<sigma>] by fastforce
      qed
    qed
    note IH = this[of "T x", folded eq_def, OF subt_aux.base[of "T x" \<sigma>, folded subt_def]]
    moreover have "eq x \<sigma> = mlup \<sigma> x" using psubset.prems(1,2) unfolding invariant_def by auto
    moreover have "iterate_dom x c \<sigma>"
      using query_iterate_eval.domintros(2)[folded dom_defs, of x c \<sigma>] IH \<open>eq x \<sigma> = mlup \<sigma> x\<close>
      by (metis Pair_inject)
    ultimately show ?case
      using iterate.psimps[folded dom_defs, of x c \<sigma>] psubset.prems(3)
      by (cases "eval x (T x) c \<sigma>") auto
  qed
  case 1 show ?case using goal ..
  case 2 show ?case using goal ..
qed


subsection \<open>Program Refinement for Code Generation\<close>

text\<open>For code generation, we define a refined version of the solver function using the
partial\_function keyword with the option attribute.\<close>

datatype ('a,'b) state = Q "'a \<times> 'a \<times> 'a set \<times> ('a, 'b) map"
  | I "'a \<times> 'a set \<times> ('a, 'b) map"  | E "'a \<times> ('a,'b) strategy_tree \<times> 'a set \<times> ('a, 'b) map"

partial_function (option)
  solve_rec_c :: "('x, 'd) state \<Rightarrow> ('d \<times> ('x, 'd) map) option"
 where
  "solve_rec_c s = (case s of Q (x, y, c, \<sigma>) \<Rightarrow>
      if y \<in> c then
        Some (mlup \<sigma> y, \<sigma>)
      else
        solve_rec_c (I (y, (insert y c), \<sigma>))
    | I (x, c, \<sigma>) \<Rightarrow>
      Option.bind (solve_rec_c (E (x, (T x), c, \<sigma>))) (\<lambda>(d_new, \<sigma>).
      if d_new = mlup \<sigma> x then
        Some (d_new, \<sigma>)
      else
        solve_rec_c (I (x, c, (\<sigma>(x \<mapsto> d_new)))))
    | E (x, t, c, \<sigma>) \<Rightarrow>
      (case t of
        Answer d \<Rightarrow> Some (d, \<sigma>)
      | Query y g \<Rightarrow> Option.bind (solve_rec_c (Q (x, y, c, \<sigma>)))
        (\<lambda>(yd, \<sigma>). solve_rec_c (E (x, (g yd), c, \<sigma>)))))"

declare solve_rec_c.simps[simp,code]

definition solve_rec_c_dom where "solve_rec_c_dom p \<equiv> \<exists>\<sigma>. solve_rec_c p = Some \<sigma>"

definition solve_c :: "'x \<Rightarrow> (('x, 'd) map) option" where
  "solve_c x = Option.bind (solve_rec_c (I (x, {x}, Map.empty))) (\<lambda>(_, \<sigma>). Some \<sigma>)"

definition solve_c_dom :: "'x \<Rightarrow> bool" where "solve_c_dom x \<equiv> \<exists>\<sigma>. solve_c x = Some \<sigma>"


text\<open>We proof the equivalence between the refined solver function for code generation and the
initial version used for the partial correctness proof.\<close>

lemma query_iterate_eval_solve_rec_c_equiv:
  shows "query_dom x y c \<sigma> \<Longrightarrow> solve_rec_c_dom (Q (x,y,c,\<sigma>))
    \<and> query x y c \<sigma> = the (solve_rec_c (Q (x,y,c,\<sigma>)))"
  and "iterate_dom x c \<sigma> \<Longrightarrow> solve_rec_c_dom (I (x,c,\<sigma>))
    \<and> iterate x c \<sigma> = the (solve_rec_c (I (x,c,\<sigma>)))"
  and "eval_dom x t c \<sigma> \<Longrightarrow> solve_rec_c_dom (E (x,t,c,\<sigma>))
    \<and> eval x t c \<sigma> = the (solve_rec_c (E (x,t,c,\<sigma>)))"
proof (induction x y c \<sigma> and x c \<sigma> and x t c \<sigma> rule: query_iterate_eval_pinduct)
  case (Query x y c \<sigma>)
  show ?case
  proof (cases "y \<in> c")
    case True
    then have "solve_rec_c (Q (x, y, c, \<sigma>)) = Some (mlup \<sigma> y, \<sigma>)" by simp
    moreover have "query x y c \<sigma> = (mlup \<sigma> y, \<sigma>)"
      using query.psimps[folded dom_defs] Query(1) True by force
    ultimately show ?thesis unfolding solve_rec_c_dom_def by auto
  next
    case False
    then have "query x y c \<sigma> = iterate y (insert y c) \<sigma>"
      using Query.IH(1) query.pelims[folded dom_defs] by fastforce
    then have "query x y c \<sigma> = the (solve_rec_c (Q (x, y, c, \<sigma>)))"
      using Query False False by simp
    moreover have "solve_rec_c_dom (Q (x, y, c, \<sigma>))"
      using Query(2) False unfolding solve_rec_c_dom_def by simp
    ultimately show ?thesis using Query unfolding solve_rec_c_dom_def by auto
  qed
next
  case (Iterate x c \<sigma>)
  obtain d1 \<sigma>1 where eval: "eval x (T x) c \<sigma> = (d1, \<sigma>1)"
    and "solve_rec_c (E (x, T x, c, \<sigma>)) = Some (d1, \<sigma>1)" using Iterate(2) solve_rec_c_dom_def by force
  show ?case
  proof (cases "d1 = mlup \<sigma>1 x")
    case True
    have "iterate x c \<sigma> = (d1, \<sigma>1)"
      using eval iterate.psimps[folded dom_defs, OF Iterate(1)] True by simp
    then show ?thesis
      using solve_rec_c_dom_def dom_defs iterate.psimps Iterate by fastforce
  next
    case False
    then have "solve_rec_c_dom (I (x, c, \<sigma>1(x \<mapsto> d1)))"
        and "iterate x c (\<sigma>1(x \<mapsto> d1)) = the (solve_rec_c (I (x, c, \<sigma>1(x \<mapsto> d1))))"
      using Iterate(3)[OF eval[symmetric] _ False] by blast+
    moreover have "iterate x c \<sigma> = iterate x c (\<sigma>1(x \<mapsto> d1))"
      using eval iterate.psimps[folded dom_defs, OF Iterate(1)] False by simp
    moreover have "solve_rec_c (I (x, c, \<sigma>1(x \<mapsto> d1))) = solve_rec_c (I (x, c, \<sigma>))"
      using False eval Iterate(2) solve_rec_c_dom_def by auto
    ultimately show ?thesis unfolding solve_rec_c_dom_def by auto
  qed
next
  case (Eval x t c \<sigma>)
  show ?case
  proof (cases t)
    case (Answer d)
    then have "eval x t c \<sigma> = (d, \<sigma>)"
      using eval.psimps query_iterate_eval.domintros(3) dom_defs(3)
      by fastforce
    then show ?thesis using Eval Answer unfolding solve_rec_c_dom_def by simp
  next
    case (Query y g)
    then obtain d1 \<sigma>1 where "solve_rec_c (Q (x, y, c, \<sigma>)) = Some (d1, \<sigma>1)"
        and "query x y c \<sigma> = (d1, \<sigma>1)"
      using Query Eval(2) unfolding solve_rec_c_dom_def by auto
    then have "solve_rec_c_dom (E (x, t, c, \<sigma>))"
        "eval x (g d1) c \<sigma>1 = the (solve_rec_c (E (x, t, c, \<sigma>)))"
      using Eval(3) Query unfolding solve_rec_c_dom_def by auto
    moreover have "eval x t c \<sigma> = eval x (g d1) c \<sigma>1"
      using Eval.IH(1) Query eval.psimps eval_dom_def
        \<open>query x y c \<sigma> = (d1, \<sigma>1)\<close>
      by fastforce
    ultimately show ?thesis by simp
  qed
qed

lemma solve_rec_c_query_iterate_eval_equiv:
  shows "solve_rec_c s = Some r \<Longrightarrow> (case s of
        Q (x,y,c,\<sigma>) \<Rightarrow> query_dom x y c \<sigma> \<and> query x y c \<sigma> = r
      | I (x,c,\<sigma>) \<Rightarrow> iterate_dom x c \<sigma> \<and> iterate x c \<sigma> = r
      | E (x,t,c,\<sigma>) \<Rightarrow> eval_dom x t c \<sigma> \<and> eval x t c \<sigma> = r)"
proof (induction arbitrary: s r rule: solve_rec_c.fixp_induct)
  case 1
  then show ?case using option_admissible by fast
next
  case 2
  then show ?case by simp
next
  case (3 S)
  show ?case
  proof (cases s)
    case (Q a)
    obtain x y c \<sigma> where "a = (x, y, c, \<sigma>)" using prod_cases4 by blast
    have "query_dom x y c \<sigma> \<and> query x y c \<sigma> = r"
    proof (cases "y \<in> c")
      case True
      then have "Some (mlup \<sigma> y, \<sigma>) = Some r" using 3(2) Q \<open>a = (x, y, c, \<sigma>)\<close> by simp
      then show ?thesis
        by (metis query.psimps query_dom_def
            query_iterate_eval.domintros(1) True option.inject)
    next
      case False
      then have "S (I (y, insert y c, \<sigma>)) = Some r"
        using 3(2) Q \<open>a = (x, y, c, \<sigma>)\<close> by auto
      then have "iterate_dom y (insert y c) \<sigma> \<and> iterate y (insert y c) \<sigma> = r"
        using 3(1) unfolding iterate_dom_def by fastforce
      then show ?thesis using False
        by (simp add: query_iterate_eval.domintros(1))
    qed
    then show ?thesis using Q \<open>a = (x, y, c, \<sigma>)\<close> unfolding query_dom_def by simp
  next
    case (I a)
    obtain x c \<sigma> where "a = (x, c, \<sigma>)" using prod_cases3 by blast
    then have IH1: "Option.bind (S (E (x, T x, c, \<sigma>)))
       (\<lambda>(d_new, \<sigma>).
         if d_new = mlup \<sigma> x then Some (d_new, \<sigma>)
         else S (I (x, c, \<sigma>(x \<mapsto> d_new)))) = Some r"
      using 3(2) I by simp
    then obtain d_new \<sigma>1 where eval_some: "S (E (x, T x, c, \<sigma>)) = Some (d_new, \<sigma>1)"
      using 3(2) I
      by (cases "S (E (x, T x, c, \<sigma>))") auto
    then have eval: "eval_dom x (T x) c \<sigma> \<and> eval x (T x) c \<sigma> = (d_new, \<sigma>1)"
      using 3(1) unfolding eval_dom_def by force
    have "iterate_dom x c \<sigma> \<and> iterate x c \<sigma> = r"
    proof (cases "d_new = mlup \<sigma>1 x")
      case True
      then show ?thesis
        using eval IH1 dom_defs(2) dom_defs(3) iterate.psimps
          query_iterate_eval.domintros(2) eval_some
        by fastforce
    next
      case False
      then have "S (I (x, c, \<sigma>1(x \<mapsto> d_new))) = Some r" using IH1 eval_some by simp
      then have "iterate_dom x c (\<sigma>1(x \<mapsto> d_new))
          \<and> iterate x c (\<sigma>1(x \<mapsto> d_new)) = r"
        using 3(1) unfolding iterate_dom_def by fastforce
      then show ?thesis using eval False
        by (smt (verit, best) Pair_inject dom_defs(2) dom_defs(3)
            iterate.psimps query_iterate_eval.domintros(2) case_prod_conv)
    qed
    then show ?thesis using I \<open>a = (x, c, \<sigma>)\<close> unfolding iterate_dom_def by simp
  next
    case (E a)
    obtain x t c \<sigma> where "a = (x, t, c, \<sigma>)" using prod_cases4 by blast
    then have "s = E (x, t, c, \<sigma>)" using E by auto
    have "eval_dom x t c \<sigma> \<and> eval x t c \<sigma> = r"
    proof (cases t)
      case (Answer d)
      then have "eval_dom x t c \<sigma>" unfolding eval_dom_def
        using query_iterate_eval.domintros(3) by fastforce
      moreover have "eval x t c \<sigma> = (d, \<sigma>)"
        by (smt (verit, del_insts) Answer eval_query_answer_cases calculation
            strategy_tree.distinct(1) strategy_tree.simps(1) surj_pair)
      moreover have "(d, \<sigma>) = r" using 3(2) \<open>s = E (x, t, c, \<sigma>)\<close> Answer by simp
      ultimately show ?thesis by simp
    next
      case (Query y g)
      then have A: "Option.bind (S (Q (x, y, c, \<sigma>))) (\<lambda>(yd, \<sigma>). S (E (x, g yd, c, \<sigma>)))
        = Some r" using \<open>s = E (x, t, c, \<sigma>)\<close> 3(2) by simp
      then obtain yd \<sigma>1 where S1: "S (Q (x, y, c, \<sigma>)) = Some (yd, \<sigma>1)"
          and S2: "S (E (x, g yd, c, \<sigma>1)) = Some r"
        by (cases "S (Q (x, y, c, \<sigma>))") auto
      then have "query_dom x y c \<sigma> \<and> query x y c \<sigma> = (yd, \<sigma>1)"
          and "eval_dom x (g yd) c \<sigma>1 \<and> eval x (g yd) c \<sigma>1 = r"
        using 3(1)[OF S1] 3(1)[OF S2] unfolding dom_defs by force+
      then show ?thesis
        using query_iterate_eval.domintros(3)[folded dom_defs, of t x c \<sigma>] Query
        by fastforce
    qed
    then show ?thesis using E \<open>a = (x, t, c, \<sigma>)\<close> unfolding eval_dom_def by simp
  qed
qed

theorem term_equivalence: "solve_dom x \<longleftrightarrow> solve_c_dom x"
  using query_iterate_eval_solve_rec_c_equiv(2)[of x "{x}" "\<lambda>x. None"]
    solve_rec_c_query_iterate_eval_equiv[of "I (x, {x}, \<lambda>x. None)"]
  unfolding solve_dom_def solve_c_dom_def solve_rec_c_dom_def solve_c_def
  by (cases "solve_rec_c (I (x, {x}, \<lambda>x. None))") force+

theorem value_equivalence:
  "solve_dom x \<Longrightarrow> \<exists>\<sigma>. solve_c x = Some \<sigma> \<and> solve x = \<sigma>"
proof goal_cases
  case 1
  then obtain r where "solve_rec_c (I (x, {x}, \<lambda>x. None)) = Some r
    \<and> iterate x {x} (\<lambda>x. None) = r"
    using query_iterate_eval_solve_rec_c_equiv(2)
    unfolding solve_rec_c_dom_def solve_dom_def
    by fastforce
  then show ?case unfolding solve_def solve_c_def by (auto split: prod.split)
qed

text\<open>Then, we can define the code equation for @{term solve} based on the refined solver program
  @{term solve_c}.\<close>

lemma solve_code_equation [code]:
  "solve x = (case solve_c x of Some r \<Rightarrow> r
  | None \<Rightarrow> Code.abort (String.implode ''Input not in domain'') (\<lambda>_. solve x))"
proof (cases "solve_dom x")
  case True
  then show ?thesis unfolding solve_def solve_c_def
    by (metis solve_def solve_c_def option.simps(5) value_equivalence)
next
  case False
  then have "solve_c x = None" using solve_c_dom_def term_equivalence by auto
  then show ?thesis by auto
qed

end

text\<open>To setup the code generation for the solver locale we use a dedicated rewrite definition.\<close>

global_interpretation TD_plain_Interp: TD_plain D T for D T
  defines TD_plain_Interp_solve = TD_plain_Interp.solve
  done

end
