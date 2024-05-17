section \<open>The Top-Down Solver\<close>

text \<open>\label{sec:td}\<close>

text\<open>In this theory we proof the partial correctness of the original TD by establishing its
  equivalence with the TD\_plain. Compared to the TD\_plain, it additionally tracks a set of
  currently stable unknowns @{term stabl}, and a map @{term infl} collecting for each unknown
  @{term x} a list of unknowns influenced by it. This allows for the optimization that skips the
  re-evaluation of unknowns which are already stable. It does, however, also require a
  destabilization mechanism triggering re-evaluation of all unknowns possibly affected by an unknown
  whose value has changed.
\<close>

theory TD_equiv
  imports Main "HOL-Library.Finite_Map" Basics TD_plain
begin

declare fun_upd_apply[simp del]

locale TD = Solver D T
  for D :: "'d::bot"
    and T :: "'x \<Rightarrow> ('x, 'd) strategy_tree"
begin

subsection \<open>Definition of Destabilize and Proof of its Termination\<close>

text\<open>The destabilization function is called by the solver before continuing iteration because the
  value of an unknown changed. In this case, also the values of unknowns whose last evaluation was
  based on the outdated value, need to be re-evaluated again. This re-evaluation of influenced
  unknowns is enforced by following the entries for directly influenced unknowns in the map
  @{term infl} and removing all transitively influenced unknowns from @{term stabl}. This way,
  influenced unknowns are not re-evaluated immediately, but instead will be re-evaluated whenever
  they are queried again.\<close>

function (domintros)
destab_iter :: "'x list \<Rightarrow> ('x, 'x list) fmap \<Rightarrow> 'x set \<Rightarrow> ('x, 'x list) fmap \<times> 'x set"
and destab :: "'x \<Rightarrow> ('x, 'x list) fmap \<Rightarrow> 'x set \<Rightarrow> ('x, 'x list) fmap \<times> 'x set" where
  "destab_iter [] infl stabl = (infl, stabl)"
| "destab_iter (y # ys) infl stabl = (
    let (infl, stabl) = destab y infl (stabl - {y}) in
    destab_iter ys infl stabl)"
| "destab x infl stabl = destab_iter (fmlookup_default infl [] x) (fmdrop x infl) stabl"
  by pat_completeness auto

definition destab_iter_dom where
  "destab_iter_dom ls infl stabl = destab_iter_destab_dom (Inl (ls, infl, stabl))"
declare destab_iter_dom_def[simp]

definition destab_dom where
  "destab_dom y infl stabl = destab_iter_destab_dom (Inr (y, infl, stabl))"
declare destab_dom_def[simp]

lemma destab_domintros:
  "destab_iter_dom [] infl stabl"
  "destab_dom y infl (stabl - {y}) \<Longrightarrow>
    destab y infl (stabl - {y}) = (infl', stabl') \<Longrightarrow>
    destab_iter_dom ys infl' stabl' \<Longrightarrow>
    destab_iter_dom (y # ys) infl stabl"
  "destab_iter_dom (fmlookup_default infl [] x) (fmdrop x infl) stabl \<Longrightarrow> destab_dom x infl stabl"
  using destab_iter_destab.domintros by auto

definition count_non_empty :: "('a, 'b list) fmap \<Rightarrow> nat" where
  "count_non_empty m = fcard (ffilter ((\<noteq>) [] \<circ> snd) (fset_of_fmap m))"

lemma count_non_empty_dec_fmdrop:
  assumes "fmlookup_default m [] x \<noteq> []"
  shows "Suc (count_non_empty (fmdrop x m)) = count_non_empty m"
proof -
  obtain ys where ys_def: "ys = fmlookup_default m [] x" and ys_non_empty: "ys \<noteq> []"
    using assms by simp
  then have in_map: "(x, ys) |\<in>| fset_of_fmap m"
    unfolding fmlookup_default_def
    by (cases "fmlookup m x"; auto)
  then have eq: "fset_of_fmap (fmdrop x m) = fset_of_fmap m |-| {|(x, ys)|}"
    by (auto split: if_splits)
  then have "ffilter ((\<noteq>) [] \<circ> snd) (fset_of_fmap (fmdrop x m))
      = (ffilter ((\<noteq>) [] \<circ> snd) (fset_of_fmap m)) |-| {|(x, ys)|}" by fastforce
  then show ?thesis
    unfolding count_non_empty_def
    using in_map ys_non_empty fcard_Suc_fminus1[of "(x, ys)"]
    by auto
qed

lemma count_non_empty_eq_fmdrop:
  assumes "fmlookup_default m [] x = []"
  shows "count_non_empty (fmdrop x m) = count_non_empty m"
proof -
  have "ffilter ((\<noteq>) [] \<circ> snd) (fset_of_fmap (fmdrop x m))
      = (ffilter ((\<noteq>) [] \<circ> snd) (fset_of_fmap m))"
    using assms
    unfolding fmlookup_default_def
    by (auto split: if_splits)
  thus ?thesis unfolding count_non_empty_def by simp
qed

termination
proof -
  {
    fix ys infl stabl
    have "destab_iter_dom ys infl stabl \<and> (destab_iter ys infl stabl = (infl', stabl')
        \<longrightarrow> count_non_empty infl' \<le> count_non_empty infl)"
      for infl' stabl'
    proof(induction "count_non_empty infl" arbitrary: ys infl stabl infl' stabl'
        rule: full_nat_induct)
      case 1
      then show ?case
      proof(induction ys arbitrary: infl stabl)
        case Nil
        then show ?case
          by (simp add: destab_iter.psimps(1) destab_iter_destab.domintros(1))
      next
        case (Cons y ys)
        have IH: "destab_iter_dom xa x xb \<and>
            (destab_iter xa x xb = (xc, xd) \<longrightarrow> count_non_empty xc \<le> count_non_empty x)"
          if "Suc m \<le> count_non_empty infl" and "m = count_non_empty x"
          for m x xa xb xc xd
        using Cons.prems that by blast
        show ?case
        proof(cases "fmlookup_default infl [] y = []")
          case True
          obtain infl1 stabl1 where inflstabl1: "destab y infl (stabl - {y}) = (infl1, stabl1)"
            by fastforce
          have y_dom: "destab_dom y infl (stabl - {y})"
            using destab_domintros(1,3) True
            by auto
          have destab_y: "destab y infl (stabl - {y}) = (fmdrop y infl, stabl - {y})"
            using destab.psimps[folded destab_dom_def, OF y_dom]
              destab_iter.psimps(1)[OF destab_iter_destab.domintros(1)] True
            by auto
          have count_eq: "count_non_empty (fmdrop y infl) = count_non_empty infl"
            using count_non_empty_eq_fmdrop[of infl y] True by auto
          then have IH: "destab_iter_dom ys (fmdrop y infl) (stabl - {y})
              \<and> (destab_iter ys (fmdrop y infl) (stabl - {y}) = (infl', stabl')
              \<longrightarrow> count_non_empty infl' \<le> count_non_empty (fmdrop y infl))"
            using Cons.IH[of "fmdrop y infl" "stabl - {y}"] Cons.prems
            by auto
          then show ?thesis
          proof (intro conjI, goal_cases)
            case 1
            then show dom_ys: ?case using destab_domintros(2)[OF y_dom destab_y] IH by auto
            case 2
            then show ?case
              using IH count_eq destab_iter.psimps(2) destab_y dom_ys
              by auto
          qed
        next
          case False
          obtain u w where
            prod: "destab_iter (fmlookup_default infl [] y) (fmdrop y infl) (stabl - {y}) = (u, w)"
            by fastforce

          have eq: "Suc (count_non_empty (fmdrop y infl)) = count_non_empty infl"
            by (simp add: False count_non_empty_dec_fmdrop)
          then have dom1: "destab_dom y infl (stabl - {y})"
            using IH destab_domintros(3) by auto
          obtain i s where i_s_def: "(i, s) = destab y infl (stabl - {y})"
            by (metis surj_pair)

          have "count_non_empty u \<le> count_non_empty (fmdrop y infl)"
            using IH eq prod
            by simp
          then have dom2: "destab_iter_dom ys i s" and dec: "destab_iter ys u w = (infl', stabl')
              \<longrightarrow> count_non_empty infl' \<le> count_non_empty infl"
            using IH[of "count_non_empty u" u ys w infl' stabl'] prod eq i_s_def destab.psimps dom1
            by auto

          show ?thesis
            using destab_iter.psimps(2) dec destab_iter_destab.domintros(2) dom1 dom2 prod
            by (simp add: destab.psimps i_s_def)
        qed
      qed
    qed
  }
  then show ?thesis using destab_iter_destab.domintros(3) unfolding destab_iter_dom_def
    by (metis prod.collapse sumE)
qed

subsection\<open>Definition of the Solver Algorithm\<close>

text\<open>Apart from passing the additional arguments for the solver state, the @{term iterate} function
  contains, compared to the TD\_plain, an additional check to skip iteration of already stable
  unknowns. Furthermore, the helper function @{term destabilize} is called whenever the newly
  evalauated value of an unknown changed compared to the value tracked in @{term \<sigma>}. Lastly, a
  dependency is recorded whenever returning from a @{term query} call for unknown  @{term x} within
  the evaluation of right-hand side of unknown @{term y}.\<close>

function (domintros)
    query :: "'x \<Rightarrow> 'x \<Rightarrow> 'x set \<Rightarrow> ('x, 'x list) fmap \<Rightarrow> 'x set \<Rightarrow> ('x, 'd) map
              \<Rightarrow> 'd \<times> ('x, 'x list) fmap \<times> 'x set \<times> ('x, 'd) map" and
  iterate :: "'x \<Rightarrow> 'x set \<Rightarrow> ('x, 'x list) fmap \<Rightarrow> 'x set \<Rightarrow> ('x, 'd) map
              \<Rightarrow> 'd \<times> ('x, 'x list) fmap \<times> 'x set \<times> ('x, 'd) map" and
     eval :: "'x \<Rightarrow> ('x, 'd) strategy_tree \<Rightarrow> 'x set \<Rightarrow> ('x, 'x list) fmap \<Rightarrow> 'x set
              \<Rightarrow> ('x, 'd) map \<Rightarrow> 'd \<times> ('x, 'x list) fmap \<times> 'x set \<times> ('x, 'd) map" where
  "query y x c infl stabl \<sigma> = (
    let (xd, infl, stabl, \<sigma>) =
      if x \<in> c then
        (mlup \<sigma> x, infl, stabl, \<sigma>)
      else
        iterate x (insert x c) infl stabl \<sigma>
    in (xd, fminsert infl x y, stabl, \<sigma>))"
| "iterate x c infl stabl \<sigma> = (
    if x \<notin> stabl then
      let (d_new, infl, stabl, \<sigma>) = eval x (T x) c infl (insert x stabl) \<sigma> in
      if mlup \<sigma> x = d_new then
        (d_new, infl, stabl, \<sigma>)
      else
        let (infl, stabl) = destab x infl stabl in
        iterate x c infl stabl (\<sigma>(x \<mapsto> d_new))
    else
      (mlup \<sigma> x, infl, stabl, \<sigma>))"
| "eval x t c infl stabl \<sigma> = (case t of
      Answer d \<Rightarrow> (d, infl, stabl, \<sigma>)
    | Query y g \<Rightarrow> (
        let (yd, infl, stabl, \<sigma>) = query x y c infl stabl \<sigma> in eval x (g yd) c infl stabl \<sigma>))"
  by pat_completeness auto

definition solve :: "'x \<Rightarrow> 'x set \<times> ('x, 'd) map" where
  "solve x = (let (_, _, stabl, \<sigma>) = iterate x {x} fmempty {} Map.empty in (stabl, \<sigma>))"

definition query_dom where
  "query_dom x y c infl stabl \<sigma> = query_iterate_eval_dom (Inl (x, y, c, infl, stabl, \<sigma>))"
declare query_dom_def [simp]
definition iterate_dom where
  "iterate_dom x c infl stabl \<sigma> = query_iterate_eval_dom (Inr (Inl (x, c, infl, stabl, \<sigma>)))"
declare iterate_dom_def [simp]
definition eval_dom where
  "eval_dom x t c infl stabl \<sigma> = query_iterate_eval_dom (Inr (Inr (x, t, c, infl, stabl, \<sigma>)))"
declare eval_dom_def [simp]

definition solve_dom where
  "solve_dom x = iterate_dom x {x} fmempty {} Map.empty"

lemmas dom_defs = query_dom_def iterate_dom_def eval_dom_def


subsection \<open>Refinement of Auto-Generated Rules\<close>

text \<open>The auto-generated \texttt{pinduct} rule contains a redundant assumption. This lemma removes
this redundant assumption such that the rule is easier to instantiate and gives comprehensible
names to the cases.\<close>

lemmas query_iterate_eval_pinduct[consumes 1, case_names Query Iterate Eval]
  = query_iterate_eval.pinduct(1)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x y c infl stabl \<sigma> for x y c infl stabl \<sigma>
    ]
    query_iterate_eval.pinduct(2)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x c infl stabl \<sigma> for x c infl stabl \<sigma>
    ]
    query_iterate_eval.pinduct(3)[
      folded query_dom_def iterate_dom_def eval_dom_def,
      of x t c infl stabl \<sigma> for x t c infl stabl \<sigma>
    ]

lemmas iterate_pinduct[consumes 1, case_names Iterate]
  = query_iterate_eval_pinduct(2)[where ?P="\<lambda>x y c infl stabl \<sigma>. True"
    and ?R="\<lambda>x t c infl stabl \<sigma>. True", simplified (no_asm_use),
    folded query_dom_def iterate_dom_def eval_dom_def]

declare query.psimps [simp]
declare iterate.psimps [simp]
declare eval.psimps [simp]

subsection \<open>Domain Lemmas\<close>

lemma dom_backwards_pinduct:
  shows "query_dom x y c infl stabl \<sigma>
    \<Longrightarrow> y \<notin> c \<Longrightarrow> iterate_dom y (insert y c) infl stabl \<sigma>"
  and "iterate_dom x c infl stabl \<sigma>
    \<Longrightarrow> x \<notin> stabl \<Longrightarrow> (eval_dom x (T x) c infl (insert x stabl) \<sigma> \<and>
        ((xd_new, infl1, stabl1, \<sigma>') = eval x (T x) c infl (insert x stabl) \<sigma>
          \<longrightarrow> mlup \<sigma>' x \<noteq> xd_new \<longrightarrow> (infl2, stabl2) = destab x infl1 stabl1 \<longrightarrow>
          iterate_dom x c infl2 stabl2 (\<sigma>'(x \<mapsto> xd_new))))"
  and "eval_dom x (Query y g) c infl stabl \<sigma>
    \<Longrightarrow> (query_dom x y c infl stabl \<sigma> \<and>
        ((yd, infl', stabl', \<sigma>') = query x y c infl stabl \<sigma> \<longrightarrow>
          eval_dom x (g yd) c infl' stabl' \<sigma>'))"
proof (induction x y c infl stabl \<sigma> and x c infl stabl \<sigma> and x "Query y g" c infl stabl \<sigma>
    arbitrary: and xd_new infl1 stabl1 infl2 stabl2 \<sigma>' and y g yd infl' stabl' \<sigma>'
    rule: query_iterate_eval_pinduct)
  case (Query y x c infl stabl \<sigma>)
  then show ?case using query_iterate_eval.domintros(2) by fastforce
next
  case (Iterate x c infl stabl \<sigma>)
  then show ?case using query_iterate_eval.domintros(2,3) by simp
next
  case (Eval x c infl stabl \<sigma>)
  then show ?case using query_iterate_eval.domintros(1,3) by simp
qed

subsection \<open>Case Rules\<close>

lemma iterate_continue_fixpoint_cases[consumes 3]:
  assumes "iterate_dom x c infl stabl \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = iterate x c infl stabl \<sigma>"
    and "x \<in> c"
  obtains (Stable) "infl' = infl"
    and "stabl' = stabl"
    and "\<sigma>' = \<sigma>"
    and "mlup \<sigma> x = xd"
    and "x \<in> stabl"
  | (Fixpoint) "eval_dom x (T x) c infl (insert x stabl) \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = eval x (T x) c infl (insert x stabl) \<sigma>"
    and "mlup \<sigma>' x = xd"
    and "x \<notin> stabl"
  | (Continue) stabl1 infl1 \<sigma>1 xd_new stabl2 infl2
  where "eval_dom x (T x) c infl (insert x stabl) \<sigma>"
    and "(xd_new, infl1, stabl1, \<sigma>1) = eval x (T x) c infl (insert x stabl) \<sigma>"
    and "mlup \<sigma>1 x \<noteq> xd_new"
    and "(infl2, stabl2) = destab x infl1 stabl1"
    and "iterate_dom x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd_new))"
    and "(xd, infl', stabl', \<sigma>') = iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd_new))"
    and "x \<notin> stabl"
proof(cases "x \<in> stabl" rule: case_split[case_names Stable Unstable])
  case Stable
  then show ?thesis using that(1) assms by auto
next
  case Unstable
  then have sldom: "eval_dom x (T x) c infl (insert x stabl) \<sigma>"
    using assms(1) dom_backwards_pinduct(2)
    by simp
  then obtain xd_new infl1 stabl1 \<sigma>1
    where slapp: "eval x (T x) c infl (insert x stabl) \<sigma> = (xd_new, infl1, stabl1, \<sigma>1)"
    by (cases "eval x (T x) c infl (insert x stabl) \<sigma>") auto
  show ?thesis
  proof (cases "mlup \<sigma>1 x = xd_new")
    case True
    then show ?thesis
      using Unstable sldom slapp assms that(2)
      by auto
  next
    case False
    then obtain infl2 stabl2 where destab: "destab x infl1 stabl1 = (infl2, stabl2)"
      by (cases "destab x infl1 stabl1")
    then have dom: "iterate_dom x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd_new))"
      and "iterate x c infl stabl \<sigma>
        = iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd_new))"
      and app: "iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd_new))
        = (xd, infl', stabl', \<sigma>')"
      using Unstable False slapp assms(1-3) dom_backwards_pinduct(2)
      by auto
    then show ?thesis
      using sldom slapp Unstable False destab that(3)
      by simp
  qed
qed

lemma iterate_fmlookup:
  assumes "iterate_dom x c infl stabl \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = iterate x c infl stabl \<sigma>"
    and "x \<in> c"
  shows "mlup \<sigma>' x = xd"
  using assms
proof(induction rule: iterate_pinduct)
  case (Iterate x c infl stabl \<sigma>)
  show ?case
    using Iterate.hyps Iterate.prems
  proof(cases rule: iterate_continue_fixpoint_cases)
    case (Continue \<sigma>1 xd_new)
    then show ?thesis
      using Iterate.prems(2) Iterate.IH
      by force
  qed (simp add: Iterate.prems(1))
qed

corollary query_fmlookup:
  assumes "query_dom y x c infl stabl \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = query y x c infl stabl \<sigma>"
  shows "mlup \<sigma>' x = xd"
  using assms iterate_fmlookup dom_backwards_pinduct(1)[of y x c infl stabl \<sigma>]
  by (auto split: prod.splits if_splits)

lemma query_iterate_lookup_cases [consumes 2]:
  assumes "query_dom y x c infl stabl \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = query y x c infl stabl \<sigma>"
  obtains (Iterate) infl1
  where "iterate_dom x (insert x c) infl stabl \<sigma>"
    and "(xd, infl1, stabl', \<sigma>') = iterate x (insert x c) infl stabl \<sigma>"
    and "infl' = fminsert infl1 x y"
    and "mlup \<sigma>' x = xd"
    and "x \<notin> c"
  | (Lookup) "mlup \<sigma> x = xd"
    and "infl' = fminsert infl x y"
    and "stabl' = stabl"
    and "\<sigma>' = \<sigma>"
    and "x \<in> c"
  using assms that dom_backwards_pinduct(1) query_fmlookup[OF assms(1,2)]
  by (cases "x \<in> c"; auto split: prod.splits)

lemma eval_query_answer_cases [consumes 2]:
  assumes "eval_dom x t c infl stabl \<sigma>"
    and "(xd, infl', stabl', \<sigma>') = eval x t c infl stabl \<sigma>"
  obtains (Query) y g yd infl1 stabl1 \<sigma>1
  where "t = Query y g"
    and "query_dom x y c infl stabl \<sigma>"
    and "(yd, infl1, stabl1, \<sigma>1) = query x y c infl stabl \<sigma>"
    and "eval_dom x (g yd) c infl1 stabl1 \<sigma>1"
    and "(xd, infl', stabl', \<sigma>') = eval x (g yd) c infl1 stabl1 \<sigma>1"
    and "mlup \<sigma>1 y = yd"
  | (Answer) "t = Answer xd"
    and "infl' = infl"
    and "stabl' = stabl"
    and "\<sigma>' = \<sigma>"
  using assms dom_backwards_pinduct(3) that query_fmlookup
  by (cases t; auto split: prod.splits)

subsection \<open>Description of the Effect of Destabilize\<close>

text\<open>To describe the effect of a call to the function @{term destab}, we define an inductive
  set that, based on some @{term infl} map, collects all unknowns transitively influenced by some
  unknown @{term x}.\<close>

inductive_set influenced_by for infl x where
  base: "fmlookup infl x = Some ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> y \<in> influenced_by infl x"
| step: "y \<in> influenced_by infl x \<Longrightarrow> fmlookup infl y = Some zs \<Longrightarrow> z \<in> set zs
    \<Longrightarrow> z \<in> influenced_by infl x"
inductive_set influenced_by_cutoff for infl x c where
  base: "x \<notin> c \<Longrightarrow> fmlookup infl x = Some ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> y \<in> influenced_by_cutoff infl x c"
| step: "y \<in> influenced_by_cutoff infl x c \<Longrightarrow> y \<notin> c \<Longrightarrow> fmlookup infl y = Some zs \<Longrightarrow> z \<in> set zs
    \<Longrightarrow> z \<in> influenced_by_cutoff infl x c"

lemma influenced_by_aux:
  shows "influenced_by infl x = (\<Union>y \<in> slookup infl x. insert y (influenced_by (fmdrop x infl) y))"
unfolding fmlookup_default_def
proof(intro equalityI subsetI, goal_cases)
  case (1 u)
  then show ?case
  proof(induction rule: influenced_by.induct)
    case (step y zs z)
    then show ?case
    proof(cases "y \<in> slookup infl x")
      case True
      then show ?thesis
        using step.hyps(2,3) influenced_by.base[of "fmdrop x infl" y]
        by (cases rule: set_fmlookup_default_cases, cases "x = y") auto
    next
      case False
      then show ?thesis
        using step.IH step.hyps(2,3) influenced_by.step[of y "fmdrop x infl"]
        by (cases rule: notin_fmlookup_default_cases, cases "x = y") auto
    qed
  qed auto
next
  case (2 z)
  then show ?case
  proof(cases "fmlookup infl x")
    case (Some xs)
    then obtain y where z_mem: "z \<in> insert y (influenced_by (fmdrop x infl) y)"
      and step: "y \<in> set (case fmlookup infl x of None \<Rightarrow> [] | Some v \<Rightarrow> v)" using 2 by blast
    then show ?thesis using Some influenced_by.base
    proof(cases "z = y")
      case False
      then have "z \<in> influenced_by (fmdrop x infl) y" using z_mem by auto
      then show ?thesis
      proof(induction rule: influenced_by.induct)
        case (base ys' y')
        then show ?case
          using Some step influenced_by.base[of infl] influenced_by.step[of y]
          by (auto split: if_splits)
      next
        case (step y' zs z)
        then show ?case using influenced_by.step
          by (auto split: if_splits)
      qed
    qed simp
  qed simp
qed

lemma lookup_in_influenced:
  shows "slookup infl x \<subseteq> influenced_by infl x"
proof(intro subsetI, goal_cases)
  case (1 y)
  then show ?case using influenced_by.base[of infl x]
  by (cases rule: set_fmlookup_default_cases) simp
qed

lemma influenced_unknowns_fmdrop_set:
  shows "influenced_by (fmdrop_set C infl) x = influenced_by_cutoff infl x C"
proof (intro equalityI subsetI, goal_cases)
  case (1 u) then show ?case by (induction rule: influenced_by.induct;
        simp add: influenced_by_cutoff.base influenced_by_cutoff.step split: if_splits)
next
  case (2 u) then show ?case by (induction rule: influenced_by_cutoff.induct;
        simp add: influenced_by.base influenced_by.step)
qed

lemma influenced_by_transitive:
  assumes "y \<in> influenced_by infl x"
    and "z \<in> influenced_by infl y"
  shows "z \<in> influenced_by infl x"
  using assms
proof (induction rule: influenced_by.induct)
  case (base ys y)
  show ?case using base(3,1,2) influenced_by.step[of _ infl x]
  proof (induction rule: influenced_by.induct)
    case (base us u)
    then show ?case using influenced_by.base[of infl x ys y] by simp
  qed simp
next
  case (step u vs v)
  have "z \<in> influenced_by infl u" using step(5,1-4)
  proof (induction rule: influenced_by.induct)
    case (base ys y)
    then show ?case using influenced_by.base[of infl] influenced_by.step[of v infl] by auto
  next
    case (step y zs z)
    then show ?case using influenced_by.step[of _ infl] by auto
  qed
  then show ?case using step by auto
qed

lemma influenced_cutoff_subset:
  "influenced_by_cutoff infl x C \<subseteq> influenced_by infl x"
proof (intro subsetI, goal_cases)
  case (1 y)
  then show ?case
    by (induction rule: influenced_by_cutoff.induct)
      (auto simp add: influenced_by.base influenced_by.step)
qed

lemma influenced_cutoff_subset_2:
  shows "influenced_by infl x - (\<Union>y \<in> C. influenced_by infl y) \<subseteq> influenced_by_cutoff infl x C"
proof (intro equalityI subsetI, elim DiffE, goal_cases)
  case (1 y)
  then show ?case
  proof (induction rule: influenced_by.induct)
    case (base ys z)
    then show ?case using 1 influenced_by_cutoff.base by fastforce
  next
    case (step y zs z)
    then show ?case
      using influenced_by.base[OF step(2,3)] influenced_by.step[of y infl]
        influenced_by_cutoff.step[of y infl x C zs z]
      by blast
  qed
qed

lemma union_influenced_to_cutoff:
  shows "insert y (influenced_by infl y) \<union> influenced_by infl x =
    insert y (influenced_by infl y) \<union> influenced_by_cutoff infl x (insert y (influenced_by infl y))"
proof -
  have "u \<in> influenced_by infl y"
    if "u \<noteq> y" and "u \<notin> influenced_by_cutoff infl x (insert y (influenced_by infl y))"
      and "u \<in> influenced_by infl x" for u
    using that influenced_cutoff_subset_2[of infl x "insert y (influenced_by infl y)"]
      influenced_by_transitive[of _ infl y] by auto
  moreover have "u \<in> influenced_by infl y"
    if "u \<noteq> y" and "u \<notin> influenced_by infl x"
      and "u \<in> influenced_by_cutoff infl x (insert y (influenced_by infl y))" for u
    using that(3)
  proof (induction rule: influenced_by_cutoff.induct)
    case (base ys y)
    then show ?case using that(2,3) influenced_cutoff_subset[of infl x] by auto
  qed simp
  ultimately show ?thesis by auto
qed

lemma destab_iter_infl_stabl_relation:
  shows
    "(infl', stabl') = destab_iter xs infl stabl
    \<Longrightarrow> infl' = fmdrop_set (\<Union>x \<in> set xs. insert x (influenced_by infl x)) infl
    \<and> stabl' = stabl - (\<Union>x \<in> set xs. insert x (influenced_by infl x))"
  and destab_infl_stabl_relation:
    "(infl', stabl') = destab x infl stabl
    \<Longrightarrow> infl' = fmdrop_set (insert x (influenced_by infl x)) infl
    \<and> stabl' = stabl - influenced_by infl x"
proof (induction xs infl stabl and x infl stabl
    arbitrary: infl' stabl' and infl' stabl' rule: destab_iter_destab.induct)
  case (1 infl stabl)
  then show ?case by simp
next
  case (2 y ys infl stabl)
  then obtain infl'' stabl'' where destab_y: "(infl'', stabl'') = destab y infl (stabl - {y})"
    and destab_ys: "(infl', stabl') = destab_iter ys infl'' stabl''"
    by (cases "destab y infl (stabl - {y})"; auto)
  note IH1 = "2.IH"(1)[OF destab_y]
  note IH2 = "2.IH"(2)[OF destab_y _ destab_ys, simplified]

  define A where "A x \<equiv> insert x (influenced_by infl x)" for x
  define B where "B x \<equiv> insert x (influenced_by_cutoff infl x (insert y (influenced_by infl y)))"
    for x
  have A_union_B_simp: "A y \<union> (\<Union>x\<in>set ys. B x) = (\<Union>x\<in>set (y#ys). A x)"
    using union_influenced_to_cutoff[of y] A_def B_def
    by fastforce

  show ?case
  proof(intro conjI, goal_cases)
    case 1
      have "infl' = fmdrop_set (\<Union>x\<in>set ys. B x) (fmdrop_set (A y) infl)"
        using IH1 IH2 influenced_unknowns_fmdrop_set[of "A y"] A_def B_def by auto
      also have "... = fmdrop_set (A y \<union> (\<Union>x\<in>set ys. B x)) infl"
        by (simp add: Un_commute)
      also have "... = fmdrop_set (\<Union>x\<in>set (y # ys). A x) infl"
        using A_union_B_simp by auto
      finally show ?case
        using A_def B_def by auto
  next
    case 2
    have "stabl' = stabl - (A y \<union> (\<Union>x\<in>set ys. B x))"
      using IH1 IH2 A_def B_def influenced_unknowns_fmdrop_set[of "A y"]
      by auto
    also have "... = stabl - (\<Union>x\<in>set (y#ys). A x)"
      using A_union_B_simp
      by auto
    finally show ?case
      using A_def B_def by auto
  qed
next
  case (3 y infl stabl)
  then have
    destab_y: "destab_iter (fmlookup_default infl [] y) (fmdrop y infl) stabl = (infl', stabl')"
    by simp
  note IH = "3.IH"[OF destab_y[symmetric]]
  then show ?case using influenced_by_aux[of infl] by simp
qed


subsection \<open>Predicate for Valid Input States\<close>

text\<open>For the TD, we extend the predicate of valid solver states of the TD\_plain, to also covers the
  additional data structures @{term stabl} and @{term infl}:\<close>

definition invariant where
  "invariant c \<sigma> infl stabl \<equiv>
    c \<subseteq> stabl
    \<and> part_solution \<sigma> (stabl - c)
    \<and> fset (fmdom infl) \<subseteq> stabl
    \<and> (\<forall>y\<in>stabl - c. \<forall>x \<in> dep \<sigma> y. y \<in> slookup infl x)"

lemma invariant_simp_c_stabl:
  assumes "x \<in> c"
    and "invariant (c - {x}) \<sigma> infl stabl"
  shows "invariant c \<sigma> infl (insert x stabl)"
  using assms
proof -
  have "c - {x} \<subseteq> stabl \<equiv> c \<subseteq> insert x stabl"
    using assms(1)
    by (simp add: subset_insert_iff)
  moreover have "stabl - (c - {x}) \<supseteq> insert x stabl - c"
    using assms(1)
    by auto
  ultimately show ?thesis
    using assms(2)
    unfolding invariant_def
    by (meson subset_iff subset_insertI2)
qed


subsection \<open>Auxiliary Lemmas for Partial Correctness Proofs\<close>

lemma stabl_infl_empty:
  assumes "x \<notin> stabl"
    and "fset (fmdom infl) \<subseteq> stabl"
  shows "slookup infl x = {}"
proof (rule ccontr, goal_cases)
  case 1
  then have "x \<in> fset (fmdom infl)"
    unfolding fmlookup_default_def by force
  then show ?case using assms by blast
qed

lemma dep_closed_implies_reach_cap_tree_closed:
  assumes "x \<in> stabl'"
    and "\<forall>\<xi>\<in>stabl' - (c - {x}). dep \<sigma>' \<xi> \<subseteq> stabl'"
  shows "reach_cap \<sigma>' (c - {x}) x \<subseteq> stabl'"
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

lemma dep_subset_stable:
  assumes "fset (fmdom infl) \<subseteq> stabl"
    and "(\<forall>y\<in>stabl - c. \<forall>x \<in> dep \<sigma> y. y \<in> slookup infl x)"
  shows "(\<forall>\<xi>\<in>stabl - c. dep \<sigma> \<xi> \<subseteq> stabl)"
  using assms stabl_infl_empty[of _ stabl infl]
  by (metis DiffD2 Diff_empty subsetI)

lemma new_lookup_to_infl_not_stabl:
  assumes "\<forall>\<xi>. (slookup infl1 \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
    and "x \<notin> stabl"
    and "fset (fmdom infl) \<subseteq> stabl"
  shows "influenced_by infl1 x \<inter> stabl = {}"
proof -
  have "u \<notin> stabl" if "u \<in> influenced_by infl1 x" for u
    using that
  proof (induction rule: influenced_by.induct)
    case (base ys y)
    have "slookup infl x = {}" using stabl_infl_empty[OF assms(2,3)] by auto
    then have "y \<in> slookup infl1 x - slookup infl x"
      using base.hyps(1,2) by auto
    then show ?case using base.hyps(1) assms(1,3) by force
  next
    case (step y zs z)
    have "slookup infl y = {}"
      by (meson assms(3) stabl_infl_empty step.IH)
    then have "z \<in> slookup infl1 y - slookup infl y"
      by (simp add: step.hyps(2,3))
    then show ?case using assms(1) stabl_infl_empty[OF _ assms(3)] by fastforce
  qed
  then show ?thesis by auto
qed

lemma infl_upd_diff:
  assumes "\<forall>\<xi>. (slookup infl' \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
  shows "\<forall>\<xi>. (slookup (fminsert infl' x y) \<xi> - slookup infl \<xi>) \<inter> (stabl - {y}) = {}"
proof(intro allI, goal_cases)
  case (1 \<xi>)
  show ?case using assms unfolding fminsert_def fmlookup_default_def
  by (cases "x = \<xi>") auto
qed

lemma infl_diff_eval_step:
  assumes "stabl \<subseteq> stabl1"
    and "\<forall>\<xi>. (slookup infl' \<xi> - slookup infl1 \<xi>) \<inter> (stabl1 - {x}) = {}"
    and "\<forall>\<xi>. (slookup infl1 \<xi> - slookup infl \<xi>) \<inter> (stabl - {x}) = {}"
  shows "\<forall>\<xi>. (slookup infl' \<xi> - slookup infl \<xi>) \<inter> (stabl - {x}) = {}"
proof(intro allI, goal_cases)
  case (1 \<xi>)
  have "((slookup infl' \<xi> - slookup infl1 \<xi>)
          \<union> (slookup infl1 \<xi> - slookup infl \<xi>)) \<inter> (stabl - {x}) = {}"
    using assms by auto
  then show ?case by blast
qed


subsection \<open>Preservation of the Invariant\<close>

text\<open>In this section, we prove that the destabilization of some unknown that is currently being
  iterated, will preserve the valid solver state invariant.\<close>

lemma destab_x_no_dep:
  assumes "stabl2 = stabl1 - influenced_by infl1 x"
    and "\<forall>y\<in>stabl1 - (c - {x}). \<forall>z\<in>dep \<sigma>1 y. y \<in> slookup infl1 z"
  shows "\<forall>y \<in> stabl2 - (c - {x}). x \<notin> dep \<sigma>1 y"
proof (intro ballI, goal_cases)
  case (1 y)
  show ?case
  proof (rule ccontr, goal_cases)
    case 1
    then have "y \<in> slookup infl1 x"
      using assms \<open>y \<in> stabl2 - (c - {x})\<close> by blast
    then have "y \<in> influenced_by infl1 x"
      using lookup_in_influenced by force
    moreover have "y \<notin> influenced_by infl1 x"
      using assms(1) \<open>y \<in> stabl2 - (c - {x})\<close> by fastforce
    ultimately show ?case by auto
  qed
qed

lemma destab_preserves_c_subset_stabl:
  assumes "c \<subseteq> stabl"
    and "stabl \<subseteq> stabl'"
  shows "c \<subseteq> stabl'"
  using assms by auto

lemma destab_preserves_infl_dom_stabl:
  assumes "(infl', stabl') = destab x infl stabl"
    and "fset (fmdom infl) \<subseteq> stabl"
  shows "fset (fmdom infl') \<subseteq> stabl'"
proof -
  have "infl' = fmdrop_set (insert x (influenced_by infl x)) infl"
    and A: "stabl' = stabl - influenced_by infl x"
    using assms(1) destab_infl_stabl_relation by metis+
  then show ?thesis
    using assms(2)
    by (metis Diff_mono fmdom'_alt_def fmdom'_drop_set subset_insertI)
qed

lemma destab_and_upd_preserves_dep_closed_in_infl:
  assumes "(infl2, stabl2) = destab x infl1 stabl1"
    and "(\<forall>y\<in>stabl1 - (c - {x}). \<forall>z\<in>dep \<sigma>1 y. y \<in> slookup infl1 z)"
  shows "(\<forall>y\<in>stabl2 - (c - {x}). \<forall>z\<in>dep (\<sigma>1(x \<mapsto> xd')) y. y \<in> slookup infl2 z)"
proof (intro ballI, goal_cases)
  case (1 z y)
  have infl2_def: "infl2 = fmdrop_set (insert x (influenced_by infl1 x)) infl1"
    and stabl2_def: "stabl2 = stabl1 - influenced_by infl1 x"
    using assms(1) destab_infl_stabl_relation by metis+

  have "y \<in> dep \<sigma>1 z"
  proof (goal_cases)
    case 1
    have "\<forall>y\<in>stabl2 - (c - {x}). x \<notin> dep \<sigma>1 y"
      using assms(2) stabl2_def destab_x_no_dep by auto
    then have "x \<notin> dep \<sigma>1 z"
        using \<open>z \<in> stabl2 - (c - {x})\<close> by blast
    then have "dep (\<sigma>1(x \<mapsto> xd')) z = dep \<sigma>1 z"
      using dep_eq[of \<sigma>1 z "\<sigma>1(x \<mapsto> xd')"] mlup_eq_mupd_set[of x "dep \<sigma>1 z" \<sigma>1 \<sigma>1 xd']
      by metis
    then show ?case using \<open>y \<in> dep (\<sigma>1(x \<mapsto> xd')) z\<close> by auto
  qed
  then have z_in_infl1_y: "z \<in> slookup infl1 y"
    using 1(1) stabl2_def assms(2) by fastforce

  have "z \<in> influenced_by infl1 y"
    using lookup_in_influenced[of infl1 y] z_in_infl1_y
    by auto
  then have "y \<notin> influenced_by infl1 x" and "y \<noteq> x"
    using stabl2_def 1(1) influenced_by_transitive[of y _ x z] by auto
  then show ?case
    using z_in_infl1_y fmlookup_drop_set infl2_def
    unfolding fmlookup_default_def
    by fastforce
qed

lemma destab_upd_preserves_part_sol:
  assumes "(infl2, stabl2) = destab x infl1 stabl1"
    and "part_solution \<sigma>1 (stabl1 - c)"
    and "\<forall>y\<in>stabl1 - (c - {x}). \<forall>x\<in>dep \<sigma>1 y. y \<in> slookup infl1 x"
    and "traverse_rhs (T x) \<sigma>1 = xd'"
  shows "part_solution (\<sigma>1(x \<mapsto> xd')) (stabl2 - (c - {x}))"
proof (intro ballI, goal_cases)
  case (1 y)
  have stabl2_def: "stabl2 = stabl1 - influenced_by infl1 x"
    using assms(1) destab_infl_stabl_relation by auto
  have x_no_dep: "\<forall>y \<in> stabl2 - (c - {x}). x \<notin> dep \<sigma>1 y"
    using destab_x_no_dep[OF stabl2_def assms(3)] by simp
  have eq_y_upd: "eq y (\<sigma>1(x \<mapsto> xd')) = eq y \<sigma>1"
    using 1 eq_mupd_no_dep[of x \<sigma>1 y] x_no_dep
    by auto
  show ?case
  proof (cases "y = x")
    case True
    then show ?thesis using assms(4) eq_y_upd unfolding mlup_def by (simp add: fun_upd_same)
  next
    case False
    then have "y \<in> stabl1 - c"
      using 1 stabl2_def by force
    then have "eq y \<sigma>1 = mlup \<sigma>1 y"
      using assms(2) by blast
    then show ?thesis using False eq_y_upd unfolding mlup_def by (simp add: fun_upd_other)
  qed
qed

subsection \<open>TD\_plain and TD Equivalence\<close>

text\<open>Finally, we can prove the equivalence of TD and TD\_plain. We split this proof into two parts:
  first we show that whenever the TD\_plain terminates the TD terminates as well and returns the
  same result, and second we show the other direction, i.e., whenever the TD terminates, the
  TD\_plain terminates as well and returns the same result.\<close>

declare TD_plain.query_dom_def[of T,simp]
declare TD_plain.eval_dom_def[of T,simp]
declare TD_plain.iterate_dom_def[of T,simp]
declare TD_plain.query.psimps[of T,simp]
declare TD_plain.iterate.psimps[of T,simp]
declare TD_plain.eval.psimps[of T,simp]

text\<open>To carry out the induction proof, we complement the valid solver state invariant, with a
  second predicate @{term update_rel}, that describes the relation between output and input solver
  states.\<close>

abbreviation "update_rel x infl stabl infl' stabl' \<equiv>
    stabl \<subseteq> stabl' \<and>
    (\<forall>u \<in> stabl. slookup infl u \<subseteq> slookup infl' u) \<and>
    (\<forall>u. (slookup infl' u - slookup infl u) \<inter> (stabl - {x}) = {})"

subsubsection \<open>TD\_plain \<open>\<rightarrow>\<close> TD\<close>

lemma TD_plain_TD_equivalence_ind:
  shows "TD_plain.query_dom T x y c \<sigma>
    \<Longrightarrow> TD_plain.query T x y c \<sigma> = (yd, \<sigma>')
    \<Longrightarrow> invariant c \<sigma> infl stabl
    \<Longrightarrow> query_dom x y c infl stabl \<sigma>
        \<and> (\<exists>infl' stabl'. query x y c infl stabl \<sigma> = (yd, infl', stabl', \<sigma>')
        \<and> invariant c \<sigma>' infl' stabl'
        \<and> x \<in> slookup infl' y
        \<and> update_rel x infl stabl infl' stabl')"
    and "TD_plain.iterate_dom T x c \<sigma>
    \<Longrightarrow> TD_plain.iterate T x c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> x \<in> c
    \<Longrightarrow> invariant (c - {x}) \<sigma> infl stabl
    \<Longrightarrow> iterate_dom x c infl stabl \<sigma>
        \<and> (\<exists>infl' stabl'. iterate x c infl stabl \<sigma> = (xd, infl', stabl', \<sigma>')
        \<and> invariant (c - {x}) \<sigma>' infl' stabl'
        \<and> x \<in> stabl'
        \<and> update_rel x infl stabl infl' stabl')"
    and "TD_plain.eval_dom T x t c \<sigma>
    \<Longrightarrow> TD_plain.eval T x t c \<sigma> = (xd, \<sigma>')
    \<Longrightarrow> invariant c \<sigma> infl stabl
    \<Longrightarrow> x \<in> stabl
    \<Longrightarrow> eval_dom x t c infl stabl \<sigma>
        \<and> (\<exists>infl' stabl'. eval x t c infl stabl \<sigma> = (xd, infl', stabl', \<sigma>')
        \<and> invariant c \<sigma>' infl' stabl'
        \<and> traverse_rhs t \<sigma>' = xd
        \<and> (\<forall>y\<in>dep_aux \<sigma>' t. x \<in> slookup infl' y)
        \<and> update_rel x infl stabl infl' stabl')"
proof(induction x y c \<sigma> and x c \<sigma> and x t c \<sigma>
    arbitrary: yd \<sigma>' infl stabl and xd \<sigma>' infl stabl and xd \<sigma>' infl stabl
    rule: TD_plain.query_iterate_eval_pinduct[of T, consumes 1, case_names Query Iterate Eval])
  case (Query x y c \<sigma>)
  show ?case using Query.IH(1) Query.prems(1)
  proof (cases rule:
      TD_plain.query_iterate_lookup_cases[of T, consumes 2, case_names Iterate Lookup])
    case Iterate
    moreover obtain infl' stabl' where IH: "iterate_dom y (insert y c) infl stabl \<sigma> \<and>
        iterate y (insert y c) infl stabl \<sigma> = (yd, infl', stabl', \<sigma>') \<and>
        invariant c \<sigma>' infl' stabl' \<and>
        y \<in> stabl' \<and>
        update_rel y infl stabl infl' stabl'"
      using Query.IH(2)[simplified, OF Iterate(4,2) Query.prems(2), folded dom_defs] by auto
    ultimately show ?thesis
    proof (intro conjI, goal_cases)
      case 1 then show dom: ?case using query_iterate_eval.domintros(1)[folded dom_defs] by auto
      case 2 then show ?case
      proof (intro exI[of _ "fminsert infl' y x"] exI[of _ stabl'], intro conjI, goal_cases)
        case 1 then show ?case using dom by simp
      next
        case 2 then show ?case
          unfolding invariant_def by (auto simp add: fminsert_def fmlookup_default_def)
      next
        case 6 then have "\<forall>\<xi>. (slookup infl' \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
          by (cases "y \<in> stabl"; auto)
        then show ?case
          using infl_upd_diff[of infl' infl stabl y x] by auto
      qed (auto simp add: fminsert_def fmlookup_default_def)
    qed
  next
    case Lookup
    then show ?thesis using Query.prems(1,2)
    proof (intro conjI, goal_cases)
      case 1 then show dom: ?case using query_iterate_eval.domintros(1)[of y c] by auto
      case 2 then show ?case
      proof (intro exI[of _ "fminsert infl y x"] exI[of _ stabl], intro conjI, goal_cases)
        case 1 then show ?case using dom by simp
      next
        case 2 then show ?case
          unfolding invariant_def by (auto simp add: fminsert_def fmlookup_default_def)
      next
        case 6 then show ?case
          using infl_upd_diff[of infl infl stabl y] by auto
      qed (auto simp add: fminsert_def fmlookup_default_def)
    qed
  qed
next
  case (Iterate x c \<sigma>)
  have inv: "invariant c \<sigma> infl (insert x stabl)"
    using Iterate.prems(2,3) invariant_simp_c_stabl by auto
  have dep_in_stabl: "\<forall>\<xi>\<in>stabl - (c - {x}). dep \<sigma> \<xi> \<subseteq> stabl"
    using Iterate.prems(3) dep_subset_stable[of infl stabl] unfolding invariant_def by auto
  show ?case
  proof(cases "x \<in> stabl" rule: case_split[case_names Stable Unstable])
    case Stable
    then show ?thesis
    proof(intro conjI, goal_cases)
      case 1 then show dom: ?case using query_iterate_eval.domintros(2)[of x stabl] by simp
      case 2 moreover have "\<sigma> = \<sigma>'"
        using Iterate.prems(3) TD_plain.already_solution(2)[OF Iterate.IH(1) Iterate.prems(1,2) 2]
          dep_in_stabl unfolding TD_plain.invariant_def invariant_def by fastforce
      ultimately show ?case
      proof (intro exI[of _ infl] exI[of _ stabl] conjI, goal_cases)
        case 1
          then show ?case using dom TD_plain.iterate_fmlookup[OF Iterate.IH(1) Iterate.prems(1,2)]
            by auto
        next
          case 2 then show ?case using Iterate.prems(3) by auto
      qed auto
    qed
  next
    case Unstable
    show ?thesis using Iterate.IH(1) Iterate.prems(1,2)
    proof(cases rule:
        TD_plain.iterate_continue_fixpoint_cases[of T, consumes 3, case_names Fixpoint Continue])
      case Fixpoint
      moreover obtain infl' stabl' where IH: "eval_dom x (T x) c infl (insert x stabl) \<sigma> \<and>
        (xd, infl', stabl', \<sigma>') = eval x (T x) c infl (insert x stabl) \<sigma> \<and>
        invariant c \<sigma>' infl' stabl' \<and>
        eq x \<sigma>' = xd \<and>
        (\<forall>y\<in>dep \<sigma>' x. x \<in> slookup infl' y) \<and>
        update_rel x infl (insert x stabl) infl' stabl'"
        using Iterate.IH(2)[OF Fixpoint(2) inv, folded dep_def] by auto
      ultimately show ?thesis using Unstable
      proof(intro conjI, goal_cases)
      case 1 then show dom: ?case using query_iterate_eval.domintros(2)[of x stabl c infl \<sigma>]
        by (cases "eval x (T x) c infl (insert x stabl) \<sigma>"; auto)
      case 2 then show ?case
        proof (intro exI[of _ infl'] exI[of _ stabl'] conjI, goal_cases)
          case 1 then show ?case using dom by (auto split: prod.splits)
        next
          case 2 then show ?case unfolding invariant_def by auto
        next
          case 3 then show ?case using Iterate.prems(2) invariant_def by fastforce
        qed auto
      qed
    next
      case (Continue \<sigma>1 xd')
      obtain infl1 stabl1 where IH: "eval_dom x (T x) c infl (insert x stabl) \<sigma> \<and>
        (xd', infl1, stabl1, \<sigma>1) = eval x (T x) c infl (insert x stabl) \<sigma> \<and>
        invariant c \<sigma>1 infl1 stabl1 \<and>
        eq x \<sigma>1 = xd' \<and>
        (\<forall>y\<in>dep \<sigma>1 x. x \<in> slookup infl1 y) \<and>
        update_rel x infl (insert x stabl) infl1 stabl1"
      using Iterate.IH(2)[OF Continue(2) inv, folded dep_def] by auto
      obtain infl2 stabl2 where destab: "(infl2, stabl2) = destab x infl1 stabl1"
        by (cases "destab x infl1 stabl1"; auto)
      then have infl2_def: "infl2 = fmdrop_set (insert x (influenced_by infl1 x)) infl1"
        and stabl2_def: "stabl2 = stabl1 - influenced_by infl1 x"
        using destab_infl_stabl_relation[of infl2 stabl2 x infl1 stabl1] by auto
      define \<sigma>2 where [simp]: "\<sigma>2 = \<sigma>1(x \<mapsto> xd')"
      have infl_diff: "\<forall>\<xi>. (slookup infl1 \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
        using Unstable Iterate.prems(3) IH
        unfolding invariant_def by auto
      have infl_closed: "\<forall>x\<in>stabl1 - (c - {x}). \<forall>y\<in>dep \<sigma>1 x. x \<in> slookup infl1 y"
        using IH unfolding dep_def invariant_def by auto
      have stabl_inc: "stabl \<subseteq> stabl2"
        using IH Iterate.prems(3) new_lookup_to_infl_not_stabl[OF infl_diff Unstable]
        unfolding invariant_def stabl2_def by auto

      have inv2: "invariant (c - {x}) \<sigma>2 infl2 stabl2"
        using IH unfolding invariant_def
      proof(elim conjE, intro conjI, goal_cases)
        case 1
        show ?case using destab_preserves_c_subset_stabl stabl_inc Iterate.prems(3)
          unfolding invariant_def by auto
      next
        case 2 then show ?case using destab_upd_preserves_part_sol[OF destab _ infl_closed] by auto
      next
        case 3 then show ?case using destab_preserves_infl_dom_stabl[OF destab] by auto
      next
        case 4 show ?case
        proof(intro ballI, goal_cases)
          case (1 y z)
          have x_no_dep: "x \<notin> dep \<sigma>1 y" if "y \<in> stabl2 - (c - {x})" for y
            using that destab_infl_stabl_relation[OF destab] infl_closed destab_x_no_dep by blast
          have "dep \<sigma>1 y = dep \<sigma>2 y" using x_no_dep[OF 1(1)] dep_eq[of \<sigma>1 _ \<sigma>2]
            unfolding mlup_def by (simp add: fun_upd_apply)
          then show ?case using 1 destab_and_upd_preserves_dep_closed_in_infl[OF destab infl_closed]
            by auto
        qed
      qed
      obtain infl' stabl' where ih: "iterate_dom x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd')) \<and>
          iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> xd')) = (xd, infl', stabl', \<sigma>') \<and>
          invariant (c - {x}) \<sigma>' infl' stabl' \<and>
          x \<in> stabl' \<and>
          update_rel x infl2 stabl2 infl' stabl'"
        using Iterate.IH(3)[OF Continue(2)[symmetric] _ Continue(3)[symmetric] Continue(5)
          Iterate.prems(2) inv2[unfolded \<sigma>2_def], simplified, folded dom_defs]
          Continue(2,3,5) Iterate.IH(3) Iterate.prems(2) \<sigma>2_def inv2
        by fastforce

      show ?thesis using IH ih destab Unstable
      proof(elim conjE, intro conjI, goal_cases)
        case 1 show dom: ?case using query_iterate_eval.domintros(2)[of x stabl c infl \<sigma>]
          using 1(1-2,3-5)
          by (cases "eval x (T x) c infl (insert x stabl) \<sigma>"; cases "destab x infl1 stabl1"; auto)
        case 2 then show ?case
        proof (intro exI[of _ infl'] exI[of _ stabl'] conjI, goal_cases)
          case 1 show ?case using 1(1,5,6) Continue(3) dom Unstable by (auto split: prod.splits)
        next
          case 4
          show ?case
            using "4"(12) stabl_inc by auto
        next
          case 5  show ?case
          proof(intro ballI subsetI, goal_cases)
            case (1 \<xi> u)
            have "\<xi> \<notin> insert x (influenced_by infl1 x)"
              using 1(1) stabl2_def stabl_inc Unstable by blast
            then show ?case using stabl_inc infl2_def 1 5(14,16)
                fmlookup_default_drop_set[of "insert x (influenced_by infl1 x)" infl1 \<xi>]
              by fastforce
          qed
        next
          case 6 show ?case
          proof(intro allI, goal_cases)
            case (1 \<xi>)
            have "slookup infl2 \<xi> \<subseteq> slookup infl1 \<xi>" using infl2_def
              unfolding fmlookup_default_def by auto
            moreover have "(slookup infl' \<xi> - slookup infl2 \<xi>) \<inter> (stabl - {x}) = {}"
              using stabl_inc ih
              by blast
            moreover have "(slookup infl1 \<xi> - slookup infl \<xi>) \<inter> (stabl - {x}) = {}"
              using 6(7)[unfolded invariant_def] infl_diff stabl_infl_empty[of \<xi> stabl1 infl1]
              by (cases "\<xi> \<in> stabl1"; auto)
            ultimately show ?case unfolding stabl2_def by auto
          qed
        qed auto
      qed
    qed
  qed
next
  case (Eval x t c \<sigma>)
  show ?case using Eval.IH(1) Eval.prems(1)
  proof(cases rule: TD_plain.eval_query_answer_cases[of T, consumes 2, case_names Query Answer])
    case (Query y g yd \<sigma>1)
    obtain infl1 stabl1 where IH: "query_dom x y c infl stabl \<sigma> \<and>
        (yd, infl1, stabl1, \<sigma>1) = query x y c infl stabl \<sigma> \<and>
        invariant c \<sigma>1 infl1 stabl1 \<and>
        x \<in> slookup infl1 y \<and>
        update_rel x infl stabl infl1 stabl1"
      using Eval.IH(2)[OF Query(1,3) Eval.prems(2)] by metis
    then obtain infl' stabl' where ih: "eval_dom x (g yd) c infl1 stabl1 \<sigma>1 \<and>
      (xd, infl', stabl', \<sigma>') = eval x (g yd) c infl1 stabl1 \<sigma>1 \<and>
      invariant c \<sigma>' infl' stabl' \<and>
      traverse_rhs (g yd) \<sigma>' = xd \<and>
      (\<forall>y\<in>dep_aux \<sigma>' (g yd). x \<in> slookup infl' y) \<and>
      update_rel x infl1 stabl1 infl' stabl'"
      using Eval.prems(3) Eval.IH(3)[OF Query(1) Query(3)[symmetric] _ Query(5), of infl1 stabl1]
      by fastforce
    have td1_inv: "TD_plain.invariant T stabl c \<sigma>"
      using Eval.prems(2) dep_subset_stable unfolding TD_plain.invariant_def invariant_def by blast
    have td1_inv2: "TD_plain.invariant T (stabl \<union> reach_cap \<sigma>1 c y) c \<sigma>1"
      using TD_plain.partial_correctness_ind(1)[OF Query(2,3) td1_inv] by auto
    have mlup: "mlup \<sigma>' y = yd"
      using TD_plain.partial_correctness_ind(3)[OF Query(4,5) td1_inv2] Query(6) by auto

    show ?thesis using IH ih
    proof (elim conjE, intro conjI, goal_cases)
      case 1
      show dom: ?case
        using 1(1-3) Query(1) query_iterate_eval.domintros(3)[of t x c infl stabl \<sigma>]
        by (cases "query x y c infl stabl \<sigma>"; fastforce)
      case 2
      then show ?case
      proof (intro exI[of _ infl'] exI[of _ stabl'] conjI, goal_cases)
        case 1 show ?case using 1(3,4) dom Query(1) by (auto split:prod.splits)
      next
        case 3 then show ?case using Query(1) mlup by auto
      next
        case 4 show ?case using 4(5,7,10,14) Query(1) mlup stabl_infl_empty[of y stabl1 infl1]
          unfolding invariant_def by auto
      next
        case 6 then show ?case by blast
      next
        case 7 show ?case
          using 7(9,12,15) infl_diff_eval_step[of stabl stabl1 infl' infl1 x infl]
          by auto
      qed auto
    qed
  next
    case Answer
    then show ?thesis using Eval.prems(2)
    proof (intro conjI, goal_cases)
      case 1 then show dom: ?case using query_iterate_eval.domintros(3)[of t] by auto
      case 2 then show ?case
      proof (intro exI[of _ infl] exI[of _ stabl] conjI, goal_cases)
        case 1 then show ?case using dom by auto
      qed auto
    qed
  qed
qed

corollary TD_plain_TD_equivalence:
  assumes "TD_plain.solve_dom T x"
    and "TD_plain.solve T x = \<sigma>"
  shows "\<exists>stabl. solve_dom x \<and> solve x = (stabl, \<sigma>)"
proof -
  obtain xd where iter: "TD_plain.iterate T x {x} Map.empty = (xd, \<sigma>)"
    using assms(2) unfolding TD_plain.solve_def by (auto split: prod.splits)
  have inv: "invariant ({x} - {x}) Map.empty fmempty {}" unfolding invariant_def by fastforce
  obtain infl stabl where "iterate_dom x {x} fmempty {} (\<lambda>x. None)"
      and "iterate x {x} fmempty {} (\<lambda>x. None) = (xd, infl, stabl, \<sigma>)"
    using TD_plain_TD_equivalence_ind(2)[OF assms(1)[unfolded TD_plain.solve_dom_def] iter _ inv]
    by auto
  then show ?thesis unfolding solve_dom_def solve_def by (auto split: prod.splits)
qed


subsubsection \<open>TD \<open>\<rightarrow>\<close> TD\_plain\<close>

lemmas TD_plain_dom_defs =
    TD_plain.query_dom_def[of T]
    TD_plain.iterate_dom_def[of T]
    TD_plain.eval_dom_def[of T]

lemma TD_TD_plain_equivalence_ind:
  shows "query_dom x y c infl stabl \<sigma>
    \<Longrightarrow> (yd, infl', stabl', \<sigma>') = query x y c infl stabl \<sigma>
    \<Longrightarrow> invariant c \<sigma> infl stabl
    \<Longrightarrow> finite stabl
    \<Longrightarrow> invariant c \<sigma>' infl' stabl'
      \<and> TD_plain.query_dom T x y c \<sigma>
      \<and> (yd, \<sigma>') = TD_plain.query T x y c \<sigma>
      \<and> finite stabl'
      \<and> x \<in> slookup infl' y
      \<and> update_rel x infl stabl infl' stabl'"
    and "iterate_dom x c infl stabl \<sigma>
    \<Longrightarrow> (xd, infl', stabl', \<sigma>') = iterate x c infl stabl \<sigma>
    \<Longrightarrow> x \<in> c
    \<Longrightarrow> invariant (c - {x}) \<sigma> infl stabl
    \<Longrightarrow> finite stabl
    \<Longrightarrow> invariant (c - {x}) \<sigma>' infl' stabl'
      \<and> TD_plain.iterate_dom T x c \<sigma>
      \<and> (xd, \<sigma>') = TD_plain.iterate T x c \<sigma>
      \<and> finite stabl'
      \<and> x \<in> stabl'
      \<and> update_rel x infl stabl infl' stabl'"
    and "eval_dom x t c infl stabl \<sigma>
    \<Longrightarrow> (xd, infl', stabl', \<sigma>') = eval x t c infl stabl \<sigma>
    \<Longrightarrow> invariant c \<sigma> infl stabl
    \<Longrightarrow> x \<in> stabl
    \<Longrightarrow> finite stabl
    \<Longrightarrow> invariant c \<sigma>' infl' stabl'
      \<and> TD_plain.eval_dom T x t c \<sigma>
      \<and> (xd, \<sigma>') = TD_plain.eval T x t c \<sigma>
      \<and> finite stabl'
      \<and> traverse_rhs t \<sigma>' = xd
      \<and> (\<forall>y\<in>dep_aux \<sigma>' t. x \<in> slookup infl' y)
      \<and> update_rel x infl stabl infl' stabl'"
proof(induction x y c infl stabl \<sigma> and y c infl stabl \<sigma> and x t c infl stabl \<sigma>
    arbitrary: yd infl' stabl' \<sigma>' and xd infl' stabl' \<sigma>' and xd infl' stabl' \<sigma>'
    rule: query_iterate_eval_pinduct)
  case (Query y x c infl stabl \<sigma>)
  show ?case using Query.IH(1) Query.prems(1)
  proof(cases rule: query_iterate_lookup_cases)
    case (Iterate infl1)
    moreover
    note IH = Query.IH(2)[simplified, folded TD_plain_dom_defs, OF Iterate(5,2) Query.prems(2,3)]
    ultimately show ?thesis
    proof(intro conjI, goal_cases)
      case 1 then show ?case unfolding invariant_def
        by (auto simp add: fminsert_def fmlookup_default_def)
    next
      case 2 then show dom: ?case using TD_plain.query_iterate_eval.domintros(1)[of x c] by auto
      case 3 then show ?case using dom by auto
    next case 8 then have "\<forall>\<xi>. (slookup infl1 \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
        using Query.prems(3)[unfolded invariant_def]
        by (cases "x \<in> stabl"; simp)
      then show ?case
        using 8 infl_upd_diff[of infl1 infl stabl x] Query.prems(2) by auto
    qed (auto simp add: fminsert_def fmlookup_default_def)
  next
    case Lookup
    then show ?thesis using Query.prems(2,3)
    proof(intro conjI, goal_cases)
      case 1 then show ?case unfolding invariant_def
        by (auto simp add: fminsert_def fmlookup_default_def)
    next
      case 2 then show dom: ?case using TD_plain.query_iterate_eval.domintros(1)[of x c] by auto
      case 3 then show ?case using dom by auto
    next case 8 then show ?case
      using infl_upd_diff[of infl infl stabl x] Query.prems(2) by auto
    qed (auto simp add: fminsert_def fmlookup_default_def)
  qed
next
  case (Iterate x c infl stabl \<sigma>)
  then have inv: "invariant c \<sigma> infl (insert x stabl)" using invariant_simp_c_stabl by metis
  have xstabl: "x \<in> insert x stabl" by simp
  have stablfinite: "finite (insert x stabl)" using Iterate.prems(4) by auto
  show ?case using Iterate.IH(1) Iterate.prems(1-2)
  proof(cases rule: iterate_continue_fixpoint_cases)
    case Stable
    have "TD_plain.invariant T stabl (c - {x}) \<sigma>"
      using Iterate.prems(3) dep_subset_stable[of infl stabl]
      unfolding invariant_def TD_plain.invariant_def[of T]
      by auto
    then have "TD_plain.iterate_dom T x c \<sigma>" and "TD_plain.iterate T x c \<sigma> = (xd, \<sigma>)"
      using Stable(5,4) Iterate.prems(2,4) TD_plain.td1_terminates_for_stabl[of x stabl T] by auto
    then show ?thesis using Stable(2,3,5) Iterate.prems(1,3,4) Iterate.IH(1) by auto
  next
    case Fixpoint
    note IH = Iterate.IH(2)[OF Fixpoint(4,2) inv xstabl stablfinite, folded eq_def dep_def]
    then show ?thesis
    proof(intro conjI, goal_cases)
      case 1 then show ?case unfolding invariant_def
      proof(intro conjI, goal_cases)
        case 1 then have "part_solution \<sigma>' (stabl' - (c - {x}))"
          using Fixpoint(3) unfolding eq_def invariant_def by auto
        then show ?case using IH invariant_def by auto
      next
        case 2
        then show ?case using Fixpoint(3) by auto
      next
        case 3 then show ?case using Iterate.prems(2) by (simp add: insert_absorb)
      qed auto
    next
      case 2 then show dom: ?case
        using Fixpoint(3) TD_plain.query_iterate_eval.domintros(2)[of T, folded TD_plain_dom_defs]
        by (metis prod.inject)
      case 3 then show ?case using dom Fixpoint(3) by (auto split: prod.splits)
    next
      case 6 then show ?case
        using Fixpoint(4) by blast
    next case 8
      have "x \<notin> fset (fmdom infl)"
        using Iterate.prems(3) Fixpoint(4)
        unfolding invariant_def
        by auto
      then have "slookup infl x = {}"
        unfolding fmlookup_default_def
        by (simp add: fmdom_notD)
      then show ?case
        using Fixpoint(4) IH lookup_in_influenced
        by auto
    qed auto
  next
    case (Continue stabl1 infl1 \<sigma>1 xd' stabl2 infl2)
    have infl2_def: "infl2 = fmdrop_set (insert x (influenced_by infl1 x)) infl1"
      and stabl2_def: "stabl2 = stabl1 - influenced_by infl1 x"
      using destab_infl_stabl_relation[of infl2 stabl2 x infl1 stabl1] Continue(4) by auto
    note IH = Iterate.IH(2)[OF Continue(7,2) inv xstabl stablfinite]

    have "(slookup infl1 \<xi> - slookup infl \<xi>) \<inter> stabl = {}" for \<xi>
      using Iterate.prems(3) Continue(7) IH
      unfolding invariant_def
      by auto
    then have stabl_inc: "stabl \<subseteq> stabl2"
      using Iterate.prems(3) Continue(4,7) new_lookup_to_infl_not_stabl[of infl1 infl stabl x]
        destab_infl_stabl_relation[of infl2 stabl2] IH
      unfolding invariant_def
      by auto

    have infl_closed: "(\<forall>x\<in>stabl1 - (c - {x}). \<forall>y\<in>dep \<sigma>1 x. x \<in> slookup infl1 y)"
      using IH[unfolded invariant_def, folded dep_def] by auto

    have x_no_dep: "x \<notin> dep \<sigma>1 y" if "y \<in> stabl2 - (c - {x})" for y
      using that Continue(4) destab_infl_stabl_relation destab_x_no_dep[OF _ infl_closed]
        by fastforce

    have "invariant (c - {x}) (\<sigma>1(x \<mapsto> xd')) infl2 stabl2"
      using IH Iterate.prems(2,3) Continue(4,7)
      unfolding invariant_def
    proof(elim conjE, intro conjI, goal_cases)
      case 1
      define \<sigma>2 where [simp]: "\<sigma>2 = \<sigma>1(x \<mapsto> xd')"
      show ?case using 1(4) stabl_inc by auto
      case 2
      show ?case
        using 2(2,8,15) destab_upd_preserves_part_sol infl_closed
        by auto
      case 3
      show ?case using 3(2,12) destab_preserves_infl_dom_stabl by auto
      case 4
      show ?case
      proof(intro ballI, goal_cases)
        case (1 y z)
        have "dep \<sigma>1 y = dep \<sigma>2 y" using x_no_dep[OF 1(1)] dep_eq[of \<sigma>1 _ \<sigma>2] \<sigma>2_def fun_upd_apply
          unfolding mlup_def by metis
        then show ?case using 1 4(2) destab_and_upd_preserves_dep_closed_in_infl infl_closed by auto
      qed
    qed
    then have "invariant (c - {x}) (\<sigma>1(x \<mapsto> xd')) infl2 stabl2" by simp+
    note inv = this
    have B: "finite stabl2"
      by (metis Continue(4) Diff_subset IH destab_infl_stabl_relation infinite_super)
    note ih = Iterate.IH(3)[OF Continue(7,2) _ _ _ Continue(3,4) _ Continue(6) Iterate.prems(2) inv
        B, of "(infl1, stabl1, \<sigma>1)" "(stabl1, \<sigma>1)", simplified, folded TD_plain_dom_defs]
    then show ?thesis
    proof(intro conjI, goal_cases)
      case 2 show dom: ?case
        using IH TD_plain.query_iterate_eval.domintros(2)[of T x c \<sigma>, folded TD_plain_dom_defs] ih
        by (metis Pair_inject)
      case 3 then show ?case using dom Continue(3) IH ih
        by (auto split: prod.split)
    next case 6 then show ?case
        using stabl_inc by auto
    next case 7
      then show ?case unfolding invariant_def
      proof(elim conjE, intro ballI subsetI, goal_cases)
        case (1 \<xi> u)
        have "\<xi> \<notin> insert x (influenced_by infl1 x)"
          using 1(13) Continue(7) stabl2_def stabl_inc by blast
        then show ?case
          using stabl_inc infl2_def 1(10,13,14) IH
            fmlookup_default_drop_set[of "insert x (influenced_by infl1 x)" infl1 \<xi>]
          by fastforce
      qed
    next case 8
      then show ?case unfolding invariant_def
      proof(intro allI, goal_cases)
        case (1 \<xi>)
        have "slookup infl2 \<xi> \<subseteq> slookup infl1 \<xi>"
          using infl2_def unfolding fmlookup_default_def by auto
        moreover have "(slookup infl' \<xi> - slookup infl2 \<xi>) \<inter> stabl = {}"
        proof (cases "x \<in> stabl2")
          case True
          then show ?thesis using Continue(5,6) by auto
        next
          case False
          then show ?thesis
            using 1(1) inv[unfolded invariant_def] stabl_inc
            by fastforce
        qed
        moreover have "(slookup infl1 \<xi> - slookup infl \<xi>) \<inter> stabl = {}"
          using Continue(7) Iterate.prems(3) IH stabl_infl_empty[of x stabl infl]
          unfolding invariant_def by auto
        ultimately show ?case using infl2_def stabl2_def by blast
      qed
    qed auto
  qed
next
  case (Eval x t c infl stabl \<sigma>)
  show ?case using Eval.IH(1) Eval.prems(1)
  proof(cases rule: eval_query_answer_cases)
    case (Query y g yd infl1 stabl1 \<sigma>1)
    note IH = Eval.IH(2)[OF Query(1,3) Eval.prems(2,4)]
    then have "invariant c \<sigma>1 infl1 stabl1
        \<and> TD_plain.invariant T
          stabl1 c \<sigma>1"
      using Eval.prems(3)
      unfolding invariant_def
    proof(elim conjE, intro conjI, goal_cases)
      case 1 show ?case using 1(2) .
    next
      case 2 show ?case using 2(4) .
    next
      case 3 show ?case using 3(6) .
    next
      case 4 show ?case using 4(7) .
    next
      case 5 show ?case using Eval.prems(3) IH
        reach_cap_tree_simp2 dep_eq unfolding TD_plain.invariant_def
        by (meson "5"(13) dep_subset_stable)
    qed
    then have "invariant c \<sigma>1 infl1 stabl1"
      and "TD_plain.invariant T stabl1 c \<sigma>1"
      by simp+
    note inv = this
    have B: "finite stabl1" using IH by simp
    have C: "x \<in> stabl1" using IH Eval.prems(3) by blast
    note ih = Eval.IH(3)[OF Query(1,3) _ _ _ Query(5) inv(1) C B,
        of "(infl1, stabl1, \<sigma>1)" "(stabl1, \<sigma>1)", simplified, folded TD_plain_dom_defs]

    have "y \<in> stabl1"
      using IH stabl_infl_empty[of y stabl1 infl1]
      unfolding invariant_def
      by fastforce
    then have "mlup \<sigma>1 y = mlup \<sigma>' y"
      using TD_plain.partial_correctness_ind(3)[of T x "g yd" c \<sigma>1 xd \<sigma>' stabl1] inv ih by auto
    then have mlup: "mlup \<sigma>' y = yd"
      using Query(6) by auto

    show ?thesis using ih
    proof(intro conjI, goal_cases)
      case 2
      then show dom: ?case
        using IH Query(1) TD_plain.query_iterate_eval.domintros(3)[of t T, folded TD_plain_dom_defs]
        by (cases "TD_plain.query T x y c \<sigma>") fastforce
      case 3
      then show ?case
        using dom IH Query(1)
          TD_plain.query_iterate_eval.domintros(3)[of t T, folded TD_plain_dom_defs]
        by (auto split: prod.splits)
    next
      case 5
      then show ?case using Query IH mlup unfolding invariant_def by auto
    next
      case 6
      then show ?case using 6 Query IH mlup \<open>y \<in> stabl1\<close> unfolding invariant_def by auto
    next
      case 7
      then show ?case using IH by auto
    next
      case 8
      then show ?case using IH by blast
    next
      case 9
      then show ?case
        using infl_diff_eval_step[of stabl stabl1 infl' infl1 x] IH ih Eval.prems(2,3) by auto
    qed auto
  next
    case Answer
    then show ?thesis using Answer TD_plain.query_iterate_eval.domintros(3) Eval.prems(2-3,4)
      by fastforce
  qed
qed

corollary TD_TD_plain_equivalence:
  assumes "solve_dom x"
    and "solve x = (stabl, \<sigma>)"
  shows "TD_plain.solve_dom T x \<and> TD_plain.solve T x = \<sigma>"
proof -
  obtain xd infl where iter: "(xd, infl, stabl, \<sigma>) = iterate x {x} fmempty {} Map.empty"
    using assms(2) unfolding solve_def by (auto split: prod.splits)
  have inv: "invariant ({x} - {x}) Map.empty fmempty {}" unfolding invariant_def by fastforce
  have "TD_plain.iterate_dom T x {x} (\<lambda>x. None) \<and> (xd, \<sigma>) = TD_plain.iterate T x {x} (\<lambda>x. None)"
    using TD_TD_plain_equivalence_ind(2)[OF assms(1)[unfolded solve_dom_def] iter _ inv, simplified]
    by auto
  then show ?thesis unfolding TD_plain.solve_dom_def TD_plain.solve_def by (auto split: prod.splits)
qed


subsection \<open>Partial Correctness of the TD\<close>

text\<open>From the equivalence of the TD and TD\_plain and the partial correctness proof of the TD\_plain
  we can now conclude partial correctness also for the TD.\<close>

corollary partial_correctness:
  assumes "solve_dom x"
    and "solve x = (stabl, \<sigma>)"
  shows "part_solution \<sigma> stabl" and "reach \<sigma> x \<subseteq> stabl"
proof(goal_cases)
  note dom = assms(1)[unfolded solve_dom_def]
  obtain infl xd where app: "(xd, infl, stabl, \<sigma>) = iterate x {x} fmempty {} Map.empty"
    using assms unfolding solve_def by (cases "iterate x {x} fmempty {} Map.empty") auto
  case 1 show ?case using TD_TD_plain_equivalence_ind(2)[OF dom app, unfolded invariant_def] by auto
  case 2 show ?case
    using TD_TD_plain_equivalence_ind(2)[OF dom app, unfolded invariant_def]
      reach_empty_capped dep_closed_implies_reach_cap_tree_closed
      dep_subset_stable[of infl stabl "{}"] by auto
qed

subsection \<open>Program Refinement for Code Generation\<close>

text\<open>To derive executable code for the TD, we do a program refinement and define an
  equivalent solve function based on partial\_function with options that can be used for the code
  generation.\<close>

datatype ('a,'b) state = Q "'a \<times> 'a \<times> 'a set \<times> ('a, 'a list) fmap \<times> 'a set \<times> ('a, 'b) map"
  | I "'a \<times> 'a set \<times> ('a, 'a list) fmap \<times> 'a set \<times> ('a, 'b) map"
  | E "'a \<times> ('a,'b) strategy_tree \<times> 'a set \<times> ('a, 'a list) fmap \<times> 'a set \<times> ('a, 'b) map"

partial_function (option) solve_rec_c ::
  "('x, 'd) state \<Rightarrow> ('d \<times> ('x, 'x list) fmap \<times> 'x set \<times> ('x, 'd) map) option"
  where
  "solve_rec_c s = (case s of Q (y,x,c,infl,stabl,\<sigma>) \<Rightarrow> Option.bind
      (if x \<in> c then
        Some (mlup \<sigma> x, infl, stabl, \<sigma>)
      else
        solve_rec_c (I (x, (insert x c), infl, stabl, \<sigma>)))
      (\<lambda> (xd, infl, stabl, \<sigma>). Some (xd, fminsert infl x y, stabl, \<sigma>))
  | I (x,c,infl,stabl,\<sigma>) \<Rightarrow>
      if x \<notin> stabl then Option.bind (
        solve_rec_c (E (x, (T x), c, infl, insert x stabl, \<sigma>))) (\<lambda>(d_new, infl, stabl, \<sigma>).
        if mlup \<sigma> x = d_new then
          Some (d_new, infl, stabl, \<sigma>)
        else
          let (infl, stabl) = destab x infl stabl in
          solve_rec_c (I (x, c, infl, stabl, \<sigma>(x \<mapsto> d_new))))
      else
        Some (mlup \<sigma> x, infl, stabl, \<sigma>)
  | E (x,t,c,infl,stabl,\<sigma>) \<Rightarrow> (case t of
        Answer d \<Rightarrow> Some (d, infl, stabl, \<sigma>)
      | Query y g \<Rightarrow> (
          Option.bind (solve_rec_c (Q (x, y, c, infl, stabl, \<sigma>))) (\<lambda>(yd, infl, stabl, \<sigma>).
          solve_rec_c (E (x, g yd, c, infl, stabl, \<sigma>))))))"

definition solve_rec_c_dom where "solve_rec_c_dom p \<equiv> \<exists>\<sigma>. solve_rec_c p = Some \<sigma>"

declare destab.simps[code]
declare destab_iter.simps[code]
declare solve_rec_c.simps[simp,code]

definition solve_c :: "'x \<Rightarrow> ('x set \<times> (('x, 'd) map)) option" where
  "solve_c x = Option.bind (solve_rec_c (I (x, {x}, fmempty, {}, Map.empty)))
    (\<lambda>(_, _, stabl, \<sigma>). Some (stabl,\<sigma>))"

definition solve_c_dom :: "'x \<Rightarrow> bool" where "solve_c_dom x \<equiv> \<exists>\<sigma>. solve_c x = Some \<sigma>"

text\<open>We prove the equivalence of the refined solver function for code generation and the initial
  version used for the partial correctness proof.\<close>

lemma query_iterate_eval_solve_rec_c_equiv:
  shows "query_dom x y c infl stabl \<sigma> \<Longrightarrow> solve_rec_c_dom (Q (x,y,c,infl,stabl,\<sigma>))
    \<and> query x y c infl stabl \<sigma> = the (solve_rec_c (Q (x,y,c,infl,stabl,\<sigma>)))"
  and "iterate_dom x c infl stabl \<sigma> \<Longrightarrow> solve_rec_c_dom (I (x,c,infl,stabl,\<sigma>))
    \<and> iterate x c infl stabl \<sigma> = the (solve_rec_c (I (x,c,infl,stabl,\<sigma>)))"
  and "eval_dom x t c infl stabl \<sigma> \<Longrightarrow> solve_rec_c_dom (E (x,t,c,infl,stabl,\<sigma>))
    \<and> eval x t c infl stabl \<sigma> = the (solve_rec_c (E (x,t,c,infl,stabl,\<sigma>)))"
proof (induction x y c infl stabl \<sigma> and x c infl stabl \<sigma> and x t c infl stabl \<sigma>
    rule: query_iterate_eval_pinduct)
  case (Query x y c infl stabl \<sigma>)
  show ?case
  proof (cases "y \<in> c")
    case True
    then have "solve_rec_c (Q (x, y, c, infl, stabl, \<sigma>))
        = Some (mlup \<sigma> y, fminsert infl y x, stabl, \<sigma>)"
      by simp
    moreover have "query x y c infl stabl \<sigma> = (mlup \<sigma> y, fminsert infl y x, stabl, \<sigma>)"
      using query.psimps[folded dom_defs] Query(1) True by force
    ultimately show ?thesis unfolding solve_rec_c_dom_def by auto
  next
    case False
    obtain d1 infl1 stabl1 \<sigma>1 where
        I: "iterate y (insert y c) infl stabl \<sigma> = (d1, infl1, stabl1, \<sigma>1)"
      using prod_cases4 by blast
    then have J: "query x y c infl stabl \<sigma> = (d1, fminsert infl1 y x, stabl1, \<sigma>1)"
      using False Query.IH(1) query.pelims[folded dom_defs] by fastforce
    then have "solve_rec_c (I (y, insert y c, infl, stabl, \<sigma>)) = Some (d1, infl1, stabl1, \<sigma>1)"
      using Query(2) False I by (simp add: solve_rec_c_dom_def)
    then have "solve_rec_c (Q (x, y, c, infl, stabl, \<sigma>)) = Some (d1, fminsert infl1 y x, stabl1, \<sigma>1)"
      using False by simp
    moreover have "solve_rec_c_dom (Q (x, y, c, infl, stabl, \<sigma>))"
      using Query(2) False unfolding solve_rec_c_dom_def by fastforce
    ultimately show ?thesis using Query J unfolding solve_rec_c_dom_def by auto
  qed
next
  case (Iterate x c infl stabl \<sigma>)
  show ?case
  proof (cases "x \<in> stabl")
    case True
    have "iterate_dom x c infl stabl \<sigma> \<and>
        iterate x c infl stabl \<sigma> = (mlup \<sigma> x, infl, stabl, \<sigma>)"
      using True iterate.psimps query_iterate_eval.domintros(2)
      unfolding iterate_dom_def
      by fastforce
    then show ?thesis using True unfolding solve_rec_c_dom_def by auto
  next
    case False
    obtain d1 infl1 stabl1 \<sigma>1 where
        eval: "eval x (T x) c infl (insert x stabl) \<sigma> = (d1, infl1, stabl1, \<sigma>1)"
        "solve_rec_c (E (x, T x, c, infl, insert x stabl, \<sigma>)) = Some (d1, infl1, stabl1, \<sigma>1)"
      using Iterate(2) solve_rec_c_dom_def False by force
    show ?thesis
    proof (cases "mlup \<sigma>1 x = d1")
      case True
      have "iterate x c infl stabl \<sigma> = (d1, infl1, stabl1, \<sigma>1)"
        using eval iterate.psimps[folded dom_defs, OF Iterate(1)] True False by simp
      moreover have "solve_rec_c (I (x, c, infl, stabl, \<sigma>)) = Some (d1, infl1, stabl1, \<sigma>1)"
        using eval False True by simp
      ultimately show ?thesis unfolding solve_rec_c_dom_def by simp
    next
      case False
      obtain infl2 stabl2 where destab: "(infl2, stabl2) = destab x infl1 stabl1"
        by (cases "destab x infl1 stabl1") auto
      have "solve_rec_c_dom (I (x, c, infl2, stabl2, \<sigma>1(x \<mapsto> d1)))"
        and "iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> d1)) =
          the (solve_rec_c (I (x, c, infl2, stabl2, \<sigma>1(x \<mapsto> d1))))"
        using Iterate(3)[OF \<open>x \<notin> stabl\<close> eval(1)[symmetric] _ _ _ False destab] by blast+
      moreover have "iterate x c infl stabl \<sigma> = iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> d1))"
        using eval iterate.psimps[folded dom_defs, OF Iterate(1)] False \<open>x \<notin> stabl\<close> destab
        by (smt (verit) case_prod_conv)
      moreover have "solve_rec_c (I (x, c, infl, stabl, \<sigma>))
          = solve_rec_c (I (x, c, infl2, stabl2, \<sigma>1(x \<mapsto> d1)))"
        using \<open>x \<notin> stabl\<close> False eval(2) destab[symmetric] by simp
      ultimately show ?thesis unfolding solve_rec_c_dom_def by auto
    qed
  qed
next
  case (Eval x t c infl stabl \<sigma>)
  show ?case
  proof (cases t)
    case (Answer d)
    then have "eval x t c infl stabl \<sigma> = (d, infl, stabl, \<sigma>)"
      using eval.psimps query_iterate_eval.domintros(3) dom_defs(3) by fastforce
    then show ?thesis using Eval Answer unfolding solve_rec_c_dom_def by simp
  next
    case (Query y g)
    then obtain d1 infl1 stabl1 \<sigma>1 where
        query: "solve_rec_c (Q (x, y, c, infl, stabl, \<sigma>)) = Some (d1, infl1, stabl1, \<sigma>1)"
          "query x y c infl stabl \<sigma> = (d1, infl1, stabl1, \<sigma>1)"
      using Query Eval(2) unfolding solve_rec_c_dom_def by auto
    then have "solve_rec_c_dom (E (x, g d1, c, infl1, stabl1, \<sigma>1))"
        "eval x (g d1) c infl1 stabl1 \<sigma>1 = the (solve_rec_c (E (x, g d1, c, infl1, stabl1, \<sigma>1)))"
      using Eval(3)[OF Query] by auto
    moreover have "eval x t c infl stabl \<sigma> = eval x (g d1) c infl1 stabl1 \<sigma>1"
      using Eval.IH(1) Query eval.psimps eval_dom_def query
      by fastforce
    moreover have "solve_rec_c (E (x, t, c, infl, stabl, \<sigma>))
        = solve_rec_c (E (x, g d1, c, infl1, stabl1, \<sigma>1))"
      using Query query solve_rec_c.simps[of "E (x,t,c,infl,stabl,\<sigma>)"]
      by (simp del: solve_rec_c.simps)
    ultimately show ?thesis using solve_rec_c_dom_def by force
  qed
qed

lemma solve_rec_c_query_iterate_eval_equiv:
  shows "solve_rec_c s = Some r \<Longrightarrow> (case s of
        Q (x,y,c,infl,stabl,\<sigma>) \<Rightarrow> query_dom x y c infl stabl \<sigma>
          \<and> query x y c infl stabl \<sigma> = r
      | I (x,c,infl,stabl,\<sigma>) \<Rightarrow> iterate_dom x c infl stabl \<sigma>
          \<and> iterate x c infl stabl \<sigma> = r
      | E (x,t,c,infl,stabl,\<sigma>) \<Rightarrow> eval_dom x t c infl stabl \<sigma>
          \<and> eval x t c infl stabl \<sigma> = r)"
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
    obtain x y c infl stabl \<sigma> where "a = (x, y, c, infl, stabl, \<sigma>)" using prod_cases6 by blast
    have "query_dom x y c infl stabl \<sigma> \<and> query x y c infl stabl \<sigma> = r"
    proof (cases "y \<in> c")
      case True
      then have "Some (mlup \<sigma> y, fminsert infl y x, stabl, \<sigma>) = Some r"
        using 3(2) Q \<open>a = (x, y, c, infl, stabl, \<sigma>)\<close> by simp
      then show ?thesis using query.psimps[folded query_dom_def, of x y c infl stabl \<sigma>]
            query_iterate_eval.domintros(1)[folded query_dom_def, of y c infl] True by simp
    next
      case False
      then have "Option.bind (S (I (y, insert y c, infl, stabl, \<sigma>))) (\<lambda>(d,infl,stabl,\<sigma>).
          Some (d, fminsert infl y x, stabl, \<sigma>)) = Some r"
        using 3(2) Q \<open>a = (x, y, c, infl, stabl, \<sigma>)\<close> by simp
      then obtain d1 infl1 stabl1 \<sigma>1
        where "S (I (y, insert y c, infl, stabl, \<sigma>)) = Some (d1 ,infl1, stabl1, \<sigma>1)"
        and "(d1, fminsert infl1 y x, stabl1, \<sigma>1) = r"
        by (cases "S (I (y, insert y c, infl, stabl, \<sigma>))") auto
      then have "iterate_dom y (insert y c) infl stabl \<sigma>
          \<and> iterate y (insert y c) infl stabl \<sigma> = (d1, infl1, stabl1, \<sigma>1)"
        using 3(1) unfolding iterate_dom_def by fastforce
      then show ?thesis using False \<open>(d1, fminsert infl1 y x, stabl1, \<sigma>1) = r\<close>
        by (simp add: query_iterate_eval.domintros(1) False)
    qed
    then show ?thesis using Q \<open>a = (x, y, c, infl, stabl, \<sigma>)\<close> by simp
  next
    case (I a)
    obtain x c infl stabl \<sigma> where "a = (x, c, infl, stabl, \<sigma>)" using prod_cases5 by blast
    show ?thesis
    proof(cases "x \<in> stabl")
      case True
      then have "(mlup \<sigma> x, infl, stabl, \<sigma>) = r" using I \<open>a = (x, c, infl, stabl, \<sigma>)\<close> 3(2) by simp
      moreover have "iterate_dom x c infl stabl \<sigma>
          \<and> iterate x c infl stabl \<sigma> = (mlup \<sigma> x, infl, stabl, \<sigma>)"
        using True query_iterate_eval.domintros(2) iterate.psimps dom_defs by fastforce
      ultimately show ?thesis using I \<open>a = (x, c, infl, stabl, \<sigma>)\<close> by simp
    next
      case False
      then have IH1: "Option.bind (S (E (x, T x, c, infl, insert x stabl, \<sigma>)))
         (\<lambda>(d_new, infl, stabl, \<sigma>).
           if mlup \<sigma> x = d_new then Some (d_new, infl, stabl, \<sigma>)
           else let (infl, stabl) = destab x infl stabl in
            S (I (x, c, infl, stabl, \<sigma>(x \<mapsto> d_new)))) = Some r"
        using 3(2) I \<open>a = (x, c, infl, stabl, \<sigma>)\<close> by simp
      then obtain d_new infl1 stabl1 \<sigma>1
        where eval_some: "S (E (x, T x, c, infl, insert x stabl, \<sigma>))
          = Some (d_new, infl1, stabl1, \<sigma>1)"
        using 3(2) I
        by (cases "S (E (x, T x, c, infl, insert x stabl, \<sigma>))") auto
      then have eval: "eval_dom x (T x) c infl (insert x stabl) \<sigma>
          \<and> eval x (T x) c infl (insert x stabl) \<sigma> = (d_new, infl1, stabl1, \<sigma>1)"
        using 3(1) unfolding TD_plain.eval_dom_def by force
      have "iterate_dom x c infl stabl \<sigma> \<and> iterate x c infl stabl \<sigma> = r"
      proof (cases "mlup \<sigma>1 x = d_new")
        case True
        then have "(d_new, infl1, stabl1, \<sigma>1) = r" using IH1 eval_some by simp
        moreover have "iterate_dom x c infl stabl \<sigma>"
          using query_iterate_eval.domintros(2)[folded dom_defs] False True eval by fastforce
        ultimately show ?thesis
          using iterate.psimps[folded dom_defs] False True eval by fastforce
      next
        case False
        obtain infl2 stabl2 where destab: "(infl2, stabl2) = destab x infl1 stabl1"
          by (cases "destab x infl1 stabl1") auto
        then have "S (I (x, c, infl2, stabl2, \<sigma>1(x \<mapsto> d_new))) = Some r"
          using IH1 False eval_some by (smt (verit, best) bind.bind_lunit case_prod_conv)
        then have iter_cont: "iterate_dom x c infl2 stabl2 (\<sigma>1(x \<mapsto> d_new))
            \<and> iterate x c infl2 stabl2 (\<sigma>1(x \<mapsto> d_new)) = r"
          using 3(1) unfolding iterate_dom_def by fastforce
        then have "iterate_dom x c infl stabl \<sigma>"
          using query_iterate_eval.domintros(2)[folded dom_defs destab.simps,
              of x stabl c infl \<sigma>] eval \<open>x \<notin> stabl\<close> False destab
          by (cases "destab x infl1 stabl1") auto
        then show ?thesis
          using iterate.psimps[folded dom_defs, of x c infl stabl \<sigma>] \<open>x \<notin> stabl\<close> destab eval
            False iter_cont
          by (cases "destab x infl1 stabl1") auto
      qed
      then show ?thesis
        using I \<open>a = (x, c, infl, stabl,  \<sigma>)\<close> by simp
    qed
  next
    case (E a)
    obtain x t c infl stabl \<sigma> where "a = (x, t, c, infl, stabl, \<sigma>)" using prod_cases6 by blast
    then have "s = E (x, t, c, infl, stabl, \<sigma>)" using E by auto
    have "eval_dom x t c infl stabl \<sigma> \<and> eval x t c infl stabl \<sigma> = r"
    proof (cases t)
      case (Answer d)
      then have "eval_dom x t c infl stabl \<sigma>"
        unfolding eval_dom_def
        using query_iterate_eval.domintros(3)
        by fastforce
      moreover have "eval x t c infl stabl \<sigma> = (d, infl, stabl, \<sigma>)"
        using Answer eval.psimps[folded dom_defs, OF calculation] by auto
      moreover have "(d, infl, stabl, \<sigma>) = r"
        using 3(2) \<open>s = E (x, t, c, infl, stabl, \<sigma>)\<close> Answer by simp
      ultimately show ?thesis by simp
    next
      case (Query y g)
      then have A: "Option.bind (S (Q (x, y, c, infl, stabl, \<sigma>))) (\<lambda>(yd, infl, stabl, \<sigma>).
        S (E (x, g yd, c, infl, stabl, \<sigma>))) = Some r" using \<open>s = E (x, t, c, infl, stabl, \<sigma>)\<close> 3(2)
        by simp
      then obtain yd infl1 stabl1 \<sigma>1
          where S1: "S (Q (x, y, c, infl, stabl, \<sigma>)) = Some (yd, infl1, stabl1, \<sigma>1)"
          and S2: "S (E (x, g yd, c, infl1, stabl1, \<sigma>1)) = Some r"
        by (cases "S (Q (x, y, c, infl, stabl, \<sigma>))") auto
      then have "query_dom x y c infl stabl \<sigma>
          \<and> query x y c infl stabl \<sigma> = (yd, infl1, stabl1, \<sigma>1)"
          and "eval_dom x (g yd) c infl1 stabl1 \<sigma>1 \<and> eval x (g yd) c infl1 stabl1 \<sigma>1 = r"
        using 3(1)[OF S1] 3(1)[OF S2] unfolding TD_plain.dom_defs by force+
      then show ?thesis
        using query_iterate_eval.domintros(3)[folded dom_defs] eval.psimps[folded dom_defs] Query
        by fastforce
    qed
    then show ?thesis
      using E \<open>a = (x, t, c, infl, stabl, \<sigma>)\<close> by simp
  qed
qed

theorem term_equivalence: "solve_dom x \<longleftrightarrow> solve_c_dom x"
  using solve_rec_c_query_iterate_eval_equiv[of "I (x, {x}, fmempty, {}, \<lambda>x. None)"]
    query_iterate_eval_solve_rec_c_equiv(2)[of x "{x}" fmempty "{}" "\<lambda>x. None"]
  unfolding solve_dom_def solve_c_dom_def solve_rec_c_dom_def solve_c_def
  by (cases "solve_rec_c (I (x, {x}, fmempty, {}, \<lambda>x. None))") fastforce+

theorem value_equivalence: "solve_dom x \<Longrightarrow> \<exists>\<sigma>. solve_c x = Some \<sigma> \<and> solve x = \<sigma>"
proof goal_cases
  case 1
  then obtain r where "solve_rec_c (I (x, {x}, fmempty, {}, \<lambda>x. None)) = Some r
    \<and> iterate x {x} fmempty {} (\<lambda>x. None) = r"
    using query_iterate_eval_solve_rec_c_equiv(2)[OF 1[unfolded solve_dom_def]]
    unfolding solve_rec_c_dom_def solve_dom_def
    by fastforce
  then show ?case unfolding solve_c_def solve_def by (auto split: prod.split)
qed

text\<open>With the equivalence of the refined version and the initial version proven, we can specify a
  the code equation.\<close>

lemma solve_code_equation [code]:
  "solve x = (case solve_c x of Some r \<Rightarrow> r
  | None \<Rightarrow> Code.abort (String.implode ''Input not in domain'') (\<lambda>_. solve x))"
proof (cases "solve_dom x")
  case True
  then show ?thesis
    using solve_c_def solve_def value_equivalence by fastforce
next
  case False
  then have "solve_c x = None" using solve_c_dom_def term_equivalence by (meson option.exhaust)
  then show ?thesis by auto
qed

end

text\<open>Finally, we use a dedicated rewrite rule for the code generation of the solver locale.\<close>

global_interpretation TD_Interp: TD D T for D T
  defines
    TD_Interp_solve = TD_Interp.solve
  done

end