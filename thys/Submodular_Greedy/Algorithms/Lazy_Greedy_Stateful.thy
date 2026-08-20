theory Lazy_Greedy_Stateful
  imports Lazy_Greedy_Oracle
begin

section \<open>Stateful lazy greedy with cached upper bounds\<close>

record 'a lg_state =
  Sg  :: "'a set"
  ubg :: "'a \<Rightarrow> real"

context Cardinality_Constraint
begin

subsection \<open>State: selected set and cached upper bounds\<close>

definition init_ub :: "'a \<Rightarrow> real" where
  "init_ub x = gain {} x"

definition init_state :: "'a lg_state" where
  "init_state = \<lparr> Sg = {}, ubg = init_ub \<rparr>"

definition remaining :: "'a lg_state \<Rightarrow> 'a set" where
  "remaining st = V - Sg st"


subsection \<open>Inner lazy selection returning updated upper bounds\<close>

fun lazy_argmax_gain_fuel_state ::
  "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<times> ('a \<Rightarrow> real))"
where
  "lazy_argmax_gain_fuel_state 0 S A ub =
     (let x = pick_ub_some A ub in (x, ub))"
| "lazy_argmax_gain_fuel_state (Suc n) S A ub =
     (let x = pick_ub_some A ub in
      if ub x = gain S x then (x, ub)
      else lazy_argmax_gain_fuel_state n S A (tighten S ub x))"

definition lazy_select :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<times> ('a \<Rightarrow> real))" where
  "lazy_select S A ub = lazy_argmax_gain_fuel_state (card A) S A ub"

lemma lazy_argmax_gain_fuel_state_fst:
  "fst (lazy_argmax_gain_fuel_state n S A ub) = lazy_argmax_gain_fuel n S A ub"
proof (induction n arbitrary: ub)
  case 0
  then show ?case by (simp add: Let_def)
next
  case (Suc n)
  then show ?case
    by (simp add: Let_def)
qed

lemma lazy_select_fst:
  "fst (lazy_select S A ub) = lazy_argmax_gain S A ub"
  unfolding lazy_select_def lazy_argmax_gain_def
  using lazy_argmax_gain_fuel_state_fst[of "card A" S A ub]
  by simp

lemma lazy_argmax_gain_fuel_state_ub_valid:
  assumes ubv: "ub_valid S A ub"
  shows "ub_valid S A (snd (lazy_argmax_gain_fuel_state n S A ub))"
  using ubv
proof (induction n arbitrary: ub)
  case 0
  show ?case
    using 0 by (simp add: Let_def)
next
  case (Suc n ub)
  from Suc.prems have ubv_current: "ub_valid S A ub" by simp

  let ?x = "pick_ub_some A ub"

  show ?case
  proof (cases "ub ?x = gain S ?x")
    case True
    then show ?thesis
      using ubv_current by (simp add: Let_def)
  next
    case False
    have ubv_tight: "ub_valid S A (tighten S ub ?x)"
      using ub_valid_tighten[OF ubv_current] .

    have IH_result: "ub_valid S A (snd (lazy_argmax_gain_fuel_state n S A (tighten S ub ?x)))"
      using Suc.IH[OF ubv_tight] .

    show ?thesis
      using False IH_result by (simp add: Let_def)
  qed
qed

lemma lazy_select_ub_valid:
  assumes ubv: "ub_valid S A ub"
  shows "ub_valid S A (snd (lazy_select S A ub))"
  unfolding lazy_select_def
  using lazy_argmax_gain_fuel_state_ub_valid[OF ubv] .

subsection \<open>Preservation of upper-bound validity across outer iterations\<close>

lemma ub_valid_init:
  "ub_valid {} V init_ub"
  unfolding ub_valid_def init_ub_def
  by simp

lemma ub_valid_after_insert:
  assumes ubv: "ub_valid S (V - S) ub"
      and Ssub: "S \<subseteq> V"
      and x_in: "x \<in> V - S"
  shows "ub_valid (insert x S) (V - insert x S) ub"
proof (unfold ub_valid_def, intro ballI)
  fix y assume yR: "y \<in> V - insert x S"
  have yV: "y \<in> V" and y_notT: "y \<notin> insert x S"
    using yR by auto

  have y_in_old: "y \<in> V - S"
    using yR by auto

  have TsubV: "insert x S \<subseteq> V"
    using Ssub x_in by auto

  have dec_ge: "gain S y \<ge> gain (insert x S) y"
    using gain_decreasing[OF _ TsubV yV y_notT] Ssub
    by auto

  have dec: "gain (insert x S) y \<le> gain S y"
    using dec_ge by linarith

  have up: "gain S y \<le> ub y"
    using ubv y_in_old unfolding ub_valid_def by auto

  show "gain (insert x S) y \<le> ub y"
    using dec up by linarith
qed


subsection \<open>One outer step and the full stateful algorithm\<close>

definition lazy_step :: "'a lg_state \<Rightarrow> 'a lg_state" where
  "lazy_step st =
     (let S = Sg st;
          A = remaining st;
          ub = ubg st
      in if A = {} then st
         else
           (let p = lazy_select S A ub;
                x = fst p;
                ub' = snd p
            in \<lparr> Sg = insert x S, ubg = ub' \<rparr>))"

lemma lazy_step_nonempty_Sg:
  assumes rem_ne: "remaining st \<noteq> {}"
  shows
    "Sg (lazy_step st) =
      insert (fst (lazy_select (Sg st) (remaining st) (ubg st))) (Sg st)"
  using rem_ne
  unfolding lazy_step_def
  by (simp add: Let_def)

lemma lazy_step_nonempty_ubg:
  assumes rem_ne: "remaining st \<noteq> {}"
  defines "p \<equiv> lazy_select (Sg st) (remaining st) (ubg st)"
  shows "ubg (lazy_step st) = snd p"
  using rem_ne
  unfolding lazy_step_def p_def
  by (simp add: Let_def)

fun lazy_state :: "nat \<Rightarrow> 'a lg_state" where
  "lazy_state 0 = init_state"
| "lazy_state (Suc i) = lazy_step (lazy_state i)"

definition lazy_set :: "nat \<Rightarrow> 'a set" where
  "lazy_set i = Sg (lazy_state i)"


subsection \<open>Main invariants: subset property and validity on the remaining set\<close>

lemma lazy_step_idle:
  assumes "remaining st = {}"
  shows "lazy_step st = st"
  using assms
  unfolding lazy_step_def remaining_def
  by (simp add: Let_def)


lemma lazy_state_subset_V:
  "Sg (lazy_state i) \<subseteq> V"
proof (induction i)
  case 0
  then show ?case
    by (simp add: init_state_def)
next
  case (Suc i)
  let ?st = "lazy_state i"
  have IH: "Sg ?st \<subseteq> V" using Suc.IH .

  show ?case
  proof (cases "remaining ?st = {}")
    case True
    have step_idle: "lazy_step ?st = ?st"
      using lazy_step_idle[OF True] .
    show ?thesis
      using IH by (simp add: step_idle)
  next
    case False
    let ?S  = "Sg ?st"
    let ?A  = "remaining ?st"
    let ?ub = "ubg ?st"
    let ?p  = "lazy_select ?S ?A ?ub"
    let ?x  = "fst ?p"

    have A_subV: "?A \<subseteq> V"
      unfolding remaining_def using IH by auto

    have finA: "finite ?A"
      by (rule finite_subset[OF A_subV finite_V])

    have neA: "?A \<noteq> {}"
      using False by simp

    have x_inA: "?x \<in> ?A"
    proof -
      have x_eq: "?x = lazy_argmax_gain ?S ?A ?ub"
        using lazy_select_fst by simp
      show ?thesis
        unfolding x_eq
        using lazy_argmax_gain_mem[OF finA neA] .
    qed

    have xV: "?x \<in> V"
      using A_subV x_inA by auto

    have Sg_step:
      "Sg (lazy_step ?st) = insert ?x ?S"
      using lazy_step_nonempty_Sg[OF False]
      by simp

    show ?thesis
      using IH xV
      by (auto simp: Sg_step)
  qed
qed

lemma lazy_state_ub_valid:
  "ub_valid (Sg (lazy_state i)) (remaining (lazy_state i)) (ubg (lazy_state i))"
proof (induction i)
  case 0
  show ?case
    unfolding lazy_state.simps init_state_def remaining_def
    using ub_valid_init by simp
next
  case (Suc i)
  let ?st = "lazy_state i"
  have IH: "ub_valid (Sg ?st) (remaining ?st) (ubg ?st)"
    by (rule Suc.IH)

  show ?case
  proof (cases "remaining ?st = {}")
    case True
    have "lazy_step ?st = ?st"
      using lazy_step_idle[OF True] .
    then show ?thesis
      using IH by simp
  next
    case False
    let ?S = "Sg ?st"
    let ?A = "remaining ?st"
    let ?ub = "ubg ?st"
    let ?p = "lazy_select ?S ?A ?ub"
    let ?x = "fst ?p"
    let ?ub' = "snd ?p"

    have ubvA: "ub_valid ?S ?A ?ub"
      using IH .
    have ubvA': "ub_valid ?S ?A ?ub'"
      using lazy_select_ub_valid[OF ubvA] by simp

    have SsubV: "?S \<subseteq> V"
      using lazy_state_subset_V[of i] by simp

    have A_def: "?A = V - ?S"
      unfolding remaining_def by simp

    have finA: "finite ?A"
      unfolding remaining_def
      using finite_V
      by simp

    have neA: "?A \<noteq> {}"
      using False by simp

    have x_inA: "?x \<in> ?A"
      using lazy_argmax_gain_mem[OF finA neA]
      by (simp add: lazy_select_fst)

    have ubvVS: "ub_valid ?S (V - ?S) ?ub'"
      using ubvA' by (simp add: A_def)

    have x_in_old: "?x \<in> V - ?S"
      using x_inA by (simp add: A_def)

    have ubv_next: "ub_valid (insert ?x ?S) (V - insert ?x ?S) ?ub'"
      using ub_valid_after_insert[OF ubvVS SsubV x_in_old] .

    have Sg_next: "Sg (lazy_step ?st) = insert ?x ?S"
      using lazy_step_nonempty_Sg[OF False] by simp

    have ubg_next: "ubg (lazy_step ?st) = ?ub'"
      using lazy_step_nonempty_ubg[OF False] by (simp add: Let_def)

    have rem_next: "remaining (lazy_step ?st) = V - insert ?x ?S"
      unfolding remaining_def Sg_next by simp

    show ?thesis
      unfolding lazy_state.simps Sg_next ubg_next rem_next
      using ubv_next by simp
  qed
qed

subsection \<open>Correctness of the lazy greedy step\<close>

lemma lazy_step_is_argmax:
  assumes rem_ne: "remaining st \<noteq> {}"
      and ubv: "ub_valid (Sg st) (remaining st) (ubg st)"
      and finA: "finite (remaining st)"
  defines "p \<equiv> lazy_select (Sg st) (remaining st) (ubg st)"
  defines "x \<equiv> fst p"
  shows "\<forall>y\<in>remaining st. gain (Sg st) y \<le> gain (Sg st) x"
proof -
  have x_eq: "x = lazy_argmax_gain (Sg st) (remaining st) (ubg st)"
    unfolding x_def p_def using lazy_select_fst by simp
  show ?thesis
    unfolding x_eq
    using lazy_argmax_gain_max[OF finA rem_ne ubv] .
qed

end

end