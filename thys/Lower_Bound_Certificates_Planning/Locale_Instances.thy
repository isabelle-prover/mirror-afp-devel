section \<open>Locale Instances\<close>

theory Locale_Instances
  imports Hmax_Certificates Efficient_PDB
begin

text \<open>Consistency witnesses for all locales of the development.  A locale whose
  assumptions are contradictory makes every theorem proved inside it vacuous;
  the interpretations below rule this out by exhibiting one concrete model for
  each of @{locale pdb_heuristic}, @{locale hmax_heuristic},
  @{locale efficient_pdb} and @{locale astar_run}.

  The witness is the smallest non-degenerate planning task: one variable
  @{text "0"}, initially false, required by the goal, and one action that adds
  it at cost 1.  The optimal plan is the single-action plan of cost 1, and we
  use the bound @{text "B = 1"}.  All interesting locale assumptions
  (the PDB distance conditions @{text d_goal}/@{text d_triangle}, the hmax
  table conditions, the A* expansion-closure condition) are discharged
  non-vacuously.

  The A* interpretation is additionally instantiated with the \<^emph>\<open>interpreted\<close>
  PDB certificate at the embedded variable type @{typ "nat + nat"} (gate names
  @{text "Inr (2*j+1)"}), i.e. the locales compose exactly as the paper's
  PDB-into-A* case study intends.  As a final sanity check the composition
  yields the concrete theorem @{text "optimal_plan demo_task [demo_act]"}.\<close>

subsection \<open>The demo task\<close>

definition demo_act :: "nat action" where
  "demo_act = \<lparr> pre = {}, add = {0}, del = {}, cost = 1 \<rparr>"

definition demo_task :: "nat strips_task" where
  "demo_task = \<lparr> vars = {0}, acts = {demo_act}, init = {}, goal = {0} \<rparr>"

lemma demo_pow: "set [{}, {0::nat}] = Pow {0}"
  by (auto dest: subset_singletonD)

subsection \<open>Interpretation of @{locale pdb_heuristic}\<close>

interpretation demo_pdb: pdb_heuristic demo_task 1 "{0::nat}"
  "\<lambda>sa. if 0 \<in> sa then 0 else 1" "[{}, {0}]" "[demo_act]" id
proof unfold_locales
  show "finite (vars demo_task)" by (simp add: demo_task_def)
  show "{0::nat} \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "set [{}, {0::nat}] = Pow {0}" by (rule demo_pow)
  show "distinct [{}, {0::nat}]" by simp
  show "\<forall>a \<in> set [demo_act].
      pre a \<subseteq> vars demo_task \<and> add a \<subseteq> vars demo_task \<and> del a \<subseteq> vars demo_task"
    by (simp add: demo_act_def demo_task_def)
  show "\<forall>a \<in> set [demo_act]. add a \<inter> del a = {}"
    by (simp add: demo_act_def)
  show "\<And>sa. sa \<subseteq> {0::nat} \<Longrightarrow> goal demo_task \<inter> {0} \<subseteq> sa \<Longrightarrow>
      (if 0 \<in> sa then 0 else 1) = (0::nat)"
    by (auto simp: demo_task_def)
  show "\<And>sa a. sa \<subseteq> {0::nat} \<Longrightarrow> a \<in> set [demo_act] \<Longrightarrow> pre a \<inter> {0} \<subseteq> sa \<Longrightarrow>
      (if 0 \<in> sa then 0 else 1)
        \<le> (if 0 \<in> (sa - del a) \<union> (add a \<inter> {0}) then 0 else 1) + cost a"
    by (auto simp: demo_act_def)
  show "inj (id :: nat \<Rightarrow> nat)" by simp
qed

text \<open>The interpreted facts are available, e.g. the validity of the PDB
  certificate for the demo table:\<close>

lemma "hc_valid demo_task 1 [demo_act] demo_pdb.pdb_cert S"
  by (rule demo_pdb.pdb_hc_valid)

subsection \<open>Interpretation of @{locale hmax_heuristic}\<close>

text \<open>The evaluated state is the initial state @{term "{} :: nat state"}; its
  hmax value is 1 (the single goal variable costs 1 to achieve), and the
  clipped max value of every variable is 1.\<close>

interpretation demo_hmax: hmax_heuristic demo_task 1 "{} :: nat state" 1
  "\<lambda>v. 1" "[0]" "[demo_act]" id
proof unfold_locales
  show "finite (vars demo_task)" by (simp add: demo_task_def)
  show "goal demo_task \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "{} \<subseteq> vars demo_task" by simp
  show "set [0] = vars demo_task" by (simp add: demo_task_def)
  show "distinct [0::nat]" by simp
  show "\<forall>a \<in> set [demo_act].
      pre a \<subseteq> vars demo_task \<and> add a \<subseteq> vars demo_task \<and> del a \<subseteq> vars demo_task"
    by (simp add: demo_act_def demo_task_def)
  show "\<forall>a \<in> set [demo_act]. add a \<inter> del a = {}"
    by (simp add: demo_act_def)
  show "\<And>v. v \<in> ({} :: nat state) \<Longrightarrow> (1::nat) = 0" by simp
  show "goal demo_task \<noteq> {} \<Longrightarrow> \<exists>v \<in> goal demo_task. (1::nat) = 1"
    by (simp add: demo_task_def)
  show "goal demo_task = {} \<Longrightarrow> (1::nat) = 0" by (simp add: demo_task_def)
  show "\<And>a v. a \<in> set [demo_act] \<Longrightarrow> v \<in> add a \<Longrightarrow> pre a \<noteq> {} \<Longrightarrow>
      \<exists>p \<in> pre a. (1::nat) \<le> 1 + cost a"
    by (simp add: demo_act_def)
  show "\<And>a v. a \<in> set [demo_act] \<Longrightarrow> v \<in> add a \<Longrightarrow> pre a = {} \<Longrightarrow>
      (1::nat) \<le> cost a"
    by (simp add: demo_act_def)
  show "inj (id :: nat \<Rightarrow> nat)" by simp
qed

lemma "hc_valid demo_task 1 [demo_act] demo_hmax.hmax_cert {{}}"
  by (rule demo_hmax.hmax_hc_valid)

subsection \<open>Interpretation of @{locale efficient_pdb}\<close>

text \<open>In the demo task every abstract state reaches the abstract goal, so the
  finiteness predicate is constantly true and the table coincides with the
  plain PDB table.\<close>

interpretation demo_epdb: efficient_pdb demo_task 1 "{0::nat}"
  "\<lambda>sa. if 0 \<in> sa then 0 else 1" "\<lambda>sa. True" "[{}, {0}]" "[demo_act]" id
proof unfold_locales
  show "finite (vars demo_task)" by (simp add: demo_task_def)
  show "{0::nat} \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "set [{}, {0::nat}] = {sa. sa \<subseteq> {0} \<and> True}"
    using demo_pow by auto
  show "distinct [{}, {0::nat}]" by simp
  show "\<forall>a \<in> set [demo_act].
      pre a \<subseteq> vars demo_task \<and> add a \<subseteq> vars demo_task \<and> del a \<subseteq> vars demo_task"
    by (simp add: demo_act_def demo_task_def)
  show "\<forall>a \<in> set [demo_act]. add a \<inter> del a = {}"
    by (simp add: demo_act_def)
  show "\<And>sa. sa \<subseteq> {0::nat} \<Longrightarrow> goal demo_task \<inter> {0} \<subseteq> sa \<Longrightarrow>
      True \<and> (if 0 \<in> sa then 0 else 1) = (0::nat)"
    by (auto simp: demo_task_def)
  show "\<And>sa a. sa \<subseteq> {0::nat} \<Longrightarrow> a \<in> set [demo_act] \<Longrightarrow> pre a \<inter> {0} \<subseteq> sa \<Longrightarrow>
      True \<Longrightarrow> True \<and> (if 0 \<in> sa then 0 else 1)
        \<le> (if 0 \<in> (sa - del a) \<union> (add a \<inter> {0}) then 0 else 1) + cost a"
    by (auto simp: demo_act_def)
  show "inj (id :: nat \<Rightarrow> nat)" by simp
qed

lemma "hc_valid demo_task 1 [demo_act] demo_epdb.epdb_cert S"
  by (rule demo_epdb.epdb_hc_valid)

subsection \<open>Interpretation of @{locale pdb_heuristic} at the embedded type\<close>

text \<open>For the A* interpretation the heuristic certificate must live at the
  extended variable type @{typ "nat + nat"} with the odd gate names
  @{text "Inr (2*j+1)"} that @{locale astar_run} reserves for the heuristic.\<close>

lemma demo_taskE_simps:
  "vars (embed_task demo_task :: (nat + nat) strips_task) = {Inl 0}"
  "goal (embed_task demo_task :: (nat + nat) strips_task) = {Inl 0}"
  "init (embed_task demo_task :: (nat + nat) strips_task) = {}"
  "acts (embed_task demo_task :: (nat + nat) strips_task) = {embed_act demo_act}"
  by (simp_all add: embed_task_def demo_task_def)

lemma demo_actE_simps:
  "pre (embed_act demo_act :: (nat + nat) action) = {}"
  "add (embed_act demo_act :: (nat + nat) action) = {Inl 0}"
  "del (embed_act demo_act :: (nat + nat) action) = {}"
  "cost (embed_act demo_act :: (nat + nat) action) = 1"
  by (simp_all add: embed_act_def demo_act_def)

lemma demo_powE: "set [{}, {Inl 0} :: (nat + nat) state] = Pow {Inl 0}"
  by (auto dest: subset_singletonD)

interpretation demoE_pdb: pdb_heuristic
  "embed_task demo_task :: (nat + nat) strips_task" 1 "{Inl 0}"
  "\<lambda>sa. if Inl 0 \<in> sa then 0 else 1" "[{}, {Inl 0}]" "[embed_act demo_act]"
  "\<lambda>j. Inr (2 * j + 1)"
proof unfold_locales
  show "finite (vars (embed_task demo_task :: (nat + nat) strips_task))"
    by (simp add: demo_taskE_simps)
  show "{Inl 0} \<subseteq> vars (embed_task demo_task :: (nat + nat) strips_task)"
    by (simp add: demo_taskE_simps)
  show "set [{}, {Inl 0} :: (nat + nat) state] = Pow {Inl 0}"
    by (rule demo_powE)
  show "distinct [{}, {Inl 0} :: (nat + nat) state]" by simp
  show "\<forall>a \<in> set [embed_act demo_act :: (nat + nat) action].
      pre a \<subseteq> vars (embed_task demo_task)
      \<and> add a \<subseteq> vars (embed_task demo_task)
      \<and> del a \<subseteq> vars (embed_task demo_task)"
    by (simp add: demo_actE_simps demo_taskE_simps)
  show "\<forall>a \<in> set [embed_act demo_act :: (nat + nat) action]. add a \<inter> del a = {}"
    by (simp add: demo_actE_simps)
  show "\<And>sa. sa \<subseteq> {Inl 0} \<Longrightarrow>
      goal (embed_task demo_task :: (nat + nat) strips_task) \<inter> {Inl 0} \<subseteq> sa \<Longrightarrow>
      (if Inl 0 \<in> sa then 0 else 1) = (0::nat)"
    by (auto simp: demo_taskE_simps)
  show "\<And>sa a. sa \<subseteq> {Inl 0} \<Longrightarrow> a \<in> set [embed_act demo_act :: (nat + nat) action] \<Longrightarrow>
      pre a \<inter> {Inl 0} \<subseteq> sa \<Longrightarrow>
      (if Inl 0 \<in> sa then 0 else 1)
        \<le> (if Inl 0 \<in> (sa - del a) \<union> (add a \<inter> {Inl 0}) then 0 else 1) + cost a"
    by (auto simp: demo_actE_simps)
  show "inj (\<lambda>j. Inr (2 * j + 1) :: nat + nat)"
    by (auto simp: inj_def)
qed

subsection \<open>Interpretation of @{locale astar_run}\<close>

text \<open>The A* snapshot after expanding the initial state: the closed list holds
  @{term "({}, 0)"}, the open list holds the goal state @{term "{0::nat}"}, and
  the heuristic certificate is the interpreted embedded PDB certificate.\<close>

interpretation demo_astar: astar_run demo_task 1 "[({}, 0)]" "[{0::nat}]"
  demoE_pdb.pdb_cert "[embed_act demo_act]"
proof unfold_locales
  show "finite (vars demo_task)" by (simp add: demo_task_def)
  show "init demo_task \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "goal demo_task \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "finite (acts demo_task)" by (simp add: demo_task_def)
  show "\<forall>a \<in> acts demo_task. add a \<inter> del a = {}"
    by (simp add: demo_task_def demo_act_def)
  show "\<forall>a \<in> acts demo_task.
      pre a \<subseteq> vars demo_task \<and> add a \<subseteq> vars demo_task \<and> del a \<subseteq> vars demo_task"
    by (simp add: demo_task_def demo_act_def)
  show "set [embed_act demo_act] = acts (embed_task demo_task)"
    by (simp add: embed_task_def demo_task_def)
  show "(1::nat) \<ge> 1" by simp
  show "(init demo_task, 0) \<in> set [({}, 0)]" by (simp add: demo_task_def)
  show "\<forall>(s, g) \<in> set [({}, 0)]. s \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "\<forall>s \<in> set [{0::nat}]. s \<subseteq> vars demo_task" by (simp add: demo_task_def)
  show "\<forall>(s, g) \<in> set [({}, 0::nat)]. is_goal_state demo_task s \<longrightarrow> g \<ge> 1"
    by (simp add: is_goal_state_def demo_task_def)
  show "\<forall>(s, g) \<in> set [({}, 0::nat)]. \<forall>a \<in> acts demo_task. applicable a s \<longrightarrow>
      (is_goal_state demo_task s \<and> g \<ge> 1)
    \<or> (\<exists>g'. (successor a s, g') \<in> set [({}, 0)] \<and> g' \<le> g + cost a)
    \<or> (successor a s \<in> set [{0::nat}] \<and>
       int (g + cost a) \<ge> int 1 - int (hc_h demoE_pdb.pdb_cert (Inl ` successor a s)))"
  proof -
    have succ: "successor demo_act {} = {0}"
      by (simp add: successor_def demo_act_def)
    have h0: "hc_h demoE_pdb.pdb_cert {Inl (0::nat)} = 0"
      unfolding demoE_pdb.pdb_cert_def by simp
    have cost_a: "cost demo_act = 1"
      by (simp add: demo_act_def)
    have third: "successor demo_act {} \<in> set [{0::nat}] \<and>
        int (0 + cost demo_act)
          \<ge> int 1 - int (hc_h demoE_pdb.pdb_cert (Inl ` successor demo_act {}))"
      by (simp add: succ h0 cost_a)
    have inner: "\<forall>a \<in> acts demo_task. applicable a {} \<longrightarrow>
        (is_goal_state demo_task {} \<and> (0::nat) \<ge> 1)
      \<or> (\<exists>g'. (successor a {}, g') \<in> set [({}, 0)] \<and> g' \<le> 0 + cost a)
      \<or> (successor a {} \<in> set [{0::nat}] \<and>
         int (0 + cost a) \<ge> int 1 - int (hc_h demoE_pdb.pdb_cert (Inl ` successor a {})))"
    proof
      fix a assume "a \<in> acts demo_task"
      then have a_eq: "a = demo_act" by (simp add: demo_task_def)
      show "applicable a {} \<longrightarrow>
          (is_goal_state demo_task {} \<and> (0::nat) \<ge> 1)
        \<or> (\<exists>g'. (successor a {}, g') \<in> set [({}, 0)] \<and> g' \<le> 0 + cost a)
        \<or> (successor a {} \<in> set [{0::nat}] \<and>
           int (0 + cost a) \<ge> int 1 - int (hc_h demoE_pdb.pdb_cert (Inl ` successor a {})))"
        unfolding a_eq using third by blast
    qed
    show ?thesis using inner by simp
  qed
  show "hc_valid (embed_task demo_task) 1 [embed_act demo_act] demoE_pdb.pdb_cert
      ((\<lambda>s. Inl ` s) ` set [{0::nat}])"
    by (rule demoE_pdb.pdb_hc_valid)
  show "\<forall>(r, cs, A) \<in> set (hc_gates demoE_pdb.pdb_cert).
      \<exists>j. r = Pos (ReifCert (Inr (2 * j + 1)))"
    using demoE_pdb.pdb_names by auto
  show "distinct (map (\<lambda>(r, cs, A). pvar_of_lit r) (hc_gates demoE_pdb.pdb_cert))"
    by (rule demoE_pdb.pdb_distinct)
  show "\<forall>i < length (hc_gates demoE_pdb.pdb_cert).
      case hc_gates demoE_pdb.pdb_cert ! i of (r, cs, A) \<Rightarrow>
        (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
          (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
          \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates demoE_pdb.pdb_cert)))"
    by (rule demoE_pdb.pdb_wf)
  show "\<forall>s \<in> set [{0::nat}].
      hc_out demoE_pdb.pdb_cert (Inl ` s) \<in> fst ` set (hc_gates demoE_pdb.pdb_cert)"
    using demoE_pdb.pdb_out_in by simp
qed

subsection \<open>End-to-end sanity check\<close>

text \<open>The composed interpretations yield a concrete, non-vacuous consequence:
  the single-action plan is optimal for the demo task.\<close>

lemma demo_plan: "is_plan_for demo_task [demo_act]"
proof -
  have succ: "successor demo_act {} = {0}"
    by (simp add: successor_def demo_act_def)
  have p0: "path (acts demo_task) (successor demo_act {}) {0} []"
    unfolding succ by (rule path.path_nil)
  have appl: "applicable demo_act {}"
    by (simp add: applicable_def demo_act_def)
  have mem: "demo_act \<in> acts demo_task"
    by (simp add: demo_task_def)
  have "path (acts demo_task) {} {0} [demo_act]"
    by (rule path.path_cons[OF appl p0 mem])
  then show ?thesis
    unfolding is_plan_for_def is_goal_state_def
    by (intro exI[of _ "{0}"]) (simp add: demo_task_def)
qed

lemma demo_cost: "plan_cost [demo_act] = 1"
  by (simp add: plan_cost_def demo_act_def)

theorem demo_optimal: "optimal_plan demo_task [demo_act]"
  by (rule demo_astar.astar_optimal[OF demo_plan demo_cost])

text \<open>And the lower bound directly: every plan for the demo task costs at
  least 1.\<close>

theorem demo_lower_bound: "is_plan_for demo_task \<pi> \<Longrightarrow> plan_cost \<pi> \<ge> 1"
  by (rule demo_astar.astar_lower_bound)

end
