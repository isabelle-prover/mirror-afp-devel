section \<open>Maximum Heuristic Certificates\<close>

theory Hmax_Certificates
  imports A_Star_Certificates
begin

text \<open>Proof-logging the maximum heuristic (paper equations (17)--(18) and
  Lemmas 14--17).  The certificate is built per evaluated state @{text s} from
  the values an hmax implementation computes anyway: the heuristic estimate
  @{text "h = hmax(s)"} and the clipped max values
  @{text "W(v) = min{Vmax(v), hmax(s)}"}.  The locale @{text hmax_heuristic}
  captures exactly the properties of this table that the soundness of the
  certificate requires (all consequences of the hmax fixed-point equations):
  @{text W} vanishes on @{text s}, some goal variable carries the full value
  @{text h} (or the goal is empty and @{text "h = 0"}), and @{text W} satisfies
  the action-step recurrence
  @{text "W(v) \<le> W(p) + cost(a)"} for add effects @{text v} and some
  precondition @{text p} (or @{text "W(v) \<le> cost(a)"} for actions without
  preconditions).  The K-gates referenced by equations (17) and (18) are inlined
  over the cost bits, as everywhere else in this formalization.  The resulting
  @{type heuristic_cert} is valid in the sense of Definition 4 for the
  singleton set of evaluated states @{text "{s}"} (the paper circuit
  @{text "\<langle>Hmax,s, rmax_s\<rangle>"} is likewise per-state).\<close>

subsection \<open>The hmax locale\<close>

locale hmax_heuristic =
  fixes \<Pi>e :: "'u::linorder strips_task"
    and B :: nat
    and s :: "'u state"
    and h :: nat
    and W :: "'u \<Rightarrow> nat"
    and vs :: "'u list"
    and as :: "'u action list"
    and nm :: "nat \<Rightarrow> 'u"
  assumes fin_vars: "finite (vars \<Pi>e)"
    and goal_sub: "goal \<Pi>e \<subseteq> vars \<Pi>e"
    and s_sub: "s \<subseteq> vars \<Pi>e"
    and vs_set: "set vs = vars \<Pi>e"
    and vs_dist: "distinct vs"
    and as_states: "\<forall>a \<in> set as. pre a \<subseteq> vars \<Pi>e \<and> add a \<subseteq> vars \<Pi>e \<and> del a \<subseteq> vars \<Pi>e"
    and as_disjoint: "\<forall>a \<in> set as. add a \<inter> del a = {}"
    and W_zero: "\<And>v. v \<in> s \<Longrightarrow> W v = 0"
    and goal_W: "goal \<Pi>e \<noteq> {} \<Longrightarrow> \<exists>v \<in> goal \<Pi>e. W v = h"
    and goal_empty: "goal \<Pi>e = {} \<Longrightarrow> h = 0"
    and W_step_pre: "\<And>a v. a \<in> set as \<Longrightarrow> v \<in> add a \<Longrightarrow> pre a \<noteq> {} \<Longrightarrow>
        \<exists>p \<in> pre a. W v \<le> W p + cost a"
    and W_step_empty: "\<And>a v. a \<in> set as \<Longrightarrow> v \<in> add a \<Longrightarrow> pre a = {} \<Longrightarrow>
        W v \<le> cost a"
    and nm_inj: "inj nm"
begin

definition n_v :: nat where
  "n_v = length vs"

definition v_i :: "nat \<Rightarrow> 'u" where
  "v_i i = vs ! i"

lemma v_i_in: "i < n_v \<Longrightarrow> v_i i \<in> vars \<Pi>e"
  using vs_set nth_mem unfolding n_v_def v_i_def by fastforce

lemma var_mem_nth:
  assumes "v \<in> vars \<Pi>e"
  shows "\<exists>i. i < n_v \<and> v_i i = v"
proof -
  have "v \<in> set vs" using assms vs_set by auto
  then show ?thesis
    unfolding n_v_def v_i_def by (auto simp: in_set_conv_nth)
qed

subsubsection \<open>Gate names\<close>

definition kv_name :: "nat \<Rightarrow> 'u pvar" where
  "kv_name i = ReifCert (nm i)"

definition rv_name :: "nat \<Rightarrow> 'u pvar" where
  "rv_name i = ReifCert (nm (n_v + i))"

definition kb_name :: "'u pvar" where
  "kb_name = ReifCert (nm (2 * n_v))"

definition max_name :: "'u pvar" where
  "max_name = ReifCert (nm (2 * n_v + 1))"

subsubsection \<open>Gates\<close>

text \<open>The K-gate part of equation (17): the clipped cost threshold for
  @{text "B - hmax(s) + Wmax(v)"}, inlined over the cost bits.\<close>

definition kvg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "kvg i = k_gate (Pos (kv_name i)) B (int B - int h + int (W (v_i i)))"

text \<open>Equation (17): the variable gate is the disjunction of the negated state
  variable and its K-gate.\<close>

definition rv_lits :: "nat \<Rightarrow> 'u pvar literal list" where
  "rv_lits i = [Neg (StateVar (v_i i)), Pos (kv_name i)]"

definition rvg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "rvg i = (Pos (rv_name i), map (\<lambda>l. (1, l)) (rv_lits i), 1)"

text \<open>The base K-gate for @{text "B - hmax(s)"} used by equation (18).\<close>

definition kbg :: "'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "kbg = k_gate (Pos kb_name) B (int B - int h)"

text \<open>Equation (18): the output is the conjunction of the base K-gate and all
  variable gates (the paper's threshold @{text "|V| + 1"} over 0/1 summands).\<close>

definition max_lits :: "'u pvar literal list" where
  "max_lits = Pos kb_name # map (\<lambda>i. Pos (rv_name i)) [0..<n_v]"

definition mxg :: "'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "mxg = (Pos max_name, map (\<lambda>l. (1, l)) max_lits, length max_lits)"

definition hmax_gates ::
  "('u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat) list" where
  "hmax_gates = map kvg [0..<n_v] @ map rvg [0..<n_v] @ [kbg, mxg]"

definition hmax_cert :: "('u) heuristic_cert" where
  "hmax_cert = \<lparr> hc_gates = hmax_gates,
                 hc_out = (\<lambda>s'. Pos max_name),
                 hc_h = (\<lambda>s'. h) \<rparr>"

subsubsection \<open>Basic structure of the gate list\<close>

lemma length_hmax_gates: "length hmax_gates = 2 * n_v + 2"
  by (simp add: hmax_gates_def)

lemma kvg_in_gates: "i < n_v \<Longrightarrow> kvg i \<in> set hmax_gates"
  by (simp add: hmax_gates_def)

lemma rvg_in_gates: "i < n_v \<Longrightarrow> rvg i \<in> set hmax_gates"
  by (simp add: hmax_gates_def)

lemma kbg_in_gates: "kbg \<in> set hmax_gates"
  by (simp add: hmax_gates_def)

lemma mxg_in_gates: "mxg \<in> set hmax_gates"
  by (simp add: hmax_gates_def)

lemma models_hmax_gate:
  assumes m: "models (hc_constraints hmax_cert) rho"
    and g_in: "(r, cs, A) \<in> set hmax_gates"
  shows "models (reification r cs A) rho"
proof (rule models_mono[OF m])
  show "reification r cs A \<subseteq> hc_constraints hmax_cert"
    using g_in unfolding hc_constraints_def hmax_cert_def by fastforce
qed

lemma models_kvg:
  assumes "models (hc_constraints hmax_cert) rho" and "i < n_v"
  shows "models (reification (Pos (kv_name i)) (k_gate_body B)
      (clip B (int B - int h + int (W (v_i i))))) rho"
  using models_hmax_gate[OF assms(1)] kvg_in_gates[OF assms(2)]
  by (simp add: kvg_def k_gate_def)

lemma models_rvg:
  assumes "models (hc_constraints hmax_cert) rho" and "i < n_v"
  shows "models (reification (Pos (rv_name i)) (map (\<lambda>l. (1, l)) (rv_lits i)) 1) rho"
  using models_hmax_gate[OF assms(1)] rvg_in_gates[OF assms(2)]
  by (simp add: rvg_def)

lemma models_kbg:
  assumes "models (hc_constraints hmax_cert) rho"
  shows "models (reification (Pos kb_name) (k_gate_body B) (clip B (int B - int h))) rho"
  using models_hmax_gate[OF assms] kbg_in_gates
  by (simp add: kbg_def k_gate_def)

lemma models_mxg:
  assumes "models (hc_constraints hmax_cert) rho"
  shows "models (reification (Pos max_name)
      (map (\<lambda>l. (1, l)) max_lits) (length max_lits)) rho"
  using models_hmax_gate[OF assms] mxg_in_gates
  by (simp add: mxg_def)

subsubsection \<open>Semantics of the gates\<close>

lemma kvg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
    and i_lt: "i < n_v"
  shows "rho (kv_name i) = 1
     \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int h + int (W (v_i i)))"
proof -
  have "eval_lit (Pos (kv_name i)) rho = 1
      \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int h + int (W (v_i i)))"
    by (rule k_gate_forces[OF rho01 models_kvg[OF m i_lt]])
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma rvg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
    and i_lt: "i < n_v"
  shows "rho (rv_name i) = 1
     \<longleftrightarrow> rho (StateVar (v_i i)) = 0 \<or> rho (kv_name i) = 1"
proof -
  have "eval_lit (Pos (rv_name i)) rho = 1
      \<longleftrightarrow> (\<exists>l \<in> set (rv_lits i). eval_lit l rho = 1)"
    by (rule disj_gate_forces[OF rho01 models_rvg[OF m i_lt]])
  then show ?thesis by (auto simp: rv_lits_def eval_lit_def)
qed

lemma kbg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
  shows "rho kb_name = 1
     \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int h)"
proof -
  have "eval_lit (Pos kb_name) rho = 1
      \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int h)"
    by (rule k_gate_forces[OF rho01 models_kbg[OF m]])
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma mxg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
  shows "rho max_name = 1
     \<longleftrightarrow> rho kb_name = 1 \<and> (\<forall>i < n_v. rho (rv_name i) = 1)"
proof -
  have "eval_lit (Pos max_name) rho = 1
      \<longleftrightarrow> (\<forall>l \<in> set max_lits. eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_mxg[OF m]])
  then show ?thesis by (auto simp: max_lits_def eval_lit_def)
qed

subsection \<open>Lemma 14: the state lemma\<close>

lemma hmax_state_lemma: "hc_state_lemma \<Pi>e B hmax_cert s"
  unfolding hc_state_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
    and sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
    and cb: "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h hmax_cert s))"
  have cb': "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int h)"
    using cb by (simp add: hmax_cert_def)
  have kb1: "rho kb_name = 1"
    using kbg_forces[OF rho01 m] cb' by simp
  have rv_all: "\<forall>i < n_v. rho (rv_name i) = 1"
  proof (intro allI impI)
    fix i assume i_lt: "i < n_v"
    show "rho (rv_name i) = 1"
    proof (cases "v_i i \<in> s")
      case True
      have "clip B (int B - int h + int (W (v_i i))) = clip B (int B - int h)"
        using W_zero[OF True] by simp
      then have "rho (kv_name i) = 1"
        using kvg_forces[OF rho01 m i_lt] cb' by simp
      then show ?thesis using rvg_forces[OF rho01 m i_lt] by blast
    next
      case False
      have "rho (StateVar (v_i i)) = 0"
        using sv v_i_in[OF i_lt] False by simp
      then show ?thesis using rvg_forces[OF rho01 m i_lt] by blast
    qed
  qed
  have "rho max_name = 1"
    using mxg_forces[OF rho01 m] kb1 rv_all by blast
  then show "eval_lit (hc_out hmax_cert s) rho = 1"
    by (simp add: hmax_cert_def eval_lit_def)
qed

subsection \<open>Lemma 15: the goal lemma\<close>

lemma hmax_goal_lemma: "hc_goal_lemma \<Pi>e B hmax_cert s'"
  unfolding hc_goal_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints hmax_cert) rho"
    and gv: "\<forall>v \<in> goal \<Pi>e. rho (StateVar v) = 1"
    and out1: "eval_lit (hc_out hmax_cert s') rho = 1"
  have mx1: "rho max_name = 1"
    using out1 by (simp add: hmax_cert_def eval_lit_def)
  have kb1: "rho kb_name = 1" and rv_all: "\<forall>i < n_v. rho (rv_name i) = 1"
    using mxg_forces[OF rho01 m] mx1 by blast+
  show "bits_val (bits_needed B) CostBit rho \<ge> B"
  proof (cases "goal \<Pi>e = {}")
    case True
    have "h = 0" by (rule goal_empty[OF True])
    then have "clip B (int B - int h) = B" by simp
    then show ?thesis using kbg_forces[OF rho01 m] kb1 by simp
  next
    case False
    obtain v where vG: "v \<in> goal \<Pi>e" and vW: "W v = h"
      using goal_W[OF False] by blast
    obtain i where i_lt: "i < n_v" and i_v: "v_i i = v"
      using var_mem_nth goal_sub vG by blast
    have "rho (StateVar v) = 1" using gv vG by blast
    then have "rho (kv_name i) = 1"
      using rvg_forces[OF rho01 m i_lt] rv_all i_lt i_v by auto
    moreover have "clip B (int B - int h + int (W (v_i i))) = B"
      by (simp add: i_v vW)
    ultimately show ?thesis using kvg_forces[OF rho01 m i_lt] by simp
  qed
qed

subsection \<open>Lemmas 16--17: the inductivity lemma\<close>

text \<open>Paper Lemma 16 establishes the step for a single action by a case
  analysis over how each variable occurs in the action's effects; Lemma 17
  generalizes over the selected action.  Semantically both collapse into one
  chase: the selected action of the encoded transition is fixed, and each
  variable gate of the primed copy is established by the add / delete / frame
  case analysis, using the @{text W}-recurrence for add effects.\<close>

lemma hmax_ind_lemma: "hc_ind_lemma \<Pi>e B as hmax_cert s'"
  unfolding hc_ind_lemma_def
proof (intro allI impI)
  fix rho :: "'u var pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mO: "models (circuit_constraints
        (orig_circuit (hc_gates hmax_cert, hc_out hmax_cert s'))) rho"
    and mP: "models (circuit_constraints
        (primed_circuit (hc_gates hmax_cert, hc_out hmax_cert s'))) rho"
    and mT: "models (encode_transition as (vars \<Pi>e) B) rho"
    and mB: "models (encode_cost_ge B) rho"
    and rT: "rho ReifT = 1"
    and outO: "eval_lit (map_literal (map_pvar Original) (hc_out hmax_cert s')) rho = 1"
  define rho_o where "rho_o = rho \<circ> map_pvar Original"
  define rho_p where "rho_p = rho \<circ> primed_pvar_map"
  have rho_o01: "\<forall>x. rho_o x = 0 \<or> rho_o x = 1"
    unfolding rho_o_def by (rule rho01_comp[OF rho01])
  have rho_p01: "\<forall>x. rho_p x = 0 \<or> rho_p x = 1"
    unfolding rho_p_def by (rule rho01_comp[OF rho01])
  have mO'': "models (circuit_constraints (hc_gates hmax_cert, hc_out hmax_cert s')) rho_o"
    using mO models_circuit_constraints_lift[of "map_pvar Original"
        "(hc_gates hmax_cert, hc_out hmax_cert s')" rho]
    unfolding rho_o_def orig_circuit_def by blast
  have mO': "models (hc_constraints hmax_cert) rho_o"
    using mO'' hc_constraints_eq_circuit[of hmax_cert "hc_out hmax_cert s'"] by simp
  have mP'': "models (circuit_constraints (hc_gates hmax_cert, hc_out hmax_cert s')) rho_p"
    using mP models_circuit_constraints_lift[of primed_pvar_map
        "(hc_gates hmax_cert, hc_out hmax_cert s')" rho]
    unfolding rho_p_def primed_circuit_def by blast
  have mP': "models (hc_constraints hmax_cert) rho_p"
    using mP'' hc_constraints_eq_circuit[of hmax_cert "hc_out hmax_cert s'"] by simp
  define c where "c = bits_val (bits_needed B) CostBit rho"
  define c' where "c' = bits_val (bits_needed B) PrimedCostBit rho"
  have c_o: "bits_val (bits_needed B) CostBit rho_o = c"
    by (simp add: rho_o_def c_def bits_val_def)
  have c_p: "bits_val (bits_needed B) CostBit rho_p = c'"
    by (simp add: rho_p_def c'_def bits_val_def)
  \<comment> \<open>The selected action (paper Lemma 17 quantifies over it).\<close>
  have mSel: "models (action_selection_reif (action_reifs as)) rho"
    by (rule trans_sel[OF mT])
  obtain rA where rA_in: "rA \<in> set (action_reifs as)" and rA1: "eval_lit rA rho = 1"
    using action_selection_forces[OF rho01 mSel] rT by blast
  obtain j where j_lt: "j < length as" and rA_eq: "rA = Pos (ReifAction j)"
    using rA_in unfolding action_reifs_def by auto
  define a where "a = as ! j"
  have a_in: "a \<in> set as" unfolding a_def by (rule nth_mem[OF j_lt])
  have satAC: "satisfies (action_constraint (Pos (ReifAction j)) a (vars \<Pi>e) B) rho"
    unfolding a_def by (rule trans_action_constraint[OF mT j_lt])
  have preS: "pre a \<subseteq> vars \<Pi>e" and addS: "add a \<subseteq> vars \<Pi>e" and delS: "del a \<subseteq> vars \<Pi>e"
    using bspec[OF as_states a_in] by auto
  have outj: "eval_lit (Pos (ReifAction j)) rho = 1"
    using rA1 rA_eq by simp
  note ext = action_constraint_extract[OF rho01 satAC outj fin_vars preS addS delS]
  have delta1: "rho (ReifDeltaCost (cost a)) = 1" using ext by blast
  have preO: "\<forall>w \<in> pre a. rho (StateVar (Original w)) = 1" using ext by blast
  have addP: "\<forall>w \<in> add a - del a. rho (StateVar (Primed w)) = 1" using ext by blast
  have delP: "\<forall>w \<in> del a - add a. rho (StateVar (Primed w)) = 0" using ext by blast
  have frameO: "\<forall>w \<in> vars \<Pi>e - evars a. rho (ReifEq (Original w)) = 1" using ext by blast
  have mD: "models (encode_delta_cost (cost a) (bits_needed B)) rho"
    by (rule trans_delta[OF mT a_in])
  have c'_eq: "c' = c + cost a"
    using encode_delta_cost_forces[OF rho01 mD] delta1
    by (simp add: c_def c'_def)
  \<comment> \<open>The true output gate on the unprimed side.\<close>
  have outO': "rho_o max_name = 1"
    using outO unfolding hmax_cert_def
    by (simp add: eval_lit_map_literal rho_o_def eval_lit_def)
  have kb_o: "rho_o kb_name = 1" and rv_o: "\<forall>i < n_v. rho_o (rv_name i) = 1"
    using mxg_forces[OF rho_o01 mO'] outO' by blast+
  have c_base: "c \<ge> clip B (int B - int h)"
    using kbg_forces[OF rho_o01 mO'] kb_o c_o by simp
  \<comment> \<open>A true unprimed state variable carries its cost threshold.\<close>
  have carry: "\<And>v. v \<in> vars \<Pi>e \<Longrightarrow> rho_o (StateVar v) = 1 \<Longrightarrow>
      c \<ge> clip B (int B - int h + int (W v))"
  proof -
    fix v assume vV: "v \<in> vars \<Pi>e" and v1: "rho_o (StateVar v) = 1"
    obtain i where i_lt: "i < n_v" and i_v: "v_i i = v"
      using var_mem_nth[OF vV] by blast
    have "rho_o (kv_name i) = 1"
      using rvg_forces[OF rho_o01 mO' i_lt] rv_o i_lt i_v v1 by auto
    then show "c \<ge> clip B (int B - int h + int (W v))"
      using kvg_forces[OF rho_o01 mO' i_lt] c_o i_v by simp
  qed
  \<comment> \<open>Base K-gate of the primed copy.\<close>
  have kb_p: "rho_p kb_name = 1"
  proof -
    have "c' \<ge> clip B (int B - int h)" using c_base c'_eq by simp
    then show ?thesis using kbg_forces[OF rho_p01 mP'] c_p by simp
  qed
  \<comment> \<open>Paper Lemma 16: the variable gates of the primed copy, by the
      add / delete / frame case analysis.\<close>
  have rv_p: "\<forall>i < n_v. rho_p (rv_name i) = 1"
  proof (intro allI impI)
    fix i assume i_lt: "i < n_v"
    define v where "v = v_i i"
    have vV: "v \<in> vars \<Pi>e" unfolding v_def by (rule v_i_in[OF i_lt])
    show "rho_p (rv_name i) = 1"
    proof (cases "rho_p (StateVar v) = 0")
      case True
      then show ?thesis
        using rvg_forces[OF rho_p01 mP' i_lt] unfolding v_def by blast
    next
      case False
      then have v1p: "rho_p (StateVar v) = 1"
        using rho_p01[rule_format, of "StateVar v"] by simp
      have c'_thr: "c' \<ge> clip B (int B - int h + int (W v))"
      proof -
        consider (AddC) "v \<in> add a" | (DelC) "v \<in> del a" "v \<notin> add a"
          | (FrameC) "v \<notin> evars a"
          by (auto simp: evars_def)
        then show ?thesis
        proof cases
          case AddC
          show ?thesis
          proof (cases "pre a = {}")
            case True
            have Wv: "W v \<le> cost a" by (rule W_step_empty[OF a_in AddC True])
            have "int B - int h + int (W v) \<le> (int B - int h) + int (cost a)"
              using Wv by linarith
            then have "clip B (int B - int h + int (W v))
                \<le> clip B ((int B - int h) + int (cost a))"
              by (rule clip_mono)
            also have "... \<le> clip B (int B - int h) + cost a"
              by (rule clip_add_le)
            also have "... \<le> c + cost a" using c_base by simp
            also have "... = c'" using c'_eq by simp
            finally show ?thesis .
          next
            case False
            obtain p where pPre: "p \<in> pre a" and Wv: "W v \<le> W p + cost a"
              using W_step_pre[OF a_in AddC False] by blast
            have pV: "p \<in> vars \<Pi>e" using preS pPre by blast
            have "rho (StateVar (Original p)) = 1" using preO pPre by blast
            then have p1: "rho_o (StateVar p) = 1" by (simp add: rho_o_def)
            have c_p_thr: "c \<ge> clip B (int B - int h + int (W p))"
              by (rule carry[OF pV p1])
            have "int B - int h + int (W v)
                \<le> (int B - int h + int (W p)) + int (cost a)"
              using Wv by linarith
            then have "clip B (int B - int h + int (W v))
                \<le> clip B ((int B - int h + int (W p)) + int (cost a))"
              by (rule clip_mono)
            also have "... \<le> clip B (int B - int h + int (W p)) + cost a"
              by (rule clip_add_le)
            also have "... \<le> c + cost a" using c_p_thr by simp
            also have "... = c'" using c'_eq by simp
            finally show ?thesis .
          qed
        next
          case DelC
          have "rho (StateVar (Primed v)) = 0" using delP DelC by blast
          then have "rho_p (StateVar v) = 0" by (simp add: rho_p_def)
          then show ?thesis using v1p by simp
        next
          case FrameC
          have w_in: "v \<in> vars \<Pi>e - evars a" using FrameC vV by auto
          then have eq1: "rho (ReifEq (Original v)) = 1" using frameO by blast
          have meq: "models (encode_eq_var v) rho"
            by (rule trans_eq_var[OF mT]) (use w_in in blast)
          have eq2: "rho (StateVar (Original v)) = rho (StateVar (Primed v))"
            using encode_eq_var_forces[OF rho01 meq] eq1 by simp
          have "rho_o (StateVar v) = 1"
            using v1p eq2 by (simp add: rho_o_def rho_p_def)
          then have "c \<ge> clip B (int B - int h + int (W v))"
            by (rule carry[OF vV])
          then show ?thesis using c'_eq by simp
        qed
      qed
      then have "rho_p (kv_name i) = 1"
        using kvg_forces[OF rho_p01 mP' i_lt] c_p unfolding v_def by simp
      then show ?thesis using rvg_forces[OF rho_p01 mP' i_lt] by blast
    qed
  qed
  have "rho_p max_name = 1"
    using mxg_forces[OF rho_p01 mP'] kb_p rv_p by blast
  then show "eval_lit (map_literal primed_pvar_map (hc_out hmax_cert s')) rho = 1"
    unfolding hmax_cert_def
    by (simp add: eval_lit_map_literal rho_p_def eval_lit_def)
qed

text \<open>The hmax certificate is a valid heuristic certificate in the sense of
  Definition 4 for the evaluated state @{text s}.\<close>

theorem hmax_hc_valid: "hc_valid \<Pi>e B as hmax_cert {s}"
  unfolding hc_valid_def
  using hmax_state_lemma hmax_goal_lemma hmax_ind_lemma by blast

subsection \<open>Structural conditions for use in the A* certificate\<close>

lemma hmax_gates_nth_kv: "i < n_v \<Longrightarrow> hmax_gates ! i = kvg i"
  by (simp add: hmax_gates_def nth_append)

lemma hmax_gates_nth_rv: "i < n_v \<Longrightarrow> hmax_gates ! (n_v + i) = rvg i"
  by (simp add: hmax_gates_def nth_append)

lemma hmax_gates_nth_kb: "hmax_gates ! (2 * n_v) = kbg"
  by (simp add: hmax_gates_def nth_append)

lemma hmax_gates_nth_mx: "hmax_gates ! (2 * n_v + 1) = mxg"
  by (simp add: hmax_gates_def nth_append)

lemma hmax_gate_name_nth:
  assumes p_lt: "p < length hmax_gates"
  shows "fst (hmax_gates ! p) = Pos (ReifCert (nm p))"
proof -
  consider (KV) "p < n_v" | (RV) "n_v \<le> p" "p < 2 * n_v"
    | (KB) "p = 2 * n_v" | (MX) "p = 2 * n_v + 1"
    using p_lt length_hmax_gates by linarith
  then show ?thesis
  proof cases
    case KV
    then show ?thesis
      using hmax_gates_nth_kv[OF KV] by (simp add: kvg_def k_gate_def kv_name_def)
  next
    case RV
    then obtain q where p_eq: "p = n_v + q" using le_iff_add by auto
    have q_lt: "q < n_v" using RV p_eq by simp
    show ?thesis
      unfolding p_eq using hmax_gates_nth_rv[OF q_lt]
      by (simp add: rvg_def rv_name_def)
  next
    case KB
    then show ?thesis
      using hmax_gates_nth_kb by (simp add: kbg_def k_gate_def kb_name_def)
  next
    case MX
    then show ?thesis
      using hmax_gates_nth_mx by (simp add: mxg_def max_name_def)
  qed
qed

lemma hmax_names:
  "\<forall>(r, cs, A) \<in> set (hc_gates hmax_cert). \<exists>j. r = Pos (ReifCert (nm j))"
proof -
  have "\<And>g. g \<in> set hmax_gates \<Longrightarrow> \<exists>j. fst g = Pos (ReifCert (nm j))"
  proof -
    fix g assume "g \<in> set hmax_gates"
    then obtain p where p_lt: "p < length hmax_gates" and g_eq: "g = hmax_gates ! p"
      by (auto simp: in_set_conv_nth)
    show "\<exists>j. fst g = Pos (ReifCert (nm j))"
      using hmax_gate_name_nth[OF p_lt] g_eq by auto
  qed
  then show ?thesis by (fastforce simp: hmax_cert_def)
qed

lemma hmax_distinct:
  "distinct (map (\<lambda>(r, cs, A). pvar_of_lit r) (hc_gates hmax_cert))"
proof -
  note len = length_hmax_gates
  have map_eq: "map (\<lambda>(r, cs, A). pvar_of_lit r) hmax_gates
      = map (\<lambda>p. ReifCert (nm p)) [0..<2 * n_v + 2]"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(r, cs, A). pvar_of_lit r) hmax_gates)
        = length (map (\<lambda>p. ReifCert (nm p)) [0..<2 * n_v + 2])"
      by (simp add: len)
    fix p assume "p < length (map (\<lambda>(r, cs, A). pvar_of_lit r) hmax_gates)"
    then have p_lt: "p < length hmax_gates" by simp
    have "(\<lambda>(r, cs, A). pvar_of_lit r) (hmax_gates ! p) = pvar_of_lit (fst (hmax_gates ! p))"
      by (simp add: split_beta)
    also have "... = ReifCert (nm p)"
      using hmax_gate_name_nth[OF p_lt] by (simp add: pvar_of_lit_def)
    finally show "map (\<lambda>(r, cs, A). pvar_of_lit r) hmax_gates ! p
        = map (\<lambda>p. ReifCert (nm p)) [0..<2 * n_v + 2] ! p"
      using p_lt len by (auto simp: nth_append less_Suc_eq)
  qed
  have "distinct (map (\<lambda>p. ReifCert (nm p)) [0..<2 * n_v + 2])"
    using nm_inj by (auto simp: distinct_map intro!: inj_onI dest: injD)
  then show ?thesis using map_eq by (simp add: hmax_cert_def)
qed

lemma hmax_out_in: "hc_out hmax_cert s' \<in> fst ` set (hc_gates hmax_cert)"
proof -
  have "fst mxg = Pos max_name" by (simp add: mxg_def)
  then show ?thesis using mxg_in_gates by (force simp: hmax_cert_def)
qed

lemma nth_in_take_hmax: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! j \<in> set (take i xs)"
  by (metis length_take min.absorb2 nth_mem nth_take)

lemma hmax_wf:
  "\<forall>i < length (hc_gates hmax_cert). case hc_gates hmax_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert)))"
proof (intro allI impI)
  fix i assume i_lt: "i < length (hc_gates hmax_cert)"
  have hcg: "hc_gates hmax_cert = hmax_gates" by (simp add: hmax_cert_def)
  have i_lt': "i < length hmax_gates" using i_lt by (simp add: hcg)
  have i_le: "i \<le> length hmax_gates" using i_lt' by simp
  consider (KV) "i < n_v" | (RV) "n_v \<le> i" "i < 2 * n_v"
    | (KB) "i = 2 * n_v" | (MX) "i = 2 * n_v + 1"
    using i_lt' length_hmax_gates by linarith
  then show "case hc_gates hmax_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert)))"
  proof cases
    case KV
    have g: "hc_gates hmax_cert ! i = kvg i"
      using hmax_gates_nth_kv[OF KV] hcg by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (k_gate_body B). (\<exists>j. x = CostBit j)"
      by (auto simp: k_gate_body_def pvar_of_lit_def)
    then show ?thesis unfolding g kvg_def k_gate_def by auto
  next
    case RV
    then obtain q where i_eq: "i = n_v + q" using le_iff_add by auto
    have q_lt: "q < n_v" using RV i_eq by simp
    have g: "hc_gates hmax_cert ! i = rvg q"
      using hmax_gates_nth_rv[OF q_lt] hcg i_eq by simp
    have kv_in: "kv_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert))"
    proof -
      have "q < i" using q_lt i_eq by simp
      then have "hmax_gates ! q \<in> set (take i hmax_gates)"
        using nth_in_take_hmax i_le by blast
      moreover have "fst (hmax_gates ! q) = Pos (kv_name q)"
        using hmax_gates_nth_kv[OF q_lt] by (simp add: kvg_def k_gate_def)
      ultimately show ?thesis using hcg by (force simp: pvar_of_lit_def)
    qed
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) (rv_lits q)).
        (\<exists>v. x = StateVar v)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert))"
      using kv_in by (auto simp: rv_lits_def pvar_of_lit_def)
    then show ?thesis unfolding g rvg_def by auto
  next
    case KB
    have g: "hc_gates hmax_cert ! i = kbg"
      using hmax_gates_nth_kb hcg KB by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (k_gate_body B). (\<exists>j. x = CostBit j)"
      by (auto simp: k_gate_body_def pvar_of_lit_def)
    then show ?thesis unfolding g kbg_def k_gate_def by auto
  next
    case MX
    have g: "hc_gates hmax_cert ! i = mxg"
      using hmax_gates_nth_mx hcg MX by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) max_lits).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert))"
    proof
      fix x assume "x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) max_lits)"
      then consider (Base) "x = kb_name"
        | (Var) q where "q < n_v" "x = rv_name q"
        by (auto simp: max_lits_def pvar_of_lit_def)
      then show "x \<in> pvar_of_lit ` fst ` set (take i (hc_gates hmax_cert))"
      proof cases
        case Base
        have "2 * n_v < i" using MX by simp
        then have "hmax_gates ! (2 * n_v) \<in> set (take i hmax_gates)"
          using nth_in_take_hmax i_le by blast
        moreover have "fst (hmax_gates ! (2 * n_v)) = Pos kb_name"
          using hmax_gates_nth_kb by (simp add: kbg_def k_gate_def)
        ultimately show ?thesis using hcg Base by (force simp: pvar_of_lit_def)
      next
        case Var
        have "n_v + q < i" using Var(1) MX by simp
        then have "hmax_gates ! (n_v + q) \<in> set (take i hmax_gates)"
          using nth_in_take_hmax i_le by blast
        moreover have "fst (hmax_gates ! (n_v + q)) = Pos (rv_name q)"
          using hmax_gates_nth_rv[OF Var(1)] by (simp add: rvg_def)
        ultimately show ?thesis using hcg Var(2) by (force simp: pvar_of_lit_def)
      qed
    qed
    then show ?thesis unfolding g mxg_def by auto
  qed
qed

end

end
