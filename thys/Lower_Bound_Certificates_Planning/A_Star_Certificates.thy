section \<open>A* Certificates\<close>

theory A_Star_Certificates
  imports Heuristic_Certificates
begin

text \<open>Proof-logging A* (paper equations (9)–(13) and Lemmas 3--7).  The locale
  @{text astar_run} captures the snapshot of a terminated proof-logging A* search:
  the closed list with g-values, the open list with a valid heuristic certificate,
  and the expansion-closure property (every applicable action from a closed state
  leads to a state covered by the closed list, by duplicate detection, or by an
  open state whose f-value reaches the bound — the paper's ``A* closes all states
  with f < B'').  From this snapshot we assemble the certificate circuit
  @{text "\<langle>A, r_A*\<rangle>"} over the extended variable type @{text "'v + nat"} and prove
  it a valid lower-bound certificate.\<close>

subsection \<open>Extracting components of the transition encoding\<close>

lemma action_reifs_nth: "j < length as \<Longrightarrow> action_reifs as ! j = Pos (ReifAction j)"
  by (simp add: action_reifs_def)

lemma trans_sel:
  assumes "models (encode_transition as V B) rho"
  shows "models (action_selection_reif (action_reifs as)) rho"
  by (rule models_mono[OF assms]) (auto simp: encode_transition_def Let_def)

lemma trans_action_constraint:
  assumes m: "models (encode_transition as V B) rho" and j: "j < length as"
  shows "satisfies (action_constraint (Pos (ReifAction j)) (as ! j) V B) rho"
proof -
  have "action_constraint (action_reifs as ! j) (as ! j) V B \<in> encode_transition as V B"
    using j unfolding encode_transition_def Let_def by auto
  then show ?thesis
    using m action_reifs_nth[OF j] unfolding models_def by auto
qed

lemma trans_delta:
  assumes m: "models (encode_transition as V B) rho" and a_in: "a \<in> set as"
  shows "models (encode_delta_cost (cost a) (bits_needed B)) rho"
  by (rule models_mono[OF m]) (use a_in in \<open>auto simp: encode_transition_def Let_def\<close>)

lemma trans_eq_var:
  assumes m: "models (encode_transition as V B) rho" and v_in: "v \<in> V"
  shows "models (encode_eq_var v) rho"
  by (rule models_mono[OF m]) (use v_in in \<open>auto simp: encode_transition_def Let_def\<close>)

lemma trans_primed_ge:
  assumes m: "models (encode_transition as V B) rho"
  shows "models (encode_cost_ge_primed B) rho"
  by (rule models_mono[OF m]) (auto simp: encode_transition_def Let_def)

subsection \<open>Embedded actions\<close>

lemma pre_embed: "pre (embed_act a) = Inl ` pre a"
  and add_embed: "add (embed_act a) = Inl ` add a"
  and del_embed: "del (embed_act a) = Inl ` del a"
  and cost_embed: "cost (embed_act a) = cost a"
  by (simp_all add: embed_act_def)

lemma evars_embed: "evars (embed_act a) = Inl ` evars a"
  by (simp add: evars_def embed_act_def image_Un)

lemma acts_embed: "acts (embed_task \<Pi>) = embed_act ` acts \<Pi>"
  by (simp add: embed_task_def)


locale astar_run =
  fixes \<Pi> :: "'v::linorder strips_task"
    and B :: nat
    and closed_list :: "('v state \<times> nat) list"
    and open_list :: "'v state list"
    and HC :: "(('v + nat)) heuristic_cert"
    and cas :: "('v + nat) action list"
  assumes fin_vars: "finite (vars \<Pi>)"
    and init_sub: "init \<Pi> \<subseteq> vars \<Pi>"
    and goal_sub: "goal \<Pi> \<subseteq> vars \<Pi>"
    and fin_acts: "finite (acts \<Pi>)"
    and acts_disjoint: "\<forall>a \<in> acts \<Pi>. add a \<inter> del a = {}"
    and acts_states_sub:
      "\<forall>a \<in> acts \<Pi>. pre a \<subseteq> vars \<Pi> \<and> add a \<subseteq> vars \<Pi> \<and> del a \<subseteq> vars \<Pi>"
    and cas_eq: "set cas = acts (embed_task \<Pi>)"
    and B_pos: "B \<ge> 1"
    \<comment> \<open>A* snapshot conditions:\<close>
    and closed_init: "(init \<Pi>, 0) \<in> set closed_list"
    and closed_sub: "\<forall>(s, g) \<in> set closed_list. s \<subseteq> vars \<Pi>"
    and open_sub: "\<forall>s \<in> set open_list. s \<subseteq> vars \<Pi>"
    and closed_goal_ge: "\<forall>(s, g) \<in> set closed_list. is_goal_state \<Pi> s \<longrightarrow> g \<ge> B"
    and expansion: "\<forall>(s, g) \<in> set closed_list. \<forall>a \<in> acts \<Pi>. applicable a s \<longrightarrow>
        (is_goal_state \<Pi> s \<and> g \<ge> B)
      \<or> (\<exists>g'. (successor a s, g') \<in> set closed_list \<and> g' \<le> g + cost a)
      \<or> (successor a s \<in> set open_list \<and>
         int (g + cost a) \<ge> int B - int (hc_h HC (Inl ` successor a s)))"
    \<comment> \<open>Heuristic certificate conditions:\<close>
    and hc_ok: "hc_valid (embed_task \<Pi>) B cas HC ((\<lambda>s. Inl ` s) ` set open_list)"
    and hc_names: "\<forall>(r, cs, A) \<in> set (hc_gates HC). \<exists>j. r = Pos (ReifCert (Inr (2 * j + 1)))"
    and hc_distinct: "distinct (map (\<lambda>(r, cs, A). pvar_of_lit r) (hc_gates HC))"
    and hc_wf: "\<forall>i < length (hc_gates HC). case hc_gates HC ! i of (r, cs, A) \<Rightarrow>
        (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
          (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
          \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates HC)))"
    and hc_out_in: "\<forall>s \<in> set open_list. hc_out HC (Inl ` s) \<in> fst ` set (hc_gates HC)"
begin

abbreviation \<Pi>e :: "('v + nat) strips_task" where
  "\<Pi>e \<equiv> embed_task \<Pi>"

definition n_cl :: nat where
  "n_cl = length closed_list"

definition n_hc :: nat where
  "n_hc = length (hc_gates HC)"

definition cl_state :: "nat \<Rightarrow> 'v state" where
  "cl_state i = fst (closed_list ! i)"

definition cl_g :: "nat \<Rightarrow> nat" where
  "cl_g i = snd (closed_list ! i)"

subsubsection \<open>Gate names\<close>

definition k_name :: "nat \<Rightarrow> ('v + nat) pvar" where
  "k_name i = ReifCert (Inr (2 * i))"

definition cl_name :: "nat \<Rightarrow> ('v + nat) pvar" where
  "cl_name i = ReifCert (Inr (2 * (n_cl + i)))"

definition out_name :: "('v + nat) pvar" where
  "out_name = ReifCert (Inr (2 * (2 * n_cl)))"

subsubsection \<open>Gates\<close>

text \<open>K-gates: for each closed pair @{text "(s, g)"} the clipped cost threshold
  gate @{text "K\<ge>g"} (paper equation (9), inlined over the cost bits).\<close>

definition kg :: "nat \<Rightarrow> ('v + nat) pvar literal \<times> (nat \<times> ('v + nat) pvar literal) list \<times> nat" where
  "kg i = k_gate (Pos (k_name i)) B (int (cl_g i))"

text \<open>Closed-state gates (paper equation (11)): the conjunction of the exact
  state description of @{text "cl_state i"} and the K-gate for @{text "cl_g i"}.\<close>

definition state_lits_exact :: "'v state \<Rightarrow> ('v + nat) pvar literal list" where
  "state_lits_exact s =
     map (\<lambda>v. if v \<in> s then Pos (StateVar (Inl v)) else Neg (StateVar (Inl v)))
       (sorted_list_of_set (vars \<Pi>))"

definition cl_lits :: "nat \<Rightarrow> ('v + nat) pvar literal list" where
  "cl_lits i = Pos (k_name i) # state_lits_exact (cl_state i)"

definition clg :: "nat \<Rightarrow> ('v + nat) pvar literal \<times> (nat \<times> ('v + nat) pvar literal) list \<times> nat" where
  "clg i = (Pos (cl_name i), map (\<lambda>l. (1, l)) (cl_lits i), length (cl_lits i))"

text \<open>The output gate (paper equation (13)): some closed-state gate or some
  open-state heuristic output is true.\<close>

definition out_lits :: "('v + nat) pvar literal list" where
  "out_lits = map (\<lambda>i. Pos (cl_name i)) [0..<n_cl]
            @ map (\<lambda>s. hc_out HC (Inl ` s)) open_list"

definition outg :: "('v + nat) pvar literal \<times> (nat \<times> ('v + nat) pvar literal) list \<times> nat" where
  "outg = (Pos out_name, map (\<lambda>l. (1, l)) out_lits, 1)"

definition astar_gates ::
  "(('v + nat) pvar literal \<times> (nat \<times> ('v + nat) pvar literal) list \<times> nat) list" where
  "astar_gates = map kg [0..<n_cl] @ map clg [0..<n_cl] @ hc_gates HC @ [outg]"

definition astar_circuit :: "('v + nat) pb_circuit" where
  "astar_circuit = (astar_gates, Pos out_name)"

definition astar_cert :: "(('v + nat)) certificate" where
  "astar_cert = \<lparr> cert_circuit = astar_circuit, cert_actions = cas \<rparr>"

subsubsection \<open>Basic structure of the gate list\<close>

lemma length_astar_gates: "length astar_gates = 2 * n_cl + n_hc + 1"
  by (simp add: astar_gates_def n_hc_def)

lemma astar_gates_nth_k:
  "i < n_cl \<Longrightarrow> astar_gates ! i = kg i"
  by (simp add: astar_gates_def nth_append)

lemma astar_gates_nth_cl:
  "i < n_cl \<Longrightarrow> astar_gates ! (n_cl + i) = clg i"
  by (simp add: astar_gates_def nth_append)

lemma astar_gates_nth_hc:
  "i < n_hc \<Longrightarrow> astar_gates ! (2 * n_cl + i) = hc_gates HC ! i"
  by (simp add: astar_gates_def n_hc_def nth_append)

lemma astar_gates_nth_out:
  "astar_gates ! (2 * n_cl + n_hc) = outg"
  by (simp add: astar_gates_def n_hc_def nth_append)

lemma kg_in_gates: "i < n_cl \<Longrightarrow> kg i \<in> set astar_gates"
  by (simp add: astar_gates_def)

lemma clg_in_gates: "i < n_cl \<Longrightarrow> clg i \<in> set astar_gates"
  by (simp add: astar_gates_def)

lemma hc_in_gates: "g \<in> set (hc_gates HC) \<Longrightarrow> g \<in> set astar_gates"
  by (simp add: astar_gates_def)

lemma outg_in_gates: "outg \<in> set astar_gates"
  by (simp add: astar_gates_def)

subsubsection \<open>Extracting per-gate models from a circuit model\<close>

lemma models_gate:
  assumes m: "models (circuit_constraints astar_circuit) rho"
    and g_in: "(r, cs, A) \<in> set astar_gates"
  shows "models (reification r cs A) rho"
proof (rule models_mono[OF m])
  show "reification r cs A \<subseteq> circuit_constraints astar_circuit"
    using g_in unfolding circuit_constraints_def astar_circuit_def by fastforce
qed

lemma models_kg:
  assumes "models (circuit_constraints astar_circuit) rho" and "i < n_cl"
  shows "models (reification (Pos (k_name i)) (k_gate_body B) (clip B (int (cl_g i)))) rho"
  using models_gate[OF assms(1)] kg_in_gates[OF assms(2)]
  by (simp add: kg_def k_gate_def)

lemma models_clg:
  assumes "models (circuit_constraints astar_circuit) rho" and "i < n_cl"
  shows "models (reification (Pos (cl_name i)) (map (\<lambda>l. (1, l)) (cl_lits i)) (length (cl_lits i))) rho"
  using models_gate[OF assms(1)] clg_in_gates[OF assms(2)]
  by (simp add: clg_def)

lemma models_outg:
  assumes "models (circuit_constraints astar_circuit) rho"
  shows "models (reification (Pos out_name) (map (\<lambda>l. (1, l)) out_lits) 1) rho"
  using models_gate[OF assms] outg_in_gates
  by (simp add: outg_def)

lemma models_hc_constraints:
  assumes "models (circuit_constraints astar_circuit) rho"
  shows "models (hc_constraints HC) rho"
proof -
  have "hc_constraints HC \<subseteq> circuit_constraints astar_circuit"
    unfolding hc_constraints_def circuit_constraints_def astar_circuit_def astar_gates_def
    by fastforce
  then show ?thesis by (rule models_mono[OF assms])
qed

subsubsection \<open>Semantics of the closed-state gates\<close>

lemma state_lits_exact_sem:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "(\<forall>l \<in> set (state_lits_exact s). eval_lit l rho = 1)
     \<longleftrightarrow> (\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0))"
proof -
  have set_eq: "set (sorted_list_of_set (vars \<Pi>)) = vars \<Pi>"
    using fin_vars by simp
  have lit_sem: "\<And>v. eval_lit (if v \<in> s then Pos (StateVar (Inl v))
        else Neg (StateVar (Inl v))) rho = 1
      \<longleftrightarrow> rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
  proof -
    fix v
    show "eval_lit (if v \<in> s then Pos (StateVar (Inl v))
        else Neg (StateVar (Inl v))) rho = 1
      \<longleftrightarrow> rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
      using rho01[rule_format, of "StateVar (Inl v)"]
      by (cases "v \<in> s") (auto simp: eval_lit_def)
  qed
  show ?thesis
  proof
    assume all1: "\<forall>l \<in> set (state_lits_exact s). eval_lit l rho = 1"
    show "\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
    proof
      fix v assume vV: "v \<in> vars \<Pi>"
      have "(if v \<in> s then Pos (StateVar (Inl v)) else Neg (StateVar (Inl v)))
            \<in> set (state_lits_exact s)"
        unfolding state_lits_exact_def using vV set_eq by auto
      then have "eval_lit (if v \<in> s then Pos (StateVar (Inl v))
          else Neg (StateVar (Inl v))) rho = 1"
        using all1 by blast
      then show "rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
        using lit_sem[of v] by simp
    qed
  next
    assume enc: "\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
    show "\<forall>l \<in> set (state_lits_exact s). eval_lit l rho = 1"
    proof
      fix l assume "l \<in> set (state_lits_exact s)"
      then obtain v where vV: "v \<in> vars \<Pi>"
        and l_eq: "l = (if v \<in> s then Pos (StateVar (Inl v)) else Neg (StateVar (Inl v)))"
        unfolding state_lits_exact_def using set_eq by auto
      show "eval_lit l rho = 1"
        using enc vV lit_sem[of v] unfolding l_eq by simp
    qed
  qed
qed

lemma clg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (circuit_constraints astar_circuit) rho"
    and i_lt: "i < n_cl"
  shows "rho (cl_name i) = 1
     \<longleftrightarrow> (rho (k_name i) = 1 \<and>
         (\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> cl_state i then 1 else 0)))"
proof -
  have "eval_lit (Pos (cl_name i)) rho = 1 \<longleftrightarrow> (\<forall>l \<in> set (cl_lits i). eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_clg[OF m i_lt]])
  also have "... \<longleftrightarrow> (eval_lit (Pos (k_name i)) rho = 1 \<and>
      (\<forall>l \<in> set (state_lits_exact (cl_state i)). eval_lit l rho = 1))"
    by (simp add: cl_lits_def)
  also have "... \<longleftrightarrow> (rho (k_name i) = 1 \<and>
      (\<forall>l \<in> set (state_lits_exact (cl_state i)). eval_lit l rho = 1))"
    by (simp add: eval_lit_def)
  also have "... \<longleftrightarrow> (rho (k_name i) = 1 \<and>
      (\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> cl_state i then 1 else 0)))"
    using state_lits_exact_sem[OF rho01, of "cl_state i"] by blast
  finally show ?thesis by (simp add: eval_lit_def)
qed

lemma kg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (circuit_constraints astar_circuit) rho"
    and i_lt: "i < n_cl"
  shows "rho (k_name i) = 1
     \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int (cl_g i))"
  using k_gate_forces[OF rho01 models_kg[OF m i_lt]]
  by (simp add: eval_lit_def)

lemma outg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (circuit_constraints astar_circuit) rho"
  shows "rho out_name = 1 \<longleftrightarrow> (\<exists>l \<in> set out_lits. eval_lit l rho = 1)"
  using disj_gate_forces[OF rho01 models_outg[OF m]]
  by (simp add: eval_lit_def)

subsubsection \<open>Embedded task bookkeeping\<close>

lemma vars_e: "vars \<Pi>e = Inl ` vars \<Pi>"
  by (simp add: embed_task_def)

lemma goal_e: "goal \<Pi>e = Inl ` goal \<Pi>"
  by (simp add: embed_task_def)

lemma init_e: "init \<Pi>e = Inl ` init \<Pi>"
  by (simp add: embed_task_def)

lemma fin_vars_e: "finite (vars \<Pi>e)"
  using fin_vars by (simp add: vars_e)

lemma init_sub_e: "init \<Pi>e \<subseteq> vars \<Pi>e"
  using init_sub by (auto simp: init_e vars_e)

lemma goal_sub_e: "goal \<Pi>e \<subseteq> vars \<Pi>e"
  using goal_sub by (auto simp: goal_e vars_e)

lemma fin_goal_e: "finite (goal \<Pi>e)"
  using goal_sub_e fin_vars_e by (rule finite_subset)

lemma closed_nth_in: "i < n_cl \<Longrightarrow> (cl_state i, cl_g i) \<in> set closed_list"
  unfolding cl_state_def cl_g_def n_cl_def by (metis nth_mem prod.collapse)

lemma closed_mem_nth: "(s, g) \<in> set closed_list \<Longrightarrow> \<exists>i < n_cl. cl_state i = s \<and> cl_g i = g"
  unfolding cl_state_def cl_g_def n_cl_def by (metis fst_conv snd_conv in_set_conv_nth)

lemma hc_ok_state: "s \<in> set open_list \<Longrightarrow> hc_state_lemma \<Pi>e B HC (Inl ` s)"
  using hc_ok unfolding hc_valid_def by blast

lemma hc_ok_goal: "s \<in> set open_list \<Longrightarrow> hc_goal_lemma \<Pi>e B HC (Inl ` s)"
  using hc_ok unfolding hc_valid_def by blast

lemma hc_ok_ind: "s \<in> set open_list \<Longrightarrow> hc_ind_lemma \<Pi>e B cas HC (Inl ` s)"
  using hc_ok unfolding hc_valid_def by blast

lemma state_descr_translate:
  "(\<forall>w \<in> vars \<Pi>e. rho (StateVar w) = (if w \<in> Inl ` s then 1 else 0))
 \<longleftrightarrow> (\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> s then 1 else 0))"
  by (auto simp: vars_e inj_image_mem_iff)

lemma neg_cost_ge_one_zero:
  assumes rho01: "\<forall>x. (rho :: ('v + nat) pvar \<Rightarrow> nat) x = 0 \<or> rho x = 1"
    and sat: "satisfies (neg_cost_ge_one B) rho"
  shows "bits_val (bits_needed B) CostBit rho = 0"
proof -
  have neg_sum: "pb_sum (map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<bits_needed B]) rho
      = (2^(bits_needed B) - 1) - bits_val (bits_needed B) CostBit rho"
    by (rule pb_sum_neg_bits_val[OF rho01])
  have ge: "pb_sum (map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<bits_needed B]) rho
      \<ge> 2^(bits_needed B) - 1"
    using sat by (simp add: neg_cost_ge_one_def satisfies_def)
  have lt: "bits_val (bits_needed B) CostBit rho < 2^(bits_needed B)"
    by (rule bits_val_lt) (use rho01 in blast)
  show ?thesis using neg_sum ge lt by linarith
qed

subsubsection \<open>The initial state lemma (paper Lemma 3)\<close>

lemma astar_init_semantic:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mI: "models (encode_init \<Pi>e) rho"
    and mC: "models (circuit_constraints astar_circuit) rho"
    and rI: "rho ReifI = 1"
    and bits0: "satisfies (neg_cost_ge_one B) rho"
  shows "rho out_name = 1"
proof -
  have c0: "bits_val (bits_needed B) CostBit rho = 0"
    by (rule neg_cost_ge_one_zero[OF rho01 bits0])
  have sv_e: "\<forall>w \<in> vars \<Pi>e. rho (StateVar w) = (if w \<in> init \<Pi>e then 1 else 0)"
    using encode_init_forces[OF rho01 mI fin_vars_e init_sub_e] rI by blast
  have sv: "\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> init \<Pi> then 1 else 0)"
    using sv_e state_descr_translate unfolding init_e by blast
  obtain i0 where i0_lt: "i0 < n_cl" and i0_s: "cl_state i0 = init \<Pi>"
    and i0_g: "cl_g i0 = 0"
    using closed_mem_nth[OF closed_init] by blast
  have k1: "rho (k_name i0) = 1"
  proof -
    have "clip B (int (cl_g i0)) = 0" by (simp add: i0_g)
    then show ?thesis using kg_forces[OF rho01 mC i0_lt] by simp
  qed
  have cl1: "rho (cl_name i0) = 1"
    using clg_forces[OF rho01 mC i0_lt] k1 sv i0_s by simp
  have "Pos (cl_name i0) \<in> set out_lits"
    unfolding out_lits_def using i0_lt by simp
  moreover have "eval_lit (Pos (cl_name i0)) rho = 1"
    using cl1 by (simp add: eval_lit_def)
  ultimately show ?thesis
    using outg_forces[OF rho01 mC] by blast
qed

subsubsection \<open>The goal lemma (paper Lemma 4)\<close>

lemma astar_goal_semantic:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mG: "models (encode_goal \<Pi>e) rho"
    and mC: "models (circuit_constraints astar_circuit) rho"
    and rG: "rho ReifG = 1"
    and out1: "rho out_name = 1"
  shows "bits_val (bits_needed B) CostBit rho \<ge> B"
proof -
  have gv: "\<forall>w \<in> goal \<Pi>e. rho (StateVar w) = 1"
    using encode_goal_forces[OF rho01 mG fin_goal_e] rG by blast
  obtain l where l_in: "l \<in> set out_lits" and l1: "eval_lit l rho = 1"
    using outg_forces[OF rho01 mC] out1 by blast
  from l_in consider
    (ClosedGate) i where "i < n_cl" and "l = Pos (cl_name i)"
  | (OpenState) s where "s \<in> set open_list" and "l = hc_out HC (Inl ` s)"
    unfolding out_lits_def by auto
  then show ?thesis
  proof cases
    case ClosedGate
    have cl1: "rho (cl_name i) = 1"
      using l1 ClosedGate by (simp add: eval_lit_def)
    have k1: "rho (k_name i) = 1"
      and sv: "\<forall>v \<in> vars \<Pi>. rho (StateVar (Inl v)) = (if v \<in> cl_state i then 1 else 0)"
      using clg_forces[OF rho01 mC ClosedGate(1)] cl1 by auto
    show ?thesis
    proof (cases "is_goal_state \<Pi> (cl_state i)")
      case True
      have "cl_g i \<ge> B"
        using closed_goal_ge closed_nth_in[OF ClosedGate(1)] True by auto
      then have "clip B (int (cl_g i)) = B" by simp
      then show ?thesis using kg_forces[OF rho01 mC ClosedGate(1)] k1 by simp
    next
      case False
      then obtain v where vG: "v \<in> goal \<Pi>" and v_not: "v \<notin> cl_state i"
        unfolding is_goal_state_def by auto
      have vV: "v \<in> vars \<Pi>" using vG goal_sub by auto
      have "rho (StateVar (Inl v)) = 0" using sv vV v_not by simp
      moreover have "rho (StateVar (Inl v)) = 1"
        using gv vG unfolding goal_e by auto
      ultimately show ?thesis by simp
    qed
  next
    case OpenState
    show ?thesis
      by (rule hc_goal_lemmaD[OF hc_ok_goal[OF OpenState(1)] rho01
            models_hc_constraints[OF mC] gv l1[unfolded OpenState(2)]])
  qed
qed

subsubsection \<open>The inductivity lemma (paper Lemmas 5--7)\<close>

text \<open>Any 0/1 model of the transition encoding together with both lifted copies of
  the circuit that selects an action (@{text "r\<^sub>T = 1"}) and satisfies the unprimed
  output gate also satisfies the primed output gate.  The proof follows the paper:
  the selected action is applicable in the closed state of the witnessing gate, and
  the successor is covered by the closed list, by duplicate detection, or by an
  open state whose heuristic state lemma (in primed variables) fires.  Models of
  the lifted circuits are analysed by precomposition with the renamings.\<close>

lemma astar_ind_semantic:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mT: "models (encode_transition cas (vars \<Pi>e) B) rho"
    and mO: "models (circuit_constraints (orig_circuit astar_circuit)) rho"
    and mP: "models (circuit_constraints (primed_circuit astar_circuit)) rho"
    and mB: "models (encode_cost_ge B) rho"
    and rT: "rho ReifT = 1"
    and outO: "rho (map_pvar Original out_name) = 1"
  shows "rho (primed_pvar_map out_name) = 1"
proof -
  define rho_o where "rho_o = rho \<circ> map_pvar Original"
  define rho_p where "rho_p = rho \<circ> primed_pvar_map"
  have rho_o01: "\<forall>x. rho_o x = 0 \<or> rho_o x = 1"
    unfolding rho_o_def by (rule rho01_comp[OF rho01])
  have rho_p01: "\<forall>x. rho_p x = 0 \<or> rho_p x = 1"
    unfolding rho_p_def by (rule rho01_comp[OF rho01])
  have mO': "models (circuit_constraints astar_circuit) rho_o"
    using mO models_circuit_constraints_lift[of "map_pvar Original" astar_circuit rho]
    unfolding rho_o_def orig_circuit_def by blast
  have mP': "models (circuit_constraints astar_circuit) rho_p"
    using mP models_circuit_constraints_lift[of primed_pvar_map astar_circuit rho]
    unfolding rho_p_def primed_circuit_def by blast
  define c where "c = bits_val (bits_needed B) CostBit rho"
  define c' where "c' = bits_val (bits_needed B) PrimedCostBit rho"
  have c_o: "bits_val (bits_needed B) CostBit rho_o = c"
    by (simp add: rho_o_def c_def bits_val_def)
  have c_p: "bits_val (bits_needed B) CostBit rho_p = c'"
    by (simp add: rho_p_def c'_def bits_val_def)
  \<comment> \<open>The selected action.\<close>
  have mSel: "models (action_selection_reif (action_reifs cas)) rho"
    by (rule trans_sel[OF mT])
  obtain rA where rA_in: "rA \<in> set (action_reifs cas)" and rA1: "eval_lit rA rho = 1"
    using action_selection_forces[OF rho01 mSel] rT by blast
  obtain j where j_lt: "j < length cas" and rA_eq: "rA = Pos (ReifAction j)"
    using rA_in unfolding action_reifs_def by auto
  have satAC: "satisfies (action_constraint (Pos (ReifAction j)) (cas ! j) (vars \<Pi>e) B) rho"
    by (rule trans_action_constraint[OF mT j_lt])
  obtain a where a\<Pi>: "a \<in> acts \<Pi>" and caj: "cas ! j = embed_act a"
    using nth_mem[OF j_lt] cas_eq unfolding acts_embed by auto
  have preS: "pre (cas ! j) \<subseteq> vars \<Pi>e"
    and addS: "add (cas ! j) \<subseteq> vars \<Pi>e"
    and delS: "del (cas ! j) \<subseteq> vars \<Pi>e"
    using caj bspec[OF acts_states_sub a\<Pi>]
    by (auto simp: pre_embed add_embed del_embed vars_e)
  have outj: "eval_lit (Pos (ReifAction j)) rho = 1"
    using rA1 rA_eq by simp
  note ext = action_constraint_extract[OF rho01 satAC outj fin_vars_e preS addS delS]
  have delta1: "rho (ReifDeltaCost (cost (cas ! j))) = 1" using ext by blast
  have bound0: "rho (ReifPrimedCostGe B) = 0" using ext by blast
  have preO: "\<forall>w \<in> pre (cas ! j). rho (StateVar (Original w)) = 1" using ext by blast
  have addP: "\<forall>w \<in> add (cas ! j) - del (cas ! j). rho (StateVar (Primed w)) = 1"
    using ext by blast
  have delP: "\<forall>w \<in> del (cas ! j) - add (cas ! j). rho (StateVar (Primed w)) = 0"
    using ext by blast
  have frameO: "\<forall>w \<in> vars \<Pi>e - evars (cas ! j). rho (ReifEq (Original w)) = 1"
    using ext by blast
  \<comment> \<open>Cost step and cost bound for the transition.\<close>
  have mD: "models (encode_delta_cost (cost (cas ! j)) (bits_needed B)) rho"
    by (rule trans_delta[OF mT nth_mem[OF j_lt]])
  have c'_eq: "c' = c + cost a"
    using encode_delta_cost_forces[OF rho01 mD] delta1
    by (simp add: c_def c'_def caj cost_embed)
  have c'_lt_B: "c' < B"
  proof -
    have "rho (ReifPrimedCostGe B) = 1 \<longleftrightarrow> c' \<ge> B"
      using encode_cost_ge_primed_forces[OF rho01 trans_primed_ge[OF mT]]
      by (simp add: c'_def)
    then show ?thesis using bound0 by auto
  qed
  \<comment> \<open>Common final step: a true output literal on the primed side suffices.\<close>
  have to_out: "\<And>lit. lit \<in> set out_lits \<Longrightarrow> eval_lit lit rho_p = 1
      \<Longrightarrow> rho (primed_pvar_map out_name) = 1"
  proof -
    fix lit assume "lit \<in> set out_lits" and "eval_lit lit rho_p = 1"
    then have "rho_p out_name = 1"
      using outg_forces[OF rho_p01 mP'] by blast
    then show "rho (primed_pvar_map out_name) = 1" by (simp add: rho_p_def)
  qed
  \<comment> \<open>Disjunction over the unprimed output gate.\<close>
  have outO': "rho_o out_name = 1" using outO by (simp add: rho_o_def)
  obtain l where l_in: "l \<in> set out_lits" and l1: "eval_lit l rho_o = 1"
    using outg_forces[OF rho_o01 mO'] outO' by blast
  from l_in consider
    (ClosedGate) i where "i < n_cl" and "l = Pos (cl_name i)"
  | (OpenState) s where "s \<in> set open_list" and "l = hc_out HC (Inl ` s)"
    unfolding out_lits_def by auto
  then show ?thesis
  proof cases
    case OpenState
    have outO_hc: "eval_lit (map_literal (map_pvar Original) (hc_out HC (Inl ` s))) rho = 1"
      using l1 unfolding OpenState(2) by (simp add: eval_lit_map_literal rho_o_def)
    have m_hc_o: "models (circuit_constraints
        (orig_circuit (hc_gates HC, hc_out HC (Inl ` s)))) rho"
    proof -
      have "models (circuit_constraints (hc_gates HC, hc_out HC (Inl ` s))) rho_o"
        using models_hc_constraints[OF mO']
        by (simp add: hc_constraints_eq_circuit[of HC "hc_out HC (Inl ` s)", symmetric])
      then show ?thesis
        using models_circuit_constraints_lift[of "map_pvar Original"
            "(hc_gates HC, hc_out HC (Inl ` s))" rho]
        unfolding rho_o_def orig_circuit_def by blast
    qed
    have m_hc_p: "models (circuit_constraints
        (primed_circuit (hc_gates HC, hc_out HC (Inl ` s)))) rho"
    proof -
      have "models (circuit_constraints (hc_gates HC, hc_out HC (Inl ` s))) rho_p"
        using models_hc_constraints[OF mP']
        by (simp add: hc_constraints_eq_circuit[of HC "hc_out HC (Inl ` s)", symmetric])
      then show ?thesis
        using models_circuit_constraints_lift[of primed_pvar_map
            "(hc_gates HC, hc_out HC (Inl ` s))" rho]
        unfolding rho_p_def primed_circuit_def by blast
    qed
    have prim_hc: "eval_lit (map_literal primed_pvar_map (hc_out HC (Inl ` s))) rho = 1"
      by (rule hc_ind_lemmaD[OF hc_ok_ind[OF OpenState(1)] rho01 m_hc_o m_hc_p mT mB rT outO_hc])
    have "eval_lit (hc_out HC (Inl ` s)) rho_p = 1"
      using prim_hc by (simp add: eval_lit_map_literal rho_p_def)
    moreover have "hc_out HC (Inl ` s) \<in> set out_lits"
      unfolding out_lits_def using OpenState(1) by auto
    ultimately show ?thesis by (rule to_out[rotated])
  next
    case ClosedGate
    define s where "s = cl_state i"
    define g where "g = cl_g i"
    have cl1: "rho_o (cl_name i) = 1"
      using l1 ClosedGate by (simp add: eval_lit_def)
    have k1o: "rho_o (k_name i) = 1"
      and svO: "\<forall>v \<in> vars \<Pi>. rho_o (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
      using clg_forces[OF rho_o01 mO' ClosedGate(1)] cl1 unfolding s_def by auto
    have c_ge: "c \<ge> clip B (int g)"
      using kg_forces[OF rho_o01 mO' ClosedGate(1)] k1o c_o unfolding g_def by simp
    \<comment> \<open>The selected action is applicable in @{term s}.\<close>
    have appl: "applicable a s"
    proof -
      have "pre a \<subseteq> s"
      proof
        fix v assume vpre: "v \<in> pre a"
        have vV: "v \<in> vars \<Pi>" using vpre a\<Pi> acts_states_sub by auto
        have "Inl v \<in> pre (cas ! j)" using vpre by (simp add: caj pre_embed)
        then have "rho (StateVar (Original (Inl v))) = 1" using preO by blast
        then have one: "rho_o (StateVar (Inl v)) = 1" by (simp add: rho_o_def)
        have eq: "rho_o (StateVar (Inl v)) = (if v \<in> s then 1 else 0)"
          using svO vV by blast
        show "v \<in> s" using one eq by (cases "v \<in> s") auto
      qed
      then show ?thesis by (simp add: applicable_def)
    qed
    define s' where "s' = successor a s"
    \<comment> \<open>The primed state variables encode the successor exactly.\<close>
    have svP: "\<forall>v \<in> vars \<Pi>. rho_p (StateVar (Inl v)) = (if v \<in> s' then 1 else 0)"
    proof
      fix v assume vV: "v \<in> vars \<Pi>"
      have rp: "rho_p (StateVar (Inl v)) = rho (StateVar (Primed (Inl v)))"
        by (simp add: rho_p_def)
      consider (AddC) "v \<in> add a" | (DelC) "v \<in> del a" "v \<notin> add a" | (FrameC) "v \<notin> evars a"
        by (auto simp: evars_def)
      then show "rho_p (StateVar (Inl v)) = (if v \<in> s' then 1 else 0)"
      proof cases
        case AddC
        have "v \<notin> del a" using AddC acts_disjoint a\<Pi> by auto
        then have "Inl v \<in> add (cas ! j) - del (cas ! j)"
          using AddC by (auto simp: caj add_embed del_embed)
        then have "rho (StateVar (Primed (Inl v))) = 1" using addP by blast
        moreover have "v \<in> s'" using AddC by (simp add: s'_def successor_def)
        ultimately show ?thesis using rp by simp
      next
        case DelC
        have "Inl v \<in> del (cas ! j) - add (cas ! j)"
          using DelC by (auto simp: caj add_embed del_embed)
        then have "rho (StateVar (Primed (Inl v))) = 0" using delP by blast
        moreover have "v \<notin> s'" using DelC by (simp add: s'_def successor_def)
        ultimately show ?thesis using rp by simp
      next
        case FrameC
        have w_in: "Inl v \<in> vars \<Pi>e - evars (cas ! j)"
          using FrameC vV by (auto simp: vars_e caj evars_embed)
        then have eq1: "rho (ReifEq (Original (Inl v))) = 1" using frameO by blast
        have meq: "models (encode_eq_var (Inl v)) rho"
          by (rule trans_eq_var[OF mT]) (use vV in \<open>simp add: vars_e\<close>)
        have eq2: "rho (StateVar (Original (Inl v))) = rho (StateVar (Primed (Inl v)))"
          using encode_eq_var_forces[OF rho01 meq] eq1 by simp
        have eq3: "rho (StateVar (Original (Inl v))) = (if v \<in> s then 1 else 0)"
          using bspec[OF svO vV] by (simp add: rho_o_def)
        have eq4: "v \<in> s' \<longleftrightarrow> v \<in> s"
          using FrameC by (auto simp: s'_def successor_def evars_def)
        show ?thesis using rp eq2 eq3 eq4 by simp
      qed
    qed
    \<comment> \<open>Case analysis along the expansion-closure condition.\<close>
    have pair_in: "(s, g) \<in> set closed_list"
      using closed_nth_in[OF ClosedGate(1)] by (simp add: s_def g_def)
    from expansion pair_in a\<Pi> appl consider
      (GoalCase) "is_goal_state \<Pi> s" and "g \<ge> B"
    | (ClosedSucc) g'' where "(s', g'') \<in> set closed_list" and "g'' \<le> g + cost a"
    | (OpenSucc) "s' \<in> set open_list" and
        "int (g + cost a) \<ge> int B - int (hc_h HC (Inl ` s'))"
      unfolding s'_def by blast
    then show ?thesis
    proof cases
      case GoalCase
      have "clip B (int g) = B" using GoalCase(2) by simp
      then have "c \<ge> B" using c_ge by simp
      then have "c' \<ge> B" using c'_eq by simp
      then have False using c'_lt_B by simp
      then show ?thesis ..
    next
      case ClosedSucc
      obtain i'' where i''_lt: "i'' < n_cl" and i''_s: "cl_state i'' = s'"
        and i''_g: "cl_g i'' = g''"
        using closed_mem_nth[OF ClosedSucc(1)] by blast
      have c'_ge: "c' \<ge> clip B (int (cl_g i''))"
      proof -
        have "clip B (int g'') \<le> clip B (int (g + cost a))"
          by (rule clip_mono) (use ClosedSucc(2) in simp)
        also have "... = clip B (int g + int (cost a))" by simp
        also have "... \<le> clip B (int g) + cost a" by (rule clip_add_le)
        also have "... \<le> c + cost a" using c_ge by simp
        also have "... = c'" using c'_eq by simp
        finally show ?thesis by (simp add: i''_g)
      qed
      have k1p: "rho_p (k_name i'') = 1"
        using kg_forces[OF rho_p01 mP' i''_lt] c'_ge c_p by simp
      have cl1p: "rho_p (cl_name i'') = 1"
        using clg_forces[OF rho_p01 mP' i''_lt] k1p svP i''_s by simp
      have "Pos (cl_name i'') \<in> set out_lits"
        unfolding out_lits_def using i''_lt by simp
      moreover have "eval_lit (Pos (cl_name i'')) rho_p = 1"
        using cl1p by (simp add: eval_lit_def)
      ultimately show ?thesis by (rule to_out)
    next
      case OpenSucc
      define h where "h = hc_h HC (Inl ` s')"
      have m_hc_p: "models (circuit_constraints
          (primed_circuit (hc_gates HC, hc_out HC (Inl ` s')))) rho"
      proof -
        have "models (circuit_constraints (hc_gates HC, hc_out HC (Inl ` s'))) rho_p"
          using models_hc_constraints[OF mP']
          by (simp add: hc_constraints_eq_circuit[of HC "hc_out HC (Inl ` s')", symmetric])
        then show ?thesis
          using models_circuit_constraints_lift[of primed_pvar_map
              "(hc_gates HC, hc_out HC (Inl ` s'))" rho]
          unfolding rho_p_def primed_circuit_def by blast
      qed
      have svP_e: "\<forall>w \<in> vars \<Pi>e. rho (StateVar (Primed w)) = (if w \<in> Inl ` s' then 1 else 0)"
      proof
        fix w assume "w \<in> vars \<Pi>e"
        then obtain v where wv: "w = Inl v" and vV: "v \<in> vars \<Pi>"
          by (auto simp: vars_e)
        have "rho (StateVar (Primed (Inl v))) = rho_p (StateVar (Inl v))"
          by (simp add: rho_p_def)
        then show "rho (StateVar (Primed w)) = (if w \<in> Inl ` s' then 1 else 0)"
          using bspec[OF svP vV] wv by (simp add: inj_image_mem_iff)
      qed
      have cb: "bits_val (bits_needed B) PrimedCostBit rho
          \<ge> clip B (int B - int (hc_h HC (Inl ` s')))"
      proof -
        have "clip B (int B - int h) \<le> clip B (int (g + cost a))"
          by (rule clip_mono) (use OpenSucc(2) in \<open>simp add: h_def\<close>)
        also have "... = clip B (int g + int (cost a))" by simp
        also have "... \<le> clip B (int g) + cost a" by (rule clip_add_le)
        also have "... \<le> c + cost a" using c_ge by simp
        also have "... = c'" using c'_eq by simp
        finally show ?thesis by (simp add: c'_def h_def)
      qed
      have prim_hc: "eval_lit (map_literal primed_pvar_map (hc_out HC (Inl ` s'))) rho = 1"
        by (rule hc_state_lemma_primed[OF hc_ok_state[OF OpenSucc(1)] rho01 m_hc_p svP_e cb])
      have "eval_lit (hc_out HC (Inl ` s')) rho_p = 1"
        using prim_hc by (simp add: eval_lit_map_literal rho_p_def)
      moreover have "hc_out HC (Inl ` s') \<in> set out_lits"
        unfolding out_lits_def using OpenSucc(1) by auto
      ultimately show ?thesis by (rule to_out[rotated])
    qed
  qed
qed

subsubsection \<open>Gate names: distinctness and freshness\<close>

lemma fst_kg: "fst (kg i) = Pos (k_name i)"
  by (simp add: kg_def k_gate_def)

lemma fst_clg: "fst (clg i) = Pos (cl_name i)"
  by (simp add: clg_def)

lemma fst_outg: "fst outg = Pos out_name"
  by (simp add: outg_def)

lemma hc_name_form:
  "g \<in> set (hc_gates HC) \<Longrightarrow> \<exists>j. pvar_of_lit (fst g) = ReifCert (Inr (2 * j + 1))"
  using hc_names by (cases g) (fastforce simp: pvar_of_lit_def)

lemma names_eq:
  "map (\<lambda>g. pvar_of_lit (fst g)) astar_gates
   = map k_name [0..<n_cl] @ map cl_name [0..<n_cl]
     @ map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC) @ [out_name]"
  by (simp add: astar_gates_def fst_kg fst_clg fst_outg pvar_of_lit_def o_def)

lemma parity_neq: "(2::nat) * m \<noteq> 2 * j + 1"
  by presburger

lemma hc_names_odd_set:
  assumes "x \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
  shows "\<exists>j. x = ReifCert (Inr (2 * j + 1))"
proof -
  obtain g where g_in: "g \<in> set (hc_gates HC)" and x_eq: "x = pvar_of_lit (fst g)"
    using assms by auto
  show ?thesis using hc_name_form[OF g_in] x_eq by simp
qed

lemma distinct_gate_names: "distinct (map (\<lambda>g. pvar_of_lit (fst g)) astar_gates)"
proof -
  have d1: "distinct (map k_name [0..<n_cl])"
    by (auto simp: distinct_map inj_on_def k_name_def)
  have d2: "distinct (map cl_name [0..<n_cl])"
    by (auto simp: distinct_map inj_on_def cl_name_def)
  have d3: "distinct (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
  proof -
    have "(\<lambda>(r, cs, A). pvar_of_lit r) = (\<lambda>g :: ('v + nat) pvar literal \<times>
        (nat \<times> ('v + nat) pvar literal) list \<times> nat. pvar_of_lit (fst g))"
      by (rule ext) (simp add: split_beta)
    then show ?thesis using hc_distinct by simp
  qed
  have inK: "\<And>x. x \<in> set (map k_name [0..<n_cl]) \<Longrightarrow> \<exists>i<n_cl. x = ReifCert (Inr (2 * i))"
    by (auto simp: k_name_def)
  have inCl: "\<And>x. x \<in> set (map cl_name [0..<n_cl]) \<Longrightarrow> \<exists>i<n_cl. x = ReifCert (Inr (2 * (n_cl + i)))"
    by (auto simp: cl_name_def)
  have disj_k_cl: "set (map k_name [0..<n_cl]) \<inter> set (map cl_name [0..<n_cl]) = {}"
    by (auto simp: k_name_def cl_name_def)
  have disj_k_hc: "set (map k_name [0..<n_cl])
      \<inter> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC)) = {}"
  proof -
    { fix x assume xK: "x \<in> set (map k_name [0..<n_cl])"
        and xH: "x \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
      obtain i where xi: "x = ReifCert (Inr (2 * i))" using inK[OF xK] by blast
      obtain j where xj: "x = ReifCert (Inr (2 * j + 1))" using hc_names_odd_set[OF xH] by blast
      from xi xj have "2 * i = 2 * j + 1" by simp
      then have False by presburger }
    then show ?thesis by blast
  qed
  have disj_k_out: "out_name \<notin> set (map k_name [0..<n_cl])"
    by (auto simp: k_name_def out_name_def)
  have disj_cl_hc: "set (map cl_name [0..<n_cl])
      \<inter> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC)) = {}"
  proof -
    { fix x assume xC: "x \<in> set (map cl_name [0..<n_cl])"
        and xH: "x \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
      obtain i where xi: "x = ReifCert (Inr (2 * (n_cl + i)))" using inCl[OF xC] by blast
      obtain j where xj: "x = ReifCert (Inr (2 * j + 1))" using hc_names_odd_set[OF xH] by blast
      from xi xj have "2 * (n_cl + i) = 2 * j + 1" by simp
      then have False by presburger }
    then show ?thesis by blast
  qed
  have disj_cl_out: "out_name \<notin> set (map cl_name [0..<n_cl])"
    by (auto simp: cl_name_def out_name_def)
  have disj_hc_out: "out_name \<notin> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
  proof
    assume "out_name \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))"
    then obtain j where "out_name = ReifCert (Inr (2 * j + 1))"
      using hc_names_odd_set by blast
    then have "2 * (2 * n_cl) = 2 * j + 1" by (simp add: out_name_def)
    then show False by presburger
  qed
  show ?thesis
    unfolding names_eq
    using d1 d2 d3 disj_k_cl disj_k_hc disj_k_out disj_cl_hc disj_cl_out disj_hc_out
    by auto
qed

lemma distinct_reif_astar: "distinct_reif_vars astar_circuit"
proof -
  have "distinct (map (\<lambda>g. pvar_of_lit (fst g)) astar_gates)"
    by (rule distinct_gate_names)
  then show ?thesis
    unfolding distinct_reif_vars_def astar_circuit_def fst_conv Let_def
    by (simp add: distinct_conv_nth)
qed

lemma names_are_cert:
  "v \<in> circuit_reif_pvars astar_circuit \<Longrightarrow> \<exists>w. v = ReifCert w"
proof -
  assume "v \<in> circuit_reif_pvars astar_circuit"
  then have "v \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) astar_gates)"
    unfolding circuit_reif_pvars_def astar_circuit_def by force
  then consider
      "v \<in> set (map k_name [0..<n_cl])" | "v \<in> set (map cl_name [0..<n_cl])"
    | "v \<in> set (map (\<lambda>g. pvar_of_lit (fst g)) (hc_gates HC))" | "v = out_name"
    unfolding names_eq by auto
  then show "\<exists>w. v = ReifCert w"
  proof cases
    case 1 then show ?thesis by (auto simp: k_name_def)
  next
    case 2 then show ?thesis by (auto simp: cl_name_def)
  next
    case 3 then show ?thesis using hc_names_odd_set by blast
  next
    case 4 then show ?thesis by (simp add: out_name_def)
  qed
qed

lemma astar_freshness:
  "\<forall>v \<in> circuit_reif_pvars astar_circuit.
      \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k) \<and> v \<noteq> ReifG \<and>
      (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
      (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
      (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
      (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and>
      (\<forall>i. v \<noteq> ReifAction i) \<and> (\<forall>i. v \<noteq> PrimedCostBit i)"
proof
  fix v assume "v \<in> circuit_reif_pvars astar_circuit"
  then obtain w where "v = ReifCert w" using names_are_cert by blast
  then show "\<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k) \<and> v \<noteq> ReifG \<and>
      (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
      (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
      (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
      (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and>
      (\<forall>i. v \<noteq> ReifAction i) \<and> (\<forall>i. v \<noteq> PrimedCostBit i)"
    by (simp add: is_input_pvar_def)
qed

subsubsection \<open>Well-formedness of the assembled circuit\<close>

lemma nth_in_take: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! j \<in> set (take i xs)"
  by (metis length_take min.absorb2 nth_mem nth_take)

lemma take_nth_ex: "g' \<in> set (take j xs) \<Longrightarrow> \<exists>p. p < j \<and> p < length xs \<and> g' = xs ! p"
  by (metis in_set_conv_nth length_take min_less_iff_conj nth_take)

lemma earlier_name:
  assumes "j < i" and "i \<le> length astar_gates"
  shows "pvar_of_lit (fst (astar_gates ! j)) \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
  using nth_in_take[OF assms] by force

lemma wf_astar_circuit: "wf_circuit astar_circuit"
proof -
  have len: "length astar_gates = 2 * n_cl + n_hc + 1" by (rule length_astar_gates)
  have main: "\<forall>i < length astar_gates.
      pvar_of_lit ` snd ` set (fst (snd (astar_gates ! i)))
        \<subseteq> {x. is_input_pvar x} \<union> pvar_of_lit ` fst ` set (take i astar_gates)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length astar_gates"
    have i_le: "i \<le> length astar_gates" using i_lt by simp
    consider (K) "i < n_cl" | (CL) "n_cl \<le> i" "i < 2 * n_cl"
      | (HCC) "2 * n_cl \<le> i" "i < 2 * n_cl + n_hc" | (OUT) "i = 2 * n_cl + n_hc"
      using i_lt len by linarith
    then show "pvar_of_lit ` snd ` set (fst (snd (astar_gates ! i)))
        \<subseteq> {x. is_input_pvar x} \<union> pvar_of_lit ` fst ` set (take i astar_gates)"
    proof cases
      case K
      have g: "astar_gates ! i = kg i" by (rule astar_gates_nth_k[OF K])
      show ?thesis
        unfolding g kg_def k_gate_def
        by (auto simp: k_gate_body_def pvar_of_lit_def is_input_pvar_def)
    next
      case CL
      define j where "j = i - n_cl"
      have j_lt: "j < n_cl" and i_eq: "i = n_cl + j" using CL by (auto simp: j_def)
      have g: "astar_gates ! i = clg j" using astar_gates_nth_cl[OF j_lt] i_eq by simp
      have kname_in: "k_name j \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
      proof -
        have "j < i" using j_lt CL i_eq by linarith
        from earlier_name[OF this i_le] show ?thesis
          using astar_gates_nth_k[OF j_lt] fst_kg by (simp add: pvar_of_lit_def)
      qed
      show ?thesis
        unfolding g clg_def
        using kname_in
        by (auto simp: cl_lits_def state_lits_exact_def pvar_of_lit_def is_input_pvar_def
            split: if_split_asm)
    next
      case HCC
      define j where "j = i - 2 * n_cl"
      have j_lt: "j < n_hc" and i_eq: "i = 2 * n_cl + j" using HCC by (auto simp: j_def)
      have g: "astar_gates ! i = hc_gates HC ! j"
        using astar_gates_nth_hc[OF j_lt] i_eq by simp
      obtain r cs A where hg: "hc_gates HC ! j = (r, cs, A)" by (metis prod_cases3)
      have body: "\<forall>x \<in> pvar_of_lit ` snd ` set cs.
          (\<exists>v. x = StateVar v) \<or> (\<exists>jj. x = CostBit jj)
          \<or> x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC))"
      proof -
        have "case hc_gates HC ! j of (r, cs, A) \<Rightarrow>
            (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
              (\<exists>v. x = StateVar v) \<or> (\<exists>jj. x = CostBit jj)
              \<or> x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC)))"
          using hc_wf[rule_format, OF j_lt[unfolded n_hc_def]] .
        then show ?thesis by (simp add: hg)
      qed
      have earlier_sub: "pvar_of_lit ` fst ` set (take j (hc_gates HC))
          \<subseteq> pvar_of_lit ` fst ` set (take i astar_gates)"
      proof
        fix x assume "x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC))"
        then obtain g' where g'_in: "g' \<in> set (take j (hc_gates HC))"
          and x_eq: "x = pvar_of_lit (fst g')" by auto
        obtain p where p_lt: "p < j" and p_len: "p < length (hc_gates HC)"
          and g'_eq: "g' = hc_gates HC ! p"
          using take_nth_ex[OF g'_in] by blast
        have pos: "astar_gates ! (2 * n_cl + p) = hc_gates HC ! p"
          using astar_gates_nth_hc p_len n_hc_def by simp
        have "2 * n_cl + p < i" using p_lt i_eq by simp
        from earlier_name[OF this i_le] show "x \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
          using pos g'_eq x_eq by simp
      qed
      show ?thesis
      proof (intro subsetI)
        fix x assume "x \<in> pvar_of_lit ` snd ` set (fst (snd (astar_gates ! i)))"
        then have x_in: "x \<in> pvar_of_lit ` snd ` set cs" by (simp add: g hg)
        from bspec[OF body x_in]
        show "x \<in> {x. is_input_pvar x} \<union> pvar_of_lit ` fst ` set (take i astar_gates)"
          using earlier_sub by (auto simp: is_input_pvar_def)
      qed
    next
      case OUT
      have g: "astar_gates ! i = outg" using astar_gates_nth_out OUT by simp
      have cl_in: "\<And>jj. jj < n_cl \<Longrightarrow> cl_name jj \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
      proof -
        fix jj assume jj: "jj < n_cl"
        have "n_cl + jj < i" using jj OUT by simp
        from earlier_name[OF this i_le] show
            "cl_name jj \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
          using astar_gates_nth_cl[OF jj] fst_clg by (simp add: pvar_of_lit_def)
      qed
      have hcl_in: "\<And>s. s \<in> set open_list \<Longrightarrow>
          pvar_of_lit (hc_out HC (Inl ` s)) \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
      proof -
        fix s assume sO: "s \<in> set open_list"
        have "hc_out HC (Inl ` s) \<in> fst ` set (hc_gates HC)" using hc_out_in sO by blast
        then obtain g' where g'_in: "g' \<in> set (hc_gates HC)"
          and out_eq: "hc_out HC (Inl ` s) = fst g'" by auto
        obtain p where p_len: "p < length (hc_gates HC)" and g'_eq: "g' = hc_gates HC ! p"
          using g'_in by (metis in_set_conv_nth)
        have pos: "astar_gates ! (2 * n_cl + p) = hc_gates HC ! p"
          using astar_gates_nth_hc p_len n_hc_def by simp
        have "2 * n_cl + p < i" using p_len OUT n_hc_def by simp
        from earlier_name[OF this i_le] show
            "pvar_of_lit (hc_out HC (Inl ` s)) \<in> pvar_of_lit ` fst ` set (take i astar_gates)"
          using pos g'_eq out_eq by simp
      qed
      show ?thesis
        unfolding g outg_def
        using cl_in hcl_in by (fastforce simp: out_lits_def pvar_of_lit_def)
    qed
  qed
  have out_cond: "Pos (pvar_of_lit (Pos out_name)) \<in> fst ` set astar_gates
      \<or> Neg (pvar_of_lit (Pos out_name)) \<in> fst ` set astar_gates"
  proof -
    have "Pos out_name \<in> fst ` set astar_gates"
      using outg_in_gates fst_outg by force
    then show ?thesis by (simp add: pvar_of_lit_def)
  qed
  show ?thesis
    unfolding wf_circuit_def astar_circuit_def Let_def
    using main out_cond by (auto simp: split_beta)
qed

lemma astar_body_pvars:
  assumes g_in: "(r, cs, A) \<in> set astar_gates"
    and x_in: "x \<in> pvar_of_lit ` snd ` set cs"
  shows "(\<exists>v. x = StateVar v) \<or> (\<exists>i. x = CostBit i) \<or> (\<exists>w. x = ReifCert w)"
proof -
  from g_in consider
    (K) i where "i < n_cl" and "(r, cs, A) = kg i"
  | (CL) i where "i < n_cl" and "(r, cs, A) = clg i"
  | (HCC) "(r, cs, A) \<in> set (hc_gates HC)"
  | (OUT) "(r, cs, A) = outg"
    unfolding astar_gates_def by auto
  then show ?thesis
  proof cases
    case K
    then have "cs = k_gate_body B" by (simp add: kg_def k_gate_def)
    then show ?thesis using x_in by (auto simp: k_gate_body_def pvar_of_lit_def)
  next
    case CL
    then have "cs = map (\<lambda>l. (1, l)) (cl_lits i)" by (simp add: clg_def)
    then show ?thesis using x_in
      by (auto simp: cl_lits_def state_lits_exact_def k_name_def pvar_of_lit_def
          split: if_split_asm)
  next
    case HCC
    then obtain j where j_len: "j < length (hc_gates HC)"
      and hg: "hc_gates HC ! j = (r, cs, A)"
      by (metis in_set_conv_nth)
    have body: "\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>jj. x = CostBit jj)
        \<or> x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC))"
    proof -
      have "case hc_gates HC ! j of (r, cs, A) \<Rightarrow>
          (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
            (\<exists>v. x = StateVar v) \<or> (\<exists>jj. x = CostBit jj)
            \<or> x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC)))"
        using hc_wf[rule_format, OF j_len] .
      then show ?thesis by (simp add: hg)
    qed
    from body x_in consider
        (SV) "(\<exists>v. x = StateVar v) \<or> (\<exists>jj. x = CostBit jj)"
      | (EN) "x \<in> pvar_of_lit ` fst ` set (take j (hc_gates HC))"
      by blast
    then show ?thesis
    proof cases
      case SV then show ?thesis by blast
    next
      case EN
      then obtain g' where g'_tk: "g' \<in> set (take j (hc_gates HC))"
        and x_eq: "x = pvar_of_lit (fst g')" by auto
      have "g' \<in> set (hc_gates HC)" using g'_tk by (rule in_set_takeD)
      then show ?thesis using hc_name_form x_eq by blast
    qed
  next
    case OUT
    then have "cs = map (\<lambda>l. (1, l)) out_lits" by (simp add: outg_def)
    then have "x \<in> pvar_of_lit ` set out_lits" using x_in by auto
    then consider
        (CLN) i where "i < n_cl" and "x = cl_name i"
      | (HCN) s where "s \<in> set open_list" and "x = pvar_of_lit (hc_out HC (Inl ` s))"
      by (auto simp: out_lits_def pvar_of_lit_def)
    then show ?thesis
    proof cases
      case CLN then show ?thesis by (simp add: cl_name_def)
    next
      case HCN
      have "hc_out HC (Inl ` s) \<in> fst ` set (hc_gates HC)" using hc_out_in HCN(1) by blast
      then obtain g' where "g' \<in> set (hc_gates HC)" and "hc_out HC (Inl ` s) = fst g'" by auto
      then show ?thesis using hc_name_form HCN(2) by fastforce
    qed
  qed
qed

lemma astar_no_pcb:
  "\<forall>(r, \<phi>) \<in> set (fst astar_circuit). \<forall>v \<in> constraint_pvars \<phi>. \<forall>i. v \<noteq> PrimedCostBit i"
proof -
  { fix r cs A v
    assume g_in: "(r, cs, A) \<in> set astar_gates"
      and v_in: "v \<in> constraint_pvars (cs, A)"
    have "v \<in> pvar_of_lit ` snd ` set cs"
      using v_in by (simp add: constraint_pvars_def)
    from astar_body_pvars[OF g_in this]
    have "\<forall>i. v \<noteq> PrimedCostBit i" by auto }
  then show ?thesis
    unfolding astar_circuit_def by fastforce
qed

subsubsection \<open>Output literal of the assembled circuit\<close>

lemma snd_circ: "snd astar_circuit = Pos out_name"
  by (simp add: astar_circuit_def)

lemma snd_orig_astar: "snd (orig_circuit astar_circuit) = Pos (map_pvar Original out_name)"
  by (simp add: snd_circ)

lemma snd_primed_astar: "snd (primed_circuit astar_circuit) = Pos (primed_pvar_map out_name)"
  by (simp add: snd_circ primed_circuit_def)

subsubsection \<open>CPR derivability of the three certificate conditions\<close>

lemma astar_init_cpr:
  "cpr_derives
     (encode_init \<Pi>e \<union> circuit_constraints astar_circuit \<union> encode_cost_ge B \<union>
      {unit_clause (Pos ReifI), neg_cost_ge_one B})
     (unit_clause (snd astar_circuit))"
proof (rule semantic_to_cpr)
  show "snd (unit_clause (snd astar_circuit)) \<ge> (1::nat)"
    by (simp add: unit_clause_def)
  show "\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow>
      models (encode_init \<Pi>e \<union> circuit_constraints astar_circuit \<union> encode_cost_ge B \<union>
        {unit_clause (Pos ReifI), neg_cost_ge_one B}) rho \<longrightarrow>
      satisfies (unit_clause (snd astar_circuit)) rho"
  proof (intro allI impI)
    fix rho :: "('v + nat) pvar \<Rightarrow> nat"
    assume rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
      and m: "models (encode_init \<Pi>e \<union> circuit_constraints astar_circuit \<union>
        encode_cost_ge B \<union> {unit_clause (Pos ReifI), neg_cost_ge_one B}) rho"
    have mI: "models (encode_init \<Pi>e) rho"
      and mC: "models (circuit_constraints astar_circuit) rho"
      and satRI: "satisfies (unit_clause (Pos ReifI)) rho"
      and bits0: "satisfies (neg_cost_ge_one B) rho"
      using m by (auto simp: models_def)
    have rI: "rho ReifI = 1"
      using satRI by (simp add: unit_clause_pos_sat[OF rho01])
    have "rho out_name = 1"
      by (rule astar_init_semantic[OF rho01 mI mC rI bits0])
    then show "satisfies (unit_clause (snd astar_circuit)) rho"
      by (simp add: snd_circ unit_clause_pos_sat[OF rho01])
  qed
qed

lemma astar_goal_cpr:
  "cpr_derives
     (encode_goal \<Pi>e \<union> circuit_constraints astar_circuit \<union> encode_cost_ge B \<union>
      {unit_clause (snd astar_circuit), unit_clause (Pos ReifG)})
     (cost_ge_constraint B)"
proof (rule semantic_to_cpr)
  show "snd (cost_ge_constraint B) \<ge> (1::nat)"
    using B_pos by (simp add: cost_ge_constraint_def)
  show "\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow>
      models (encode_goal \<Pi>e \<union> circuit_constraints astar_circuit \<union> encode_cost_ge B \<union>
        {unit_clause (snd astar_circuit), unit_clause (Pos ReifG)}) rho \<longrightarrow>
      satisfies (cost_ge_constraint B) rho"
  proof (intro allI impI)
    fix rho :: "('v + nat) pvar \<Rightarrow> nat"
    assume rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
      and m: "models (encode_goal \<Pi>e \<union> circuit_constraints astar_circuit \<union>
        encode_cost_ge B \<union> {unit_clause (snd astar_circuit), unit_clause (Pos ReifG)}) rho"
    have mG: "models (encode_goal \<Pi>e) rho"
      and mC: "models (circuit_constraints astar_circuit) rho"
      and satOut: "satisfies (unit_clause (snd astar_circuit)) rho"
      and satRG: "satisfies (unit_clause (Pos ReifG)) rho"
      using m by (auto simp: models_def)
    have out1: "rho out_name = 1"
      using satOut by (simp add: snd_circ unit_clause_pos_sat[OF rho01])
    have rG: "rho ReifG = 1"
      using satRG by (simp add: unit_clause_pos_sat[OF rho01])
    have "bits_val (bits_needed B) CostBit rho \<ge> B"
      by (rule astar_goal_semantic[OF rho01 mG mC rG out1])
    then show "satisfies (cost_ge_constraint B) rho"
      by (simp add: cost_ge_constraint_def satisfies_def pb_sum_bits_val)
  qed
qed

lemma astar_ind_cpr:
  "cpr_derives
     (encode_transition cas (vars \<Pi>e) B \<union>
      circuit_constraints (orig_circuit astar_circuit) \<union>
      circuit_constraints (primed_circuit astar_circuit) \<union>
      encode_cost_ge B \<union>
      {unit_clause (snd (orig_circuit astar_circuit)), unit_clause (Pos ReifT)})
     (unit_clause (snd (primed_circuit astar_circuit)))"
proof (rule semantic_to_cpr)
  show "snd (unit_clause (snd (primed_circuit astar_circuit))) \<ge> (1::nat)"
    by (simp add: unit_clause_def)
  show "\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow>
      models (encode_transition cas (vars \<Pi>e) B \<union>
        circuit_constraints (orig_circuit astar_circuit) \<union>
        circuit_constraints (primed_circuit astar_circuit) \<union>
        encode_cost_ge B \<union>
        {unit_clause (snd (orig_circuit astar_circuit)), unit_clause (Pos ReifT)}) rho \<longrightarrow>
      satisfies (unit_clause (snd (primed_circuit astar_circuit))) rho"
  proof (intro allI impI)
    fix rho :: "(('v + nat) var) pvar \<Rightarrow> nat"
    assume rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
      and m: "models (encode_transition cas (vars \<Pi>e) B \<union>
        circuit_constraints (orig_circuit astar_circuit) \<union>
        circuit_constraints (primed_circuit astar_circuit) \<union>
        encode_cost_ge B \<union>
        {unit_clause (snd (orig_circuit astar_circuit)), unit_clause (Pos ReifT)}) rho"
    have mT: "models (encode_transition cas (vars \<Pi>e) B) rho"
      and mO: "models (circuit_constraints (orig_circuit astar_circuit)) rho"
      and mP: "models (circuit_constraints (primed_circuit astar_circuit)) rho"
      and mB: "models (encode_cost_ge B) rho"
      and satO: "satisfies (unit_clause (snd (orig_circuit astar_circuit))) rho"
      and satRT: "satisfies (unit_clause (Pos ReifT)) rho"
      using m by (auto simp: models_def)
    have outO: "rho (map_pvar Original out_name) = 1"
      using satO unfolding snd_orig_astar by (simp add: unit_clause_pos_sat[OF rho01])
    have rT: "rho ReifT = 1"
      using satRT by (simp add: unit_clause_pos_sat[OF rho01])
    have "rho (primed_pvar_map out_name) = 1"
      by (rule astar_ind_semantic[OF rho01 mT mO mP mB rT outO])
    then show "satisfies (unit_clause (snd (primed_circuit astar_circuit))) rho"
      by (simp add: snd_primed_astar unit_clause_pos_sat[OF rho01])
  qed
qed

subsubsection \<open>Main results: the A* snapshot yields a valid certificate\<close>

theorem astar_certificate_valid: "certificate_valid_cpr B \<Pi>e astar_cert"
proof -
  have fin_acts_e: "finite (acts \<Pi>e)"
    by (simp add: acts_embed fin_acts)
  have acts_sub: "acts \<Pi>e \<subseteq> set cas"
    using cas_eq by simp
  have cas_states: "\<forall>a \<in> set cas. pre a \<subseteq> vars \<Pi>e \<and> add a \<subseteq> vars \<Pi>e \<and> del a \<subseteq> vars \<Pi>e"
  proof
    fix a' assume "a' \<in> set cas"
    then obtain a0 where a0_in: "a0 \<in> acts \<Pi>" and a'_eq: "a' = embed_act a0"
      using cas_eq unfolding acts_embed by auto
    have "pre a0 \<subseteq> vars \<Pi> \<and> add a0 \<subseteq> vars \<Pi> \<and> del a0 \<subseteq> vars \<Pi>"
      using bspec[OF acts_states_sub a0_in] .
    then show "pre a' \<subseteq> vars \<Pi>e \<and> add a' \<subseteq> vars \<Pi>e \<and> del a' \<subseteq> vars \<Pi>e"
      by (auto simp: a'_eq pre_embed add_embed del_embed vars_e)
  qed
  show ?thesis
    unfolding certificate_valid_cpr_def Let_def
    using fin_vars_e init_sub_e goal_sub_e fin_acts_e acts_sub cas_states
      wf_astar_circuit distinct_reif_astar astar_no_pcb astar_freshness
      astar_init_cpr astar_goal_cpr astar_ind_cpr
    by (simp add: astar_cert_def)
qed

theorem astar_lower_bound:
  assumes "is_plan_for \<Pi> \<pi>"
  shows "plan_cost \<pi> \<ge> B"
  by (rule embedded_certificate_lower_bound[OF astar_certificate_valid assms])

corollary astar_optimal:
  assumes "is_plan_for \<Pi> \<pi>" and "plan_cost \<pi> = B"
  shows "optimal_plan \<Pi> \<pi>"
  by (rule embedded_certificate_optimality[OF astar_certificate_valid assms])

end

end
