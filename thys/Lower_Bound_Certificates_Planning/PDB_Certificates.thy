section \<open>Pattern Database Certificates\<close>

theory PDB_Certificates
  imports A_Star_Certificates
begin

text \<open>Proof-logging pattern database heuristics (paper equations (14)--(16) and
  Lemmas 8--13).  A PDB heuristic for a pattern @{text "P \<subseteq> V"} abstracts each
  state @{text s} to @{text "\<alpha>(s) = s \<inter> P"} and returns the precomputed abstract
  goal distance @{text "d(\<alpha>(s))"}.  The locale @{text pdb_heuristic} captures a
  PDB table over the abstract state space @{text "Pow P"}; the two semantic
  conditions on the table --- goal states have distance 0, and the distance is
  consistent along abstract transitions --- are exactly what the soundness of the
  generated certificate requires (the paper's ``relies on the correctness and
  admissibility of the PDB heuristic'').  From the table we assemble a
  @{type heuristic_cert} whose gates realize equations (14)--(16), with the
  K-gates of equation (15) inlined over the cost bits as everywhere else in this
  formalization, and prove it valid in the sense of Definition 4.\<close>

subsection \<open>The PDB locale\<close>

locale pdb_heuristic =
  fixes \<Pi>e :: "'u::linorder strips_task"
    and B :: nat
    and P :: "'u set"
    and d :: "'u state \<Rightarrow> nat"
    and Ss :: "'u state list"
    and as :: "'u action list"
    and nm :: "nat \<Rightarrow> 'u"
  assumes fin_vars: "finite (vars \<Pi>e)"
    and P_sub: "P \<subseteq> vars \<Pi>e"
    and Ss_set: "set Ss = Pow P"
    and Ss_dist: "distinct Ss"
    and as_states: "\<forall>a \<in> set as. pre a \<subseteq> vars \<Pi>e \<and> add a \<subseteq> vars \<Pi>e \<and> del a \<subseteq> vars \<Pi>e"
    and as_disjoint: "\<forall>a \<in> set as. add a \<inter> del a = {}"
    and d_goal: "\<And>sa. sa \<subseteq> P \<Longrightarrow> goal \<Pi>e \<inter> P \<subseteq> sa \<Longrightarrow> d sa = 0"
    and d_triangle: "\<And>sa a. sa \<subseteq> P \<Longrightarrow> a \<in> set as \<Longrightarrow> pre a \<inter> P \<subseteq> sa \<Longrightarrow>
        d sa \<le> d ((sa - del a) \<union> (add a \<inter> P)) + cost a"
    and nm_inj: "inj nm"
begin

lemma fin_P: "finite P"
  using fin_vars P_sub by (rule rev_finite_subset)

definition n_s :: nat where
  "n_s = length Ss"

definition sa_i :: "nat \<Rightarrow> 'u state" where
  "sa_i i = Ss ! i"

lemma sa_i_sub: "i < n_s \<Longrightarrow> sa_i i \<subseteq> P"
  using Ss_set nth_mem unfolding n_s_def sa_i_def by fastforce

lemma abs_mem_nth:
  assumes "sa \<subseteq> P"
  shows "\<exists>i. i < n_s \<and> sa_i i = sa"
proof -
  have "sa \<in> set Ss" using assms Ss_set by auto
  then show ?thesis
    unfolding n_s_def sa_i_def by (auto simp: in_set_conv_nth)
qed

subsubsection \<open>Gate names\<close>

definition abs_name :: "nat \<Rightarrow> 'u pvar" where
  "abs_name i = ReifCert (nm i)"

definition kk_name :: "nat \<Rightarrow> 'u pvar" where
  "kk_name i = ReifCert (nm (n_s + i))"

definition thr_name :: "nat \<Rightarrow> 'u pvar" where
  "thr_name i = ReifCert (nm (2 * n_s + i))"

definition pout_name :: "'u pvar" where
  "pout_name = ReifCert (nm (3 * n_s))"

subsubsection \<open>Gates\<close>

text \<open>Equation (14): the abstract-state gate is true iff the state variables
  restricted to the pattern encode exactly the abstract state.\<close>

definition abs_lits :: "nat \<Rightarrow> 'u pvar literal list" where
  "abs_lits i =
     map (\<lambda>v. if v \<in> sa_i i then Pos (StateVar v) else Neg (StateVar v))
       (sorted_list_of_set P)"

definition absg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "absg i = (Pos (abs_name i), map (\<lambda>l. (1, l)) (abs_lits i), length (abs_lits i))"

text \<open>The K-gate part of equation (15): the clipped cost threshold for
  @{text "B - d(s\<alpha>)"}, inlined over the cost bits.\<close>

definition kgg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "kgg i = k_gate (Pos (kk_name i)) B (int B - int (d (sa_i i)))"

text \<open>Equation (15): the conjunction of the abstract-state gate and its K-gate.\<close>

definition thr_lits :: "nat \<Rightarrow> 'u pvar literal list" where
  "thr_lits i = [Pos (abs_name i), Pos (kk_name i)]"

definition thrg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "thrg i = (Pos (thr_name i), map (\<lambda>l. (1, l)) (thr_lits i), length (thr_lits i))"

text \<open>Equation (16): the output disjunction over all abstract states.\<close>

definition pout_lits :: "'u pvar literal list" where
  "pout_lits = map (\<lambda>i. Pos (thr_name i)) [0..<n_s]"

definition poutg :: "'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "poutg = (Pos pout_name, map (\<lambda>l. (1, l)) pout_lits, 1)"

definition pdb_gates ::
  "('u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat) list" where
  "pdb_gates = map absg [0..<n_s] @ map kgg [0..<n_s] @ map thrg [0..<n_s] @ [poutg]"

definition pdb_cert :: "('u) heuristic_cert" where
  "pdb_cert = \<lparr> hc_gates = pdb_gates,
                hc_out = (\<lambda>s. Pos pout_name),
                hc_h = (\<lambda>s. d (s \<inter> P)) \<rparr>"

subsubsection \<open>Basic structure of the gate list\<close>

lemma length_pdb_gates: "length pdb_gates = 3 * n_s + 1"
  by (simp add: pdb_gates_def)

lemma absg_in_gates: "i < n_s \<Longrightarrow> absg i \<in> set pdb_gates"
  by (simp add: pdb_gates_def)

lemma kgg_in_gates: "i < n_s \<Longrightarrow> kgg i \<in> set pdb_gates"
  by (simp add: pdb_gates_def)

lemma thrg_in_gates: "i < n_s \<Longrightarrow> thrg i \<in> set pdb_gates"
  by (simp add: pdb_gates_def)

lemma poutg_in_gates: "poutg \<in> set pdb_gates"
  by (simp add: pdb_gates_def)

lemma models_pdb_gate:
  assumes m: "models (hc_constraints pdb_cert) rho"
    and g_in: "(r, cs, A) \<in> set pdb_gates"
  shows "models (reification r cs A) rho"
proof (rule models_mono[OF m])
  show "reification r cs A \<subseteq> hc_constraints pdb_cert"
    using g_in unfolding hc_constraints_def pdb_cert_def by fastforce
qed

lemma models_absg:
  assumes "models (hc_constraints pdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (abs_name i))
      (map (\<lambda>l. (1, l)) (abs_lits i)) (length (abs_lits i))) rho"
  using models_pdb_gate[OF assms(1)] absg_in_gates[OF assms(2)]
  by (simp add: absg_def)

lemma models_kgg:
  assumes "models (hc_constraints pdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (kk_name i)) (k_gate_body B)
      (clip B (int B - int (d (sa_i i))))) rho"
  using models_pdb_gate[OF assms(1)] kgg_in_gates[OF assms(2)]
  by (simp add: kgg_def k_gate_def)

lemma models_thrg:
  assumes "models (hc_constraints pdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (thr_name i))
      (map (\<lambda>l. (1, l)) (thr_lits i)) (length (thr_lits i))) rho"
  using models_pdb_gate[OF assms(1)] thrg_in_gates[OF assms(2)]
  by (simp add: thrg_def)

lemma models_poutg:
  assumes "models (hc_constraints pdb_cert) rho"
  shows "models (reification (Pos pout_name) (map (\<lambda>l. (1, l)) pout_lits) 1) rho"
  using models_pdb_gate[OF assms] poutg_in_gates
  by (simp add: poutg_def)

subsubsection \<open>Semantics of the gates\<close>

lemma abs_lits_sem:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "(\<forall>l \<in> set (abs_lits i). eval_lit l rho = 1)
     \<longleftrightarrow> (\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0))"
proof -
  have set_eq: "set (sorted_list_of_set P) = P"
    using fin_P by simp
  have lit_sem: "\<And>v. eval_lit (if v \<in> sa_i i then Pos (StateVar v)
        else Neg (StateVar v)) rho = 1
      \<longleftrightarrow> rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
  proof -
    fix v
    show "eval_lit (if v \<in> sa_i i then Pos (StateVar v) else Neg (StateVar v)) rho = 1
      \<longleftrightarrow> rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
      using rho01[rule_format, of "StateVar v"] by (auto simp: eval_lit_def)
  qed
  show ?thesis
  proof
    assume all1: "\<forall>l \<in> set (abs_lits i). eval_lit l rho = 1"
    show "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    proof
      fix v assume vP: "v \<in> P"
      have "(if v \<in> sa_i i then Pos (StateVar v) else Neg (StateVar v))
            \<in> set (abs_lits i)"
        unfolding abs_lits_def using vP set_eq by auto
      then have "eval_lit (if v \<in> sa_i i then Pos (StateVar v)
          else Neg (StateVar v)) rho = 1"
        using all1 by blast
      then show "rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
        using lit_sem[of v] by simp
    qed
  next
    assume enc: "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    show "\<forall>l \<in> set (abs_lits i). eval_lit l rho = 1"
    proof
      fix l assume "l \<in> set (abs_lits i)"
      then obtain v where vP: "v \<in> P"
        and l_eq: "l = (if v \<in> sa_i i then Pos (StateVar v) else Neg (StateVar v))"
        unfolding abs_lits_def using set_eq by auto
      show "eval_lit l rho = 1"
        using enc vP lit_sem[of v] unfolding l_eq by simp
    qed
  qed
qed

lemma absg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
    and i_lt: "i < n_s"
  shows "rho (abs_name i) = 1
     \<longleftrightarrow> (\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0))"
proof -
  have "eval_lit (Pos (abs_name i)) rho = 1
      \<longleftrightarrow> (\<forall>l \<in> set (abs_lits i). eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_absg[OF m i_lt]])
  then show ?thesis
    unfolding abs_lits_sem[OF rho01] by (simp add: eval_lit_def)
qed

lemma kgg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
    and i_lt: "i < n_s"
  shows "rho (kk_name i) = 1
     \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (d (sa_i i)))"
proof -
  have "eval_lit (Pos (kk_name i)) rho = 1
      \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (d (sa_i i)))"
    by (rule k_gate_forces[OF rho01 models_kgg[OF m i_lt]])
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma thrg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
    and i_lt: "i < n_s"
  shows "rho (thr_name i) = 1 \<longleftrightarrow> rho (abs_name i) = 1 \<and> rho (kk_name i) = 1"
proof -
  have "eval_lit (Pos (thr_name i)) rho = 1
      \<longleftrightarrow> (\<forall>l \<in> set (thr_lits i). eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_thrg[OF m i_lt]])
  then show ?thesis by (simp add: thr_lits_def eval_lit_def)
qed

lemma poutg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
  shows "rho pout_name = 1 \<longleftrightarrow> (\<exists>i < n_s. rho (thr_name i) = 1)"
proof -
  have "eval_lit (Pos pout_name) rho = 1
      \<longleftrightarrow> (\<exists>l \<in> set pout_lits. eval_lit l rho = 1)"
    by (rule disj_gate_forces[OF rho01 models_poutg[OF m]])
  then show ?thesis by (auto simp: pout_lits_def eval_lit_def)
qed

subsection \<open>Lemma 8: the state lemma\<close>

lemma pdb_state_lemma: "hc_state_lemma \<Pi>e B pdb_cert s"
  unfolding hc_state_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
    and sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
    and cb: "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h pdb_cert s))"
  obtain i where i_lt: "i < n_s" and i_s: "sa_i i = s \<inter> P"
    using abs_mem_nth[of "s \<inter> P"] by auto
  have abs1: "rho (abs_name i) = 1"
  proof -
    have "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    proof
      fix v assume vP: "v \<in> P"
      have "rho (StateVar v) = (if v \<in> s then 1 else 0)"
        using sv P_sub vP by blast
      then show "rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
        using vP by (simp add: i_s)
    qed
    then show ?thesis using absg_forces[OF rho01 m i_lt] by blast
  qed
  have kk1: "rho (kk_name i) = 1"
  proof -
    have "hc_h pdb_cert s = d (sa_i i)" by (simp add: pdb_cert_def i_s)
    then show ?thesis using kgg_forces[OF rho01 m i_lt] cb by simp
  qed
  have thr1: "rho (thr_name i) = 1"
    using thrg_forces[OF rho01 m i_lt] abs1 kk1 by blast
  have "rho pout_name = 1"
    using poutg_forces[OF rho01 m] thr1 i_lt by blast
  then show "eval_lit (hc_out pdb_cert s) rho = 1"
    by (simp add: pdb_cert_def eval_lit_def)
qed

subsection \<open>Lemma 9: the goal lemma\<close>

lemma pdb_goal_lemma: "hc_goal_lemma \<Pi>e B pdb_cert s"
  unfolding hc_goal_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints pdb_cert) rho"
    and gv: "\<forall>v \<in> goal \<Pi>e. rho (StateVar v) = 1"
    and out1: "eval_lit (hc_out pdb_cert s) rho = 1"
  have p1: "rho pout_name = 1"
    using out1 by (simp add: pdb_cert_def eval_lit_def)
  obtain i where i_lt: "i < n_s" and thr1: "rho (thr_name i) = 1"
    using poutg_forces[OF rho01 m] p1 by blast
  have abs1: "rho (abs_name i) = 1" and kk1: "rho (kk_name i) = 1"
    using thrg_forces[OF rho01 m i_lt] thr1 by blast+
  have absv: "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    using absg_forces[OF rho01 m i_lt] abs1 by blast
  have goal_in: "goal \<Pi>e \<inter> P \<subseteq> sa_i i"
  proof
    fix v assume vGP: "v \<in> goal \<Pi>e \<inter> P"
    have "rho (StateVar v) = 1" using gv vGP by blast
    moreover have "rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
      using absv vGP by blast
    ultimately show "v \<in> sa_i i" by (cases "v \<in> sa_i i") auto
  qed
  have d0: "d (sa_i i) = 0"
    using d_goal[OF sa_i_sub[OF i_lt] goal_in] .
  have "clip B (int B - int (d (sa_i i))) = B"
    using d0 by simp
  then show "bits_val (bits_needed B) CostBit rho \<ge> B"
    using kgg_forces[OF rho01 m i_lt] kk1 by simp
qed

subsection \<open>Lemmas 10--13: the inductivity lemma\<close>

text \<open>Paper Lemmas 10--13 build the inductivity lemma in four steps: the abstract
  transition for a single action (Lemma 10), the per-action invariant step
  (Lemma 11), the generalization over the transition relation (Lemma 12), and
  over all abstract states (Lemma 13).  Semantically these collapse into one
  chase through the encoded transition; the proof below follows the same steps:
  the selected action, the abstract successor state (Lemma 10), the cost step
  along the K-gates (Lemma 11), quantified over the selected action (Lemma 12)
  and the true abstract-state gate (Lemma 13).\<close>

lemma pdb_ind_lemma: "hc_ind_lemma \<Pi>e B as pdb_cert s"
  unfolding hc_ind_lemma_def
proof (intro allI impI)
  fix rho :: "'u var pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mO: "models (circuit_constraints
        (orig_circuit (hc_gates pdb_cert, hc_out pdb_cert s))) rho"
    and mP: "models (circuit_constraints
        (primed_circuit (hc_gates pdb_cert, hc_out pdb_cert s))) rho"
    and mT: "models (encode_transition as (vars \<Pi>e) B) rho"
    and mB: "models (encode_cost_ge B) rho"
    and rT: "rho ReifT = 1"
    and outO: "eval_lit (map_literal (map_pvar Original) (hc_out pdb_cert s)) rho = 1"
  define rho_o where "rho_o = rho \<circ> map_pvar Original"
  define rho_p where "rho_p = rho \<circ> primed_pvar_map"
  have rho_o01: "\<forall>x. rho_o x = 0 \<or> rho_o x = 1"
    unfolding rho_o_def by (rule rho01_comp[OF rho01])
  have rho_p01: "\<forall>x. rho_p x = 0 \<or> rho_p x = 1"
    unfolding rho_p_def by (rule rho01_comp[OF rho01])
  have mO'': "models (circuit_constraints (hc_gates pdb_cert, hc_out pdb_cert s)) rho_o"
    using mO models_circuit_constraints_lift[of "map_pvar Original"
        "(hc_gates pdb_cert, hc_out pdb_cert s)" rho]
    unfolding rho_o_def orig_circuit_def by blast
  have mO': "models (hc_constraints pdb_cert) rho_o"
    using mO'' hc_constraints_eq_circuit[of pdb_cert "hc_out pdb_cert s"] by simp
  have mP'': "models (circuit_constraints (hc_gates pdb_cert, hc_out pdb_cert s)) rho_p"
    using mP models_circuit_constraints_lift[of primed_pvar_map
        "(hc_gates pdb_cert, hc_out pdb_cert s)" rho]
    unfolding rho_p_def primed_circuit_def by blast
  have mP': "models (hc_constraints pdb_cert) rho_p"
    using mP'' hc_constraints_eq_circuit[of pdb_cert "hc_out pdb_cert s"] by simp
  define c where "c = bits_val (bits_needed B) CostBit rho"
  define c' where "c' = bits_val (bits_needed B) PrimedCostBit rho"
  have c_o: "bits_val (bits_needed B) CostBit rho_o = c"
    by (simp add: rho_o_def c_def bits_val_def)
  have c_p: "bits_val (bits_needed B) CostBit rho_p = c'"
    by (simp add: rho_p_def c'_def bits_val_def)
  \<comment> \<open>The selected action (paper Lemma 12 quantifies over it).\<close>
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
  \<comment> \<open>The true abstract-state gate on the unprimed side (paper Lemma 13
      quantifies over it).\<close>
  have outO': "rho_o pout_name = 1"
    using outO unfolding pdb_cert_def
    by (simp add: eval_lit_map_literal rho_o_def eval_lit_def)
  obtain i where i_lt: "i < n_s" and thr1: "rho_o (thr_name i) = 1"
    using poutg_forces[OF rho_o01 mO'] outO' by blast
  have abs1: "rho_o (abs_name i) = 1" and kk1: "rho_o (kk_name i) = 1"
    using thrg_forces[OF rho_o01 mO' i_lt] thr1 by blast+
  define sa where "sa = sa_i i"
  have sa_sub: "sa \<subseteq> P" unfolding sa_def by (rule sa_i_sub[OF i_lt])
  have absv: "\<forall>v \<in> P. rho_o (StateVar v) = (if v \<in> sa then 1 else 0)"
    using absg_forces[OF rho_o01 mO' i_lt] abs1 unfolding sa_def by blast
  have c_ge: "c \<ge> clip B (int B - int (d sa))"
    using kgg_forces[OF rho_o01 mO' i_lt] kk1 c_o unfolding sa_def by simp
  \<comment> \<open>The induced abstract action is applicable in the abstract state.\<close>
  have pre_sa: "pre a \<inter> P \<subseteq> sa"
  proof
    fix v assume vp: "v \<in> pre a \<inter> P"
    have "rho (StateVar (Original v)) = 1" using preO vp by blast
    then have "rho_o (StateVar v) = 1" by (simp add: rho_o_def)
    moreover have "rho_o (StateVar v) = (if v \<in> sa then 1 else 0)"
      using absv vp by blast
    ultimately show "v \<in> sa" by (cases "v \<in> sa") auto
  qed
  define sa' where "sa' = (sa - del a) \<union> (add a \<inter> P)"
  have sa'_sub: "sa' \<subseteq> P" using sa_sub unfolding sa'_def by auto
  obtain i' where i'_lt: "i' < n_s" and i'_s: "sa_i i' = sa'"
    using abs_mem_nth[OF sa'_sub] by auto
  \<comment> \<open>Paper Lemma 10: the primed state variables encode the abstract successor.\<close>
  have absv': "\<forall>v \<in> P. rho_p (StateVar v) = (if v \<in> sa' then 1 else 0)"
  proof
    fix v assume vP: "v \<in> P"
    have rp: "rho_p (StateVar v) = rho (StateVar (Primed v))"
      by (simp add: rho_p_def)
    consider (AddC) "v \<in> add a" | (DelC) "v \<in> del a" "v \<notin> add a" | (FrameC) "v \<notin> evars a"
      by (auto simp: evars_def)
    then show "rho_p (StateVar v) = (if v \<in> sa' then 1 else 0)"
    proof cases
      case AddC
      have "v \<notin> del a" using AddC bspec[OF as_disjoint a_in] by auto
      then have "rho (StateVar (Primed v)) = 1" using addP AddC by blast
      moreover have "v \<in> sa'" using AddC vP by (simp add: sa'_def)
      ultimately show ?thesis using rp by simp
    next
      case DelC
      have "rho (StateVar (Primed v)) = 0" using delP DelC by blast
      moreover have "v \<notin> sa'" using DelC by (auto simp: sa'_def)
      ultimately show ?thesis using rp by simp
    next
      case FrameC
      have w_in: "v \<in> vars \<Pi>e - evars a" using FrameC vP P_sub by auto
      then have eq1: "rho (ReifEq (Original v)) = 1" using frameO by blast
      have meq: "models (encode_eq_var v) rho"
        by (rule trans_eq_var[OF mT]) (use w_in in blast)
      have eq2: "rho (StateVar (Original v)) = rho (StateVar (Primed v))"
        using encode_eq_var_forces[OF rho01 meq] eq1 by simp
      have eq3: "rho (StateVar (Original v)) = (if v \<in> sa then 1 else 0)"
        using bspec[OF absv vP] by (simp add: rho_o_def)
      have eq4: "v \<in> sa' \<longleftrightarrow> v \<in> sa"
        using FrameC by (auto simp: sa'_def evars_def)
      show ?thesis using rp eq2 eq3 eq4 by simp
    qed
  qed
  have abs1': "rho_p (abs_name i') = 1"
    using absg_forces[OF rho_p01 mP' i'_lt, unfolded i'_s] absv' by blast
  \<comment> \<open>Paper Lemma 11: the cost step along the K-gates.\<close>
  have c'_ge: "c' \<ge> clip B (int B - int (d sa'))"
  proof -
    have tri: "d sa \<le> d sa' + cost a"
      using d_triangle[OF sa_sub a_in pre_sa] unfolding sa'_def .
    have "int B - int (d sa') \<le> (int B - int (d sa)) + int (cost a)"
      using tri by linarith
    then have "clip B (int B - int (d sa')) \<le> clip B ((int B - int (d sa)) + int (cost a))"
      by (rule clip_mono)
    also have "... \<le> clip B (int B - int (d sa)) + cost a"
      by (rule clip_add_le)
    also have "... \<le> c + cost a" using c_ge by simp
    also have "... = c'" using c'_eq by simp
    finally show ?thesis .
  qed
  have kk1': "rho_p (kk_name i') = 1"
    using kgg_forces[OF rho_p01 mP' i'_lt, unfolded i'_s] c'_ge c_p by simp
  have thr1': "rho_p (thr_name i') = 1"
    using thrg_forces[OF rho_p01 mP' i'_lt] abs1' kk1' by blast
  have "rho_p pout_name = 1"
    using poutg_forces[OF rho_p01 mP'] thr1' i'_lt by blast
  then show "eval_lit (map_literal primed_pvar_map (hc_out pdb_cert s)) rho = 1"
    unfolding pdb_cert_def
    by (simp add: eval_lit_map_literal rho_p_def eval_lit_def)
qed

text \<open>The PDB certificate is a valid heuristic certificate in the sense of
  Definition 4, for any set of evaluated states.\<close>

theorem pdb_hc_valid: "hc_valid \<Pi>e B as pdb_cert S"
  unfolding hc_valid_def
  using pdb_state_lemma pdb_goal_lemma pdb_ind_lemma by blast

subsection \<open>Structural conditions for use in the A* certificate\<close>

text \<open>The remaining conditions of the @{text astar_run} locale on the heuristic
  certificate: every gate is named @{text "ReifCert (nm p)"} (instantiating
  @{text nm} with @{text "\<lambda>j. Inr (2 * j + 1)"} at type @{text "'v + nat"} yields
  exactly the odd gate names required there), the names are distinct, gate
  bodies only mention state variables, cost bits and earlier gate names, and the
  output literal is a gate name.\<close>

lemma pdb_gates_nth_abs: "i < n_s \<Longrightarrow> pdb_gates ! i = absg i"
  by (simp add: pdb_gates_def nth_append)

lemma pdb_gates_nth_kgg: "i < n_s \<Longrightarrow> pdb_gates ! (n_s + i) = kgg i"
  by (simp add: pdb_gates_def nth_append)

lemma pdb_gates_nth_thrg: "i < n_s \<Longrightarrow> pdb_gates ! (2 * n_s + i) = thrg i"
  by (simp add: pdb_gates_def nth_append)

lemma pdb_gates_nth_out: "pdb_gates ! (3 * n_s) = poutg"
  by (simp add: pdb_gates_def nth_append)

lemma pdb_gate_name_nth:
  assumes p_lt: "p < length pdb_gates"
  shows "fst (pdb_gates ! p) = Pos (ReifCert (nm p))"
proof -
  consider (A) "p < n_s" | (K) "n_s \<le> p" "p < 2 * n_s"
    | (T) "2 * n_s \<le> p" "p < 3 * n_s" | (OUT) "p = 3 * n_s"
    using p_lt length_pdb_gates by linarith
  then show ?thesis
  proof cases
    case A
    then show ?thesis
      using pdb_gates_nth_abs[OF A] by (simp add: absg_def abs_name_def)
  next
    case K
    then obtain q where p_eq: "p = n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using K p_eq by simp
    show ?thesis
      unfolding p_eq using pdb_gates_nth_kgg[OF q_lt]
      by (simp add: kgg_def k_gate_def kk_name_def)
  next
    case T
    then obtain q where p_eq: "p = 2 * n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using T p_eq by simp
    show ?thesis
      unfolding p_eq using pdb_gates_nth_thrg[OF q_lt]
      by (simp add: thrg_def thr_name_def)
  next
    case OUT
    then show ?thesis
      using pdb_gates_nth_out by (simp add: poutg_def pout_name_def)
  qed
qed

lemma pdb_names:
  "\<forall>(r, cs, A) \<in> set (hc_gates pdb_cert). \<exists>j. r = Pos (ReifCert (nm j))"
proof -
  have "\<And>g. g \<in> set pdb_gates \<Longrightarrow> \<exists>j. fst g = Pos (ReifCert (nm j))"
  proof -
    fix g assume "g \<in> set pdb_gates"
    then obtain p where p_lt: "p < length pdb_gates" and g_eq: "g = pdb_gates ! p"
      by (auto simp: in_set_conv_nth)
    show "\<exists>j. fst g = Pos (ReifCert (nm j))"
      using pdb_gate_name_nth[OF p_lt] g_eq by auto
  qed
  then show ?thesis by (fastforce simp: pdb_cert_def)
qed

lemma pdb_distinct:
  "distinct (map (\<lambda>(r, cs, A). pvar_of_lit r) (hc_gates pdb_cert))"
proof -
  note len = length_pdb_gates
  have map_eq: "map (\<lambda>(r, cs, A). pvar_of_lit r) pdb_gates
      = map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 1]"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(r, cs, A). pvar_of_lit r) pdb_gates)
        = length (map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 1])"
      by (simp add: len)
    fix p assume "p < length (map (\<lambda>(r, cs, A). pvar_of_lit r) pdb_gates)"
    then have p_lt: "p < length pdb_gates" by simp
    have "(\<lambda>(r, cs, A). pvar_of_lit r) (pdb_gates ! p) = pvar_of_lit (fst (pdb_gates ! p))"
      by (simp add: split_beta)
    also have "... = ReifCert (nm p)"
      using pdb_gate_name_nth[OF p_lt] by (simp add: pvar_of_lit_def)
    finally show "map (\<lambda>(r, cs, A). pvar_of_lit r) pdb_gates ! p
        = map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 1] ! p"
      using p_lt len by (auto simp: nth_append less_Suc_eq)
  qed
  have "distinct (map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 1])"
    using nm_inj by (auto simp: distinct_map intro!: inj_onI dest: injD)
  then show ?thesis using map_eq by (simp add: pdb_cert_def)
qed

lemma pdb_out_in: "hc_out pdb_cert s \<in> fst ` set (hc_gates pdb_cert)"
proof -
  have "fst poutg = Pos pout_name" by (simp add: poutg_def)
  then show ?thesis using poutg_in_gates by (force simp: pdb_cert_def)
qed

lemma nth_in_take_pdb: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! j \<in> set (take i xs)"
  by (metis length_take min.absorb2 nth_mem nth_take)

lemma pdb_wf:
  "\<forall>i < length (hc_gates pdb_cert). case hc_gates pdb_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert)))"
proof (intro allI impI)
  fix i assume i_lt: "i < length (hc_gates pdb_cert)"
  have hcg: "hc_gates pdb_cert = pdb_gates" by (simp add: pdb_cert_def)
  have i_lt': "i < length pdb_gates" using i_lt by (simp add: hcg)
  have i_le: "i \<le> length pdb_gates" using i_lt' by simp
  consider (A) "i < n_s" | (K) "n_s \<le> i" "i < 2 * n_s"
    | (T) "2 * n_s \<le> i" "i < 3 * n_s" | (OUT) "i = 3 * n_s"
    using i_lt' length_pdb_gates by linarith
  then show "case hc_gates pdb_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert)))"
  proof cases
    case A
    have g: "hc_gates pdb_cert ! i = absg i"
      using pdb_gates_nth_abs[OF A] hcg by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) (abs_lits i)).
        (\<exists>v. x = StateVar v)"
      by (auto simp: abs_lits_def pvar_of_lit_def split: if_splits)
    then show ?thesis unfolding g absg_def by auto
  next
    case K
    then obtain q where i_eq: "i = n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using K i_eq by simp
    have g: "hc_gates pdb_cert ! i = kgg q"
      using pdb_gates_nth_kgg[OF q_lt] hcg i_eq by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (k_gate_body B). (\<exists>j. x = CostBit j)"
      by (auto simp: k_gate_body_def pvar_of_lit_def)
    then show ?thesis unfolding g kgg_def k_gate_def by auto
  next
    case T
    then obtain q where i_eq: "i = 2 * n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using T i_eq by simp
    have g: "hc_gates pdb_cert ! i = thrg q"
      using pdb_gates_nth_thrg[OF q_lt] hcg i_eq by simp
    have abs_in: "abs_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert))"
    proof -
      have "q < i" using q_lt i_eq by simp
      then have "pdb_gates ! q \<in> set (take i pdb_gates)"
        using nth_in_take_pdb i_le by blast
      moreover have "fst (pdb_gates ! q) = Pos (abs_name q)"
        using pdb_gates_nth_abs[OF q_lt] by (simp add: absg_def)
      ultimately show ?thesis using hcg by (force simp: pvar_of_lit_def)
    qed
    have kk_in: "kk_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert))"
    proof -
      have "n_s + q < i" using q_lt i_eq by simp
      then have "pdb_gates ! (n_s + q) \<in> set (take i pdb_gates)"
        using nth_in_take_pdb i_le by blast
      moreover have "fst (pdb_gates ! (n_s + q)) = Pos (kk_name q)"
        using pdb_gates_nth_kgg[OF q_lt] by (simp add: kgg_def k_gate_def)
      ultimately show ?thesis using hcg by (force simp: pvar_of_lit_def)
    qed
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) (thr_lits q)).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert))"
      using abs_in kk_in by (auto simp: thr_lits_def pvar_of_lit_def)
    then show ?thesis unfolding g thrg_def by auto
  next
    case OUT
    have g: "hc_gates pdb_cert ! i = poutg"
      using pdb_gates_nth_out hcg OUT by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) pout_lits).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert))"
    proof
      fix x assume "x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) pout_lits)"
      then obtain q where q_lt: "q < n_s" and x_eq: "x = thr_name q"
        by (auto simp: pout_lits_def pvar_of_lit_def)
      have "2 * n_s + q < i" using q_lt OUT by simp
      then have "pdb_gates ! (2 * n_s + q) \<in> set (take i pdb_gates)"
        using nth_in_take_pdb i_le by blast
      moreover have "fst (pdb_gates ! (2 * n_s + q)) = Pos (thr_name q)"
        using pdb_gates_nth_thrg[OF q_lt] by (simp add: thrg_def)
      ultimately show "x \<in> pvar_of_lit ` fst ` set (take i (hc_gates pdb_cert))"
        using hcg x_eq by (force simp: pvar_of_lit_def)
    qed
    then show ?thesis unfolding g poutg_def by auto
  qed
qed

end

end

