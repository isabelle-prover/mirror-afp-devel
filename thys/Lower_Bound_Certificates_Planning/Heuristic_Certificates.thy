section \<open>Heuristic Certificates\<close>

theory Heuristic_Certificates
  imports K_Gates
begin

text \<open>Definition 4 of the paper: heuristic certificates.  A heuristic maintains a
  PB circuit @{text H} (a gate list shared across all evaluated states) and, per
  evaluated state @{text s}, an output literal @{text "r\<^sup>h\<^sub>s"} and an estimate
  @{text "h s"}.  The three obligations (state, goal, inductivity lemma) are
  stated semantically over 0/1 models; by @{thm cpr_derives_iff_semantic} this is
  interchangeable with the paper's CPR-derivability formulation (a bridge for the
  state lemma is proved at the end of this theory).\<close>

subsection \<open>Renaming assignments along literal maps\<close>

lemma eval_lit_map_literal:
  "eval_lit (map_literal f l) rho = eval_lit l (rho \<circ> f)"
  by (cases l) (simp_all add: eval_lit_def)

lemma lit_neg_map_literal:
  "lit_neg (map_literal f l) = map_literal f (lit_neg l)"
  by (cases l) (simp_all add: lit_neg_def)

lemma pb_sum_map_literal:
  "pb_sum (map (\<lambda>(a, l). (a, map_literal f l)) cs) rho = pb_sum cs (rho \<circ> f)"
  by (induction cs) (auto simp: eval_lit_map_literal o_def)

lemma models_Union_iff:
  "models (\<Union>x\<in>S. F x) rho \<longleftrightarrow> (\<forall>x\<in>S. models (F x) rho)"
  unfolding models_def by blast

lemma models_reification_lift:
  "models (reification (map_literal f r) (map (\<lambda>(a, l). (a, map_literal f l)) cs) A) rho
   \<longleftrightarrow> models (reification r cs A) (rho \<circ> f)"
proof -
  have pos_sum: "pb_sum (map (\<lambda>(a, l). (a, map_literal f l)) cs) rho = pb_sum cs (rho \<circ> f)"
    by (rule pb_sum_map_literal)
  have fst_eq: "map (fst \<circ> (\<lambda>(a, l). (a, map_literal f l))) cs = map fst cs"
    by (induction cs) auto
  have neg_sum: "pb_sum (map ((\<lambda>(a, l). (a, lit_neg l)) \<circ> (\<lambda>(a, l). (a, map_literal f l))) cs) rho
      = pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) cs) (rho \<circ> f)"
    by (induction cs) (auto simp: lit_neg_map_literal eval_lit_map_literal o_def)
  have fwd: "satisfies (reif_fwd (map_literal f r) (map (\<lambda>(a, l). (a, map_literal f l)) cs) A) rho
      \<longleftrightarrow> satisfies (reif_fwd r cs A) (rho \<circ> f)"
    by (simp add: reif_fwd_def satisfies_def pos_sum
        lit_neg_map_literal eval_lit_map_literal)
  have bwd: "satisfies (reif_bwd (map_literal f r) (map (\<lambda>(a, l). (a, map_literal f l)) cs) A) rho
      \<longleftrightarrow> satisfies (reif_bwd r cs A) (rho \<circ> f)"
    by (simp add: reif_bwd_def satisfies_def Let_def fst_eq neg_sum eval_lit_map_literal)
  show ?thesis
    by (simp add: reification_def models_def fwd bwd)
qed

lemma models_circuit_constraints_lift:
  "models (circuit_constraints (lift_circuit f C)) rho
   \<longleftrightarrow> models (circuit_constraints C) (rho \<circ> f)"
proof -
  obtain pairs out where C: "C = (pairs, out)" by (cases C)
  have set_lift: "set (fst (lift_circuit f C))
      = (\<lambda>(r, cs, A). (map_literal f r, map (\<lambda>(a, l). (a, map_literal f l)) cs, A)) ` set pairs"
    by (simp add: C lift_circuit_def)
  have "models (circuit_constraints (lift_circuit f C)) rho
      \<longleftrightarrow> (\<forall>(r, cs, A) \<in> set pairs.
          models (reification (map_literal f r) (map (\<lambda>(a, l). (a, map_literal f l)) cs) A) rho)"
    unfolding circuit_constraints_def set_lift
    by (fastforce simp: models_Union_iff split_beta)
  also have "... \<longleftrightarrow> (\<forall>(r, cs, A) \<in> set pairs. models (reification r cs A) (rho \<circ> f))"
    using models_reification_lift by (fastforce simp: split_beta)
  also have "... \<longleftrightarrow> models (circuit_constraints C) (rho \<circ> f)"
    unfolding C circuit_constraints_def
    by (fastforce simp: models_Union_iff split_beta)
  finally show ?thesis .
qed

lemma rho01_comp:
  "(\<forall>x. rho x = 0 \<or> rho x = 1) \<Longrightarrow> (\<forall>x. (rho \<circ> f) x = 0 \<or> (rho \<circ> f) x = 1)"
  by simp

subsection \<open>Heuristic certificates (Definition 4)\<close>

record ('u) heuristic_cert =
  hc_gates :: "('u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat) list"
  hc_out   :: "'u state \<Rightarrow> 'u pvar literal"
  hc_h     :: "'u state \<Rightarrow> nat"

definition hc_constraints :: "('u) heuristic_cert \<Rightarrow> 'u pconstraint set" where
  "hc_constraints HC \<equiv> \<Union>(r, cs, A) \<in> set (hc_gates HC). reification r cs A"

lemma hc_constraints_eq_circuit:
  "hc_constraints HC = circuit_constraints (hc_gates HC, out)"
  by (simp add: hc_constraints_def circuit_constraints_def)

text \<open>State lemma: if the state variables encode exactly @{text s} on the task
  variables and the cost bits witness @{text "clip B (B - h s)"}, the output gate
  for @{text s} is forced.  (Paper: @{text "(r\<^sub>s \<and> cost\<ge>max{0,B−h(s)}) \<rightarrow> r\<^sup>h\<^sub>s"}.)\<close>

definition hc_state_lemma ::
  "'u strips_task \<Rightarrow> nat \<Rightarrow> ('u) heuristic_cert \<Rightarrow> 'u state \<Rightarrow> bool" where
  "hc_state_lemma \<Pi>e B HC s \<equiv>
    \<forall>rho. (\<forall>x. rho x = 0 \<or> rho x = 1) \<longrightarrow>
      models (hc_constraints HC) rho \<longrightarrow>
      (\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)) \<longrightarrow>
      bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h HC s)) \<longrightarrow>
      eval_lit (hc_out HC s) rho = 1"

lemma hc_state_lemmaD:
  assumes "hc_state_lemma \<Pi>e B HC s"
    and "\<forall>x. rho x = 0 \<or> rho x = 1"
    and "models (hc_constraints HC) rho"
    and "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
    and "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h HC s))"
  shows "eval_lit (hc_out HC s) rho = 1"
  using assms unfolding hc_state_lemma_def by blast

text \<open>Goal lemma: a true output gate together with a satisfied goal forces the
  cost bits to reach @{text B}.  (Paper: @{text "(r\<^sub>G \<and> r\<^sup>h\<^sub>s) \<rightarrow> cost\<ge>B"}.)\<close>

definition hc_goal_lemma ::
  "'u strips_task \<Rightarrow> nat \<Rightarrow> ('u) heuristic_cert \<Rightarrow> 'u state \<Rightarrow> bool" where
  "hc_goal_lemma \<Pi>e B HC s \<equiv>
    \<forall>rho. (\<forall>x. rho x = 0 \<or> rho x = 1) \<longrightarrow>
      models (hc_constraints HC) rho \<longrightarrow>
      (\<forall>v \<in> goal \<Pi>e. rho (StateVar v) = 1) \<longrightarrow>
      eval_lit (hc_out HC s) rho = 1 \<longrightarrow>
      bits_val (bits_needed B) CostBit rho \<ge> B"

lemma hc_goal_lemmaD:
  assumes "hc_goal_lemma \<Pi>e B HC s"
    and "\<forall>x. rho x = 0 \<or> rho x = 1"
    and "models (hc_constraints HC) rho"
    and "\<forall>v \<in> goal \<Pi>e. rho (StateVar v) = 1"
    and "eval_lit (hc_out HC s) rho = 1"
  shows "bits_val (bits_needed B) CostBit rho \<ge> B"
  using assms unfolding hc_goal_lemma_def by blast

text \<open>Inductivity lemma: across one encoded transition, a true (unprimed) output
  gate forces the primed copy.  (Paper: @{text "(r\<^sup>h\<^sub>s \<and> r\<^sub>T) \<rightarrow> r\<^sup>h\<^sub>s'"} from
  @{text "C\<^sub>t\<^sub>r\<^sub>a\<^sub>n\<^sub>s \<union> H \<union> H' \<union> C\<^sub>\<ge> \<union> C\<^sub>K"}.)\<close>

definition hc_ind_lemma ::
  "'u::linorder strips_task \<Rightarrow> nat \<Rightarrow> 'u action list \<Rightarrow> ('u) heuristic_cert \<Rightarrow> 'u state \<Rightarrow> bool" where
  "hc_ind_lemma \<Pi>e B as HC s \<equiv>
    \<forall>rho. (\<forall>x. rho x = 0 \<or> rho x = 1) \<longrightarrow>
      models (circuit_constraints (orig_circuit (hc_gates HC, hc_out HC s))) rho \<longrightarrow>
      models (circuit_constraints (primed_circuit (hc_gates HC, hc_out HC s))) rho \<longrightarrow>
      models (encode_transition as (vars \<Pi>e) B) rho \<longrightarrow>
      models (encode_cost_ge B) rho \<longrightarrow>
      rho ReifT = 1 \<longrightarrow>
      eval_lit (map_literal (map_pvar Original) (hc_out HC s)) rho = 1 \<longrightarrow>
      eval_lit (map_literal primed_pvar_map (hc_out HC s)) rho = 1"

lemma hc_ind_lemmaD:
  assumes "hc_ind_lemma \<Pi>e B as HC s"
    and "\<forall>x. rho x = 0 \<or> rho x = 1"
    and "models (circuit_constraints (orig_circuit (hc_gates HC, hc_out HC s))) rho"
    and "models (circuit_constraints (primed_circuit (hc_gates HC, hc_out HC s))) rho"
    and "models (encode_transition as (vars \<Pi>e) B) rho"
    and "models (encode_cost_ge B) rho"
    and "rho ReifT = 1"
    and "eval_lit (map_literal (map_pvar Original) (hc_out HC s)) rho = 1"
  shows "eval_lit (map_literal primed_pvar_map (hc_out HC s)) rho = 1"
  using assms unfolding hc_ind_lemma_def by blast

definition hc_valid ::
  "'u::linorder strips_task \<Rightarrow> nat \<Rightarrow> 'u action list \<Rightarrow> ('u) heuristic_cert \<Rightarrow> 'u state set \<Rightarrow> bool" where
  "hc_valid \<Pi>e B as HC S \<equiv>
    \<forall>s \<in> S. hc_state_lemma \<Pi>e B HC s \<and> hc_goal_lemma \<Pi>e B HC s \<and> hc_ind_lemma \<Pi>e B as HC s"

subsection \<open>The state lemma in primed variables\<close>

text \<open>The paper requires the heuristic to ``log a proof for the state lemma in
  terms of the primed variables''.  Formally this is a consequence of the
  unprimed state lemma, by precomposing a model of the primed circuit copy with
  the renaming @{const primed_pvar_map}.\<close>

lemma hc_state_lemma_primed:
  fixes \<Pi>e :: "'u::linorder strips_task"
  assumes sl: "hc_state_lemma \<Pi>e B HC s"
    and rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (circuit_constraints (primed_circuit (hc_gates HC, out))) rho"
    and sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar (Primed v)) = (if v \<in> s then 1 else 0)"
    and cb: "bits_val (bits_needed B) PrimedCostBit rho \<ge> clip B (int B - int (hc_h HC s))"
  shows "eval_lit (map_literal primed_pvar_map (hc_out HC s)) rho = 1"
proof -
  let ?rho' = "rho \<circ> primed_pvar_map"
  have rho'01: "\<forall>x. ?rho' x = 0 \<or> ?rho' x = 1"
    by (rule rho01_comp[OF rho01])
  have m': "models (hc_constraints HC) ?rho'"
    using m models_circuit_constraints_lift[of primed_pvar_map "(hc_gates HC, out)" rho]
    by (simp add: primed_circuit_def hc_constraints_eq_circuit[of HC out])
  have sv': "\<forall>v \<in> vars \<Pi>e. ?rho' (StateVar v) = (if v \<in> s then 1 else 0)"
    using sv by simp
  have cb': "bits_val (bits_needed B) CostBit ?rho' \<ge> clip B (int B - int (hc_h HC s))"
    using cb by (simp add: bits_val_def)
  have "eval_lit (hc_out HC s) ?rho' = 1"
    by (rule hc_state_lemmaD[OF sl rho'01 m' sv' cb'])
  then show ?thesis by (simp add: eval_lit_map_literal)
qed

text \<open>The analogous fact for the unprimed copy embedded by @{const orig_circuit}.\<close>

lemma hc_state_lemma_orig:
  fixes \<Pi>e :: "'u::linorder strips_task"
  assumes sl: "hc_state_lemma \<Pi>e B HC s"
    and rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (circuit_constraints (orig_circuit (hc_gates HC, out))) rho"
    and sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar (Original v)) = (if v \<in> s then 1 else 0)"
    and cb: "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h HC s))"
  shows "eval_lit (map_literal (map_pvar Original) (hc_out HC s)) rho = 1"
proof -
  let ?rho' = "rho \<circ> map_pvar Original"
  have rho'01: "\<forall>x. ?rho' x = 0 \<or> ?rho' x = 1"
    by (rule rho01_comp[OF rho01])
  have m': "models (hc_constraints HC) ?rho'"
    using m models_circuit_constraints_lift[of "map_pvar Original" "(hc_gates HC, out)" rho]
    by (simp add: orig_circuit_def hc_constraints_eq_circuit[of HC out])
  have sv': "\<forall>v \<in> vars \<Pi>e. ?rho' (StateVar v) = (if v \<in> s then 1 else 0)"
    using sv by simp
  have cb': "bits_val (bits_needed B) CostBit ?rho' \<ge> clip B (int B - int (hc_h HC s))"
    using cb by (simp add: bits_val_def)
  have "eval_lit (hc_out HC s) ?rho' = 1"
    by (rule hc_state_lemmaD[OF sl rho'01 m' sv' cb'])
  then show ?thesis by (simp add: eval_lit_map_literal)
qed

subsection \<open>Faithfulness bridge: the state lemma as a CPR derivation\<close>

text \<open>The paper states Definition 4 via CPR proofs.  The semantic conditions above
  are interchangeable with that formulation; we make this explicit for the state
  lemma (the other two obligations are analogous).  The state description
  @{text "C\<^sub>s"} of the paper becomes a set of unit clauses, and the clipped cost
  premise its bit-level constraint.\<close>

definition state_unit_clauses :: "'u strips_task \<Rightarrow> 'u state \<Rightarrow> 'u pconstraint set" where
  "state_unit_clauses \<Pi>e s \<equiv>
     (\<lambda>v. unit_clause (Pos (StateVar v))) ` (vars \<Pi>e \<inter> s)
   \<union> (\<lambda>v. unit_clause (Neg (StateVar v))) ` (vars \<Pi>e - s)"

lemma unit_clause_pos_sat:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "satisfies (unit_clause (Pos w)) rho \<longleftrightarrow> rho w = 1"
proof -
  have "rho w \<le> 1" by (rule rho01_le_one[OF rho01])
  then show ?thesis
    by (auto simp: unit_clause_def satisfies_def eval_lit_def)
qed

lemma unit_clause_neg_sat:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "satisfies (unit_clause (Neg w)) rho \<longleftrightarrow> rho w = 0"
  using rho01[rule_format, of w]
  by (auto simp: unit_clause_def satisfies_def eval_lit_def)

lemma state_unit_clauses_sat:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "models (state_unit_clauses \<Pi>e s) rho
       \<longleftrightarrow> (\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0))"
proof
  assume m: "models (state_unit_clauses \<Pi>e s) rho"
  show "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
  proof
    fix v assume vV: "v \<in> vars \<Pi>e"
    show "rho (StateVar v) = (if v \<in> s then 1 else 0)"
    proof (cases "v \<in> s")
      case True
      then have "unit_clause (Pos (StateVar v)) \<in> state_unit_clauses \<Pi>e s"
        using vV by (auto simp: state_unit_clauses_def)
      then have "satisfies (unit_clause (Pos (StateVar v))) rho"
        using m by (auto simp: models_def)
      then show ?thesis using True unit_clause_pos_sat[OF rho01] by simp
    next
      case False
      then have "unit_clause (Neg (StateVar v)) \<in> state_unit_clauses \<Pi>e s"
        using vV by (auto simp: state_unit_clauses_def)
      then have "satisfies (unit_clause (Neg (StateVar v))) rho"
        using m by (auto simp: models_def)
      then show ?thesis using False unit_clause_neg_sat[OF rho01] by simp
    qed
  qed
next
  assume enc: "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
  show "models (state_unit_clauses \<Pi>e s) rho"
    unfolding state_unit_clauses_def models_def
    using enc unit_clause_pos_sat[OF rho01] unit_clause_neg_sat[OF rho01]
    by auto
qed

theorem hc_state_lemma_cpr:
  fixes \<Pi>e :: "'u::linorder strips_task"
  assumes sl: "hc_state_lemma \<Pi>e B HC s"
  shows "cpr_derives
    (hc_constraints HC \<union> state_unit_clauses \<Pi>e s
     \<union> {clip_cost_constraint B (int B - int (hc_h HC s))})
    (unit_clause (hc_out HC s))"
proof (rule semantic_to_cpr)
  show "snd (unit_clause (hc_out HC s)) \<ge> (1::nat)"
    by (simp add: unit_clause_def)
  show "\<forall>rho. (\<forall>x. rho x = 0 \<or> rho x = 1) \<longrightarrow>
      models (hc_constraints HC \<union> state_unit_clauses \<Pi>e s
        \<union> {clip_cost_constraint B (int B - int (hc_h HC s))}) rho \<longrightarrow>
      satisfies (unit_clause (hc_out HC s)) rho"
  proof (intro allI impI)
    fix rho :: "'u pvar \<Rightarrow> nat"
    assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
      and m: "models (hc_constraints HC \<union> state_unit_clauses \<Pi>e s
        \<union> {clip_cost_constraint B (int B - int (hc_h HC s))}) rho"
    have m1: "models (hc_constraints HC) rho"
      and m2: "models (state_unit_clauses \<Pi>e s) rho"
      and m3: "satisfies (clip_cost_constraint B (int B - int (hc_h HC s))) rho"
      using m by (auto simp: models_def)
    have sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
      using state_unit_clauses_sat[OF rho01] m2 by blast
    have cb: "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h HC s))"
      using clip_cost_constraint_sat[OF rho01] m3 by blast
    have "eval_lit (hc_out HC s) rho = 1"
      by (rule hc_state_lemmaD[OF sl rho01 m1 sv cb])
    then show "satisfies (unit_clause (hc_out HC s)) rho"
      by (simp add: unit_clause_def satisfies_def)
  qed
qed

subsection \<open>Generic conjunction and disjunction gates\<close>

text \<open>The circuits of the paper's case study are built almost exclusively from two
  gate forms over unit-coefficient literal lists: conjunction gates
  @{text "r \<Leftrightarrow> \<Sigma> ℓᵢ \<ge> n"} (all of the @{text n} literals true) and disjunction
  gates @{text "r \<Leftrightarrow> \<Sigma> ℓᵢ \<ge> 1"} (some literal true).\<close>

lemma sum_list_units_all_one:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "(\<Sum>l\<leftarrow>ls. f l) \<ge> length ls" and "\<forall>l\<in>set ls. f l \<le> 1"
  shows "\<forall>l\<in>set ls. f l = 1"
  using assms
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons x ls)
  have x_le: "f x \<le> 1" and ls_le: "\<forall>l\<in>set ls. f l \<le> 1"
    using Cons.prems(2) by auto
  have ls_sum_le: "(\<Sum>l\<leftarrow>ls. f l) \<le> length ls"
    using ls_le by (induction ls) fastforce+
  have x1: "f x = 1" and rest: "(\<Sum>l\<leftarrow>ls. f l) \<ge> length ls"
    using Cons.prems(1) x_le ls_sum_le by auto
  show ?case using x1 Cons.IH[OF rest ls_le] by simp
qed

lemma conj_gate_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (reification r (map (\<lambda>l. (1, l)) ls) (length ls)) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> (\<forall>l\<in>set ls. eval_lit l rho = 1)"
proof -
  have sum_eq: "pb_sum (map (\<lambda>l. (1, l)) ls) rho = (\<Sum>l\<leftarrow>ls. eval_lit l rho)"
    by (induction ls) auto
  have le1: "\<forall>l\<in>set ls. eval_lit l rho \<le> 1"
    by (intro ballI eval_lit_le_one[OF rho01])
  have iff1: "eval_lit r rho = 1 \<longleftrightarrow> (\<Sum>l\<leftarrow>ls. eval_lit l rho) \<ge> length ls"
    using reification_forces[OF rho01 m] unfolding sum_eq .
  show ?thesis
  proof
    assume "eval_lit r rho = 1"
    then have "(\<Sum>l\<leftarrow>ls. eval_lit l rho) \<ge> length ls" using iff1 by simp
    then show "\<forall>l\<in>set ls. eval_lit l rho = 1"
      by (rule sum_list_units_all_one[OF _ le1])
  next
    assume all1: "\<forall>l\<in>set ls. eval_lit l rho = 1"
    have "(\<Sum>l\<leftarrow>ls. eval_lit l rho) = length ls"
      using all1 by (induction ls) auto
    then show "eval_lit r rho = 1" using iff1 by simp
  qed
qed

lemma disj_gate_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (reification r (map (\<lambda>l. (1, l)) ls) 1) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> (\<exists>l\<in>set ls. eval_lit l rho = 1)"
proof -
  have iff1: "eval_lit r rho = 1 \<longleftrightarrow> pb_sum (map (\<lambda>l. (1, l)) ls) rho \<ge> 1"
    by (rule reification_forces[OF rho01 m])
  show ?thesis
  proof
    assume "eval_lit r rho = 1"
    then have "pb_sum (map (\<lambda>l. (1, l)) ls) rho \<ge> 1" using iff1 by simp
    then have "\<exists>(a, l) \<in> set (map (\<lambda>l. (1, l)) ls). a * eval_lit l rho \<ge> 1"
      by (rule pb_sum_pos_ex)
    then obtain a l where "(a, l) \<in> set (map (\<lambda>l. (1, l)) ls)"
      and "a * eval_lit l rho \<ge> 1" by auto
    then have "l \<in> set ls" and "eval_lit l rho \<ge> 1" by auto
    then show "\<exists>l\<in>set ls. eval_lit l rho = 1"
      using eval_lit_le_one[OF rho01] by (metis le_antisym)
  next
    assume "\<exists>l\<in>set ls. eval_lit l rho = 1"
    then obtain l where l_in: "l \<in> set ls" and l1: "eval_lit l rho = 1" by blast
    have "pb_sum (map (\<lambda>l. (1, l)) ls) rho \<ge> 1"
      using l_in l1
    proof (induction ls)
      case Nil
      then show ?case by simp
    next
      case (Cons q ls)
      then show ?case by (cases "l = q") auto
    qed
    then show "eval_lit r rho = 1" using iff1 by simp
  qed
qed

end