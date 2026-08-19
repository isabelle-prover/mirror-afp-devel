section \<open>Efficient Pattern Databases\<close>

theory Efficient_PDB
  imports PDB_Certificates
begin

text \<open>Efficiently proof-logging PDB heuristics (paper appendix: Lemma 18,
  Definition 5 and Lemmas 19--29).  Definition 5 restricts the PDB circuit to
  the abstract states with finite goal distance --- the part of the abstract
  state space an efficient PDB implementation actually traverses --- and adds a
  gate @{text "r\<infinity>"} (equation (24)) that is true exactly when the current
  abstract state is none of the finite-distance ones.  The output (equation
  (25)) is the disjunction of @{text "r\<infinity>"} and the per-state threshold gates of
  equation (23).

  The distance table is now partial: @{text "d s\<alpha>"} together with a finiteness
  predicate @{text "fin s\<alpha>"} (@{text "d(s\<alpha>) < \<infinity>"} in the paper).  The two table
  conditions become: abstract goal states are finite with distance 0, and
  finiteness propagates backwards along applicable abstract transitions
  together with the triangle inequality (so an infinite-distance state can
  never reach a finite-distance one).

  Lemma 18 is a statement about the \<^emph>\<open>length\<close> of a CPR derivation of the
  covering disjunction over all extensions of a partial assignment; under the
  semantic RUP over-approximation used throughout this formalization its
  content reduces to the existence of the witnessing extension in any 0/1
  model (@{text assignment_extension_witness} below); the step-count aspect is
  out of scope, as everywhere else.\<close>

subsection \<open>Lemma 18, semantic form\<close>

text \<open>Any 0/1 model whose @{text Y}-variables follow the pattern of a partial
  assignment determines a unique total extension on @{text "Z \<supseteq> Y"}: the set of
  @{text Z}-variables that are true.  With exact-state gates for all extensions
  this witness forces the covering disjunction (21) of the paper.\<close>

lemma assignment_extension_witness:
  fixes rho :: "'w \<Rightarrow> nat" and f :: "'u \<Rightarrow> 'w"
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and YZ: "Y \<subseteq> Z"
    and al_pat: "\<forall>v \<in> Y. rho (f v) = (if v \<in> al then 1 else 0)"
  shows "\<exists>t \<subseteq> Z. t \<inter> Y = al \<inter> Y \<and> (\<forall>v \<in> Z. rho (f v) = (if v \<in> t then 1 else 0))"
proof -
  define t where "t = {v \<in> Z. rho (f v) = 1}"
  have t_sub: "t \<subseteq> Z" unfolding t_def by auto
  have t_Y: "t \<inter> Y = al \<inter> Y"
  proof (rule set_eqI)
    fix v
    show "v \<in> t \<inter> Y \<longleftrightarrow> v \<in> al \<inter> Y"
    proof (cases "v \<in> Y")
      case True
      then have "rho (f v) = (if v \<in> al then 1 else 0)" using al_pat by blast
      then show ?thesis using True YZ unfolding t_def by (auto split: if_splits)
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have t_pat: "\<forall>v \<in> Z. rho (f v) = (if v \<in> t then 1 else 0)"
  proof
    fix v assume vZ: "v \<in> Z"
    show "rho (f v) = (if v \<in> t then 1 else 0)"
    proof (cases "v \<in> t")
      case True
      then show ?thesis unfolding t_def by simp
    next
      case False
      then have "rho (f v) \<noteq> 1" using vZ unfolding t_def by simp
      then show ?thesis using rho01[rule_format, of "f v"] False by simp
    qed
  qed
  show ?thesis using t_sub t_Y t_pat by blast
qed

subsection \<open>The efficient PDB locale\<close>

locale efficient_pdb =
  fixes \<Pi>e :: "'u::linorder strips_task"
    and B :: nat
    and P :: "'u set"
    and d :: "'u state \<Rightarrow> nat"
    and fin :: "'u state \<Rightarrow> bool"
    and Ss :: "'u state list"
    and as :: "'u action list"
    and nm :: "nat \<Rightarrow> 'u"
  assumes fin_vars: "finite (vars \<Pi>e)"
    and P_sub: "P \<subseteq> vars \<Pi>e"
    and Ss_set: "set Ss = {sa. sa \<subseteq> P \<and> fin sa}"
    and Ss_dist: "distinct Ss"
    and as_states: "\<forall>a \<in> set as. pre a \<subseteq> vars \<Pi>e \<and> add a \<subseteq> vars \<Pi>e \<and> del a \<subseteq> vars \<Pi>e"
    and as_disjoint: "\<forall>a \<in> set as. add a \<inter> del a = {}"
    and fin_goal: "\<And>sa. sa \<subseteq> P \<Longrightarrow> goal \<Pi>e \<inter> P \<subseteq> sa \<Longrightarrow> fin sa \<and> d sa = 0"
    and d_triangle: "\<And>sa a. sa \<subseteq> P \<Longrightarrow> a \<in> set as \<Longrightarrow> pre a \<inter> P \<subseteq> sa \<Longrightarrow>
        fin ((sa - del a) \<union> (add a \<inter> P)) \<Longrightarrow>
        fin sa \<and> d sa \<le> d ((sa - del a) \<union> (add a \<inter> P)) + cost a"
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

lemma sa_i_fin: "i < n_s \<Longrightarrow> fin (sa_i i)"
  using Ss_set nth_mem unfolding n_s_def sa_i_def by fastforce

lemma fin_mem_nth:
  assumes "sa \<subseteq> P" and "fin sa"
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

definition inf_name :: "'u pvar" where
  "inf_name = ReifCert (nm (3 * n_s))"

definition pout_name :: "'u pvar" where
  "pout_name = ReifCert (nm (3 * n_s + 1))"

subsubsection \<open>Gates\<close>

text \<open>Equations (22), (23) as in the plain PDB circuit, but only for the
  finite-distance abstract states.\<close>

definition abs_lits :: "nat \<Rightarrow> 'u pvar literal list" where
  "abs_lits i =
     map (\<lambda>v. if v \<in> sa_i i then Pos (StateVar v) else Neg (StateVar v))
       (sorted_list_of_set P)"

definition absg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "absg i = (Pos (abs_name i), map (\<lambda>l. (1, l)) (abs_lits i), length (abs_lits i))"

definition kgg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "kgg i = k_gate (Pos (kk_name i)) B (int B - int (d (sa_i i)))"

definition thr_lits :: "nat \<Rightarrow> 'u pvar literal list" where
  "thr_lits i = [Pos (abs_name i), Pos (kk_name i)]"

definition thrg :: "nat \<Rightarrow> 'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "thrg i = (Pos (thr_name i), map (\<lambda>l. (1, l)) (thr_lits i), length (thr_lits i))"

text \<open>Equation (24): @{text "r\<infinity>"} is the conjunction of the negated
  abstract-state gates --- true iff the current abstract state is none of the
  finite-distance ones.\<close>

definition inf_lits :: "'u pvar literal list" where
  "inf_lits = map (\<lambda>i. Neg (abs_name i)) [0..<n_s]"

definition infg :: "'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "infg = (Pos inf_name, map (\<lambda>l. (1, l)) inf_lits, length inf_lits)"

text \<open>Equation (25): the output disjunction of @{text "r\<infinity>"} and the threshold
  gates.\<close>

definition pout_lits :: "'u pvar literal list" where
  "pout_lits = Pos inf_name # map (\<lambda>i. Pos (thr_name i)) [0..<n_s]"

definition poutg :: "'u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat" where
  "poutg = (Pos pout_name, map (\<lambda>l. (1, l)) pout_lits, 1)"

definition epdb_gates ::
  "('u pvar literal \<times> (nat \<times> 'u pvar literal) list \<times> nat) list" where
  "epdb_gates = map absg [0..<n_s] @ map kgg [0..<n_s] @ map thrg [0..<n_s]
              @ [infg, poutg]"

definition epdb_cert :: "('u) heuristic_cert" where
  "epdb_cert = \<lparr> hc_gates = epdb_gates,
                 hc_out = (\<lambda>s. Pos pout_name),
                 hc_h = (\<lambda>s. if fin (s \<inter> P) then d (s \<inter> P) else B) \<rparr>"

subsubsection \<open>Basic structure of the gate list\<close>

lemma length_epdb_gates: "length epdb_gates = 3 * n_s + 2"
  by (simp add: epdb_gates_def)

lemma absg_in_gates: "i < n_s \<Longrightarrow> absg i \<in> set epdb_gates"
  by (simp add: epdb_gates_def)

lemma kgg_in_gates: "i < n_s \<Longrightarrow> kgg i \<in> set epdb_gates"
  by (simp add: epdb_gates_def)

lemma thrg_in_gates: "i < n_s \<Longrightarrow> thrg i \<in> set epdb_gates"
  by (simp add: epdb_gates_def)

lemma infg_in_gates: "infg \<in> set epdb_gates"
  by (simp add: epdb_gates_def)

lemma poutg_in_gates: "poutg \<in> set epdb_gates"
  by (simp add: epdb_gates_def)

lemma models_epdb_gate:
  assumes m: "models (hc_constraints epdb_cert) rho"
    and g_in: "(r, cs, A) \<in> set epdb_gates"
  shows "models (reification r cs A) rho"
proof (rule models_mono[OF m])
  show "reification r cs A \<subseteq> hc_constraints epdb_cert"
    using g_in unfolding hc_constraints_def epdb_cert_def by fastforce
qed

lemma models_absg:
  assumes "models (hc_constraints epdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (abs_name i))
      (map (\<lambda>l. (1, l)) (abs_lits i)) (length (abs_lits i))) rho"
  using models_epdb_gate[OF assms(1)] absg_in_gates[OF assms(2)]
  by (simp add: absg_def)

lemma models_kgg:
  assumes "models (hc_constraints epdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (kk_name i)) (k_gate_body B)
      (clip B (int B - int (d (sa_i i))))) rho"
  using models_epdb_gate[OF assms(1)] kgg_in_gates[OF assms(2)]
  by (simp add: kgg_def k_gate_def)

lemma models_thrg:
  assumes "models (hc_constraints epdb_cert) rho" and "i < n_s"
  shows "models (reification (Pos (thr_name i))
      (map (\<lambda>l. (1, l)) (thr_lits i)) (length (thr_lits i))) rho"
  using models_epdb_gate[OF assms(1)] thrg_in_gates[OF assms(2)]
  by (simp add: thrg_def)

lemma models_infg:
  assumes "models (hc_constraints epdb_cert) rho"
  shows "models (reification (Pos inf_name)
      (map (\<lambda>l. (1, l)) inf_lits) (length inf_lits)) rho"
  using models_epdb_gate[OF assms] infg_in_gates
  by (simp add: infg_def)

lemma models_poutg:
  assumes "models (hc_constraints epdb_cert) rho"
  shows "models (reification (Pos pout_name) (map (\<lambda>l. (1, l)) pout_lits) 1) rho"
  using models_epdb_gate[OF assms] poutg_in_gates
  by (simp add: poutg_def)

subsubsection \<open>Semantics of the gates\<close>

text \<open>The abstract state encoded by a 0/1 assignment of the state variables
  (the witness of Lemma 18 for @{text "Z = P"}).\<close>

definition abs_state :: "('u pvar \<Rightarrow> nat) \<Rightarrow> 'u state" where
  "abs_state rho = {v \<in> P. rho (StateVar v) = 1}"

lemma abs_state_sub: "abs_state rho \<subseteq> P"
  unfolding abs_state_def by auto

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
    and m: "models (hc_constraints epdb_cert) rho"
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

lemma absg_forces_eq:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
    and i_lt: "i < n_s"
  shows "rho (abs_name i) = 1 \<longleftrightarrow> abs_state rho = sa_i i"
proof -
  have "rho (abs_name i) = 1
      \<longleftrightarrow> (\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0))"
    by (rule absg_forces[OF rho01 m i_lt])
  also have "... \<longleftrightarrow> abs_state rho = sa_i i"
  proof
    assume A: "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    show "abs_state rho = sa_i i"
    proof (rule set_eqI)
      fix v
      show "v \<in> abs_state rho \<longleftrightarrow> v \<in> sa_i i"
      proof (cases "v \<in> P")
        case True
        then show ?thesis using A unfolding abs_state_def by (auto split: if_splits)
      next
        case False
        then show ?thesis using sa_i_sub[OF i_lt] unfolding abs_state_def by auto
      qed
    qed
  next
    assume E: "abs_state rho = sa_i i"
    show "\<forall>v \<in> P. rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
    proof
      fix v assume vP: "v \<in> P"
      show "rho (StateVar v) = (if v \<in> sa_i i then 1 else 0)"
      proof (cases "v \<in> sa_i i")
        case True
        then have "v \<in> abs_state rho" using E by simp
        then show ?thesis using True unfolding abs_state_def by simp
      next
        case False
        then have "v \<notin> abs_state rho" using E by simp
        then have "rho (StateVar v) \<noteq> 1" using vP unfolding abs_state_def by simp
        then show ?thesis using rho01[rule_format, of "StateVar v"] False by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma kgg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
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
    and m: "models (hc_constraints epdb_cert) rho"
    and i_lt: "i < n_s"
  shows "rho (thr_name i) = 1 \<longleftrightarrow> rho (abs_name i) = 1 \<and> rho (kk_name i) = 1"
proof -
  have "eval_lit (Pos (thr_name i)) rho = 1
      \<longleftrightarrow> (\<forall>l \<in> set (thr_lits i). eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_thrg[OF m i_lt]])
  then show ?thesis by (simp add: thr_lits_def eval_lit_def)
qed

lemma infg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
  shows "rho inf_name = 1 \<longleftrightarrow> (\<forall>i < n_s. rho (abs_name i) = 0)"
proof -
  have neg_sem: "\<And>i. eval_lit (Neg (abs_name i)) rho = 1 \<longleftrightarrow> rho (abs_name i) = 0"
  proof -
    fix i
    show "eval_lit (Neg (abs_name i)) rho = 1 \<longleftrightarrow> rho (abs_name i) = 0"
      by (cases "rho (abs_name i)") (auto simp: eval_lit_def)
  qed
  have "eval_lit (Pos inf_name) rho = 1
      \<longleftrightarrow> (\<forall>l \<in> set inf_lits. eval_lit l rho = 1)"
    by (rule conj_gate_forces[OF rho01 models_infg[OF m]])
  also have "... \<longleftrightarrow> (\<forall>i < n_s. rho (abs_name i) = 0)"
  proof
    assume L: "\<forall>l \<in> set inf_lits. eval_lit l rho = 1"
    show "\<forall>i < n_s. rho (abs_name i) = 0"
    proof (intro allI impI)
      fix i assume "i < n_s"
      then have "Neg (abs_name i) \<in> set inf_lits" by (auto simp: inf_lits_def)
      then have "eval_lit (Neg (abs_name i)) rho = 1" using L by blast
      then show "rho (abs_name i) = 0" using neg_sem by blast
    qed
  next
    assume R: "\<forall>i < n_s. rho (abs_name i) = 0"
    show "\<forall>l \<in> set inf_lits. eval_lit l rho = 1"
    proof
      fix l assume "l \<in> set inf_lits"
      then obtain i where "i < n_s" and "l = Neg (abs_name i)"
        by (auto simp: inf_lits_def)
      then show "eval_lit l rho = 1" using R neg_sem by blast
    qed
  qed
  finally show ?thesis by (simp add: eval_lit_def)
qed

lemma poutg_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
  shows "rho pout_name = 1
     \<longleftrightarrow> rho inf_name = 1 \<or> (\<exists>i < n_s. rho (thr_name i) = 1)"
proof -
  have "eval_lit (Pos pout_name) rho = 1
      \<longleftrightarrow> (\<exists>l \<in> set pout_lits. eval_lit l rho = 1)"
    by (rule disj_gate_forces[OF rho01 models_poutg[OF m]])
  then show ?thesis by (auto simp: pout_lits_def eval_lit_def)
qed

text \<open>If the encoded abstract state has infinite distance, all abstract-state
  gates are false and @{text "r\<infinity>"} fires (second case of Lemma 19).\<close>

lemma not_fin_inf:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
    and nf: "\<not> fin (abs_state rho)"
  shows "rho inf_name = 1"
proof -
  have "\<forall>i < n_s. rho (abs_name i) = 0"
  proof (intro allI impI)
    fix i assume i_lt: "i < n_s"
    have "abs_state rho \<noteq> sa_i i" using nf sa_i_fin[OF i_lt] by auto
    then have "rho (abs_name i) \<noteq> 1" using absg_forces_eq[OF rho01 m i_lt] by simp
    then show "rho (abs_name i) = 0" using rho01[rule_format] by blast
  qed
  then show ?thesis using infg_forces[OF rho01 m] by blast
qed

subsection \<open>Lemma 19: the state lemma\<close>

lemma epdb_state_lemma: "hc_state_lemma \<Pi>e B epdb_cert s"
  unfolding hc_state_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
    and sv: "\<forall>v \<in> vars \<Pi>e. rho (StateVar v) = (if v \<in> s then 1 else 0)"
    and cb: "bits_val (bits_needed B) CostBit rho \<ge> clip B (int B - int (hc_h epdb_cert s))"
  have abs_s: "abs_state rho = s \<inter> P"
  proof (rule set_eqI)
    fix v
    show "v \<in> abs_state rho \<longleftrightarrow> v \<in> s \<inter> P"
    proof (cases "v \<in> P")
      case True
      then have "rho (StateVar v) = (if v \<in> s then 1 else 0)"
        using sv P_sub by blast
      then show ?thesis using True unfolding abs_state_def by (auto split: if_splits)
    next
      case False
      then show ?thesis unfolding abs_state_def by auto
    qed
  qed
  show "eval_lit (hc_out epdb_cert s) rho = 1"
  proof (cases "fin (s \<inter> P)")
    case True
    obtain i where i_lt: "i < n_s" and i_s: "sa_i i = s \<inter> P"
      using fin_mem_nth[OF _ True] by auto
    have abs1: "rho (abs_name i) = 1"
      using absg_forces_eq[OF rho01 m i_lt] abs_s i_s by simp
    have kk1: "rho (kk_name i) = 1"
    proof -
      have "hc_h epdb_cert s = d (sa_i i)" using True by (simp add: epdb_cert_def i_s)
      then show ?thesis using kgg_forces[OF rho01 m i_lt] cb by simp
    qed
    have thr1: "rho (thr_name i) = 1"
      using thrg_forces[OF rho01 m i_lt] abs1 kk1 by blast
    then have "rho pout_name = 1"
      using poutg_forces[OF rho01 m] i_lt by blast
    then show ?thesis by (simp add: epdb_cert_def eval_lit_def)
  next
    case False
    have "rho inf_name = 1"
      by (rule not_fin_inf[OF rho01 m]) (simp add: abs_s False)
    then have "rho pout_name = 1"
      using poutg_forces[OF rho01 m] by blast
    then show ?thesis by (simp add: epdb_cert_def eval_lit_def)
  qed
qed

subsection \<open>Lemma 20: the goal lemma\<close>

lemma epdb_goal_lemma: "hc_goal_lemma \<Pi>e B epdb_cert s"
  unfolding hc_goal_lemma_def
proof (intro allI impI)
  fix rho :: "'u pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (hc_constraints epdb_cert) rho"
    and gv: "\<forall>v \<in> goal \<Pi>e. rho (StateVar v) = 1"
    and out1: "eval_lit (hc_out epdb_cert s) rho = 1"
  have p1: "rho pout_name = 1"
    using out1 by (simp add: epdb_cert_def eval_lit_def)
  have goal_t: "goal \<Pi>e \<inter> P \<subseteq> abs_state rho"
    using gv unfolding abs_state_def by auto
  from poutg_forces[OF rho01 m] p1
  consider (Inf) "rho inf_name = 1" | (Thr) i where "i < n_s" "rho (thr_name i) = 1"
    by blast
  then show "bits_val (bits_needed B) CostBit rho \<ge> B"
  proof cases
    case Inf
    \<comment> \<open>Impossible: the encoded abstract state contains the abstract goal and is
        therefore a finite-distance state, contradicting @{text "r\<infinity>"}.\<close>
    have fin_t: "fin (abs_state rho)"
      using fin_goal[OF abs_state_sub goal_t] by blast
    obtain i where i_lt: "i < n_s" and i_s: "sa_i i = abs_state rho"
      using fin_mem_nth[OF abs_state_sub fin_t] by auto
    have "rho (abs_name i) = 1"
      using absg_forces_eq[OF rho01 m i_lt] i_s by simp
    moreover have "rho (abs_name i) = 0"
      using infg_forces[OF rho01 m] Inf i_lt by blast
    ultimately have False by simp
    then show ?thesis ..
  next
    case Thr
    have abs1: "rho (abs_name i) = 1" and kk1: "rho (kk_name i) = 1"
      using thrg_forces[OF rho01 m Thr(1)] Thr(2) by blast+
    have i_s: "sa_i i = abs_state rho"
      using absg_forces_eq[OF rho01 m Thr(1)] abs1 by simp
    have goal_in: "goal \<Pi>e \<inter> P \<subseteq> sa_i i"
      using goal_t i_s by simp
    have d0: "d (sa_i i) = 0"
      using fin_goal[OF sa_i_sub[OF Thr(1)] goal_in] by blast
    have "clip B (int B - int (d (sa_i i))) = B"
      using d0 by simp
    then show ?thesis using kgg_forces[OF rho01 m Thr(1)] kk1 by simp
  qed
qed

subsection \<open>Lemmas 21--29: the inductivity lemma\<close>

text \<open>Paper Lemmas 21--24 treat the threshold-gate cases (finite source state,
  finite or infinite successor), Lemmas 25--28 the @{text "r\<infinity>"} cases, and
  Lemma 29 combines them.  Semantically all of them collapse into one chase
  with a case analysis on which disjunct of the output gate is true on the
  unprimed side and on whether the abstract successor state has finite
  distance.\<close>

lemma epdb_ind_lemma: "hc_ind_lemma \<Pi>e B as epdb_cert s"
  unfolding hc_ind_lemma_def
proof (intro allI impI)
  fix rho :: "'u var pvar \<Rightarrow> nat"
  assume rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mO: "models (circuit_constraints
        (orig_circuit (hc_gates epdb_cert, hc_out epdb_cert s))) rho"
    and mP: "models (circuit_constraints
        (primed_circuit (hc_gates epdb_cert, hc_out epdb_cert s))) rho"
    and mT: "models (encode_transition as (vars \<Pi>e) B) rho"
    and mB: "models (encode_cost_ge B) rho"
    and rT: "rho ReifT = 1"
    and outO: "eval_lit (map_literal (map_pvar Original) (hc_out epdb_cert s)) rho = 1"
  define rho_o where "rho_o = rho \<circ> map_pvar Original"
  define rho_p where "rho_p = rho \<circ> primed_pvar_map"
  have rho_o01: "\<forall>x. rho_o x = 0 \<or> rho_o x = 1"
    unfolding rho_o_def by (rule rho01_comp[OF rho01])
  have rho_p01: "\<forall>x. rho_p x = 0 \<or> rho_p x = 1"
    unfolding rho_p_def by (rule rho01_comp[OF rho01])
  have mO'': "models (circuit_constraints (hc_gates epdb_cert, hc_out epdb_cert s)) rho_o"
    using mO models_circuit_constraints_lift[of "map_pvar Original"
        "(hc_gates epdb_cert, hc_out epdb_cert s)" rho]
    unfolding rho_o_def orig_circuit_def by blast
  have mO': "models (hc_constraints epdb_cert) rho_o"
    using mO'' hc_constraints_eq_circuit[of epdb_cert "hc_out epdb_cert s"] by simp
  have mP'': "models (circuit_constraints (hc_gates epdb_cert, hc_out epdb_cert s)) rho_p"
    using mP models_circuit_constraints_lift[of primed_pvar_map
        "(hc_gates epdb_cert, hc_out epdb_cert s)" rho]
    unfolding rho_p_def primed_circuit_def by blast
  have mP': "models (hc_constraints epdb_cert) rho_p"
    using mP'' hc_constraints_eq_circuit[of epdb_cert "hc_out epdb_cert s"] by simp
  define c where "c = bits_val (bits_needed B) CostBit rho"
  define c' where "c' = bits_val (bits_needed B) PrimedCostBit rho"
  have c_o: "bits_val (bits_needed B) CostBit rho_o = c"
    by (simp add: rho_o_def c_def bits_val_def)
  have c_p: "bits_val (bits_needed B) CostBit rho_p = c'"
    by (simp add: rho_p_def c'_def bits_val_def)
  \<comment> \<open>The selected action.\<close>
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
  \<comment> \<open>The encoded abstract states of both sides, and the abstract transition
      between them (paper Lemmas 21, 25, 26).\<close>
  define t where "t = abs_state rho_o"
  define t' where "t' = abs_state rho_p"
  have t_sub: "t \<subseteq> P" unfolding t_def by (rule abs_state_sub)
  have pre_t: "pre a \<inter> P \<subseteq> t"
  proof
    fix v assume vp: "v \<in> pre a \<inter> P"
    have "rho (StateVar (Original v)) = 1" using preO vp by blast
    then have "rho_o (StateVar v) = 1" by (simp add: rho_o_def)
    then show "v \<in> t" using vp unfolding t_def abs_state_def by auto
  qed
  have step: "t' = (t - del a) \<union> (add a \<inter> P)"
  proof (rule set_eqI)
    fix v
    show "v \<in> t' \<longleftrightarrow> v \<in> (t - del a) \<union> (add a \<inter> P)"
    proof (cases "v \<in> P")
      case False
      then show ?thesis
        unfolding t_def t'_def abs_state_def by auto
    next
      case True
      have rp: "rho_p (StateVar v) = rho (StateVar (Primed v))"
        by (simp add: rho_p_def)
      consider (AddC) "v \<in> add a" | (DelC) "v \<in> del a" "v \<notin> add a"
        | (FrameC) "v \<notin> evars a"
        by (auto simp: evars_def)
      then show ?thesis
      proof cases
        case AddC
        have "v \<notin> del a" using AddC bspec[OF as_disjoint a_in] by auto
        then have "rho (StateVar (Primed v)) = 1" using addP AddC by blast
        then have "v \<in> t'" using True rp unfolding t'_def abs_state_def by simp
        then show ?thesis using AddC True by simp
      next
        case DelC
        have "rho (StateVar (Primed v)) = 0" using delP DelC by blast
        then have "v \<notin> t'" using rp unfolding t'_def abs_state_def by simp
        moreover have "v \<notin> (t - del a) \<union> (add a \<inter> P)" using DelC by auto
        ultimately show ?thesis by simp
      next
        case FrameC
        have w_in: "v \<in> vars \<Pi>e - evars a" using FrameC True P_sub by auto
        then have eq1: "rho (ReifEq (Original v)) = 1" using frameO by blast
        have meq: "models (encode_eq_var v) rho"
          by (rule trans_eq_var[OF mT]) (use w_in in blast)
        have eq2: "rho (StateVar (Original v)) = rho (StateVar (Primed v))"
          using encode_eq_var_forces[OF rho01 meq] eq1 by simp
        have mem_eq: "v \<in> t' \<longleftrightarrow> v \<in> t"
          using True eq2 unfolding t_def t'_def abs_state_def rho_o_def rho_p_def
          by simp
        have "v \<in> (t - del a) \<union> (add a \<inter> P) \<longleftrightarrow> v \<in> t"
          using FrameC by (auto simp: evars_def)
        then show ?thesis using mem_eq by simp
      qed
    qed
  qed
  \<comment> \<open>Common final step: with a true gate of the primed copy, the primed output
      fires.\<close>
  have to_out: "rho_p pout_name = 1 \<Longrightarrow>
      eval_lit (map_literal primed_pvar_map (hc_out epdb_cert s)) rho = 1"
    unfolding epdb_cert_def
    by (simp add: eval_lit_map_literal rho_p_def eval_lit_def)
  \<comment> \<open>If the successor state has infinite distance, the primed
      @{text "r\<infinity>"}-gate fires (paper Lemmas 23, 25--27).\<close>
  have inf_succ: "\<not> fin t' \<Longrightarrow> rho_p pout_name = 1"
  proof -
    assume "\<not> fin t'"
    then have "\<not> fin (abs_state rho_p)" unfolding t'_def by simp
    then have "rho_p inf_name = 1" by (rule not_fin_inf[OF rho_p01 mP'])
    then show "rho_p pout_name = 1" using poutg_forces[OF rho_p01 mP'] by blast
  qed
  \<comment> \<open>Disjunction over the unprimed output gate.\<close>
  have outO': "rho_o pout_name = 1"
    using outO unfolding epdb_cert_def
    by (simp add: eval_lit_map_literal rho_o_def eval_lit_def)
  from poutg_forces[OF rho_o01 mO'] outO'
  consider (Inf) "rho_o inf_name = 1"
    | (Thr) i where "i < n_s" "rho_o (thr_name i) = 1"
    by blast
  then have "rho_p pout_name = 1"
  proof cases
    case Inf
    \<comment> \<open>Paper Lemmas 25--28: the unprimed state has infinite distance, hence so
        does the successor (finiteness would propagate backwards).\<close>
    have nf_t: "\<not> fin t"
    proof
      assume "fin t"
      then obtain i where i_lt: "i < n_s" and i_s: "sa_i i = t"
        using fin_mem_nth[OF t_sub] by auto
      have "rho_o (abs_name i) = 1"
        using absg_forces_eq[OF rho_o01 mO' i_lt] i_s unfolding t_def by simp
      moreover have "rho_o (abs_name i) = 0"
        using infg_forces[OF rho_o01 mO'] Inf i_lt by blast
      ultimately show False by simp
    qed
    have "\<not> fin t'"
    proof
      assume "fin t'"
      then have "fin ((t - del a) \<union> (add a \<inter> P))" using step by simp
      then have "fin t" using d_triangle[OF t_sub a_in pre_t] by blast
      then show False using nf_t by simp
    qed
    then show ?thesis by (rule inf_succ)
  next
    case Thr
    \<comment> \<open>Paper Lemmas 21--24: the unprimed state is a finite-distance abstract
        state with a true threshold gate.\<close>
    have abs1: "rho_o (abs_name i) = 1" and kk1: "rho_o (kk_name i) = 1"
      using thrg_forces[OF rho_o01 mO' Thr(1)] Thr(2) by blast+
    have i_t: "sa_i i = t"
      using absg_forces_eq[OF rho_o01 mO' Thr(1)] abs1 unfolding t_def by simp
    have c_ge: "c \<ge> clip B (int B - int (d t))"
      using kgg_forces[OF rho_o01 mO' Thr(1)] kk1 c_o i_t by simp
    show ?thesis
    proof (cases "fin t'")
      case False
      then show ?thesis by (rule inf_succ)
    next
      case True
      \<comment> \<open>Paper Lemma 22: finite successor, threshold gate of the primed copy.\<close>
      have t'_sub: "t' \<subseteq> P" unfolding t'_def by (rule abs_state_sub)
      obtain i' where i'_lt: "i' < n_s" and i'_t: "sa_i i' = t'"
        using fin_mem_nth[OF t'_sub True] by auto
      have abs1': "rho_p (abs_name i') = 1"
        using absg_forces_eq[OF rho_p01 mP' i'_lt] i'_t unfolding t'_def by simp
      have tri: "d t \<le> d t' + cost a"
        using d_triangle[OF t_sub a_in pre_t] True step by auto
      have c'_ge: "c' \<ge> clip B (int B - int (d t'))"
      proof -
        have "int B - int (d t') \<le> (int B - int (d t)) + int (cost a)"
          using tri by linarith
        then have "clip B (int B - int (d t'))
            \<le> clip B ((int B - int (d t)) + int (cost a))"
          by (rule clip_mono)
        also have "... \<le> clip B (int B - int (d t)) + cost a"
          by (rule clip_add_le)
        also have "... \<le> c + cost a" using c_ge by simp
        also have "... = c'" using c'_eq by simp
        finally show ?thesis .
      qed
      have kk1': "rho_p (kk_name i') = 1"
        using kgg_forces[OF rho_p01 mP' i'_lt] c'_ge c_p i'_t by simp
      have "rho_p (thr_name i') = 1"
        using thrg_forces[OF rho_p01 mP' i'_lt] abs1' kk1' by blast
      then show ?thesis using poutg_forces[OF rho_p01 mP'] i'_lt by blast
    qed
  qed
  then show "eval_lit (map_literal primed_pvar_map (hc_out epdb_cert s)) rho = 1"
    by (rule to_out)
qed

text \<open>The efficient PDB certificate is a valid heuristic certificate in the
  sense of Definition 4, for any set of evaluated states.\<close>

theorem epdb_hc_valid: "hc_valid \<Pi>e B as epdb_cert S"
  unfolding hc_valid_def
  using epdb_state_lemma epdb_goal_lemma epdb_ind_lemma by blast

subsection \<open>Structural conditions for use in the A* certificate\<close>

lemma epdb_gates_nth_abs: "i < n_s \<Longrightarrow> epdb_gates ! i = absg i"
  by (simp add: epdb_gates_def nth_append)

lemma epdb_gates_nth_kgg: "i < n_s \<Longrightarrow> epdb_gates ! (n_s + i) = kgg i"
  by (simp add: epdb_gates_def nth_append)

lemma epdb_gates_nth_thrg: "i < n_s \<Longrightarrow> epdb_gates ! (2 * n_s + i) = thrg i"
  by (simp add: epdb_gates_def nth_append)

lemma epdb_gates_nth_inf: "epdb_gates ! (3 * n_s) = infg"
  by (simp add: epdb_gates_def nth_append)

lemma epdb_gates_nth_out: "epdb_gates ! (3 * n_s + 1) = poutg"
  by (simp add: epdb_gates_def nth_append)

lemma epdb_gate_name_nth:
  assumes p_lt: "p < length epdb_gates"
  shows "fst (epdb_gates ! p) = Pos (ReifCert (nm p))"
proof -
  consider (A) "p < n_s" | (K) "n_s \<le> p" "p < 2 * n_s"
    | (T) "2 * n_s \<le> p" "p < 3 * n_s" | (INF) "p = 3 * n_s" | (OUT) "p = 3 * n_s + 1"
    using p_lt length_epdb_gates by linarith
  then show ?thesis
  proof cases
    case A
    then show ?thesis
      using epdb_gates_nth_abs[OF A] by (simp add: absg_def abs_name_def)
  next
    case K
    then obtain q where p_eq: "p = n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using K p_eq by simp
    show ?thesis
      unfolding p_eq using epdb_gates_nth_kgg[OF q_lt]
      by (simp add: kgg_def k_gate_def kk_name_def)
  next
    case T
    then obtain q where p_eq: "p = 2 * n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using T p_eq by simp
    show ?thesis
      unfolding p_eq using epdb_gates_nth_thrg[OF q_lt]
      by (simp add: thrg_def thr_name_def)
  next
    case INF
    then show ?thesis
      using epdb_gates_nth_inf by (simp add: infg_def inf_name_def)
  next
    case OUT
    then show ?thesis
      using epdb_gates_nth_out by (simp add: poutg_def pout_name_def)
  qed
qed

lemma epdb_names:
  "\<forall>(r, cs, A) \<in> set (hc_gates epdb_cert). \<exists>j. r = Pos (ReifCert (nm j))"
proof -
  have "\<And>g. g \<in> set epdb_gates \<Longrightarrow> \<exists>j. fst g = Pos (ReifCert (nm j))"
  proof -
    fix g assume "g \<in> set epdb_gates"
    then obtain p where p_lt: "p < length epdb_gates" and g_eq: "g = epdb_gates ! p"
      by (auto simp: in_set_conv_nth)
    show "\<exists>j. fst g = Pos (ReifCert (nm j))"
      using epdb_gate_name_nth[OF p_lt] g_eq by auto
  qed
  then show ?thesis by (fastforce simp: epdb_cert_def)
qed

lemma epdb_distinct:
  "distinct (map (\<lambda>(r, cs, A). pvar_of_lit r) (hc_gates epdb_cert))"
proof -
  note len = length_epdb_gates
  have map_eq: "map (\<lambda>(r, cs, A). pvar_of_lit r) epdb_gates
      = map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 2]"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(r, cs, A). pvar_of_lit r) epdb_gates)
        = length (map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 2])"
      by (simp add: len)
    fix p assume "p < length (map (\<lambda>(r, cs, A). pvar_of_lit r) epdb_gates)"
    then have p_lt: "p < length epdb_gates" by simp
    have "(\<lambda>(r, cs, A). pvar_of_lit r) (epdb_gates ! p) = pvar_of_lit (fst (epdb_gates ! p))"
      by (simp add: split_beta)
    also have "... = ReifCert (nm p)"
      using epdb_gate_name_nth[OF p_lt] by (simp add: pvar_of_lit_def)
    finally show "map (\<lambda>(r, cs, A). pvar_of_lit r) epdb_gates ! p
        = map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 2] ! p"
      using p_lt len by (auto simp: nth_append less_Suc_eq)
  qed
  have "distinct (map (\<lambda>p. ReifCert (nm p)) [0..<3 * n_s + 2])"
    using nm_inj by (auto simp: distinct_map intro!: inj_onI dest: injD)
  then show ?thesis using map_eq by (simp add: epdb_cert_def)
qed

lemma epdb_out_in: "hc_out epdb_cert s \<in> fst ` set (hc_gates epdb_cert)"
proof -
  have "fst poutg = Pos pout_name" by (simp add: poutg_def)
  then show ?thesis using poutg_in_gates by (force simp: epdb_cert_def)
qed

lemma nth_in_take_epdb: "j < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs ! j \<in> set (take i xs)"
  by (metis length_take min.absorb2 nth_mem nth_take)

lemma epdb_wf:
  "\<forall>i < length (hc_gates epdb_cert). case hc_gates epdb_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert)))"
proof (intro allI impI)
  fix i assume i_lt: "i < length (hc_gates epdb_cert)"
  have hcg: "hc_gates epdb_cert = epdb_gates" by (simp add: epdb_cert_def)
  have i_lt': "i < length epdb_gates" using i_lt by (simp add: hcg)
  have i_le: "i \<le> length epdb_gates" using i_lt' by simp
  have abs_take: "\<And>q. q < n_s \<Longrightarrow> q < i \<Longrightarrow>
      abs_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
  proof -
    fix q assume q_lt: "q < n_s" and q_i: "q < i"
    have "epdb_gates ! q \<in> set (take i epdb_gates)"
      using nth_in_take_epdb q_i i_le by blast
    moreover have "fst (epdb_gates ! q) = Pos (abs_name q)"
      using epdb_gates_nth_abs[OF q_lt] by (simp add: absg_def)
    ultimately show "abs_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
      using hcg by (force simp: pvar_of_lit_def)
  qed
  consider (A) "i < n_s" | (K) "n_s \<le> i" "i < 2 * n_s"
    | (T) "2 * n_s \<le> i" "i < 3 * n_s" | (INF) "i = 3 * n_s" | (OUT) "i = 3 * n_s + 1"
    using i_lt' length_epdb_gates by linarith
  then show "case hc_gates epdb_cert ! i of (r, cs, A) \<Rightarrow>
      (\<forall>x \<in> pvar_of_lit ` snd ` set cs.
        (\<exists>v. x = StateVar v) \<or> (\<exists>j. x = CostBit j)
        \<or> x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert)))"
  proof cases
    case A
    have g: "hc_gates epdb_cert ! i = absg i"
      using epdb_gates_nth_abs[OF A] hcg by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) (abs_lits i)).
        (\<exists>v. x = StateVar v)"
      by (auto simp: abs_lits_def pvar_of_lit_def split: if_splits)
    then show ?thesis unfolding g absg_def by auto
  next
    case K
    then obtain q where i_eq: "i = n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using K i_eq by simp
    have g: "hc_gates epdb_cert ! i = kgg q"
      using epdb_gates_nth_kgg[OF q_lt] hcg i_eq by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (k_gate_body B). (\<exists>j. x = CostBit j)"
      by (auto simp: k_gate_body_def pvar_of_lit_def)
    then show ?thesis unfolding g kgg_def k_gate_def by auto
  next
    case T
    then obtain q where i_eq: "i = 2 * n_s + q" using le_iff_add by auto
    have q_lt: "q < n_s" using T i_eq by simp
    have g: "hc_gates epdb_cert ! i = thrg q"
      using epdb_gates_nth_thrg[OF q_lt] hcg i_eq by simp
    have abs_in: "abs_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
      using abs_take q_lt i_eq by simp
    have kk_in: "kk_name q \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
    proof -
      have "n_s + q < i" using q_lt i_eq by simp
      then have "epdb_gates ! (n_s + q) \<in> set (take i epdb_gates)"
        using nth_in_take_epdb i_le by blast
      moreover have "fst (epdb_gates ! (n_s + q)) = Pos (kk_name q)"
        using epdb_gates_nth_kgg[OF q_lt] by (simp add: kgg_def k_gate_def)
      ultimately show ?thesis using hcg by (force simp: pvar_of_lit_def)
    qed
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) (thr_lits q)).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
      using abs_in kk_in by (auto simp: thr_lits_def pvar_of_lit_def)
    then show ?thesis unfolding g thrg_def by auto
  next
    case INF
    have g: "hc_gates epdb_cert ! i = infg"
      using epdb_gates_nth_inf hcg INF by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) inf_lits).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
    proof
      fix x assume "x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) inf_lits)"
      then obtain q where q_lt: "q < n_s" and x_eq: "x = abs_name q"
        by (auto simp: inf_lits_def pvar_of_lit_def)
      have "q < i" using q_lt INF by simp
      then show "x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
        using abs_take q_lt x_eq by simp
    qed
    then show ?thesis unfolding g infg_def by auto
  next
    case OUT
    have g: "hc_gates epdb_cert ! i = poutg"
      using epdb_gates_nth_out hcg OUT by simp
    have "\<forall>x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) pout_lits).
        x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
    proof
      fix x assume "x \<in> pvar_of_lit ` snd ` set (map (\<lambda>l. (1, l)) pout_lits)"
      then consider (Base) "x = inf_name"
        | (Var) q where "q < n_s" "x = thr_name q"
        by (auto simp: pout_lits_def pvar_of_lit_def)
      then show "x \<in> pvar_of_lit ` fst ` set (take i (hc_gates epdb_cert))"
      proof cases
        case Base
        have "3 * n_s < i" using OUT by simp
        then have "epdb_gates ! (3 * n_s) \<in> set (take i epdb_gates)"
          using nth_in_take_epdb i_le by blast
        moreover have "fst (epdb_gates ! (3 * n_s)) = Pos inf_name"
          using epdb_gates_nth_inf by (simp add: infg_def)
        ultimately show ?thesis using hcg Base by (force simp: pvar_of_lit_def)
      next
        case Var
        have "2 * n_s + q < i" using Var(1) OUT by simp
        then have "epdb_gates ! (2 * n_s + q) \<in> set (take i epdb_gates)"
          using nth_in_take_epdb i_le by blast
        moreover have "fst (epdb_gates ! (2 * n_s + q)) = Pos (thr_name q)"
          using epdb_gates_nth_thrg[OF Var(1)] by (simp add: thrg_def)
        ultimately show ?thesis using hcg Var(2) by (force simp: pvar_of_lit_def)
      qed
    qed
    then show ?thesis unfolding g poutg_def by auto
  qed
qed

end

end
