section \<open>Encoding Semantics\<close>

theory Encoding_Semantics
  imports Lower_Bound_Certificates
begin

text \<open>Shared toolkit for formalizing the remainder of arXiv:2504.18443:
  semantic analysis of 0/1 models of the PB encoding (converse direction of the
  existing @{text "*_sound"} lemmas), the bridge between semantic 0/1 implication
  and @{const cpr_derives}, and the task embedding into an extended variable type
  that provides unboundedly many fresh circuit gate names.\<close>

subsection \<open>Basic facts about 0/1 assignments\<close>

lemma eval_lit_le_one:
  assumes "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "eval_lit l rho \<le> 1"
proof (cases l)
  case (Pos v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def)
next
  case (Neg v)
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma eval_lit_01:
  assumes "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "eval_lit l rho = 0 \<or> eval_lit l rho = 1"
proof (cases l)
  case (Pos v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def)
next
  case (Neg v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def)
qed

lemma eval_lit_neg_conv:
  assumes "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "eval_lit (lit_neg l) rho = 1 - eval_lit l rho"
proof (cases l)
  case (Pos v)
  then show ?thesis by (simp add: eval_lit_def lit_neg_def)
next
  case (Neg v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def lit_neg_def)
qed

lemma eval_lit_neg_sum_one:
  assumes "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "eval_lit l rho + eval_lit (lit_neg l) rho = 1"
proof (cases l)
  case (Pos v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def lit_neg_def)
next
  case (Neg v)
  then show ?thesis using assms[rule_format, of v] by (auto simp: eval_lit_def lit_neg_def)
qed

lemma pb_sum_le_weight:
  assumes "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "pb_sum coeffs rho \<le> sum_list (map fst coeffs)"
proof (induction coeffs)
  case Nil
  then show ?case by simp
next
  case (Cons p coeffs)
  obtain a l where p: "p = (a, l)" by (cases p)
  have "a * eval_lit l rho \<le> a * 1"
    by (rule mult_le_mono2[OF eval_lit_le_one[OF assms]])
  then have head: "a * eval_lit l rho \<le> a" by simp
  have "a * eval_lit l rho + pb_sum coeffs rho \<le> a + sum_list (map fst coeffs)"
    using head Cons.IH by (rule add_mono)
  then show ?case by (simp add: p)
qed

lemma pb_sum_unit_list:
  "pb_sum (map (\<lambda>v. (1, lt v)) xs) rho = (\<Sum>v\<leftarrow>xs. eval_lit (lt v) rho)"
  by (induction xs) auto

lemma pb_sum_unit_set:
  assumes "finite S"
  shows "pb_sum (map (\<lambda>v. (1, lt v)) (sorted_list_of_set S)) rho
       = (\<Sum>v\<in>S. eval_lit (lt v) rho)"
proof -
  have "pb_sum (map (\<lambda>v. (1, lt v)) (sorted_list_of_set S)) rho
      = (\<Sum>v\<leftarrow>sorted_list_of_set S. eval_lit (lt v) rho)"
    by (rule pb_sum_unit_list)
  also have "... = (\<Sum>v\<in>set (sorted_list_of_set S). eval_lit (lt v) rho)"
    by (rule sum_list_distinct_conv_sum_set) simp
  also have "set (sorted_list_of_set S) = S" using assms by simp
  finally show ?thesis .
qed

lemma sum_units_all_one:
  fixes f :: "'a \<Rightarrow> nat"
  assumes fin: "finite S"
    and total: "(\<Sum>v\<in>S. f v) \<ge> card S"
    and bnd: "\<forall>v\<in>S. f v \<le> 1"
  shows "\<forall>v\<in>S. f v = 1"
proof (rule ccontr)
  assume "\<not> (\<forall>v\<in>S. f v = 1)"
  then obtain v0 where v0: "v0 \<in> S" and "f v0 \<noteq> 1" by blast
  with bnd have f_v0: "f v0 = 0" by fastforce
  have cardpos: "0 < card S" using fin v0 by (auto simp: card_gt_0_iff)
  have bound_rest: "(\<Sum>v\<in>S - {v0}. f v) \<le> card (S - {v0})"
    using sum_bounded_above[of "S - {v0}" f 1] bnd by simp
  have "(\<Sum>v\<in>S. f v) = f v0 + (\<Sum>v\<in>S - {v0}. f v)"
    using fin v0 by (simp add: sum.remove)
  also have "... \<le> 0 + card (S - {v0})"
    using f_v0 bound_rest by simp
  also have "... = card S - 1"
    using fin v0 by (simp add: card_Diff_singleton)
  also have "... < card S"
    using cardpos by linarith
  finally show False using total by simp
qed

lemma pb_sum_pos_ex:
  assumes "pb_sum coeffs rho \<ge> 1"
  shows "\<exists>(a, l) \<in> set coeffs. a * eval_lit l rho \<ge> 1"
  using assms
proof (induction coeffs)
  case Nil
  then show ?case by simp
next
  case (Cons p coeffs)
  obtain a l where p: "p = (a, l)" by (cases p)
  show ?case
  proof (cases "a * eval_lit l rho \<ge> 1")
    case True
    then show ?thesis by (auto simp: p)
  next
    case False
    then have zero: "a * eval_lit l rho = 0" by linarith
    have "pb_sum coeffs rho \<ge> 1" using Cons.prems by (simp add: p zero)
    from Cons.IH[OF this] show ?thesis by (auto simp: p)
  qed
qed

subsection \<open>Semantic implication and CPR derivability\<close>

text \<open>Because the formal CPR system contains the semantic @{thm cpr_derives.rup}
  rule, derivability of a constraint with positive threshold is \<^emph>\<open>equivalent\<close> to
  semantic implication over 0/1 assignments.  All ``it is possible to derive''
  lemmas of the paper are proved through this bridge.\<close>

lemma implies01_unsat_neg:
  assumes impl: "\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow> models CC rho \<longrightarrow> satisfies C rho"
    and A_pos: "snd C \<ge> (1::nat)"
  shows "unsat_01 (CC \<union> {constraint_neg C})"
proof (rule ccontr)
  assume "\<not> unsat_01 (CC \<union> {constraint_neg C})"
  then obtain rho where rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (CC \<union> {constraint_neg C}) rho"
    unfolding unsat_01_def by blast
  obtain coeffs A where C: "C = (coeffs, A)" by (cases C)
  have A1: "A \<ge> 1" using A_pos C by simp
  have mCC: "models CC rho" using m by (simp add: models_def)
  have satC: "satisfies C rho" using impl rho01 mCC by blast
  have pos: "pb_sum coeffs rho \<ge> A" using satC by (simp add: C satisfies_def)
  let ?neg = "map (\<lambda>(a, l). (a, lit_neg l)) coeffs"
  let ?M = "sum_list (map fst coeffs)"
  have satN: "satisfies (constraint_neg C) rho" using m by (simp add: models_def)
  have neg: "pb_sum ?neg rho \<ge> ?M - (A - 1)"
    using satN by (simp add: constraint_neg_def C satisfies_def Let_def)
  have sum_eq: "pb_sum coeffs rho + pb_sum ?neg rho = ?M"
    by (rule pb_sum_add_negated_gen[OF rho01])
  show False
  proof (cases "A \<le> ?M")
    case True
    have "?M - (A - 1) = ?M - A + 1"
      using A1 True by simp
    then have "A + (?M - A + 1) \<le> pb_sum coeffs rho + pb_sum ?neg rho"
      using pos neg by (intro add_mono) auto
    then have "?M + 1 \<le> ?M" using sum_eq True by simp
    then show False by simp
  next
    case False
    have "pb_sum coeffs rho \<le> ?M" by (rule pb_sum_le_weight[OF rho01])
    with pos False show False by simp
  qed
qed

lemma semantic_to_cpr:
  assumes "\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow> models CC rho \<longrightarrow> satisfies C rho"
    and "snd C \<ge> (1::nat)"
  shows "cpr_derives CC C"
  by (rule cpr_derives.rup[OF implies01_unsat_neg[OF assms]])

lemma cpr_derives_iff_semantic:
  assumes "snd C \<ge> (1::nat)"
  shows "cpr_derives CC C \<longleftrightarrow>
    (\<forall>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<longrightarrow> models CC rho \<longrightarrow> satisfies C rho)"
  using cpr_sound semantic_to_cpr[OF _ assms] by blast

subsection \<open>Reification semantics\<close>

text \<open>In any 0/1 model of a reification pair, the gate literal carries exactly the
  truth value of the reified body — the semantic core of every RUP argument in the
  paper.\<close>

lemma reification_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (reification r coeffs A) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> pb_sum coeffs rho \<ge> A"
proof
  assume out: "eval_lit r rho = 1"
  have fwd: "satisfies (reif_fwd r coeffs A) rho"
    using m by (simp add: models_def reification_def)
  have negr: "eval_lit (lit_neg r) rho = 0"
    using eval_lit_neg_conv[OF rho01, of r] out by simp
  show "pb_sum coeffs rho \<ge> A"
    using fwd by (simp add: reif_fwd_def satisfies_def negr)
next
  assume body: "pb_sum coeffs rho \<ge> A"
  let ?M = "sum_list (map fst coeffs)"
  let ?neg = "map (\<lambda>(a, l). (a, lit_neg l)) coeffs"
  have bwd: "satisfies (reif_bwd r coeffs A) rho"
    using m by (simp add: models_def reification_def)
  have bwd': "(?M + 1 - A) * eval_lit r rho + pb_sum ?neg rho \<ge> ?M + 1 - A"
    using bwd by (simp add: reif_bwd_def satisfies_def Let_def)
  have sum_eq: "pb_sum coeffs rho + pb_sum ?neg rho = ?M"
    by (rule pb_sum_add_negated_gen[OF rho01])
  show "eval_lit r rho = 1"
  proof (rule ccontr)
    assume "eval_lit r rho \<noteq> 1"
    with eval_lit_01[OF rho01, of r] have r0: "eval_lit r rho = 0" by auto
    have negsum: "pb_sum ?neg rho \<ge> ?M + 1 - A"
      using bwd' by (simp add: r0)
    have pos_le: "pb_sum coeffs rho \<le> ?M"
      using sum_eq by linarith
    show False
    proof (cases "A \<le> ?M")
      case True
      have "A + (?M + 1 - A) \<le> pb_sum coeffs rho + pb_sum ?neg rho"
        using body negsum by (rule add_mono)
      also have "... = ?M" by (rule sum_eq)
      finally show False using True by simp
    next
      case False
      then show False using body pos_le by simp
    qed
  qed
qed

subsection \<open>Binary cost values\<close>

text \<open>The numeric value carried by a block of cost bits in an assignment.
  @{text cb} selects the bit variables (e.g. @{const CostBit} or
  @{const PrimedCostBit}).\<close>

definition bits_val :: "nat \<Rightarrow> (nat \<Rightarrow> 'w) \<Rightarrow> ('w \<Rightarrow> nat) \<Rightarrow> nat" where
  "bits_val k cb rho \<equiv> \<Sum>i<k. 2^i * rho (cb i)"

lemma bits_val_Suc: "bits_val (Suc k) cb rho = bits_val k cb rho + 2^k * rho (cb k)"
  by (simp add: bits_val_def)

lemma pb_sum_bits_val:
  "pb_sum (map (\<lambda>i. (2^i, Pos (cb i))) [0..<k]) rho = bits_val k cb rho"
proof (induction k)
  case 0
  then show ?case by (simp add: bits_val_def)
next
  case (Suc k)
  have "pb_sum (map (\<lambda>i. (2^i, Pos (cb i))) [0..<Suc k]) rho
      = pb_sum (map (\<lambda>i. (2^i, Pos (cb i))) [0..<k]) rho + 2^k * rho (cb k)"
    by (simp add: pb_sum_append eval_lit_def)
  then show ?case using Suc.IH by (simp add: bits_val_Suc)
qed

lemma bits_val_lt:
  assumes "\<forall>i. rho (cb i) = 0 \<or> rho (cb i) = 1"
  shows "bits_val k cb rho < 2^k"
proof (induction k)
  case 0
  then show ?case by (simp add: bits_val_def)
next
  case (Suc k)
  have "rho (cb k) \<le> 1" using assms[rule_format, of k] by auto
  then have bnd: "2^k * rho (cb k) \<le> 2^k" by simp
  have "bits_val (Suc k) cb rho < 2^k + 2^k"
    unfolding bits_val_Suc by (rule add_less_le_mono[OF Suc.IH bnd])
  then show ?case by simp
qed

lemma bits_val_eq_of_binary:
  assumes "\<forall>i < k. rho (cb i) = (c div 2^i) mod 2"
  shows "bits_val k cb rho = c mod 2^k"
  using assms
proof (induction k)
  case 0
  then show ?case by (simp add: bits_val_def)
next
  case (Suc k)
  have IH: "bits_val k cb rho = c mod 2^k" using Suc.IH Suc.prems by simp
  have bk: "rho (cb k) = (c div 2^k) mod 2" using Suc.prems by simp
  have "bits_val (Suc k) cb rho = c mod 2^k + 2^k * ((c div 2^k) mod 2)"
    by (simp add: bits_val_Suc IH bk)
  also have "... = c mod 2^(Suc k)"
    by (metis add.commute mod_mult2_eq mult.commute power_Suc)
  finally show ?case .
qed

lemma pb_sum_neg_bits_val:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
  shows "pb_sum (map (\<lambda>i. (2^i, Neg (cb i))) [0..<k]) rho
       = (2^k - 1) - bits_val k cb rho"
proof -
  let ?pos = "map (\<lambda>i. (2^i, Pos (cb i))) [0..<k]"
  let ?neg = "map (\<lambda>i. (2^i, Neg (cb i))) [0..<k]"
  have neg_eq: "map (\<lambda>(a, l). (a, lit_neg l)) ?pos = ?neg"
    by (simp add: lit_neg_def)
  have fst_eq: "map fst ?pos = map ((^) 2) [0..<k]"
    by simp
  have sum01: "pb_sum ?pos rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?pos) rho
      = sum_list (map fst ?pos)"
    by (rule pb_sum_add_negated_gen[OF rho01])
  have key: "bits_val k cb rho + pb_sum ?neg rho = 2^k - 1"
    using sum01 unfolding neg_eq fst_eq pb_sum_bits_val sum_list_exp by simp
  then show ?thesis by linarith
qed

text \<open>Semantics of a threshold gate over a block of cost bits, and of the encoding
  reifications (4) and (5).\<close>

lemma cost_threshold_gate_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (reification r (map (\<lambda>i. (2^i, Pos (cb i))) [0..<k]) A) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> bits_val k cb rho \<ge> A"
  using reification_forces[OF rho01 m] by (simp add: pb_sum_bits_val)

lemma encode_cost_ge_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_cost_ge k) rho"
  shows "rho (ReifCostGe k) = 1 \<longleftrightarrow> bits_val (bits_needed k) CostBit rho \<ge> k"
proof -
  have "eval_lit (Pos (ReifCostGe k)) rho = 1 \<longleftrightarrow> bits_val (bits_needed k) CostBit rho \<ge> k"
    using m unfolding encode_cost_ge_def
    by (intro cost_threshold_gate_forces[OF rho01]) simp
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma encode_cost_ge_primed_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_cost_ge_primed k) rho"
  shows "rho (ReifPrimedCostGe k) = 1 \<longleftrightarrow> bits_val (bits_needed k) PrimedCostBit rho \<ge> k"
proof -
  have "eval_lit (Pos (ReifPrimedCostGe k)) rho = 1
      \<longleftrightarrow> bits_val (bits_needed k) PrimedCostBit rho \<ge> k"
    using m unfolding encode_cost_ge_primed_def
    by (intro cost_threshold_gate_forces[OF rho01]) simp
  then show ?thesis by (simp add: eval_lit_def)
qed

lemma models_mono:
  "models CC rho \<Longrightarrow> DD \<subseteq> CC \<Longrightarrow> models DD rho"
  unfolding models_def by blast

subsection \<open>Semantics of the transition encoding gates\<close>

text \<open>Equation (3): the three-gate circuit for @{text "\<Delta>c=k"} pins
  @{const ReifDeltaCost} to the truth of @{text "c' = c + k"}.\<close>

lemma encode_delta_cost_lower_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_delta_cost k nb) rho"
  shows "rho (ReifDeltaCostLower k) = 1
       \<longleftrightarrow> bits_val nb PrimedCostBit rho \<ge> bits_val nb CostBit rho + k"
proof -
  let ?c = "bits_val nb CostBit rho"
  let ?c' = "bits_val nb PrimedCostBit rho"
  let ?M = "(2::nat)^nb - 1"
  have c_le: "?c \<le> ?M"
    using bits_val_lt[of rho CostBit nb] rho01 by fastforce
  have mlow: "models (reification (Pos (ReifDeltaCostLower k))
      (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<nb]
       @ map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<nb]) (k + ?M)) rho"
    by (rule models_mono[OF m]) (auto simp: encode_delta_cost_def Let_def)
  have sum_eq: "pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<nb]
       @ map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<nb]) rho = ?c' + (?M - ?c)"
    by (simp add: pb_sum_append pb_sum_bits_val pb_sum_neg_bits_val[OF rho01])
  have "eval_lit (Pos (ReifDeltaCostLower k)) rho = 1 \<longleftrightarrow> ?c' + (?M - ?c) \<ge> k + ?M"
    using reification_forces[OF rho01 mlow] by (simp add: sum_eq)
  moreover have "?c' + (?M - ?c) \<ge> k + ?M \<longleftrightarrow> ?c' \<ge> ?c + k"
    using c_le by linarith
  ultimately show ?thesis by (simp add: eval_lit_def)
qed

lemma encode_delta_cost_upper_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_delta_cost k nb) rho"
  shows "rho (ReifDeltaCostUpper k) = 1
       \<longleftrightarrow> bits_val nb PrimedCostBit rho \<le> bits_val nb CostBit rho + k"
proof -
  let ?c = "bits_val nb CostBit rho"
  let ?c' = "bits_val nb PrimedCostBit rho"
  let ?M = "(2::nat)^nb - 1"
  have c'_le: "?c' \<le> ?M"
    using bits_val_lt[of rho PrimedCostBit nb] rho01 by fastforce
  have mup: "models (reification (Pos (ReifDeltaCostUpper k))
      (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<nb]
       @ map (\<lambda>i. (2^i, Neg (PrimedCostBit i))) [0..<nb]) (?M - k)) rho"
    by (rule models_mono[OF m]) (auto simp: encode_delta_cost_def Let_def)
  have sum_eq: "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<nb]
       @ map (\<lambda>i. (2^i, Neg (PrimedCostBit i))) [0..<nb]) rho = ?c + (?M - ?c')"
    by (simp add: pb_sum_append pb_sum_bits_val pb_sum_neg_bits_val[OF rho01])
  have "eval_lit (Pos (ReifDeltaCostUpper k)) rho = 1 \<longleftrightarrow> ?c + (?M - ?c') \<ge> ?M - k"
    using reification_forces[OF rho01 mup] by (simp add: sum_eq)
  moreover have "?c + (?M - ?c') \<ge> ?M - k \<longleftrightarrow> ?c' \<le> ?c + k"
    using c'_le by linarith
  ultimately show ?thesis by (simp add: eval_lit_def)
qed

lemma encode_delta_cost_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_delta_cost k nb) rho"
  shows "rho (ReifDeltaCost k) = 1
       \<longleftrightarrow> bits_val nb PrimedCostBit rho = bits_val nb CostBit rho + k"
proof -
  let ?L = "ReifDeltaCostLower k"
  let ?U = "ReifDeltaCostUpper k"
  have mdelta: "models (reification (Pos (ReifDeltaCost k))
      [(1, Pos ?L), (1, Pos ?U)] 2) rho"
    by (rule models_mono[OF m]) (auto simp: encode_delta_cost_def Let_def)
  have L_le: "rho ?L \<le> 1" and U_le: "rho ?U \<le> 1"
    using rho01[rule_format, of ?L] rho01[rule_format, of ?U] by auto
  have "eval_lit (Pos (ReifDeltaCost k)) rho = 1 \<longleftrightarrow> rho ?L + rho ?U \<ge> 2"
    using reification_forces[OF rho01 mdelta] by (simp add: eval_lit_def)
  moreover have "rho ?L + rho ?U \<ge> 2 \<longleftrightarrow> rho ?L = 1 \<and> rho ?U = 1"
    using L_le U_le by linarith
  ultimately have "rho (ReifDeltaCost k) = 1 \<longleftrightarrow> rho ?L = 1 \<and> rho ?U = 1"
    by (simp add: eval_lit_def)
  then show ?thesis
    using encode_delta_cost_lower_forces[OF rho01 m]
      encode_delta_cost_upper_forces[OF rho01 m]
    by auto
qed

text \<open>Equation (6): the equality gate @{const ReifEq} pins the truth of
  @{text "v = v'"}.\<close>

lemma encode_eq_var_geq_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_eq_var v) rho"
  shows "rho (ReifGeq (Original v)) = 1
       \<longleftrightarrow> rho (StateVar (Primed v)) \<le> rho (StateVar (Original v))"
proof -
  let ?x = "rho (StateVar (Original v))"
  let ?y = "rho (StateVar (Primed v))"
  have mg: "models (reification (Pos (ReifGeq (Original v)))
      [(1, Pos (StateVar (Original v))), (1, Neg (StateVar (Primed v)))] 1) rho"
    by (rule models_mono[OF m]) (auto simp: encode_eq_var_def)
  have y_le: "?y \<le> 1" using rho01[rule_format, of "StateVar (Primed v)"] by auto
  have "eval_lit (Pos (ReifGeq (Original v))) rho = 1 \<longleftrightarrow> ?x + (1 - ?y) \<ge> 1"
    using reification_forces[OF rho01 mg] by (simp add: eval_lit_def)
  moreover have "?x + (1 - ?y) \<ge> 1 \<longleftrightarrow> ?y \<le> ?x"
    using y_le rho01[rule_format, of "StateVar (Original v)"] by auto
  ultimately show ?thesis by (simp add: eval_lit_def)
qed

lemma encode_eq_var_leq_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_eq_var v) rho"
  shows "rho (ReifLeq (Original v)) = 1
       \<longleftrightarrow> rho (StateVar (Original v)) \<le> rho (StateVar (Primed v))"
proof -
  let ?x = "rho (StateVar (Original v))"
  let ?y = "rho (StateVar (Primed v))"
  have ml: "models (reification (Pos (ReifLeq (Original v)))
      [(1, Neg (StateVar (Original v))), (1, Pos (StateVar (Primed v)))] 1) rho"
    by (rule models_mono[OF m]) (auto simp: encode_eq_var_def)
  have x_le: "?x \<le> 1" using rho01[rule_format, of "StateVar (Original v)"] by auto
  have "eval_lit (Pos (ReifLeq (Original v))) rho = 1 \<longleftrightarrow> (1 - ?x) + ?y \<ge> 1"
    using reification_forces[OF rho01 ml] by (simp add: eval_lit_def)
  moreover have "(1 - ?x) + ?y \<ge> 1 \<longleftrightarrow> ?x \<le> ?y"
    using x_le rho01[rule_format, of "StateVar (Primed v)"] by auto
  ultimately show ?thesis by (simp add: eval_lit_def)
qed

lemma encode_eq_var_forces:
  assumes rho01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and m: "models (encode_eq_var v) rho"
  shows "rho (ReifEq (Original v)) = 1
       \<longleftrightarrow> rho (StateVar (Original v)) = rho (StateVar (Primed v))"
proof -
  let ?L = "ReifLeq (Original v)"
  let ?G = "ReifGeq (Original v)"
  have meq: "models (reification (Pos (ReifEq (Original v)))
      [(1, Pos ?L), (1, Pos ?G)] 2) rho"
    by (rule models_mono[OF m]) (auto simp: encode_eq_var_def)
  have L_le: "rho ?L \<le> 1" and G_le: "rho ?G \<le> 1"
    using rho01[rule_format, of ?L] rho01[rule_format, of ?G] by auto
  have "eval_lit (Pos (ReifEq (Original v))) rho = 1 \<longleftrightarrow> rho ?L + rho ?G \<ge> 2"
    using reification_forces[OF rho01 meq] by (simp add: eval_lit_def)
  moreover have "rho ?L + rho ?G \<ge> 2 \<longleftrightarrow> rho ?L = 1 \<and> rho ?G = 1"
    using L_le G_le by linarith
  ultimately have "rho (ReifEq (Original v)) = 1 \<longleftrightarrow> rho ?L = 1 \<and> rho ?G = 1"
    by (simp add: eval_lit_def)
  then show ?thesis
    using encode_eq_var_leq_forces[OF rho01 m] encode_eq_var_geq_forces[OF rho01 m]
    by auto
qed

text \<open>Pointwise sums of unit literals over a finite variable set.\<close>

lemma rho01_le_one:
  fixes rho :: "'w \<Rightarrow> nat"
  assumes "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "rho y \<le> 1"
  using assms[rule_format, of y] by auto

lemma pb_sum_unit_set_pos:
  assumes "finite S"
  shows "pb_sum (map (\<lambda>v. (1, Pos (f v))) (sorted_list_of_set S)) rho = (\<Sum>v\<in>S. rho (f v))"
  using pb_sum_unit_set[OF assms, of "\<lambda>v. Pos (f v)" rho]
  by (simp add: eval_lit_def)

lemma pb_sum_unit_set_neg:
  assumes "finite S"
  shows "pb_sum (map (\<lambda>v. (1, Neg (f v))) (sorted_list_of_set S)) rho = (\<Sum>v\<in>S. 1 - rho (f v))"
  using pb_sum_unit_set[OF assms, of "\<lambda>v. Neg (f v)" rho]
  by (simp add: eval_lit_def)

lemma sum_le_card:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite S" and "\<forall>v\<in>S. f v \<le> 1"
  shows "(\<Sum>v\<in>S. f v) \<le> card S"
proof -
  have "(\<Sum>v\<in>S. f v) \<le> (\<Sum>v\<in>S. 1)" using assms(2) by (intro sum_mono) auto
  then show ?thesis by simp
qed

lemma sum_eq_card_ones:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<forall>v\<in>S. f v = 1"
  shows "(\<Sum>v\<in>S. f v) = card S"
proof -
  have "(\<Sum>v\<in>S. f v) = (\<Sum>v\<in>S. 1)" using assms by (intro sum.cong) auto
  then show ?thesis by simp
qed

lemma sum_rho_all_one:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and fin: "finite S"
    and total: "(\<Sum>v\<in>S. rho (f v)) \<ge> card S"
  shows "\<forall>v\<in>S. rho (f v) = 1"
proof -
  have bnd: "\<forall>v\<in>S. rho (f v) \<le> 1"
    by (intro ballI rho01_le_one[OF rho01])
  show ?thesis by (rule sum_units_all_one[OF fin total bnd])
qed

lemma sum_rho_all_zero:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and fin: "finite S"
    and total: "(\<Sum>v\<in>S. 1 - rho (f v)) \<ge> card S"
  shows "\<forall>v\<in>S. rho (f v) = 0"
proof -
  have "\<forall>v\<in>S. 1 - rho (f v) = 1"
    by (rule sum_units_all_one[OF fin total]) auto
  then show ?thesis using rho01 by (metis diff_self_eq_0 zero_neq_one)
qed

lemma sum_rho_le_card:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and fin: "finite S"
  shows "(\<Sum>v\<in>S. rho (f v)) \<le> card S"
  by (rule sum_le_card[OF fin]) (intro ballI rho01_le_one[OF rho01])

lemma sum_one_minus_le_card:
  fixes rho :: "'w \<Rightarrow> nat"
  assumes fin: "finite S"
  shows "(\<Sum>v\<in>S. 1 - rho (f v)) \<le> card S"
  by (rule sum_le_card[OF fin]) auto

subsection \<open>Semantics of the initial state, goal, and action selection gates\<close>

text \<open>Equation (1): @{const ReifI} is true iff the state variables encode exactly
  the initial state on @{text "vars \<Pi>"}.\<close>

lemma encode_init_forces:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (encode_init \<Pi>) rho"
    and fin: "finite (vars \<Pi>)"
    and init_sub: "init \<Pi> \<subseteq> vars \<Pi>"
  shows "rho ReifI = 1
       \<longleftrightarrow> (\<forall>v \<in> vars \<Pi>. rho (StateVar v) = (if v \<in> init \<Pi> then 1 else 0))"
proof -
  let ?I = "init \<Pi>"
  let ?V = "vars \<Pi>"
  let ?body = "state_lits ?I @ neg_state_lits (?V - ?I)"
  have fin_I: "finite ?I" and fin_VI: "finite (?V - ?I)"
    using fin init_sub by (auto intro: finite_subset)
  have m': "models (reification (Pos ReifI) ?body (card ?V)) rho"
    using m by (simp add: encode_init_def Let_def)
  have s_pos: "pb_sum (state_lits ?I) rho = (\<Sum>v\<in>?I. rho (StateVar v))"
    unfolding state_lits_def by (rule pb_sum_unit_set_pos[OF fin_I])
  have s_neg: "pb_sum (neg_state_lits (?V - ?I)) rho = (\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v))"
    unfolding neg_state_lits_def by (rule pb_sum_unit_set_neg[OF fin_VI])
  have body_sum: "pb_sum ?body rho
      = (\<Sum>v\<in>?I. rho (StateVar v)) + (\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v))"
    by (simp add: pb_sum_append s_pos s_neg)
  have card_split: "card ?I + card (?V - ?I) = card ?V"
    using fin init_sub
    by (metis card_Diff_subset card_mono finite_subset le_add_diff_inverse)
  show ?thesis
  proof
    assume "rho ReifI = 1"
    then have "pb_sum ?body rho \<ge> card ?V"
      using reification_forces[OF rho01 m'] by (simp add: eval_lit_def)
    then have total: "(\<Sum>v\<in>?I. rho (StateVar v)) + (\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v))
        \<ge> card ?I + card (?V - ?I)"
      using body_sum card_split by simp
    have bnd1: "(\<Sum>v\<in>?I. rho (StateVar v)) \<le> card ?I"
      by (rule sum_rho_le_card[OF rho01 fin_I])
    have bnd2: "(\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v)) \<le> card (?V - ?I)"
      by (rule sum_one_minus_le_card[OF fin_VI])
    have t1: "(\<Sum>v\<in>?I. rho (StateVar v)) \<ge> card ?I"
      using total bnd1 bnd2 by linarith
    have t2: "(\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v)) \<ge> card (?V - ?I)"
      using total bnd1 bnd2 by linarith
    have ones: "\<forall>v\<in>?I. rho (StateVar v) = 1"
      by (rule sum_rho_all_one[OF rho01 fin_I t1])
    have zeros: "\<forall>v\<in>?V - ?I. rho (StateVar v) = 0"
      by (rule sum_rho_all_zero[OF rho01 fin_VI t2])
    show "\<forall>v \<in> ?V. rho (StateVar v) = (if v \<in> ?I then 1 else 0)"
      using ones zeros init_sub by auto
  next
    assume enc: "\<forall>v \<in> ?V. rho (StateVar v) = (if v \<in> ?I then 1 else 0)"
    have s1: "(\<Sum>v\<in>?I. rho (StateVar v)) = card ?I"
      using enc init_sub by (intro sum_eq_card_ones) auto
    have s2: "(\<Sum>v\<in>?V - ?I. 1 - rho (StateVar v)) = card (?V - ?I)"
      using enc by (intro sum_eq_card_ones) auto
    have "pb_sum ?body rho = card ?V"
      using body_sum s1 s2 card_split by simp
    then have "eval_lit (Pos ReifI) rho = 1"
      using reification_forces[OF rho01 m'] by simp
    then show "rho ReifI = 1" by (simp add: eval_lit_def)
  qed
qed

text \<open>Equation (2): @{const ReifG} is true iff all goal variables are true.\<close>

lemma encode_goal_forces:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (encode_goal \<Pi>) rho"
    and fin: "finite (goal \<Pi>)"
  shows "rho ReifG = 1 \<longleftrightarrow> (\<forall>v \<in> goal \<Pi>. rho (StateVar v) = 1)"
proof -
  let ?G = "goal \<Pi>"
  have m': "models (reification (Pos ReifG) (state_lits ?G) (card ?G)) rho"
    using m by (simp add: encode_goal_def Let_def)
  have body_sum: "pb_sum (state_lits ?G) rho = (\<Sum>v\<in>?G. rho (StateVar v))"
    unfolding state_lits_def by (rule pb_sum_unit_set_pos[OF fin])
  show ?thesis
  proof
    assume "rho ReifG = 1"
    then have "(\<Sum>v\<in>?G. rho (StateVar v)) \<ge> card ?G"
      using reification_forces[OF rho01 m'] body_sum by (simp add: eval_lit_def)
    then show "\<forall>v \<in> ?G. rho (StateVar v) = 1"
      by (rule sum_rho_all_one[OF rho01 fin])
  next
    assume "\<forall>v \<in> ?G. rho (StateVar v) = 1"
    then have "(\<Sum>v\<in>?G. rho (StateVar v)) = card ?G"
      by (intro sum_eq_card_ones) auto
    then have "eval_lit (Pos ReifG) rho = 1"
      using reification_forces[OF rho01 m'] body_sum by simp
    then show "rho ReifG = 1" by (simp add: eval_lit_def)
  qed
qed

text \<open>Equation (8): if @{const ReifT} is true, some action gate is selected, and
  conversely a selected action gate forces @{const ReifT}.\<close>

lemma action_selection_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (action_selection_reif rs) rho"
  shows "rho ReifT = 1 \<longleftrightarrow> (\<exists>r \<in> set rs. eval_lit r rho = 1)"
proof -
  have m': "models (reification (Pos ReifT) (map (\<lambda>r. (1, r)) rs) 1) rho"
    using m by (simp add: action_selection_reif_def)
  have iff1: "eval_lit (Pos ReifT) rho = 1 \<longleftrightarrow> pb_sum (map (\<lambda>r. (1, r)) rs) rho \<ge> 1"
    by (rule reification_forces[OF rho01 m'])
  show ?thesis
  proof
    assume "rho ReifT = 1"
    then have "pb_sum (map (\<lambda>r. (1, r)) rs) rho \<ge> 1"
      using iff1 by (simp add: eval_lit_def)
    then have "\<exists>(a, l) \<in> set (map (\<lambda>r. (1, r)) rs). a * eval_lit l rho \<ge> 1"
      by (rule pb_sum_pos_ex)
    then obtain a l where al_in: "(a, l) \<in> set (map (\<lambda>r. (1, r)) rs)"
      and al_pos: "a * eval_lit l rho \<ge> 1" by auto
    have r_in: "l \<in> set rs" and a1: "a = 1" using al_in by auto
    have "eval_lit l rho \<ge> 1" using al_pos a1 by simp
    then have "eval_lit l rho = 1"
      using eval_lit_le_one[OF rho01, of l] by simp
    then show "\<exists>r \<in> set rs. eval_lit r rho = 1" using r_in by blast
  next
    assume "\<exists>r \<in> set rs. eval_lit r rho = 1"
    then obtain r where r_in: "r \<in> set rs" and r1: "eval_lit r rho = 1" by blast
    have "pb_sum (map (\<lambda>r. (1, r)) rs) rho \<ge> 1"
      using r_in r1
    proof (induction rs)
      case Nil
      then show ?case by simp
    next
      case (Cons q rs)
      then show ?case by (cases "r = q") auto
    qed
    then have "eval_lit (Pos ReifT) rho = 1" using iff1 by simp
    then show "rho ReifT = 1" by (simp add: eval_lit_def)
  qed
qed

subsection \<open>Semantics of the action constraint (equation (7))\<close>

text \<open>A selected action gate forces all conjuncts of the action constraint:
  the cost-delta gate, the preconditions on the unprimed side, the effects on
  the primed side, the frame gates, and the negated cost bound.  Variables in
  @{text "add a \<inter> del a"} are unconstrained by the encoding (their two literals
  always contribute exactly 1), which matches the relaxation discussed in the
  faithfulness assessment.\<close>

lemma action_constraint_extract:
  fixes a :: "'v::linorder action" and V :: "'v set" and rho :: "'v var pvar \<Rightarrow> nat"
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and sat: "satisfies (action_constraint r a V B) rho"
    and out: "eval_lit r rho = 1"
    and finV: "finite V"
    and pre_sub: "pre a \<subseteq> V" and add_sub: "add a \<subseteq> V" and del_sub: "del a \<subseteq> V"
  shows "rho (ReifDeltaCost (cost a)) = 1
       \<and> rho (ReifPrimedCostGe B) = 0
       \<and> (\<forall>v \<in> pre a. rho (StateVar (Original v)) = 1)
       \<and> (\<forall>v \<in> add a - del a. rho (StateVar (Primed v)) = 1)
       \<and> (\<forall>v \<in> del a - add a. rho (StateVar (Primed v)) = 0)
       \<and> (\<forall>v \<in> V - evars a. rho (ReifEq (Original v)) = 1)"
proof -
  have fin_pre: "finite (pre a)" and fin_add: "finite (add a)"
    and fin_del: "finite (del a)" and fin_frame: "finite (V - evars a)"
    using finV pre_sub add_sub del_sub by (auto intro: finite_subset)
  have fin_amd: "finite (add a - del a)" and fin_dma: "finite (del a - add a)"
    and fin_int: "finite (add a \<inter> del a)"
    using fin_add fin_del by auto
  define A where "A = 2 + card (pre a) + card V"
  define D where "D = rho (ReifDeltaCost (cost a))"
  define Bv where "Bv = rho (ReifPrimedCostGe B)"
  define Spre where "Spre = (\<Sum>v\<in>pre a. rho (StateVar (Original v)))"
  define Sadd where "Sadd = (\<Sum>v\<in>add a. rho (StateVar (Primed v)))"
  define Sdel where "Sdel = (\<Sum>v\<in>del a. 1 - rho (StateVar (Primed v)))"
  define Sfr where "Sfr = (\<Sum>v\<in>V - evars a. rho (ReifEq (Original v)))"
  have negr: "eval_lit (lit_neg r) rho = 0"
    using eval_lit_neg_conv[OF rho01, of r] out by simp
  have e_pre: "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre a))) rho = Spre"
    unfolding Spre_def by (rule pb_sum_unit_set_pos[OF fin_pre])
  have e_add: "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add a))) rho = Sadd"
    unfolding Sadd_def by (rule pb_sum_unit_set_pos[OF fin_add])
  have e_del: "pb_sum (map (\<lambda>v. (1, Neg (StateVar (Primed v)))) (sorted_list_of_set (del a))) rho = Sdel"
    unfolding Sdel_def by (rule pb_sum_unit_set_neg[OF fin_del])
  have e_fr: "pb_sum (map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars a))) rho = Sfr"
    unfolding Sfr_def by (rule pb_sum_unit_set_pos[OF fin_frame])
  have snd_ac: "snd (action_constraint r a V B) = A"
    unfolding action_constraint_def Let_def A_def by simp
  have ge0: "pb_sum (fst (action_constraint r a V B)) rho \<ge> A"
    using sat snd_ac unfolding satisfies_def by (simp add: split_beta)
  have lhs_eq: "pb_sum (fst (action_constraint r a V B)) rho
      = A * eval_lit (lit_neg r) rho + D + Spre + Sadd + Sdel + Sfr + (1 - Bv)"
    unfolding action_constraint_def fst_conv Let_def
    by (simp add: pb_sum_append A_def D_def Bv_def eval_lit_def
      e_pre[symmetric] e_add[symmetric] e_del[symmetric] e_fr[symmetric] add_ac)
  have main_ge: "D + Spre + Sadd + Sdel + Sfr + (1 - Bv) \<ge> A"
    using ge0 lhs_eq negr by simp
  \<comment> \<open>Bounds for each component.\<close>
  have D_le: "D \<le> 1" unfolding D_def by (rule rho01_le_one[OF rho01])
  have Bv_le: "Bv \<le> 1" unfolding Bv_def by (rule rho01_le_one[OF rho01])
  have Spre_le: "Spre \<le> card (pre a)"
    unfolding Spre_def by (rule sum_rho_le_card[OF rho01 fin_pre])
  have Sfr_le: "Sfr \<le> card (V - evars a)"
    unfolding Sfr_def by (rule sum_rho_le_card[OF rho01 fin_frame])
  \<comment> \<open>Split the add/del sums along the overlap.\<close>
  have Sadd_split: "Sadd = (\<Sum>v\<in>add a - del a. rho (StateVar (Primed v)))
       + (\<Sum>v\<in>add a \<inter> del a. rho (StateVar (Primed v)))"
  proof -
    have "(\<Sum>v\<in>(add a - del a) \<union> (add a \<inter> del a). rho (StateVar (Primed v)))
        = (\<Sum>v\<in>add a - del a. rho (StateVar (Primed v)))
        + (\<Sum>v\<in>add a \<inter> del a. rho (StateVar (Primed v)))"
      by (rule sum.union_disjoint) (use fin_amd fin_int in auto)
    moreover have "(add a - del a) \<union> (add a \<inter> del a) = add a" by auto
    ultimately show ?thesis unfolding Sadd_def by simp
  qed
  have Sdel_split: "Sdel = (\<Sum>v\<in>del a - add a. 1 - rho (StateVar (Primed v)))
       + (\<Sum>v\<in>add a \<inter> del a. 1 - rho (StateVar (Primed v)))"
  proof -
    have "(\<Sum>v\<in>(del a - add a) \<union> (add a \<inter> del a). 1 - rho (StateVar (Primed v)))
        = (\<Sum>v\<in>del a - add a. 1 - rho (StateVar (Primed v)))
        + (\<Sum>v\<in>add a \<inter> del a. 1 - rho (StateVar (Primed v)))"
      by (rule sum.union_disjoint) (use fin_dma fin_int in auto)
    moreover have "(del a - add a) \<union> (add a \<inter> del a) = del a" by auto
    ultimately show ?thesis unfolding Sdel_def by simp
  qed
  have pair_sum: "(\<Sum>v\<in>add a \<inter> del a. rho (StateVar (Primed v)))
       + (\<Sum>v\<in>add a \<inter> del a. 1 - rho (StateVar (Primed v))) = card (add a \<inter> del a)"
  proof -
    have each: "\<forall>v\<in>add a \<inter> del a.
        rho (StateVar (Primed v)) + (1 - rho (StateVar (Primed v))) = 1"
    proof
      fix v assume "v \<in> add a \<inter> del a"
      show "rho (StateVar (Primed v)) + (1 - rho (StateVar (Primed v))) = 1"
        using rho01_le_one[OF rho01, of "StateVar (Primed v)"] by linarith
    qed
    have "(\<Sum>v\<in>add a \<inter> del a. rho (StateVar (Primed v)))
       + (\<Sum>v\<in>add a \<inter> del a. 1 - rho (StateVar (Primed v)))
       = (\<Sum>v\<in>add a \<inter> del a. rho (StateVar (Primed v)) + (1 - rho (StateVar (Primed v))))"
      by (rule sum.distrib[symmetric])
    also have "... = card (add a \<inter> del a)"
      using each by (rule sum_eq_card_ones)
    finally show ?thesis .
  qed
  have amd_le: "(\<Sum>v\<in>add a - del a. rho (StateVar (Primed v))) \<le> card (add a - del a)"
    by (rule sum_rho_le_card[OF rho01 fin_amd])
  have dma_le: "(\<Sum>v\<in>del a - add a. 1 - rho (StateVar (Primed v))) \<le> card (del a - add a)"
    by (rule sum_one_minus_le_card[OF fin_dma])
  \<comment> \<open>Cardinality bookkeeping.\<close>
  have evars_sub: "evars a \<subseteq> V" using add_sub del_sub by (auto simp: evars_def)
  have fin_evars: "finite (evars a)" using fin_add fin_del by (simp add: evars_def)
  have card_evars: "card (add a - del a) + card (del a - add a) + card (add a \<inter> del a)
      = card (evars a)"
  proof -
    have d1: "(add a - del a) \<inter> (add a \<inter> del a) = {}" by auto
    have u1: "(add a - del a) \<union> (add a \<inter> del a) = add a" by auto
    have c1: "card (add a - del a) + card (add a \<inter> del a) = card (add a)"
      using card_Un_disjoint[OF fin_amd fin_int d1] u1 by simp
    have d2: "add a \<inter> (del a - add a) = {}" by auto
    have u2: "add a \<union> (del a - add a) = evars a" by (auto simp: evars_def)
    have c2: "card (add a) + card (del a - add a) = card (evars a)"
      using card_Un_disjoint[OF fin_add fin_dma d2] u2 by simp
    show ?thesis using c1 c2 by linarith
  qed
  have card_V_split: "card (evars a) + card (V - evars a) = card V"
    using finV evars_sub
    by (metis card_Diff_subset card_mono finite_subset le_add_diff_inverse)
  \<comment> \<open>All inequalities are tight.\<close>
  have t_D: "D = 1"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  have t_B: "Bv = 0"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  have t_pre: "Spre \<ge> card (pre a)"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  have t_amd: "(\<Sum>v\<in>add a - del a. rho (StateVar (Primed v))) \<ge> card (add a - del a)"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  have t_dma: "(\<Sum>v\<in>del a - add a. 1 - rho (StateVar (Primed v))) \<ge> card (del a - add a)"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  have t_fr: "Sfr \<ge> card (V - evars a)"
    using main_ge D_le Bv_le Spre_le Sfr_le Sadd_split Sdel_split pair_sum
      amd_le dma_le card_evars card_V_split A_def by linarith
  \<comment> \<open>Pointwise consequences.\<close>
  have pre_ones: "\<forall>v \<in> pre a. rho (StateVar (Original v)) = 1"
    using t_pre unfolding Spre_def by (rule sum_rho_all_one[OF rho01 fin_pre])
  have add_ones: "\<forall>v \<in> add a - del a. rho (StateVar (Primed v)) = 1"
    using t_amd by (rule sum_rho_all_one[OF rho01 fin_amd])
  have del_zeros: "\<forall>v \<in> del a - add a. rho (StateVar (Primed v)) = 0"
    using t_dma by (rule sum_rho_all_zero[OF rho01 fin_dma])
  have fr_ones: "\<forall>v \<in> V - evars a. rho (ReifEq (Original v)) = 1"
    using t_fr unfolding Sfr_def by (rule sum_rho_all_one[OF rho01 fin_frame])
  show ?thesis
    using t_D t_B pre_ones add_ones del_zeros fr_ones
    unfolding D_def Bv_def by blast
qed

subsection \<open>Task embedding into an extended variable type\<close>

text \<open>The certificate format restricts circuit gate names to @{term "ReifCert x"}
  with @{text "x :: 'v"} — at most as many names as the task has variables.  The
  A*, PDB and hmax circuits need unboundedly many gates.  Since Theorem 1 is
  polymorphic in the variable type, we instantiate it at the sum type
  @{text "'v + 'g"}: the task lives in the @{const Inl} part, and certificate
  gate names @{term "ReifCert (Inr i)"} are guaranteed fresh.\<close>

instantiation sum :: (linorder, linorder) linorder
begin

definition less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  "less_eq_sum x y \<equiv> case (x, y) of
    (Inl a, Inl b) \<Rightarrow> a \<le> b
  | (Inl _, Inr _) \<Rightarrow> True
  | (Inr _, Inl _) \<Rightarrow> False
  | (Inr a, Inr b) \<Rightarrow> a \<le> b"

definition less_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  "less_sum x y \<equiv> x \<le> y \<and> \<not> y \<le> x"

instance
  by standard (auto simp: less_eq_sum_def less_sum_def split: sum.splits)

end

definition embed_act :: "'v action \<Rightarrow> ('v + 'g) action" where
  "embed_act a \<equiv> \<lparr> pre = Inl ` pre a, add = Inl ` add a, del = Inl ` del a,
                   cost = cost a \<rparr>"

definition embed_task :: "'v strips_task \<Rightarrow> ('v + 'g) strips_task" where
  "embed_task \<Pi> \<equiv> \<lparr> vars = Inl ` vars \<Pi>, acts = embed_act ` acts \<Pi>,
                    init = Inl ` init \<Pi>, goal = Inl ` goal \<Pi> \<rparr>"

lemma embed_act_applicable:
  "applicable (embed_act a) (Inl ` s) \<longleftrightarrow> applicable a s"
  by (simp add: applicable_def embed_act_def inj_image_subset_iff)

lemma embed_act_successor:
  "successor (embed_act a) (Inl ` s) = Inl ` successor a s"
  by (simp add: successor_def embed_act_def image_Un image_set_diff)

lemma embed_path:
  assumes "path (acts \<Pi>) s t \<pi>"
  shows "path (acts (embed_task \<Pi>)) (Inl ` s) (Inl ` t) (map embed_act \<pi>)"
  using assms
proof (induction rule: path.induct)
  case (path_nil s)
  show ?case by (simp add: path.path_nil)
next
  case (path_cons a s t \<pi>)
  then show ?case
    by (auto intro!: path.path_cons
        simp: embed_act_applicable embed_act_successor embed_task_def)
qed

lemma embed_plan_cost:
  "plan_cost (map embed_act \<pi>) = plan_cost \<pi>"
  by (simp add: plan_cost_def embed_act_def o_def)

lemma embed_is_plan_for:
  assumes "is_plan_for \<Pi> \<pi>"
  shows "is_plan_for (embed_task \<Pi>) (map embed_act \<pi>)"
proof -
  from assms obtain s where p: "path (acts \<Pi>) (init \<Pi>) s \<pi>"
    and g: "is_goal_state \<Pi> s"
    unfolding is_plan_for_def by blast
  have ip: "init (embed_task \<Pi>) = Inl ` init \<Pi>"
    by (simp add: embed_task_def)
  have "path (acts (embed_task \<Pi>)) (Inl ` init \<Pi>) (Inl ` s) (map embed_act \<pi>)"
    by (rule embed_path[OF p])
  moreover have "is_goal_state (embed_task \<Pi>) (Inl ` s)"
    using g by (auto simp: is_goal_state_def embed_task_def)
  ultimately show ?thesis unfolding is_plan_for_def ip by blast
qed

text \<open>Theorem 1 transported back to the original task: a valid certificate over
  the extended variable type bounds the cost of every plan of the original task.\<close>

theorem embedded_certificate_lower_bound:
  fixes \<Pi> :: "'v::linorder strips_task"
    and Cert :: "(('v + 'g::linorder)) certificate"
  assumes cert: "certificate_valid_cpr B (embed_task \<Pi>) Cert"
    and plan: "is_plan_for \<Pi> \<pi>"
  shows "plan_cost \<pi> \<ge> B"
proof -
  have "is_plan_for (embed_task \<Pi>) (map embed_act \<pi>)"
    by (rule embed_is_plan_for[OF plan])
  from theorem_1_from_cpr[OF cert this]
  show ?thesis by (simp add: embed_plan_cost)
qed

corollary embedded_certificate_optimality:
  fixes \<Pi> :: "'v::linorder strips_task"
    and Cert :: "(('v + 'g::linorder)) certificate"
  assumes cert: "certificate_valid_cpr B (embed_task \<Pi>) Cert"
    and plan: "is_plan_for \<Pi> \<pi>" and cost: "plan_cost \<pi> = B"
  shows "optimal_plan \<Pi> \<pi>"
  unfolding optimal_plan_def
  using plan cost embedded_certificate_lower_bound[OF cert] by auto

end
