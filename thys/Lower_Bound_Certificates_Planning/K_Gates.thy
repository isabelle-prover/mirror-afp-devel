section \<open>K-Gates\<close>

theory K_Gates
  imports Encoding_Semantics
begin

text \<open>The paper's placeholder variables @{text "K\<ge>l"} (equations (9)/(10)) reify
  the clipped cost condition @{text "cost \<ge> min{B, max{0, l}}"} with @{text "l \<in> \<int>"}.
  In the paper they are defined via the reification variables @{text "cost\<ge>k"} from
  the encoding family (4)/(5); since the certificate format keeps circuit gates
  disjoint from the encoding's reification variables, we inline that composition:
  a K-gate reifies the clipped threshold \<^emph>\<open>directly over the cost bits\<close>.  The
  primed copy of such a gate (under @{const primed_circuit}) then constrains
  @{const PrimedCostBit} — exactly the paper's @{text "K'\<ge>l"}.

  The paper proves its Lemmas 1 and 2 with the RED rule (empty witness).  RED with
  an empty witness concludes @{text C} from @{text "C \<union> {\<not>C} \<Turnstile> C"}, i.e. from
  semantic implication — which is subsumed by the semantic @{thm cpr_derives.rup}
  rule of the formal system, so no additional proof rule is needed.\<close>

subsection \<open>Clipping arithmetic\<close>

definition clip :: "nat \<Rightarrow> int \<Rightarrow> nat" where
  "clip B l \<equiv> min B (nat l)"

lemma clip_nonpos[simp]: "l \<le> 0 \<Longrightarrow> clip B l = 0"
  by (simp add: clip_def)

lemma clip_ge_B[simp]: "l \<ge> int B \<Longrightarrow> clip B l = B"
  by (simp add: clip_def min_def nat_le_eq_zle)

lemma clip_in_range[simp]: "0 \<le> l \<Longrightarrow> l \<le> int B \<Longrightarrow> clip B l = nat l"
proof -
  assume "0 \<le> l" and "l \<le> int B"
  then have "nat l \<le> B" by simp
  then show ?thesis by (simp add: clip_def min_def)
qed

lemma clip_le_B: "clip B l \<le> B"
  by (simp add: clip_def)

lemma clip_mono:
  assumes "j \<le> j'"
  shows "clip B j \<le> clip B j'"
proof -
  have "nat j \<le> nat j'" using assms by (rule nat_mono)
  then show ?thesis unfolding clip_def by (intro min.mono) auto
qed

lemma nat_add_int_le: "nat (l + int m) \<le> nat l + m"
  by (cases "l \<ge> 0") auto

lemma clip_add_le:
  "clip B (l + int m) \<le> clip B l + m"
proof (cases "nat l \<le> B")
  case True
  have "clip B (l + int m) \<le> nat (l + int m)" by (simp add: clip_def)
  also have "... \<le> nat l + m" by (rule nat_add_int_le)
  also have "... = clip B l + m" using True by (simp add: clip_def min_def)
  finally show ?thesis .
next
  case False
  have "clip B (l + int m) \<le> B" by (rule clip_le_B)
  also have "... \<le> clip B l + m" using False by (simp add: clip_def min_def)
  finally show ?thesis .
qed

subsection \<open>K-gates and their semantics\<close>

text \<open>The gate triple for a K-gate with name literal @{text r}: it reifies
  @{text "\<Sigma> 2^i\<sqdot>cᵢ \<ge> clip B l"} over the @{text "bits_needed B"}-bit cost block.
  All new cost bodies use this width so they stay aligned with the
  @{const encode_delta_cost} gates of the transition encoding.\<close>

definition k_gate_body :: "nat \<Rightarrow> (nat \<times> 'w pvar literal) list" where
  "k_gate_body B \<equiv> map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]"

definition k_gate :: "'w pvar literal \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
    'w pvar literal \<times> (nat \<times> 'w pvar literal) list \<times> nat" where
  "k_gate r B l \<equiv> (r, k_gate_body B, clip B l)"

lemma k_gate_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (reification r (k_gate_body B) (clip B l)) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B l"
  using cost_threshold_gate_forces[OF rho01 m[unfolded k_gate_body_def]] .

text \<open>Lemma 1 of the paper, semantically: if the cost bits witness the larger
  clipped threshold @{text "clip B (j + k)"}, they witness the smaller one
  @{text "clip B j"}.  At the gate level: a true K-gate for @{text "j + k"}
  forces the K-gate for @{text j}.\<close>

lemma k_gate_mono_semantic:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m_hi: "models (reification r_hi (k_gate_body B) (clip B (j + int k))) rho"
    and m_lo: "models (reification r_lo (k_gate_body B) (clip B j)) rho"
    and hi: "eval_lit r_hi rho = 1"
  shows "eval_lit r_lo rho = 1"
proof -
  have "bits_val (bits_needed B) CostBit rho \<ge> clip B (j + int k)"
    using k_gate_forces[OF rho01 m_hi] hi by simp
  moreover have "clip B j \<le> clip B (j + int k)"
    by (rule clip_mono) simp
  ultimately have "bits_val (bits_needed B) CostBit rho \<ge> clip B j"
    by simp
  then show ?thesis using k_gate_forces[OF rho01 m_lo] by simp
qed

text \<open>Lemma 2 of the paper, semantically: from @{text "cost \<ge> clip B l"} and
  @{text "\<Delta>c = m"} conclude @{text "cost' \<ge> clip B (l + m)"}.  The primed K-gate
  body is the @{const PrimedCostBit} block, which is what @{const primed_circuit}
  produces from a K-gate.\<close>

definition k_gate_body_primed :: "nat \<Rightarrow> (nat \<times> 'w pvar literal) list" where
  "k_gate_body_primed B \<equiv> map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]"

lemma k_gate_primed_forces:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and m: "models (reification r (k_gate_body_primed B) (clip B l)) rho"
  shows "eval_lit r rho = 1 \<longleftrightarrow> bits_val (bits_needed B) PrimedCostBit rho \<ge> clip B l"
  using cost_threshold_gate_forces[OF rho01 m[unfolded k_gate_body_primed_def]] .

lemma k_gate_step_semantic:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
    and mK: "models (reification rK (k_gate_body B) (clip B l)) rho"
    and mK': "models (reification rK' (k_gate_body_primed B) (clip B (l + int m))) rho"
    and mD: "models (encode_delta_cost m (bits_needed B)) rho"
    and K1: "eval_lit rK rho = 1"
    and D1: "rho (ReifDeltaCost m) = 1"
  shows "eval_lit rK' rho = 1"
proof -
  let ?c = "bits_val (bits_needed B) CostBit rho"
  let ?c' = "bits_val (bits_needed B) PrimedCostBit rho"
  have c_ge: "?c \<ge> clip B l"
    using k_gate_forces[OF rho01 mK] K1 by simp
  have c'_eq: "?c' = ?c + m"
    using encode_delta_cost_forces[OF rho01 mD] D1 by simp
  have "clip B (l + int m) \<le> clip B l + m"
    by (rule clip_add_le)
  also have "... \<le> ?c + m" using c_ge by simp
  also have "... = ?c'" using c'_eq by simp
  finally show ?thesis
    using k_gate_primed_forces[OF rho01 mK'] by simp
qed

text \<open>Bit-level form of the premise @{text "cost \<ge> clip B l"} as a PB constraint —
  used when a deduction-style hypothesis set assumes a clipped cost bound
  directly (the analogue of @{const cost_ge_constraint} for clipped thresholds).\<close>

definition clip_cost_constraint :: "nat \<Rightarrow> int \<Rightarrow> 'w pconstraint" where
  "clip_cost_constraint B l \<equiv> (k_gate_body B, clip B l)"

lemma clip_cost_constraint_sat:
  assumes rho01: "\<forall>x. rho x = 0 \<or> rho x = 1"
  shows "satisfies (clip_cost_constraint B l) rho
       \<longleftrightarrow> bits_val (bits_needed B) CostBit rho \<ge> clip B l"
  by (simp add: clip_cost_constraint_def k_gate_body_def satisfies_def
      pb_sum_bits_val)

end
