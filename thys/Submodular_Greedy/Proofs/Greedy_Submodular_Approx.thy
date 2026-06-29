theory Greedy_Submodular_Approx
  imports
    Greedy_Step_Spec
begin

text \<open>
  We first derive analytic bounds for the coefficient
  \<open>1 - (1 - 1/k)^k\<close> appearing in the Nemhauser–Wolsey approximation ratio.
  These bounds are later combined with the greedy gap recurrence to obtain
  the standard \<open>1 - 1/exp 1\<close> guarantee.
\<close>

text \<open>
  First, we relate the finite quantity \<open>(1 - 1/k)^k\<close> to the exponential
  function via a standard exponential inequality.
\<close>

lemma pow_one_minus_inv_le_exp_neg1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "(1 - 1 / real k) ^ k \<le> exp (-1 :: real)"
proof -
  have f1: "0 < k"
    using assms by auto
  have "1 \<le> real k"
    using assms one_of_nat_le_iff by blast
  then show ?thesis
    using f1 exp_ge_one_minus_x_over_n_power_n by presburger
qed

text \<open>
  As a corollary, we obtain a uniform lower bound
  \<open>1 - (1 - 1/k)^k \<ge> 1 - 1/exp 1\<close> for all \<open>k \<ge> 1\<close>.
\<close>

lemma coeff_ge_1_minus_inv_exp:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "1 - (1 - 1 / real k) ^ k \<ge> 1 - 1 / exp 1"
proof -
  from pow_one_minus_inv_le_exp_neg1[OF assms]
  have "(1 - 1 / real k) ^ k \<le> exp (-1 :: real)" .
  then have "1 - (1 - 1 / real k) ^ k \<ge> 1 - exp (-1 :: real)"
    by simp
  also have "exp (-1 :: real) = 1 / exp 1"
    by (simp add: exp_minus field_simps)
  finally show ?thesis .
qed


context Greedy_Setup
begin

section \<open>Greedy approximation for monotone submodular maximization\<close>

text \<open>
  In this section we formalize the classical Nemhauser–Wolsey guarantee:
  for a non-negative, monotone, submodular function on a finite ground set,
  the greedy algorithm that selects \<open>k\<close> elements achieves at least
  \<open>1 - (1 - 1/k)^k\<close> times the optimal value. Combining this with the analytic
  bound above yields the familiar \<open>1 - 1/e\<close> approximation factor.
\<close>

text \<open>Elementary algebraic identity used in the gap recurrence.\<close>
lemma one_minus_inv_times:
  fixes x :: real
  shows "(1 - 1 / real k) * x = x - x / real k"
  by (simp add: left_diff_distrib)

subsection \<open>Greedy gap analysis\<close>

text \<open>
  We use the problem-level optimal value and the reusable marginal-gain
  averaging lemma from the base cardinality context to derive the greedy
  gap recurrence.
\<close>

subsubsection \<open>Gap sequence\<close>

text \<open>
  We introduce the gap sequence \<open>gap i = OPT_k - f (greedy_set i)\<close> and
  show that it satisfies a simple linear recurrence under the greedy update.
\<close>

definition gap :: "nat \<Rightarrow> real" where
  "gap i = OPT_k - f (greedy_set i)"

text \<open>
  One-step inequality: the marginal gain of the greedy choice lower-bounds
  the average improvement towards \<open>OPT_k\<close>.
\<close>
lemma greedy_step_ineq:
  assumes "i < k"
    and S_sub: "greedy_set i \<subseteq> V"
    and R_nonempty: "V - greedy_set i \<noteq> {}"
  shows "gain (greedy_set i)
           (argmax_gain (greedy_set i) (V - greedy_set i))
         \<ge> (OPT_k - f (greedy_set i)) / real k"
proof -
  let ?S = "greedy_set i"
  let ?R = "V - ?S"

  obtain X where X_feas: "feasible X" and X_opt: "f X = OPT_k"
    using exists_opt_set by blast
  from X_feas have X_sub: "X \<subseteq> V" and cardX_le_k: "card X \<le> k"
    unfolding feasible_def by auto

  have S_sub': "?S \<subseteq> V"
    using S_sub .

  have cardS_lt_k: "card ?S < k"
  proof -
    have "card ?S \<le> i"
      by (rule card_greedy_le_i)
    with assms(1) show ?thesis
      by (meson le_less_trans)
  qed

  from marginal_gain_lower_bound[
        OF S_sub' X_sub cardS_lt_k cardX_le_k]
  obtain e where e_inR: "e \<in> V - ?S"
    and e_lb: "gain ?S e \<ge> (f X - f ?S) / real k"
    by blast

  have finV: "finite V"
    by (rule finite_V)

  have finR: "finite ?R"
    using finV by auto
  have R_nonempty': "?R \<noteq> {}"
    using R_nonempty by simp

  have argmax_max:
    "\<forall>y\<in>?R. gain ?S y \<le> gain ?S (argmax_gain ?S ?R)"
    using argmax_gain_max[OF finR R_nonempty'] .

  from argmax_max e_inR
  have e_le_argmax:
    "gain ?S e \<le> gain ?S (argmax_gain ?S ?R)"
    by auto

  have argmax_lb:
    "gain ?S (argmax_gain ?S ?R)
       \<ge> (f X - f ?S) / real k"
    using e_lb e_le_argmax by linarith

  have "(f X - f ?S) / real k = (OPT_k - f ?S) / real k"
    using X_opt by simp

  with argmax_lb
  have "gain ?S (argmax_gain ?S ?R)
        \<ge> (OPT_k - f ?S) / real k"
    by simp

  thus ?thesis
    by simp
qed

text \<open>Greedy sets are feasible whenever their size is at most \<open>k\<close>.\<close>

lemma greedy_set_feasible:
  assumes S_sub: "greedy_set i \<subseteq> V"
      and card_le_i: "card (greedy_set i) \<le> i"
      and i_le_k: "i \<le> k"
  shows "feasible (greedy_set i)"
proof -
  have "card (greedy_set i) \<le> k"
    using card_le_i i_le_k by (meson order_trans)
  with S_sub show ?thesis
    unfolding feasible_def by auto
qed

corollary greedy_feasible:
  assumes "i \<le> k"
  shows "feasible (greedy_set i)"
  using greedy_set_feasible[OF greedy_subset_V card_greedy_le_i assms] .

text \<open>The gap is non-negative along the greedy sequence.\<close>
lemma gap_nonneg:
  assumes S_sub: "greedy_set i \<subseteq> V"
      and card_le_i: "card (greedy_set i) \<le> i"
      and i_le_k: "i \<le> k"
  shows "0 \<le> gap i"
proof -
  have S_feas: "feasible (greedy_set i)"
    using greedy_set_feasible[OF S_sub card_le_i i_le_k] .
  have "f (greedy_set i) \<le> OPT_k"
    using OPT_k_upper_bound[OF S_feas] .
  then have "0 \<le> OPT_k - f (greedy_set i)"
    by simp
  thus ?thesis
    unfolding gap_def by simp
qed

corollary greedy_gap_nonneg:
  assumes "i \<le> k"
  shows "0 \<le> gap i"
  using gap_nonneg[OF greedy_subset_V card_greedy_le_i assms] .

corollary greedy_remainder_nonempty:
  assumes "i < k"
  shows "V - greedy_set i \<noteq> {}"
proof -
  have "card (greedy_set i) \<le> i"
    by (rule card_greedy_le_i)
  also have "... < k"
    using assms by simp
  also have "... \<le> card V"
    using k_le_cardV by simp
  finally have "card (greedy_set i) < card V" .
  thus ?thesis
    by (rule remainder_nonempty_if_card_ltV)
qed

text \<open>
  Gap recurrence: each step reduces the gap by at least a \<open>1/k\<close> fraction.
\<close>
lemma gap_step_diff:
  assumes "i < k"
    and S_sub: "greedy_set i \<subseteq> V"
    and R_nonempty: "V - greedy_set i \<noteq> {}"
  shows "gap (Suc i) \<le> gap i - gap i / real k"
proof -
  let ?S = "greedy_set i"

  have base:
    "gain ?S (argmax_gain ?S (V - ?S))
       \<ge> (OPT_k - f ?S) / real k"
    using greedy_step_ineq[OF assms] by simp

  have gap_Suc_eq:
    "gap (Suc i)
       = OPT_k - f ?S
         - gain ?S (argmax_gain ?S (V - ?S))"
  proof -
    have "gap (Suc i) = OPT_k - f (greedy_set (Suc i))"
      by (simp add: gap_def)
    also have "\<dots> = OPT_k
                 - (f ?S
                    + gain ?S (argmax_gain ?S (V - ?S)))"
      using greedy_step_f_eq[OF R_nonempty] by simp
    also have "\<dots> = OPT_k - f ?S
                   - gain ?S (argmax_gain ?S (V - ?S))"
      by simp
    finally show ?thesis .
  qed

  have "OPT_k - f ?S
        - gain ?S (argmax_gain ?S (V - ?S))
      \<le> OPT_k - f ?S
        - (OPT_k - f ?S) / real k"
    using base by linarith
  hence "gap (Suc i)
         \<le> OPT_k - f ?S - (OPT_k - f ?S) / real k"
    using gap_Suc_eq by simp

  also have "OPT_k - f ?S - (OPT_k - f ?S) / real k
             = gap i - gap i / real k"
    by (simp add: gap_def)

  finally show ?thesis .
qed

text \<open>
  In multiplicative form, the gap shrinks by a factor of at most
  \<open>1 - 1/real k\<close> per step.
\<close>
lemma gap_step:
  assumes "i < k"
    and "greedy_set i \<subseteq> V"
    and "V - greedy_set i \<noteq> {}"
  shows "gap (Suc i) \<le> (1 - 1 / real k) * gap i"
proof -
  have "gap (Suc i) \<le> gap i - gap i / real k"
    using gap_step_diff[OF assms] .
  also have "gap i - gap i / real k
             = (1 - 1 / real k) * gap i"
    using one_minus_inv_times[of "gap i"] by simp
  finally show ?thesis .
qed

lemma gap_0[simp]: "gap 0 = OPT_k"
proof -
  have "gap 0 = OPT_k - f (greedy_set 0)"
    by (simp add: gap_def)
  also have "greedy_set 0 = {}" by simp
  also have "f {} = 0" by (rule f_empty)
  finally show ?thesis by simp
qed

text \<open>
  Geometric decay of the gap: after \<open>i\<close> greedy steps the remaining gap is
  bounded by \<open>(1 - 1/real k)^i * OPT_k\<close>.
\<close>
lemma gap_geometric:
  assumes k_pos: "k > 0"
    and i_le_k: "i \<le> k"
  shows "gap i \<le> (1 - 1 / real k) ^ i * OPT_k"
using i_le_k
proof (induction i)
  case 0
  have "gap 0 = OPT_k" by simp
  thus ?case by simp
next
  case (Suc i)
  have i_le_k: "i \<le> k" using Suc.prems by simp
  have i_lt_k: "i < k" using Suc.prems by simp

  have S_sub: "greedy_set i \<subseteq> V"
    by (rule greedy_subset_V)

  have cardSi_lt_V: "card (greedy_set i) < card V"
  proof -
    have "card (greedy_set i) \<le> i"
      by (rule card_greedy_le_i)
    also have "... < k" using i_lt_k by simp
    also have "... \<le> card V" using k_le_cardV by simp
    finally show ?thesis .
  qed

  have R_nonempty: "V - greedy_set i \<noteq> {}"
    using remainder_nonempty_if_card_ltV[OF cardSi_lt_V] .

  have step:
    "gap (Suc i) \<le> (1 - 1 / real k) * gap i"
    using gap_step[OF i_lt_k S_sub R_nonempty] .

  have coef_nonneg: "0 \<le> (1 - 1 / real k)"
  proof -
    have "1 \<le> real k" using k_pos by simp
    then have "1 / real k \<le> 1"
      by (simp add: field_simps)
    then show ?thesis
      by simp
  qed

  have mult_mono:
    "(1 - 1 / real k) * gap i
      \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
  proof -
    have IH: "gap i \<le> (1 - 1 / real k) ^ i * OPT_k"
      using Suc.IH i_le_k by simp
    from IH coef_nonneg show ?thesis
      by (rule mult_left_mono)
  qed

  have pow_Suc:
   "(1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)
     = (1 - 1 / real k) ^ Suc i * OPT_k"
   by (simp add: mult_ac)

  from step mult_mono have
    "gap (Suc i)
       \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
    by (rule order_trans)
  hence "gap (Suc i)
         \<le> (1 - 1 / real k) ^ Suc i * OPT_k"
    by (simp add: pow_Suc)
  thus ?case
    by simp
qed

text \<open>
  As a consequence, the value of the greedy solution after \<open>k\<close> steps is
  at least \<open>(1 - (1 - 1/real k)^k) * OPT_k\<close>.
\<close>
lemma greedy_sequence_bound:
  assumes k_pos: "k > 0"
  shows "f (greedy_set k) \<ge> (1 - (1 - 1 / real k) ^ k) * OPT_k"
proof -
  have gap_bound:
    "gap k \<le> (1 - 1 / real k) ^ k * OPT_k"
    using gap_geometric[OF k_pos le_refl] .

  have f_eq:
    "f (greedy_set k) = OPT_k - gap k"
    by (simp add: gap_def)

  have lower_bound:
    "OPT_k - gap k \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
  proof -
    have "- gap k \<ge> - ((1 - 1 / real k) ^ k * OPT_k)"
      using gap_bound by simp
    thus ?thesis
      by simp
  qed

  have "f (greedy_set k) \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
    using f_eq lower_bound by simp

  also have "OPT_k - (1 - 1 / real k) ^ k * OPT_k
             = (1 - (1 - 1 / real k) ^ k) * OPT_k"
  proof -
    have "OPT_k - (1 - 1 / real k) ^ k * OPT_k
          = 1 * OPT_k - (1 - 1 / real k) ^ k * OPT_k"
      by simp
    also have "... = (1 - (1 - 1 / real k) ^ k) * OPT_k"
      by (simp add: left_diff_distrib)
    finally show ?thesis .
  qed

  finally show ?thesis .
qed

subsection \<open>Non-negativity of OPT and approximation ratio\<close>

text \<open>
  Combining the discrete bound with the analytic inequality for
  \<open>1 - (1 - 1/k)^k\<close> yields the standard \<open>1 - 1/e\<close> approximation factor.
\<close>
theorem greedy_approximation:
  assumes k_pos: "k > 0"
  shows "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
proof -
  have base_bound:
    "f (greedy_set k) \<ge> (1 - (1 - 1 / real k) ^ k) * OPT_k"
    using greedy_sequence_bound[OF k_pos] .

  have k_ge1: "k \<ge> 1"
    using k_pos by simp

  have coeff_bound:
    "1 - (1 - 1 / real k) ^ k \<ge> 1 - 1 / exp 1"
    using coeff_ge_1_minus_inv_exp[OF k_ge1] .

  have nonneg: "0 \<le> OPT_k"
    by (rule OPT_k_nonneg)

  have coeff_mono:
    "(1 - (1 - 1 / real k) ^ k) * OPT_k
      \<ge> (1 - 1 / exp 1) * OPT_k"
    using coeff_bound nonneg
    by (rule mult_right_mono)

  from base_bound coeff_mono
  have "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
    by (meson order_trans)
  thus ?thesis .
qed

subsection \<open>Corollaries\<close>

text \<open>
  Define the approximation ratio of the greedy algorithm for a given \<open>k\<close>
  (with the convention that the ratio is \<open>1\<close> when \<open>OPT_k = 0\<close>), and show
  that it is always at least \<open>1 - 1/exp 1\<close>.
\<close>
definition greedy_ratio :: real where
  "greedy_ratio = (if OPT_k = 0 then 1 else f (greedy_set k) / OPT_k)"

corollary greedy_ratio_ge_1_minus_inv_exp:
  assumes "k > 0"
  shows "greedy_ratio \<ge> 1 - 1 / exp 1"
proof (cases "OPT_k = 0")
  case True
  then show ?thesis
    unfolding greedy_ratio_def
    by simp
next
  case False
  then have OPT_pos: "OPT_k > 0"
    using OPT_k_nonneg by auto
  have main: "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
    using greedy_approximation[OF assms] .
  show ?thesis
    unfolding greedy_ratio_def
    using main False OPT_pos
    by (simp add: field_simps)
qed

end

section \<open>Step-spec corollary\<close>

text \<open>
  Since \<open>Greedy_Step_Oracle\<close> is a named instance of \<open>Greedy_Setup\<close>, the
  Nemhauser--Wolsey approximation guarantee transfers directly to any oracle
  satisfying the step-specification assumptions.
\<close>

context Greedy_Step_Oracle
begin

theorem greedy_step_oracle_approximation:
  assumes "k > 0"
  shows
    "f (Greedy_Setup.greedy_set V select k)
       \<ge> (1 - 1 / exp 1) * OPT_k"
  using greedy_approximation[OF assms] .

end

end
