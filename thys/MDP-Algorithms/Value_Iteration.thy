(* Author: Maximilian Schäffeler *)

theory Value_Iteration
  imports "MDP-Rewards.MDP_reward"
begin

context MDP_att_\<L>
begin

section \<open>Value Iteration\<close>
text \<open>
In the previous sections we derived that repeated application of @{const "\<L>\<^sub>b"} to any bounded 
function from states to the reals converges to the optimal value of the MDP @{const "\<nu>\<^sub>b_opt"}.

We can turn this procedure into an algorithm that computes not only an approximation of 
@{const "\<nu>\<^sub>b_opt"} but also a policy that is arbitrarily close to optimal.

Most of the proofs rely on the assumption that the supremum in @{const "\<L>\<^sub>b"} can always be attained.
\<close>

text \<open>
The following lemma shows that the relation we use to prove termination of the value iteration 
algorithm decreases in each step.
In essence, the distance of the estimate to the optimal value decreases by a factor of at 
least @{term l} per iteration.\<close>


lemma vi_rel_dec: 
  assumes "l \<noteq> 0" "\<L>\<^sub>b v \<noteq> \<nu>\<^sub>b_opt"
  shows "\<lceil>log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) - c\<rceil> < \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) - c\<rceil>"
proof -
  have "log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (l * dist v \<nu>\<^sub>b_opt) - c"
    using contraction_\<L>[of _ "\<nu>\<^sub>b_opt"] disc_lt_one
    by (auto simp: assms less_le intro: log_le)
  also have "\<dots> = log (1 / l) l + log (1/l) (dist v \<nu>\<^sub>b_opt) - c"
    using assms disc_lt_one 
    by (auto simp: less_le intro!: log_mult)
  also have "\<dots> = -(log (1 / l) (1/l)) + (log (1/l) (dist v \<nu>\<^sub>b_opt)) - c"
    using assms disc_lt_one
    by (subst log_inverse[symmetric]) (auto simp: less_le right_inverse_eq)
  also have "\<dots> = (log (1/l) (dist v \<nu>\<^sub>b_opt)) - 1 - c"
    using assms order.strict_implies_not_eq[OF disc_lt_one]
    by (auto intro!: log_eq_one neq_le_trans)
  finally have "log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (dist v \<nu>\<^sub>b_opt) - 1 - c" .
  thus ?thesis
    by linarith
qed

lemma dist_\<L>\<^sub>b_lt_dist_opt: "dist v (\<L>\<^sub>b v) \<le> 2 * dist v \<nu>\<^sub>b_opt"
proof -
  have le1: "dist v (\<L>\<^sub>b v) \<le> dist v \<nu>\<^sub>b_opt + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    by (simp add: dist_triangle dist_commute)
  have le2: "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt \<le> l * dist v \<nu>\<^sub>b_opt"
    using \<L>\<^sub>b_opt contraction_\<L>
    by metis
  show ?thesis
    using mult_right_mono[of l 1] disc_lt_one 
    by (fastforce intro!: order.trans[OF le2] order.trans[OF le1])
qed

abbreviation "term_measure \<equiv> (\<lambda>(eps, v).
    if v = \<nu>\<^sub>b_opt \<or> l = 0
    then 0
    else nat (ceiling (log (1/l) (dist v \<nu>\<^sub>b_opt) - log (1/l) (eps * (1-l) / (8 * l)))))"

function value_iteration :: "real \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" where
  "value_iteration eps v =
  (if 2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l) \<or> eps \<le> 0 then \<L>\<^sub>b v else value_iteration eps (\<L>\<^sub>b v))"
  by auto

termination
proof (relation "Wellfounded.measure term_measure", (simp; fail), cases "l = 0")
  case False
  fix eps v
  assume h: "\<not> (2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0)"
  show "((eps, \<L>\<^sub>b v), eps, v) \<in> Wellfounded.measure term_measure"
  proof -
    have gt_zero[simp]: "l \<noteq> 0" "eps > 0" and dist_ge: "eps * (1 - l) \<le> dist v (\<L>\<^sub>b v) * (2 * l)"
      using h
      by (auto simp: algebra_simps)
    have v_not_opt: "v \<noteq> \<nu>\<^sub>b_opt"
      using h
      by force
    have "log (1 / l) (eps * (1 - l) / (8 * l)) < log (1 / l) (dist v \<nu>\<^sub>b_opt)"
    proof (intro log_less)
      show "1 < 1 / l"
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "0 < eps * (1 - l) / (8 * l)" 
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "eps * (1 - l) / (8 * l) < dist v \<nu>\<^sub>b_opt" 
        using dist_pos_lt[OF v_not_opt] dist_\<L>\<^sub>b_lt_dist_opt[of v] gt_zero zero_le_disc 
          mult_strict_left_mono[of "dist v (\<L>\<^sub>b v)" "(4 * dist v \<nu>\<^sub>b_opt)" l]
        by (intro mult_imp_div_pos_less le_less_trans[OF dist_ge], argo+)
    qed
    thus ?thesis
      using vi_rel_dec h
      by auto
  qed
qed auto

text \<open>
The distance between an estimate for the value and the optimal value can be bounded with respect to 
the distance between the estimate and the result of applying it to @{const \<L>\<^sub>b}
\<close>
lemma contraction_\<L>_dist: "(1 - l) * dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v)"
  using contraction_dist contraction_\<L> disc_lt_one zero_le_disc
  by fastforce

lemma dist_\<L>\<^sub>b_opt_eps:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
proof -
  have "dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v) / (1 - l)"
    using contraction_\<L>_dist
    by (simp add: mult.commute pos_le_divide_eq)
  hence "2 * l * dist v \<nu>\<^sub>b_opt \<le> 2 * l * (dist v (\<L>\<^sub>b v) / (1 - l))"
    using contraction_\<L>_dist assms mult_le_cancel_left_pos[of "2 * l"]
    by (fastforce intro!: mult_left_mono[of _ _ "2 * l"])
  hence "2 * l * dist v \<nu>\<^sub>b_opt < eps"
    by (auto simp: assms(2) pos_divide_less_eq intro: order.strict_trans1)
  hence "dist v \<nu>\<^sub>b_opt * l < eps / 2"
    by argo
  hence "l * dist v \<nu>\<^sub>b_opt < eps / 2"
    by (auto simp: algebra_simps)
  thus "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
    using contraction_\<L>[of v \<nu>\<^sub>b_opt] 
    by auto
qed

text \<open>
The estimates above allow to give a bound on the error of @{const value_iteration}.
\<close>
declare value_iteration.simps[simp del]

lemma value_iteration_error: 
  assumes "eps > 0"
  shows "dist (value_iteration eps v) \<nu>\<^sub>b_opt < eps / 2"
  using assms dist_\<L>\<^sub>b_opt_eps value_iteration.simps
  by (induction eps v rule: value_iteration.induct) auto

text \<open>
After the value iteration terminates, one can easily obtain a stationary deterministic 
epsilon-optimal policy.

Such a policy does not exist in general, attainment of the supremum in @{const \<L>\<^sub>b} is required.
\<close>
definition "find_policy (v :: 's \<Rightarrow>\<^sub>b real) s = arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)"

definition "vi_policy eps v = find_policy (value_iteration eps v)"

text \<open>
We formalize the attainment of the supremum using a predicate @{const has_arg_max}.
\<close>

abbreviation "vi u n \<equiv> (\<L>\<^sub>b ^^n) u"

lemma \<L>\<^sub>b_iter_mono:
  assumes "u \<le> v" shows "vi u n \<le> vi v n"
  using assms \<L>\<^sub>b_mono 
  by (induction n) auto

lemma 
  assumes "vi v (Suc n) \<le> vi v n" 
  shows "vi v (Suc n + m) \<le> vi v (n + m)"
proof -
  have "vi v (Suc n + m) = vi (vi v (Suc n)) m"
    by (simp add: Groups.add_ac(2) funpow_add funpow_swap1)
  also have "... \<le> vi (vi v n) m"
    using \<L>\<^sub>b_iter_mono[OF assms]
    by auto
  also have "... = vi v (n + m)"
    by (simp add: add.commute funpow_add)
  finally show ?thesis .
qed


lemma 
  assumes "vi v n \<le> vi v (Suc n)" 
  shows "vi v (n + m) \<le> vi v (Suc n + m)"
proof -
  have "vi v (n + m) \<le> vi (vi v n) m"
    by (simp add: Groups.add_ac(2) funpow_add funpow_swap1)
  also have "\<dots> \<le> vi v (Suc n + m)"
    using \<L>\<^sub>b_iter_mono[OF assms]
    by (auto simp only: add.commute funpow_add o_apply)
  finally show ?thesis .
qed

(* 6.3.1 *)
(* a) *)
lemma "vi v \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
  using \<L>\<^sub>b_lim.

lemma "(\<lambda>n. dist (vi v (Suc n)) (vi v n)) \<longlonglongrightarrow> 0"
  using thm_6_3_1_b_aux[of v]
  by (auto simp only: dist_commute[of "((\<L>\<^sub>b ^^ Suc _) v)"])



end

context MDP_att_\<L> 
begin

text \<open>
The error of the resulting policy is bounded by the distance from its value to the value computed 
by the value iteration plus the error in the value iteration itself.
We show that both are less than @{term "eps / 2"} when the algorithm terminates.
\<close>
lemma find_policy_error_bound:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (find_policy (\<L>\<^sub>b v)))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?d = "mk_dec_det (find_policy (\<L>\<^sub>b v))"
  let ?p = "mk_stationary ?d"
    (* shorter proof:     by (auto simp: arg_max_SUP[OF find_policy_QR_is_arg_max] \<L>\<^sub>b_split.rep_eq \<L>_split_def )*)
  have L_eq_\<L>\<^sub>b: "L (mk_dec_det (find_policy v)) v = \<L>\<^sub>b v" for v
    unfolding find_policy_def
  proof (intro antisym)
    show "L (mk_dec_det (\<lambda>s. arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s))) v \<le> \<L>\<^sub>b v"
      using Sup_att has_arg_max_arg_max abs_L_le
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det less_eq_bfun_def arg_max_on_def is_dec_det_def max_L_ex_def
      by (auto intro!: cSUP_upper bounded_imp_bdd_above boundedI[of _ "r\<^sub>M + l * norm v"])
  next
    show "\<L>\<^sub>b v \<le> L (mk_dec_det (\<lambda>s. arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s))) v"
      unfolding less_eq_bfun_def \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det
      using Sup_att ex_dec_det
      by (auto intro!: cSUP_least app_arg_max_ge simp: L_eq_L\<^sub>a_det max_L_ex_def is_dec_det_def)
  qed
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix 
    by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle 
    by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    by (auto simp: L_eq_\<L>\<^sub>b)
  also have "\<dots> \<le> l *  dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> contraction_L
    by (fastforce intro!: add_mono)
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v" .
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) - l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by auto
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> l * dist (\<L>\<^sub>b v) v"
    by argo
  hence  "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1-l) \<le> 2 * (l * dist (\<L>\<^sub>b v) v)"
    using zero_le_disc mult_left_mono 
    by auto
  also have "\<dots> \<le> eps * (1-l)"
    using assms
    by (auto intro!: mult_left_mono simp: dist_commute pos_divide_le_eq)
  finally have "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> eps * (1 - l)" .
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps"
    using disc_lt_one mult_right_le_imp_le
    by auto
  moreover have "2 * dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps"
    using dist_\<L>\<^sub>b_opt_eps assms 
    by fastforce
  moreover have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle 
    by blast  
  ultimately show ?thesis 
    by auto
qed

lemma vi_policy_opt:
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_policy eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_policy_def 
  using assms
proof (induction eps v rule: value_iteration.induct)
  case (1 v)
  then show ?case
    using find_policy_error_bound
    by (subst value_iteration.simps) auto
qed

lemma lemma_6_3_1_d:
  assumes "eps > 0"
  assumes "2 * l * dist (vi v (Suc n)) (vi v n) < eps * (1-l)"
  shows "dist (vi v (Suc n)) \<nu>\<^sub>b_opt < eps / 2"
  using dist_\<L>\<^sub>b_opt_eps assms
  by (simp add: dist_commute)

end

context MDP_act begin

definition "find_policy' (v :: 's \<Rightarrow>\<^sub>b real) s = arb_act (opt_acts v s)"

definition "vi_policy' eps v = find_policy' (value_iteration eps v)"

lemma find_policy'_error_bound:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v)))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?d = "mk_dec_det (find_policy' (\<L>\<^sub>b v))"
  let ?p = "mk_stationary ?d"
  have L_eq_\<L>\<^sub>b: "L (mk_dec_det (find_policy' v)) v = \<L>\<^sub>b v" for v
    unfolding find_policy'_def
    by (metis \<nu>_improving_imp_\<L>\<^sub>b \<nu>_improving_opt_acts)
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix 
    by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle 
    by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    by (auto simp: L_eq_\<L>\<^sub>b)
  also have "\<dots> \<le> l *  dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> contraction_L
    by (fastforce intro!: add_mono)
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v" .
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) - l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by auto
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> l * dist (\<L>\<^sub>b v) v"
    by argo
  hence  "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1-l) \<le> 2 * (l * dist (\<L>\<^sub>b v) v)"
    using zero_le_disc mult_left_mono 
    by auto
  also have "\<dots> \<le> eps * (1-l)"
    using assms
    by (auto intro!: mult_left_mono simp: dist_commute pos_divide_le_eq)
  finally have "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> eps * (1 - l)".
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps"
    using disc_lt_one mult_right_le_imp_le
    by auto
  moreover have "2 * dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps"
    using dist_\<L>\<^sub>b_opt_eps assms 
    by fastforce
  moreover have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle 
    by blast  
  ultimately show ?thesis 
    by auto
qed

lemma vi_policy'_opt:
  assumes "eps > 0" "l > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_policy' eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_policy'_def 
  using assms
proof (induction eps v rule: value_iteration.induct)
  case (1 v)
  then show ?case
    using find_policy'_error_bound
    by (subst value_iteration.simps) auto
qed

end
end