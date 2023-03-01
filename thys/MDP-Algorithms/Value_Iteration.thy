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

abbreviation "term_measure \<equiv> (\<lambda>(eps, v). LEAST n. (2 * l * dist ((\<L>\<^sub>b^^(Suc n)) v) ((\<L>\<^sub>b^^n) v) < eps * (1-l)))"

lemma Least_Suc_less:
  assumes "\<exists>n. P n" "\<not>P 0"
  shows "Least (\<lambda>n. P (Suc n)) < Least P"
  using assms by (auto simp: Least_Suc)

function value_iteration :: "real \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" where
  "value_iteration eps v =
  (if 2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l) \<or> eps \<le> 0 then \<L>\<^sub>b v else value_iteration eps (\<L>\<^sub>b v))"
  by auto
termination
proof (relation "Wellfounded.measure term_measure")
  fix eps v
  assume h: "\<not> (2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0)"
  show "((eps, \<L>\<^sub>b v), eps, v) \<in> Wellfounded.measure term_measure"
  proof -
    have "(\<lambda>n. dist ((\<L>\<^sub>b ^^ Suc n) v) ((\<L>\<^sub>b ^^ n) v)) \<longlonglongrightarrow> 0" 
      using dist_\<L>\<^sub>b_tendsto
      by (auto simp: dist_commute)
    hence *: "\<exists>n. dist ((\<L>\<^sub>b ^^ Suc n) v) ((\<L>\<^sub>b ^^ n) v) < eps" if "eps > 0" for eps
      unfolding LIMSEQ_def using that by auto
    have **: "0 < l * 2" if "0 \<noteq> l"
      using zero_le_disc that by linarith
    hence "(LEAST n. (2 * l) * dist ((\<L>\<^sub>b ^^ (Suc (Suc n))) v) ((\<L>\<^sub>b ^^ (Suc n)) v) < eps * (1 - l)) < 
      (LEAST n. (2 * l) * dist ((\<L>\<^sub>b ^^ Suc n) v) ((\<L>\<^sub>b ^^ n) v) <  eps * (1 - l))" if "0 \<noteq> l"
        using h *[of "eps * (1-l) / (2 * l)"] that
        by (fastforce simp: ** algebra_simps dist_commute pos_less_divide_eq intro!: Least_Suc_less)
      thus ?thesis
      using h by (cases "l = 0") (auto simp: funpow_swap1)
  qed
qed auto

text \<open>
The distance between an estimate for the value and the optimal value can be bounded with respect to 
the distance between the estimate and the result of applying it to @{const \<L>\<^sub>b}
\<close>
(* 2nd to last inequality in the proof of Thm 6.3.1 *)
lemma contraction_\<L>_dist: "(1 - l) * dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v)"
  using contraction_dist contraction_\<L> disc_lt_one zero_le_disc by fastforce

lemma dist_\<L>\<^sub>b_opt_eps:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "2 * dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps"
proof -
  have "2 * l * dist v \<nu>\<^sub>b_opt * (1 - l) \<le> 2 * l * dist v (\<L>\<^sub>b v)"
    using contraction_\<L>_dist by (simp add: mult_left_mono mult.commute)
  hence "2 * l * dist v \<nu>\<^sub>b_opt * (1 - l) < eps * (1-l)"
    using assms(2) by linarith
  hence "2 * l * dist v \<nu>\<^sub>b_opt < eps"
    by force
  thus "2 * dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps"
    using contraction_\<L>[of v \<nu>\<^sub>b_opt] by auto
qed

lemma dist_\<L>\<^sub>b_lt_dist_opt: "dist v (\<L>\<^sub>b v) \<le> 2 * dist v \<nu>\<^sub>b_opt"
proof -
  have le1: "dist v (\<L>\<^sub>b v) \<le> dist v \<nu>\<^sub>b_opt + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    by (simp add: dist_triangle dist_commute)
  have le2: "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt \<le> l * dist v \<nu>\<^sub>b_opt"
    using \<L>\<^sub>b_opt contraction_\<L> by metis
  show ?thesis
    using mult_right_mono[of l 1] disc_lt_one 
    by (fastforce intro!: order.trans[OF le2] order.trans[OF le1])
qed

text \<open>
The estimates above allow to give a bound on the error of @{const value_iteration}.
\<close>
declare value_iteration.simps[simp del]

lemma value_iteration_error: 
  assumes "eps > 0"
  shows "2 * dist (value_iteration eps v) \<nu>\<^sub>b_opt < eps"
  using assms dist_\<L>\<^sub>b_opt_eps value_iteration.simps
  by (induction eps v rule: value_iteration.induct) auto

text \<open>
After the value iteration terminates, one can easily obtain a stationary deterministic 
epsilon-optimal policy.

Such a policy does not exist in general, attainment of the supremum in @{const \<L>\<^sub>b} is required.
\<close>
definition "find_policy (v :: 's \<Rightarrow>\<^sub>b real) s = arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)"

definition "vi_policy eps v = find_policy (value_iteration eps v)"

abbreviation "vi u n \<equiv> (\<L>\<^sub>b ^^ n) u"

lemma \<L>\<^sub>b_iter_mono:
  assumes "u \<le> v" shows "vi u n \<le> vi v n"
  using assms \<L>\<^sub>b_mono by (induction n) auto

lemma 
  assumes "vi v (Suc n) \<le> vi v n" 
  shows "vi v (Suc n + m) \<le> vi v (n + m)"
proof -
  have "vi v (Suc n + m) = vi (vi v (Suc n)) m"
    by (simp add: Groups.add_ac(2) funpow_add funpow_swap1)
  also have "... \<le> vi (vi v n) m"
    using \<L>\<^sub>b_iter_mono[OF assms] by auto
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
    using \<L>\<^sub>b_iter_mono[OF assms] by (auto simp only: add.commute funpow_add o_apply)
  finally show ?thesis .
qed

lemma "(\<lambda>n. dist (vi v (Suc n)) (vi v n)) \<longlonglongrightarrow> 0"
  using dist_\<L>\<^sub>b_tendsto[of v] by (auto simp: dist_commute)

end

context MDP_att_\<L> 
begin

lemma is_arg_max_find_policy: "is_arg_max (\<lambda>d. L\<^sub>a d (apply_bfun v) s) (\<lambda>d. d \<in> A s)  (find_policy v s)"
  using Sup_att
  by (simp add: find_policy_def arg_max_on_def arg_max_def someI_ex max_L_ex_def has_arg_max_def)

text \<open>
The error of the resulting policy is bounded by the distance from its value to the value computed 
by the value iteration plus the error in the value iteration itself.
We show that both are less than @{term "eps / 2"} when the algorithm terminates.
\<close>
lemma find_policy_dist_\<L>\<^sub>b:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "2 * dist (\<nu>\<^sub>b (mk_stationary_det (find_policy (\<L>\<^sub>b v)))) (\<L>\<^sub>b v) \<le> eps"
proof -
  let ?d = "mk_dec_det (find_policy (\<L>\<^sub>b v))"
  let ?p = "mk_stationary ?d"
  have L_eq_\<L>\<^sub>b: "L (mk_dec_det (find_policy v)) v = \<L>\<^sub>b v" for v
    by (auto simp: L_eq_L\<^sub>a_det \<L>\<^sub>b_eq_argmax_L\<^sub>a[OF is_arg_max_find_policy])
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    by (auto simp: L_eq_\<L>\<^sub>b)
  also have "\<dots> \<le> l *  dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> contraction_L by (fastforce intro!: add_mono)
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v" .
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> l * dist (\<L>\<^sub>b v) v"
    by (auto simp: algebra_simps)
  hence *: "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> 2 * l * dist (\<L>\<^sub>b v) v"
    using zero_le_disc mult_left_mono by auto
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> eps * (1 - l)"
     using assms by (fastforce simp: dist_commute intro!: order.trans[OF *])
  thus "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps"
    by auto
qed  

lemma find_policy_error_bound:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (find_policy (\<L>\<^sub>b v)))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?p = "mk_stationary_det (find_policy (\<L>\<^sub>b v))"
  have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle by blast  
  thus ?thesis
    using find_policy_dist_\<L>\<^sub>b[OF assms] dist_\<L>\<^sub>b_opt_eps[OF assms] by simp
qed

lemma vi_policy_opt:
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_policy eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_policy_def 
  using assms
proof (induction eps v rule: value_iteration.induct)
  case (1 v)
  then show ?case
    using find_policy_error_bound by (subst value_iteration.simps) auto
qed

lemma lemma_6_3_1_d:
  assumes "eps > 0" "2 * l * dist (vi v (Suc n)) (vi v n) < eps * (1-l)"
  shows "2 * dist (vi v (Suc n)) \<nu>\<^sub>b_opt < eps"
  using dist_\<L>\<^sub>b_opt_eps assms by (simp add: dist_commute)
end

context MDP_act_disc begin
                 
definition "find_policy' (v :: 's \<Rightarrow>\<^sub>b real) s = arb_act (opt_acts v s)"

definition "vi_policy' eps v = find_policy' (value_iteration eps v)"

lemma is_arg_max_find_policy': "is_arg_max (\<lambda>d. L\<^sub>a d (apply_bfun v) s) (\<lambda>d. d \<in> A s) (find_policy' v s)"
  using is_opt_act_some by (auto simp: find_policy'_def is_opt_act_def)

lemma find_policy'_dist_\<L>\<^sub>b:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "2 * dist (\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v)))) (\<L>\<^sub>b v) \<le> eps"
proof -
  let ?d = "mk_dec_det (find_policy' (\<L>\<^sub>b v))"
  let ?p = "mk_stationary ?d"
  have L_eq_\<L>\<^sub>b: "L (mk_dec_det (find_policy' v)) v = \<L>\<^sub>b v" for v
    by (auto simp: L_eq_L\<^sub>a_det \<L>\<^sub>b_eq_argmax_L\<^sub>a[OF is_arg_max_find_policy'])
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    by (auto simp: L_eq_\<L>\<^sub>b)
  also have "\<dots> \<le> l *  dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> contraction_L by (fastforce intro!: add_mono)
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v" .
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> l * dist (\<L>\<^sub>b v) v"
    by (auto simp: algebra_simps)
  hence *: "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> 2 * l * dist (\<L>\<^sub>b v) v"
    using zero_le_disc mult_left_mono by auto
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) * (1 - l) \<le> eps * (1 - l)"
     using assms by (fastforce simp: dist_commute intro!: order.trans[OF *])
  thus "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps"
    by auto
qed

lemma find_policy'_error_bound:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v)))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?p = "mk_stationary_det (find_policy' (\<L>\<^sub>b v))"
  have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle by blast  
  thus ?thesis
    using find_policy'_dist_\<L>\<^sub>b[OF assms] dist_\<L>\<^sub>b_opt_eps[OF assms] by simp
qed

lemma vi_policy'_opt:
  assumes "eps > 0" "l > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_policy' eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_policy'_def 
  using assms
proof (induction eps v rule: value_iteration.induct)
  case (1 eps v)
  then show ?case
    using find_policy'_error_bound by (auto simp: value_iteration.simps[of _ v])
qed

end
end