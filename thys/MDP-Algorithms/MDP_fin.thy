theory MDP_fin
  imports 
  "MDP-Rewards.MDP_reward"
begin

locale MDP_on = MDP_act_disc arb_act A K r l 
  for
    A and
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" and r l arb_act +
  fixes S :: "'s set"
  assumes 
    fin_states: "finite S" and 
    fin_actions: "\<And>s. finite (A s)" and
    K_closed: "set_pmf (K (s,a)) \<subseteq> S"
begin

lemma \<L>\<^sub>b_indep:
  assumes "\<And>s. s \<in> S \<Longrightarrow> apply_bfun v s = apply_bfun v' s"
    and "s \<in> S"
  shows "\<L>\<^sub>b v s = \<L>\<^sub>b v' s"
proof -
  have "measure_pmf.expectation (K (s, a)) (apply_bfun v) = measure_pmf.expectation (K (s, a)) (apply_bfun v')" for a
    using assms K_closed subsetD
    by (auto intro!: AE_pmfI Bochner_Integration.integral_cong_AE)
  thus ?thesis
    unfolding \<L>\<^sub>b_eq_SUP_L\<^sub>a L\<^sub>a_int by auto
qed

end

locale MDP_nat_type = MDP_act A K
  for A :: "nat \<Rightarrow> nat set" and K +
  assumes A_fin : "\<And>s. finite (A s)"

locale MDP_nat = MDP_nat_type +
  fixes states :: nat
  assumes K_closed: "\<forall>s < states. set_pmf (K (s,a)) \<subseteq> {0..<states}"
  assumes K_closed_compl: "\<forall>s\<ge> states. set_pmf (K (s,a)) \<subseteq> {states..}"
  assumes A_outside: "\<And>s. s \<ge> states \<Longrightarrow> A s = {0}"


locale MDP_nat_disc = MDP_nat arb_act A K states + MDP_act_disc arb_act A K r l 
  for A K r l arb_act states +
  assumes reward_zero_outside: "\<forall>s\<ge>states. r (s,a) = 0"
begin
lemma \<L>\<^sub>b_eq_L\<^sub>a_max': "\<L>\<^sub>b v s = (MAX a \<in> A s. L\<^sub>a a v s)"
  unfolding \<L>\<^sub>b_eq_L\<^sub>a_max
  using finite_arg_max_eq_Max[of "A s" "\<lambda>a. L\<^sub>a a v s"] A_ne A_fin
  by auto

abbreviation "state_space \<equiv> {0..<states}"

lemma set_pmf_Xn': "s \<notin> state_space \<Longrightarrow> set_pmf (Xn' p s i) \<subseteq> {states..}"
  using K_closed_compl 
  by (induction i arbitrary: p s) (auto dest!: subsetD simp: Suc_Xn' linorder_not_less)

lemma set_pmf_Pn': "s \<notin> state_space \<Longrightarrow> (\<forall>sa \<in> set_pmf (Pn' p s i). fst sa\<notin> state_space)"
  using set_pmf_Xn'[unfolded Xn'_Pn'] by fastforce

lemma reward_Pn'_notin: "s \<notin> state_space \<Longrightarrow> (\<forall>sa \<in> set_pmf (Pn' p s i). r sa = 0)"
  using set_pmf_Pn' reward_zero_outside by (fastforce simp: linorder_not_less)

lemma \<nu>_zero_notin:
  assumes "s \<notin> state_space" 
  shows "\<nu> p s = 0"
proof -
  have "\<nu>_fin p n s = 0" for n
    using assms reward_Pn'_notin
    by (auto simp: \<nu>_fin_eq_Pn intro!: sum.neutral integral_eq_zero_AE AE_pmfI)
  thus ?thesis 
    unfolding \<nu>_def by auto
qed

lemma \<nu>_opt_zero_notin:
  assumes "s \<notin> state_space" 
  shows "\<nu>_opt s = 0"
  unfolding \<nu>_opt_def using assms \<nu>_zero_notin policies_ne by auto

end

end