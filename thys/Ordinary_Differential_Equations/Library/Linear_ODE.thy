section \<open>Linear ODE\<close>
theory Linear_ODE
imports
  "../IVP/Flow"
  Bounded_Linear_Operator
  Multivariate_Taylor
begin

lemma
  exp_scaleR_has_derivative_right[derivative_intros]:
  fixes f::"real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. exp (f x *\<^sub>R A)) has_derivative (\<lambda>h. f' h *\<^sub>R (exp (f x *\<^sub>R A) * A))) (at x within s)"
proof -
  from assms have "bounded_linear f'" by auto
  with real_bounded_linear obtain m where f': "f' = (\<lambda>h. h * m)" by blast
  show ?thesis
    using vector_diff_chain_within[OF _ exp_scaleR_has_vector_derivative_right, of f m x s A] assms f'
    by (auto simp: has_vector_derivative_def o_def)
qed

locale linear_ivp = ivp i for i :: "'a::{banach,perfect_space} ivp" +
  fixes A::"'a blinop" and s::real
  assumes rhs: "ivp_f i = (\<lambda>(t, x). A x)"
  assumes time: "ivp_T i = UNIV"
  assumes domain: "ivp_X i = UNIV"
  assumes t0: "ivp_t0 i = s"
begin

lemma exp_is_solution: "is_solution (\<lambda>t. exp ((t - t0) *\<^sub>R A) x0)"
  by (auto intro!: is_solutionI derivative_eq_intros
    simp: rhs domain has_vector_derivative_def blinop.bilinear_simps exp_times_scaleR_commute)

sublocale has_solution
  by unfold_locales (rule exI[where P=is_solution, OF exp_is_solution])

sublocale unique_solution
proof(rule unique_solutionI[OF exp_is_solution])
  fix s t assume "is_solution s" and "t \<in> T"
  then have [derivative_intros]: "(s has_derivative (\<lambda>h. h *\<^sub>R A (s t))) (at t)" for t
    by (auto dest!: is_solutionD(2) simp: has_vector_derivative_def rhs time)
  have "((\<lambda>t. exp (-(t - t0) *\<^sub>R A) (s t)) has_derivative (\<lambda>_. 0)) (at t)"
    (is "(?es has_derivative _) _")
    for t
    by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def
      blinop.bilinear_simps)
  from has_derivative_zero_constant[OF _ this]
  obtain c where c: "?es = (\<lambda>_. c)"
    by (auto simp: time)
  hence "(\<lambda>t. (exp ((t - t0) *\<^sub>R A) * (exp (-((t - t0) *\<^sub>R A)))) (s t)) = (\<lambda>t. exp ((t - t0) *\<^sub>R A) c)"
    by (metis (no_types, hide_lams) blinop_apply_times_blinop real_vector.scale_minus_left)
  then have s_def: "s = (\<lambda>t. exp ((t - t0) *\<^sub>R A) c)"
    by (simp add: exp_minus_inverse)
  from \<open>is_solution s\<close> s_def t0 is_solution_def
  have "exp ((t0 - t0) *\<^sub>R A) c = x0" by simp
  hence "c = x0" by (simp add: )
  thus "s t = exp ((t - t0) *\<^sub>R A) x0" using s_def by simp
qed

end

end
