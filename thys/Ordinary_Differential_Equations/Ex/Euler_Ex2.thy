theory Euler_Ex2
imports Euler_Ex
begin

subsection{* $\dot{x}~t := x$ *}

text {* Solution $x(t) = e^t$. *}

text{* Definitions for bounds *}

locale example2_aux = fixes t0' x0' :: float and b r T::real
  assumes interval_pos: "t0' \<le> T"
begin

definition "B == max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar>"

definition "L = 1"

definition "B' = 1 / 2 * B"

end

sublocale example2_aux \<subseteq> ex_aux: example_aux t0' x0' b r T B L B'
using interval_pos
by unfold_locales (auto simp: B_def B'_def bounded_abs mult_nonneg_nonneg)

locale example2 = example2_aux +
  fixes h' T' :: float and e'::int
  assumes step_bounds: "h' \<in> {0<..h}"
  assumes interval_bounds: "T' \<in> {t0'..min T (real t0' + \<bar>b\<bar> / B)}"
  assumes precision: "2 powr (- e') \<le> B' / 2 * real h'"
begin

definition "f = snd"

definition "f' = (\<lambda>tx dtx. snd dtx)"

end

sublocale example2 \<subseteq> ex_ivp: example_ivp t0' x0' b r T B L B' h' T' e' f
  using step_bounds interval_bounds precision
  by unfold_locales (auto simp: less_eq_float_def less_float_def)

context example2 begin

lemma derivative:
  fixes tx::"real \<times> real"
  shows "(f has_derivative f' tx) (at tx)"
  unfolding i_def f_def f'_def by (auto intro!: FDERIV_intros)

lemma f_bounded:
  fixes x s
  assumes "s \<in> I"
  assumes "x \<in> D"
  shows "\<bar>f (s, x)\<bar> \<le> B"
  using assms
  apply (simp add: ex_ivp.i_def f_def[symmetric] B_def)
  apply (simp add: f_def bounded_abs)
  done

lemma f'_bounded:
  assumes "s \<in> I"
  assumes "x \<in> D"
  assumes "\<bar>dx\<bar> \<le> B"
  shows "\<bar>f' (s, x) (1, dx)\<bar> \<le> 2 * B'"
using assms by (simp add: f'_def i_def B_def B'_def bounded_abs)

lemma lipschitz:
  shows "lipschitz {x0 - \<bar>b\<bar> - \<bar>r\<bar>..x0 + \<bar>b\<bar> + \<bar>r\<bar>} (\<lambda>x. x) L" "L \<ge> (0::real)"
  by (simp_all add: lipschitz_def L_def)

end

sublocale example2 \<subseteq> ex: example t0' x0' b r T B L B' h' T' e' f f f'
  using derivative f_bounded f'_bounded lipschitz B'_nonneg
  by unfold_locales (auto simp: f_def f'_def mult_nonneg_nonneg grid_stepsize_nonneg)

subsubsection {* Concrete computation *}

definition t0'::float where [code_unfold]:"t0' = 0"
definition x0'::float where [code_unfold]:"x0' = 1"
definition b::float where [code_unfold]:"b = 2"
definition r::float where [code_unfold]:"r = Float 1 -14"
definition T::float where [code_unfold]:"T = 1"
definition e'::int where [code_unfold]:"e' = 21"
definition T'::float where [code_unfold]:"T' = Float 5 -3"
definition H::float where [code_unfold]:"H = Float 1 -20"

interpretation E: example2_aux t0' x0' b r T
  by unfold_locales (simp_all add: t0'_def r_def less_eq_float_def[symmetric] T_def)

text {* Correctness of the bounds we have chosen *}

interpretation E: example2 t0' x0' b r T H T' e'
proof unfold_locales
  show "H \<in> {0<..E.h}" unfolding E.h_def
    unfolding E.L_def E.B'_def E.B_def
    unfolding E.h_def T_def b_def t0'_def x0'_def H_def r_def
    apply (simp add: is_float_pos_def[symmetric] max_def)
    apply (approximation 10)
    done
next
  show "T' \<in> {t0'..min T (t0' + \<bar>real b\<bar> / E.B)}"
    unfolding E.h_def E.L_def E.B'_def E.B_def
    unfolding r_def T_def b_def t0'_def x0'_def H_def e'_def T'_def
    using lapprox_rat[of 12 2 3] lapprox_rat_nonneg
    by (simp add: max_def)
next
  have "e' > 0" by (simp add: e'_def)
  hence r: "2 powr -e' = inverse (2^nat e')" by (simp add: powr_realpow[symmetric] powr_minus)
  thus "2 powr -e' \<le> E.B' / 2 * real H"
    unfolding E.h_def E.L_def E.B'_def E.B_def r
    unfolding  r_def T_def b_def t0'_def x0'_def H_def e'_def
    by simp
qed

declare E.ex_ivp.Delta_def [code] -- {* explicit is better than implicit *}

hide_const error_bound error_bound'

definition "error_bound = 2 * E.B'/ E.L * (exp (E.L * real (T' - t0') + 1) - 1) * H"

(* obtained as an approximation of error_bound *)

definition "error_bound' = 0.0000123"

lemma error_bound: "error_bound \<le> error_bound'"
  unfolding error_bound_def error_bound'_def
  unfolding E.h_def E.L_def E.B'_def E.B_def
  unfolding E.h_def r_def T_def b_def t0'_def x0'_def H_def T'_def
  by simp (approximation 10)

definition i_max::nat where "i_max = 2 ^ 19"

lemma T_max: "E.Delta i_max = 0.5" by eval  

lemma i_max_correct: "\<And>i. i \<le> i_max \<Longrightarrow> E.Delta i \<le> T'"
  unfolding E.Delta_def
  unfolding H_def T'_def t0'_def i_max_def
  by simp

hide_const euler_result
definition "euler_result i = euler_float e' E.f x0' E.Delta i"

lemma convergence:
  assumes i: "i \<le> i_max"
  shows "dist (E.solution (real (E.Delta i))) (real (euler_result i)) \<le> error_bound'"
  using E.convergence_float[OF i_max_correct[OF i]]
  unfolding E.max_step_eq_h error_bound_def[symmetric]
  unfolding euler_result_def E.f_def
  using error_bound by simp

lemma sol_bounds:
  assumes i: "i \<le> i_max"
  shows "E.solution (E.Delta i) \<in> {euler_result i - error_bound'..euler_result i + error_bound'}"
  using convergence[OF i] by (auto simp add: dist_real_def)

lemma euler_result: "euler_result i_max = Float 3625575212341 -41" by eval

lemma sol_dec: "E.solution 0.5 \<in> {1.648708..1.648734}"
proof -
  have "{real (euler_result i_max) -
     error_bound'..real (euler_result i_max) +
                   error_bound'} \<subseteq> {1.648708..1.648734}"
    unfolding euler_result error_bound'_def T_max
    by (auto simp add: powr_minus)
  thus ?thesis apply (rule set_mp)
  using sol_bounds[OF le_refl] unfolding T_max .
qed

text {* Comparison with real result *}

lemma exp_has_vector_derivative: "(exp has_vector_derivative exp t) (at t)"
  using DERIV_exp[of t] unfolding DERIV_conv_has_vector_derivative .

lemma "E.is_solution exp"
proof
  show "exp E.t0 = E.x0" by (simp add: E.i_def) (simp add: t0'_def x0'_def)
next
  fix t
  assume "t \<in> E.I"
  from exp_has_vector_derivative
  show "(exp has_vector_derivative ivp_f E.i (t, exp t)) (at t within E.I)"
    by (simp add: E.i_def) (simp add: E.f_def has_vector_derivative_at_within)
  have "-1 \<le> t \<and> t \<le> 5/8 \<longrightarrow> exp t \<le> 3" by (approximation 10)
  moreover have "-1 \<le> t \<and> t \<le> 5/8 \<longrightarrow> -1 \<le> exp t" by (approximation 10)
  ultimately show "exp t \<in> E.D" using `t \<in> E.I`
    by (simp add: E.i_def) (simp add: t0'_def x0'_def b_def T'_def)
qed

definition "error_bound'' = 0.00000055"

lemma real_error:
  shows "dist (exp (E.Delta i_max)) (real (euler_result i_max)) \<le> error_bound''"
  unfolding euler_result T_max dist_real_def error_bound''_def by (approximation 80)

lemma "error_bound' / error_bound'' > (22::real)"
  by (simp add: error_bound'_def error_bound''_def)

end
