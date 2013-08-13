header{* Examples *}
theory Euler_Ex
  imports Runge_Kutta "~~/src/HOL/Decision_Procs/Approximation"
begin
text{*\label{sec:example}*}

subsection {* Generic setup for examples *}

locale example_aux = fixes t0' x0' ::float and b r T B L B'::real
  assumes interval_pos: "t0' \<le> T"
  assumes B_nonneg: "B \<ge> 0"
  assumes B'_nonneg: "B' \<ge> 0"
begin

definition "h = \<bar>r / 2\<bar> * L / B' / (exp (L * (T - t0') + 1) - 1)"

end

text{* Additional assumptions depending on bounds *}

locale example_ivp = example_aux +
  fixes h' T':: float and e'::int and f :: "real \<times> real \<Rightarrow> real"
  assumes h': "0 < h'" "h' \<le> h" and e': "2 powr - e' \<le> B' / 2 * h'"  and T': "t0' \<le> T'" "T' \<le> min T (t0' + \<bar>b\<bar>/B)"
begin

lemma interval_nonneg': "t0' \<le> T"
  using interval_pos T' B_nonneg by (auto intro: divide_nonneg_nonneg)

text {* Definition of the IVP *}

definition i where "i =
  \<lparr>ivp_f = f,
  ivp_t0 = t0', ivp_x0 = x0',
  ivp_I = {t0'..T'},
  ivp_D = {x0' - \<bar>b\<bar>..x0' + \<bar>b\<bar>}\<rparr>"

lemma h_pos: "h > 0"
  using h' by simp

end

sublocale example_ivp \<subseteq> ivp i
  using interval_nonneg' T'
  by unfold_locales (auto simp add: i_def less_eq_float_def)

definition (in example_ivp) Delta :: "nat \<Rightarrow> float" where
  "Delta j = t0' + Float (int j) 0 * h'"

sublocale example_ivp \<subseteq> grid_from: grid_from Delta t0'
  using h' by unfold_locales (auto intro!: mult_right_mono
    simp: Delta_def less_float_def less_eq_float_def)

lemma (in example_ivp) step_eq_h: "stepsize j = h'"
  unfolding stepsize_def by(auto simp: Delta_def field_simps)

lemma (in example_ivp) max_step_eq_h: "max_stepsize j = h'"
  unfolding max_stepsize_def
  apply (rule Max_eqI)
  using step_eq_h by auto

lemma le_imp_less:
  fixes z::real
  shows "a \<le> z \<Longrightarrow> a < 1 + z" by simp

locale example = example_ivp +
  fixes f_float :: "float \<times> float \<Rightarrow> float" and f'
  assumes derivative: "(f has_derivative f' tx) (at tx)"
  assumes f_bounded: "s \<in> I \<Longrightarrow> x \<in> D \<Longrightarrow> \<bar>f (s, x)\<bar> \<le> B"
  assumes f'_bounded:
    "s \<in> I \<Longrightarrow> x \<in> D \<Longrightarrow> \<bar>dx\<bar> \<le> B \<Longrightarrow> \<bar>f' (s, x) (1, dx)\<bar> \<le> 2 * B'"
  assumes lipschitz:
    "lipschitz {x0 - \<bar>b\<bar> - \<bar>r\<bar>..x0 + \<bar>b\<bar> + \<bar>r\<bar>} (\<lambda>x. f (t, x)) L"
    "L \<ge> 0"
  assumes f_approx:
    "dist (f (tf, xf)) (f_float (tf, xf)) \<le> B' / 2 * stepsize j"

sublocale example \<subseteq> max_step1 Delta T' L B' "r / 2"
  apply unfold_locales
  unfolding max_step_eq_h
  using h'
  using h_def T'
  apply (simp add: Delta_def)
proof -
  case goal1
  moreover
  have "\<bar>r\<bar> * L / (2 * B' * (exp (L * (T - real t0') + 1) - 1)) \<le> \<bar>r\<bar> * L / (2 * B' * (exp (L * (real T' - real t0') + 1) - 1))"
    apply (cases "B' = 0", simp)
    using T' lipschitz B'_nonneg interval_notempty interval_nonneg' B_nonneg
    apply (auto
      intro!: min_max.le_supI1 mult_left_mono divide_left_mono mult_nonneg_nonneg mult_pos_pos
      add_nonneg_pos
      simp: diff_less_iff diff_le_iff less_eq_float_def
    ) done
  ultimately show ?case by simp
qed

sublocale example \<subseteq> bounded_deriv: ivp_bounded_derivative i B f' B'
  using f_bounded derivative f'_bounded
  by unfold_locales (simp_all add: i_def)

sublocale example \<subseteq> ivp_on_interval i T'
  using iv_defined
  by unfold_locales (auto simp: i_def)

sublocale example \<subseteq> rectangle i T' "\<bar>b\<bar>"
  by unfold_locales (auto simp: i_def)

sublocale example \<subseteq> cont: continuous I D f
  using derivative
  apply unfold_locales
  apply (intro differentiable_imp_continuous_on)
  apply (auto simp add: differentiable_on_def differentiable_def
    has_vector_derivative_def i_def
    intro: has_derivative_at_within differentiable_imp_continuous_on)
  done

sublocale example \<subseteq> sol_in_rect: solution_in_rectangle i T' "\<bar>b\<bar>" B
  using f_bounded T' continuous
  by unfold_locales (auto simp add: i_def)

sublocale example \<subseteq> unique: unique_on_rectangle i T' "\<bar>b\<bar>" B L
  "{x0 - abs b - abs r..x0 + abs b + abs r}"
  using lipschitz by unfold_locales (auto simp: i_def)

sublocale example \<subseteq> euler_rounded_on_rectangle i Delta t0' x0' T' "\<bar>b\<bar>" "r" L B B' f' f_float e'
proof
  show "t0 = t0'" by (simp add: i_def)
next
  fix j x
  show "dist (ivp_f i (case (Delta j, x) of (x, y) \<Rightarrow> (real x, y)))
        (real (f_float (Delta j, x)))
       \<le> B' / 2 * stepsize j"
    using Bf'_nonneg grid_stepsize_nonneg f_approx
    by (auto simp add: i_def intro!: mult_nonneg_nonneg)
next
  show "dist (ivp_x0 i) (real x0') \<le> B' / L * (exp 1 - 1) * grid.stepsize (\<lambda>x. real (Delta x)) 0"
    using Bf'_nonneg unique.lipschitz
    by (auto simp add: i_def diff_le_iff
      intro!: divide_nonneg_nonneg mult_nonneg_nonneg grid_stepsize_nonneg)
next
  fix j assume "Delta j \<le> T'"
  with e' show "2 powr - e' \<le> B' / 2 * grid.stepsize (\<lambda>x. real (Delta x)) j"
    by (simp add: step_eq_h)
qed

subsection{* $\dot{x}~t := x^2 - t$ *}

text{* Definitions for bounds *}

locale example1_aux = fixes t0' x0' :: float and b r T::real
  assumes interval_pos: "t0' \<le> T"
begin

definition "B = (max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar>)\<^sup>2 + max \<bar>T\<bar> \<bar>t0'\<bar>"

definition "L = 2 * max \<bar>x0' - abs b - abs r\<bar> \<bar>x0' + abs b + abs r\<bar>"

definition "B' = (max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar>) * B + 0.5"

end

sublocale example1_aux \<subseteq> ex_aux: example_aux t0' x0' b r T B L B'
using interval_pos
by unfold_locales (auto simp: B_def B'_def bounded_abs mult_nonneg_nonneg)

locale example1 = example1_aux +
  fixes h' T' :: float and e'::int
  assumes step_bounds: "h' \<in> {0<..h}"
  assumes interval_bounds: "T' \<in> {t0'..min T (real t0' + \<bar>b\<bar> / B)}"
  assumes precision: "2 powr (- e') \<le> B' / 2 * real h'"
begin

definition "f = (\<lambda>(t, x). (x^2 - t))"

definition "f' = (\<lambda>tx (dt, dx). 2 * snd tx * dx - dt)"

end

sublocale example1 \<subseteq> ex_ivp: example_ivp t0' x0' b r T B L B' h' T' e' f
  using step_bounds interval_bounds precision
  by unfold_locales (auto simp: less_eq_float_def less_float_def)

context example1
begin

lemma derivative_of_square_x_minus_t:
  fixes t x::real
  shows "((\<lambda>(t, x). x^2 - t) has_derivative (\<lambda>(dt, dx). 2*x*dx - dt)) (at (t, x))"
  by (auto intro!: FDERIV_eq_intros)

lemma derivative:
  fixes tx::"real \<times> real"
  shows "(f has_derivative f' tx) (at tx)"
  using derivative_of_square_x_minus_t[of "snd tx" "fst tx"]
  by (simp add: f_def f'_def i_def)

lemma f'_bounded:
  assumes "s \<in> I"
  assumes "x \<in> D"
  assumes "\<bar>dx\<bar> \<le> B"
  shows "\<bar>f' (s, x) (1, dx)\<bar> \<le> 2 * B'"
proof -
  have "\<bar>2 * x * dx - 1\<bar> \<le> \<bar>2 * x * dx\<bar> + 1" by simp
  also have "\<bar>2 * x * dx\<bar> \<le> 2 * max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar> * B"
    using assms
    unfolding abs_mult
    by (intro mult_mono) (simp_all add: i_def bounded_abs)
  finally show ?thesis 
    by (simp add: algebra_simps f'_def B'_def)
qed

lemma f_bounded:
  fixes x s
  assumes "s \<in> I"
  assumes "x \<in> D"
  shows "\<bar>f (s, x)\<bar> \<le> B"
proof -
  have "abs (x\<^sup>2 - s) \<le> x^2 + abs s"
    by (metis abs_power2 abs_triangle_ineq4)
  also have "abs s \<le> max (abs t0') (abs T)"
    using assms using T' by (auto intro: bounded_abs simp: i_def)
  also have "x^2 \<le> max (abs (x0-abs b)) (abs (x0+abs b)) ^ 2" using assms
    by (auto simp add: real_abs_le_square_iff[symmetric] bounded_abs i_def)
  finally
  show ?thesis using T'
    by (simp add: min_max.sup_commute B_def ex_ivp.i_def) (simp add: f_def)
qed

lemma lipschitz:
  fixes t
  shows "lipschitz {x0 - \<bar>b\<bar> - \<bar>r\<bar>..x0 + \<bar>b\<bar> + \<bar>r\<bar>} (\<lambda>x. f (t, x)) L" "L \<ge> 0"
unfolding lipschitz_def
proof safe
  fix x y::real
  assume H:
    "x \<in> {x0 - abs b - abs r.. x0 + abs b + abs r}"
    "y \<in> {x0 - abs b - abs r..x0+abs b+abs r}"
  have "abs (x^2 - y^2) = abs (x + y)* abs(x - y)"
    by (auto simp add: power2_eq_square square_diff_square_factored abs_mult)
  also have "abs (x + y) \<le> L"
  proof -
    have "abs (x + y) \<le> abs x + abs y" by simp
    also have "abs x \<le> max \<bar>x0 - abs b - abs r\<bar> \<bar>x0 + abs b + abs r\<bar>" using H
      by (simp add: bounded_abs)
    also have "abs y \<le> max \<bar>x0 - abs b - abs r\<bar> \<bar>x0 + abs b + abs r\<bar>" using H
      by (simp add: bounded_abs)
    finally show "abs (x + y) \<le> L" by (simp add: L_def i_def)
  qed
  finally
  show "dist (f (t, x)) (f (t, y)) \<le> L * dist x y"
    by (auto simp: dist_real_def field_simps f_def) (metis abs_ge_zero mult_right_mono)
qed (simp add: L_def)

end

sublocale example1 \<subseteq> ex: example t0' x0' b r T B L B' h' T' e' f f f'
using derivative f_bounded f'_bounded lipschitz B'_nonneg
by unfold_locales (auto simp: f_def mult_nonneg_nonneg grid_stepsize_nonneg)

subsubsection {* Concrete computation *}

definition t0'::float where [code_unfold]:"t0' = 0"
definition x0'::float where [code_unfold]:"x0' = 0"
definition b::float where [code_unfold]:"b = 1"
definition r::float where [code_unfold]:"r = Float 1 -8"
definition T::float where [code_unfold]:"T = 1"
definition T'::float where [code_unfold]:"T' = Float 1 -1"
definition H::float where [code_unfold]:"H = Float 1 -14"
definition e'::int where [code_unfold]:"e' = 14"

interpretation E: example1_aux t0' x0' b r T
  by unfold_locales (simp_all add: t0'_def r_def less_eq_float_def[symmetric] T_def)

text {* Correctness of the bounds we have chosen *}

lemma
  compute_powr_numeral:
    assumes "x > 0"
    shows "x powr numeral k = x ^ numeral k"
    "x powr neg_numeral k = 1 / x ^ numeral k"
  by (simp_all only: powr_realpow[OF `x>0`, symmetric] neg_numeral_def
    powr_minus inverse_eq_divide real_of_nat_numeral)

interpretation E: example1 t0' x0' b r T H T' e'
proof unfold_locales
  show "H \<in> {0<..E.h}" unfolding E.h_def
    unfolding E.L_def E.B'_def E.B_def
    unfolding E.h_def r_def T_def b_def t0'_def x0'_def H_def
    by (simp add: H_def is_float_pos_def[symmetric])
       (approximation 10)
next
  show "T' \<in> {t0'..min T (t0' + \<bar>real b\<bar> / E.B)}"
    unfolding E.h_def E.L_def E.B'_def E.B_def
    unfolding  r_def T_def b_def t0'_def x0'_def H_def e'_def T'_def
    by simp
next
  have "e' > 0" by (simp add: e'_def)
  hence r: "2 powr -e' = inverse (2^nat e')" by (simp add: powr_realpow[symmetric] powr_minus)
  thus "2 powr -e' \<le> example1_aux.B' t0' x0' (real b) (real T) / 2 * real H"
    unfolding E.h_def E.L_def E.B'_def E.B_def r
    unfolding  r_def T_def b_def t0'_def x0'_def H_def e'_def
    by simp
qed

definition "error_bound = 2 * E.B'/ E.L * (exp (E.L * real (T' - t0') + 1) - 1) * H"

definition "error_bound' = 0.001"

lemma error_bound: "error_bound \<le> error_bound'"
  unfolding error_bound_def error_bound'_def
  unfolding E.h_def E.L_def E.B'_def E.B_def
  unfolding E.h_def r_def T_def b_def t0'_def x0'_def H_def T'_def
  by simp (approximation 20)

definition i_max::nat where "i_max = 2 ^ 13"

lemma [code_unfold]: -- {* Workaround to avoid non-pattern @{term "0::int"} in LHS of code equations *}
  "0 = int_of_integer 0"
  by simp

lemma T_max: "E.Delta i_max = 0.5" by eval

lemma i_max_correct: "\<And>i. i \<le> i_max \<Longrightarrow> E.Delta i \<le> T'"
  unfolding E.Delta_def
  unfolding H_def T'_def t0'_def i_max_def
  by simp

definition "euler_result i = euler_float e' (\<lambda>(t, x). x\<^sup>2 - t) x0' E.Delta i"

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

lemma euler_result: "euler_result i_max = Float -33140952 -28" by eval

lemma "euler_result i_max \<in> {-0.1235..-0.1234}"
  by (simp add: euler_result)

lemma sol_dec: "E.solution 0.5 \<in> {-0.1245..-0.1224}"
proof -
  have "{real (euler_result i_max) -
     error_bound'..real (euler_result i_max) +
                   error_bound'} \<subseteq> {-0.1245..-0.1224}"
    unfolding euler_result error_bound'_def T_max
    by simp
  thus ?thesis apply (rule set_mp)
  using sol_bounds[OF le_refl] unfolding T_max .
qed

text {* How low could the Precision have been? *}

definition i_max'::"nat \<Rightarrow> nat" where "i_max' P = 2 ^ (P - 1)"
definition H'::"nat \<Rightarrow> float" where "H' P = Float 1 (- P)"
definition Delta' :: "nat \<Rightarrow> nat \<Rightarrow> float" where
  "Delta' P j = t0' + Float j 0 * H' P"

definition "euler_result' P = euler_float P (\<lambda>(t, x). x^2 - t) x0' (Delta' P) (i_max' P)"
lemma "euler_result' 11 \<in> {-0.1235..-0.1234}" by simp eval
lemma "euler_result' 10 \<notin> {-0.1235..-0.1234}" by simp eval

end
