theory Euler_Ex3
  imports Euler_Ex
begin

subsection{* $\dot{x}~t := x^2 + t^2$ *}

text{* Definitions for bounds *}

locale example3_aux = fixes t0' x0' :: float and b r T::real
  assumes interval_pos: "t0' \<le> T"
begin

definition "B = (max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar>)\<twosuperior> + (max \<bar>T\<bar> \<bar>t0'\<bar>)\<twosuperior>"

definition "L = 2 * max \<bar>x0' - abs b - abs r\<bar> \<bar>x0' + abs b + abs r\<bar>"

definition "B' = (max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar>) * B + 0.5"

end

sublocale example3_aux \<subseteq> ex_aux: example_aux t0' x0' b r T B L B'
using interval_pos
by unfold_locales (auto simp: B_def B'_def bounded_abs mult_nonneg_nonneg)

locale example3 = example3_aux +
  fixes h' T' :: float and e'::int
  assumes step_bounds: "h' \<in> {0<..h}"
  assumes interval_bounds: "T' \<in> {t0'..min T (real t0' + \<bar>b\<bar> / B)}"
  assumes precision: "2 powr (- e') \<le> B' / 2 * real h'"
  assumes time: "t0' = 0" "T \<le> 1/2"
begin

definition "f = (\<lambda>(t, x). (x^2 + t^2))"

definition "f' = (\<lambda>tx (dt, dx). 2 * snd tx * dx + 2 * fst tx * dt)"

end

sublocale example3 \<subseteq> ex_ivp: example_ivp t0' x0' b r T B L B' h' T' e' f
  using step_bounds interval_bounds precision
  by unfold_locales (auto simp: less_eq_float_def less_float_def)

context example3
begin

lemma derivative_of_square_x_plus_square_t:
  fixes t x::real
  shows "((\<lambda>(t, x). x^2 + t^2) has_derivative (\<lambda>(dt, dx). 2*x*dx + 2*t*dt)) (at (t, x))"
proof -
  have "((\<lambda>tx. (tx \<bullet> (0,1))^2 + (tx \<bullet> (1,0))^2) has_derivative
    (\<lambda>dtx. 2 * ((t, x) \<bullet> (0, 1)) * (dtx \<bullet> (0, 1)) + 2 * ((t, x) \<bullet> (1, 0)) * (dtx \<bullet> (1, 0)))) (at (t, x))"
  proof -
    have f: "(\<lambda>x. (x \<bullet> (0,1))\<twosuperior>) = (\<lambda>x. x^2)o(\<lambda>x. x \<bullet> (0,1))" by auto
    have f': "(\<lambda>dtx. 2*((t, x) \<bullet> (0,1))*(dtx \<bullet> (0,1))) =
      (op * (of_nat 2 * ((t, x) \<bullet> (0,1)) ^ (2 - 1)))o(\<lambda>h. h \<bullet> (0,1))" by auto
    have "((\<lambda>x. (x \<bullet> (0,1))\<twosuperior>) has_derivative (\<lambda>h. 2 * ((t, x) \<bullet> (0,1)) * (h \<bullet> (0,1)))) (at (t, x))"
      unfolding f f'
      by (intro diff_chain_at has_derivative_intros FDERIV_power[unfolded FDERIV_conv_has_derivative])
    moreover
    have f: "(\<lambda>x. (x \<bullet> (1,0))\<twosuperior>) = (\<lambda>x. x^2)o(\<lambda>x. x \<bullet> (1,0))" by auto
    have f': "(\<lambda>dtx. 2*((t, x) \<bullet> (1,0))*(dtx \<bullet> (1,0))) =
      (op * (of_nat 2 * ((t, x) \<bullet> (1,0)) ^ (2 - 1)))o(\<lambda>h. h \<bullet> (1,0))" by auto
    have "((\<lambda>x. (x \<bullet> (1,0))\<twosuperior>) has_derivative (\<lambda>h. 2 * ((t, x) \<bullet> (1,0)) * (h \<bullet> (1,0)))) (at (t, x))"
      unfolding f f'
      by (intro diff_chain_at has_derivative_intros FDERIV_power[unfolded FDERIV_conv_has_derivative])
    ultimately
    show ?thesis by (intro has_derivative_intros)
  qed
  also have "(\<lambda>tx. (tx \<bullet> (0,1))\<twosuperior> + (tx \<bullet> (1,0))^2) = (\<lambda>(t, x). x^2 + t^2)"
    by auto
  also have "(\<lambda>dtx. 2 * ((t, x) \<bullet> (0,1)) * (dtx \<bullet> (0,1)) + 2 * ((t, x) \<bullet> (1,0)) * (dtx \<bullet> (1,0))) =
    (\<lambda>(dt, dx). 2 * x * dx + 2 * t * dt)"
    by auto
  finally show ?thesis .
qed

lemma derivative:
  fixes tx::"real \<times> real"
  shows "(f has_derivative f' tx) (at tx)"
  using derivative_of_square_x_plus_square_t[of "snd tx" "fst tx"]
  by (simp add: f_def f'_def i_def)

lemma f'_bounded:
  assumes "s \<in> I"
  assumes s: "s \<ge> 0" "s \<le> 0.5"
  assumes "x \<in> D"
  assumes "\<bar>dx\<bar> \<le> B"
  shows "\<bar>f' (s, x) (1, dx)\<bar> \<le> 2 * B'"
proof -
  have "\<bar>f' (s, x) (1, dx)\<bar> = \<bar>2 * x * dx + 2 * s\<bar>" by (simp add: f'_def)
  also have "\<dots> \<le> \<bar>2 * x * dx\<bar> + \<bar>2 * s\<bar>" by simp
  also have "\<bar>2 * x * dx\<bar> \<le> 2 * max \<bar>x0' - \<bar>b\<bar>\<bar> \<bar>x0' + \<bar>b\<bar>\<bar> * B"
    using assms
    unfolding abs_mult
    by (intro mult_mono) (simp_all add: i_def bounded_abs)
  also have "\<dots> + \<bar>2 * s\<bar> \<le> 2 * B'" using s by (simp add: B'_def)
  finally show ?thesis by simp
qed

lemma f_bounded:
  fixes x s
  assumes "s \<in> I"
  assumes "x \<in> D"
  shows "\<bar>f (s, x)\<bar> \<le> B"
proof -
  have "abs (x\<twosuperior> + s^2) \<le> x^2 + s^2"
    by (metis abs_of_nonneg order_eq_iff sum_power2_ge_zero)
  also have "s^2 \<le> max (abs t0) (abs T) ^ 2" using assms
    apply (auto simp add: real_abs_le_square_iff[symmetric] bounded_abs i_def)
    by (metis T'(2) bounded_abs min_max.le_inf_iff order_trans)
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

sublocale example3 \<subseteq> ex: example t0' x0' b r T B L B' h' T' e' f f f'
using derivative f_bounded f'_bounded lipschitz B'_nonneg
  apply unfold_locales
  apply (auto simp: f_def mult_nonneg_nonneg grid_stepsize_nonneg)
  using i_def
  apply (auto simp: f_def mult_nonneg_nonneg grid_stepsize_nonneg)
  apply (rule f'_bounded) using time interval_bounds
  apply (auto simp: f_def mult_nonneg_nonneg grid_stepsize_nonneg)
  done

subsubsection {* Concrete computation *}

definition t0'::float where [code_unfold]:"t0' = 0"
definition x0'::float where [code_unfold]:"x0' = 1"
definition b::float where [code_unfold]:"b = 1"
definition r::float where [code_unfold]:"r = Float 1 -8"
definition T::float where [code_unfold]:"T = Float 1 -1"
definition T'::float where [code_unfold]:"T' = Float 1 -3"
definition H::float where [code_unfold]:"H = Float 1 -20"
definition e'::int where [code_unfold]:"e' = 20"

interpretation E: example3_aux t0' x0' b r T
  by unfold_locales (simp_all add: t0'_def r_def less_eq_float_def[symmetric] T_def)

text {* Correctness of the bounds we have chosen *}

interpretation E: example3 t0' x0' b r T H T' e'
proof unfold_locales
  show "H \<in> {0<..E.h}" unfolding E.h_def
    unfolding E.L_def E.B'_def E.B_def
    unfolding E.h_def r_def T_def b_def t0'_def x0'_def H_def
    by (simp add: H_def is_float_pos_def[symmetric] max_def)
       (approximation 10)
next
  show "T' \<in> {t0'..min T (t0' + \<bar>real b\<bar> / E.B)}"
    unfolding E.h_def E.L_def E.B'_def E.B_def
    unfolding  r_def T_def b_def t0'_def x0'_def H_def e'_def T'_def
    apply (simp add: max_def)
    apply (approximation 10)
    done
next
  have "e' > 0" by (simp add: e'_def)
  hence r: "2 powr -e' = inverse (2^nat e')" by (simp add: powr_realpow[symmetric] powr_minus)
  thus "2 powr -e' \<le> E.B' / 2 * real H"
    unfolding E.h_def E.L_def E.B'_def E.B_def r
    unfolding  r_def T_def b_def t0'_def x0'_def H_def e'_def
    apply (simp add: max_def)
    apply (approximation 10)
    done
next
  show "t0' = 0" by (simp add: t0'_def)
  show "T \<le> 1/2" by (simp add: T_def)
qed

definition "error_bound3 = 2 * E.B'/ E.L * (exp (E.L * real (T' - t0') + 1) - 1) * H"

definition "error_bound3' = 0.0000151"

lemma error_bound: "error_bound3 \<le> error_bound3'"
  unfolding error_bound3_def error_bound3'_def
  unfolding E.h_def E.L_def E.B'_def E.B_def
  unfolding E.h_def r_def T_def b_def t0'_def x0'_def H_def T'_def
  by simp (approximation 10)

definition i_max::nat where "i_max = 2 ^ 17"

lemma T_max: "E.Delta i_max = 0.125" by eval

lemma i_max_correct: "\<And>i. i \<le> i_max \<Longrightarrow> E.Delta i \<le> T'"
  unfolding E.Delta_def
  unfolding H_def T'_def t0'_def i_max_def
  by simp

definition "euler_result3 i = euler_float e' (\<lambda>(t, x). x\<twosuperior> + t\<twosuperior>) x0' E.Delta i"

lemma convergence:
  assumes i: "i \<le> i_max"
  shows "dist (E.solution (real (E.Delta i))) (real (euler_result3 i)) \<le> error_bound3'"
  using E.convergence_float[OF i_max_correct[OF i]]
  unfolding E.max_step_eq_h error_bound3_def[symmetric]
  unfolding euler_result3_def E.f_def
  using error_bound
  by simp

lemma sol_bounds:
  assumes i: "i \<le> i_max"
  shows "E.solution (E.Delta i) \<in> {euler_result3 i - error_bound3'..euler_result3 i + error_bound3'}"
  using convergence[OF i] by (auto simp add: dist_real_def)

lemma euler_result[code_unfold]: "euler_result3 i_max = Float 1257352878524 -40" by eval

lemma sol_dec: "E.solution 0.125 \<in> {1.14354..1.14358}"
proof -
  have "{real (euler_result3 i_max) -
     error_bound3'..real (euler_result3 i_max) +
                   error_bound3'} \<subseteq>  {1.14354..1.14358}"
    unfolding euler_result error_bound3'_def T_max
    by simp
  thus ?thesis
    apply (rule set_mp)
    using sol_bounds[OF le_refl] unfolding T_max .
qed

lemma error: "1.1435598 - 1.143552 \<le> 1/(10::real)^5" by simp

text {* Comparison with bounds analytically obtained by Walter~\cite{walter} in section 9,
  Example V. *}

text {* First approximation. *}

notepad begin
  assume Walter: "\<And>x. E.solution x \<in> {1/(1 - x)..tan(x + pi/4)}"
  let ?x = "0.125::real"
  value "1 / (1 - 0.125)"
  have "1/(1-?x) \<in> {1.142857139 .. 1.142857146}" by simp
  moreover
  value "tan (0.125 + pi/4)"
  have "tan(?x + pi/4) \<in> {1.287426935 .. 1.287426955}"
    by (approximation 40)
  ultimately
  have "{1/(1-?x)..tan(?x + pi/4)} \<subseteq> {1.142857139 .. 1.287426955}" by simp
  with Walter have "E.solution ?x \<in> {1.142857139 .. 1.287426955}" by blast
end

text {* Better approximation. *}

notepad begin
  assume Walter: "\<And>x. E.solution x \<in> {1/(1-x)..16 / (16 - 17*x)}"
  let ?x = "0.125::real"
  value "1 / (1 - ?x)"
  have "1/(1-?x) \<in> {1.142857139 .. 1.142857146}" by simp
  moreover
  value "16 / (16 - 17*?x)"
  have "16 / (16 - 17*?x) \<in> {1.153153151 .. 1.153153155}"
    by (approximation 40)
  ultimately
  have "{1/(1-?x)..16 / (16 - 17*?x)} \<subseteq> {1.142857139 .. 1.153153155}" by simp
  with Walter have "E.solution ?x \<in> {1.142857139 .. 1.153153155}" by blast
  have error: "16 / (16 - 17*?x) - 1 / (1 - ?x) \<ge> 1/10^2" by (approximation 20)
end

end
