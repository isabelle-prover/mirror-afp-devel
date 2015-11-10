section{* Runge-Kutta methods*}
theory Runge_Kutta
imports
  One_Step_Method
  "~~/src/HOL/Library/Float"
  "../../Affine_Arithmetic/Executable_Euclidean_Space"
begin

text{*\label{sec:rk}*}

subsection {* Definitions *}
text{*\label{sec:rk-definition}*}

declare setsum.cong[fundef_cong]
fun rk_eval :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real\<times>'a::real_vector \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "rk_eval A c f t h x j =
  f (t + h * c j, x + h *\<^sub>R (\<Sum>l=1 ..< j. A j l *\<^sub>R rk_eval A c f t h x l))"

primrec rk_eval_dynamic :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real\<times>'a::{comm_monoid_add, scaleR} \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "rk_eval_dynamic A c f t h x 0 = (\<lambda>i. 0)"
| "rk_eval_dynamic A c f t h x (Suc j) =
  (let K = rk_eval_dynamic A c f t h x j in
  K(Suc j:=f (t + h * c (Suc j), x + h *\<^sub>R (\<Sum>l=1..j. A (Suc j) l *\<^sub>R K l))))"

definition rk_increment where
  "rk_increment f s A b c h t x = (\<Sum>j=1..s. b j *\<^sub>R rk_eval A c f t h x j)"

definition rk_increment' where
  "rk_increment' error f s A b c h t x =
  eucl_down error (\<Sum>j=1..s. b j *\<^sub>R rk_eval A c f t h x j)"

definition euler_increment where
  "euler_increment f = rk_increment f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler where
  "euler f = grid_function (discrete_evolution (euler_increment f))"

definition euler_increment' where
"euler_increment' e f = rk_increment' e f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler' where
  "euler' e f = grid_function (discrete_evolution (euler_increment' e f))"


subsection {* Euler method is consistent *}
text{*\label{sec:rk-euler-cons}*}

lemma euler_increment:
  fixes f::"_ \<Rightarrow> 'a::real_vector"
  shows "euler_increment f h t x = f (t, x)"
  unfolding euler_increment_def rk_increment_def
  by (subst rk_eval.simps) (simp del: rk_eval.simps)

lemma euler_float_increment:
  fixes f::"_ \<Rightarrow> 'a::executable_euclidean_space"
  shows "euler_increment' e f h t x = eucl_down e (f (t, x))"
  unfolding euler_increment'_def rk_increment'_def
  by (subst rk_eval.simps) (simp del: rk_eval.simps)

lemma euler_lipschitz:
  fixes x::"real \<Rightarrow> real"
  fixes f::"_ \<Rightarrow> 'a::real_normed_vector"
  assumes t: "t \<in> {t0..T}"
  assumes lipschitz: "\<forall>t\<in>{t0..T}. lipschitz D' (\<lambda>x. f (t, x)) L"
  shows "lipschitz D' (euler_increment f h t) L"
  using t lipschitz
  by (simp add: lipschitz_def euler_increment del: One_nat_def)

subsection {* Set-Based Consistency of Euler Method *}
text {*\label{sec:setconsistent}*}

locale derivative_set_bounded = derivative_on_convex +
  fixes  F F'
  assumes f_set_bounded: "bounded F" "\<And>t x. t\<in>T \<Longrightarrow> x\<in>X \<Longrightarrow> (x, f (t, x)) \<in> F"
  assumes f'_ivl_bounded: "is_interval F'" "bounded F'" "\<And>t x d. t\<in>T \<Longrightarrow> (x, d) \<in> F \<Longrightarrow>
    f' (t,x) (1, d) \<in> F'"
begin

lemma F_nonempty: "F \<noteq> {}"
  and F'_nonempty: "F' \<noteq> {}"
  using nonempty
  unfolding ex_in_conv[symmetric]
  by (auto intro!: f_set_bounded f'_ivl_bounded)

lemma euler_consistent_traj_set:
  fixes t
  assumes ht: "0 \<le> h" "t + h \<le> u"
  assumes T: "{t..u} \<subseteq> T"
  assumes x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within {t..u})"
  assumes x: "\<And>s. s \<in> {t..u} \<Longrightarrow> x s \<in> X"
  shows "x (t + h) - discrete_evolution (euler_increment f) (t + h) t (x t) \<in> op *\<^sub>R (h\<^sup>2 / 2) ` F'"
proof cases
  assume "h = 0"
  from F'_nonempty obtain f' where "f' \<in> F'" by auto
  from this `h = 0` show ?thesis
    by (auto simp: discrete_evolution_def)
next
  assume "h \<noteq> 0"
  from this ht have "t < u" by simp
  from ht have line_subset: "(\<lambda>ta. t + ta * h) ` {0..1} \<subseteq> {t..u}"
    by (auto intro!: order_trans[OF add_left_mono[OF mult_left_le_one_le]])
  hence line_in: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> 1 \<Longrightarrow> t + s * h \<in> {t..u}"
    by (rule set_mp) auto
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  let ?T = "{t..u}"
  from ht have subset: "{t .. t + h} \<subseteq> {t .. u}" by simp
  from `t < u` have "t \<in> ?T" by auto
  from `t < u` have tx: "t \<in> T" "x t \<in> X" using assms by auto
  from tx assms have "0 \<le> norm (f (t, x t))" by simp
  have x_diff: "\<And>s. s \<in> ?T \<Longrightarrow> x differentiable at s within ?T"
    by (rule differentiableI, rule x'[simplified has_vector_derivative_def])
  have f': "\<And>t x. t \<in> ?T \<Longrightarrow> x \<in> X \<Longrightarrow> (f has_derivative f' (t, x)) (at (t, x) within (?T \<times> X))"
    using T by (intro has_derivative_subset[OF f']) auto
  let ?p = "(\<lambda>t. f' (t, x t) (1, f (t, x t)))"
  def diff \<equiv> "\<lambda>n::nat. if n = 0 then x else if n = 1 then \<lambda>t. f (t, x t) else ?p"
  have diff_0[simp]: "diff 0 = x" by (simp add: diff_def)
  {
    fix m::nat and ta::real
    assume mta: "m < 2" "t \<le> ta" "ta \<le> t + h"
    have image_subset: "(\<lambda>xa. (xa, x xa)) ` {t..u} \<subseteq> {t..u} \<times> X"
      using assms by auto
    note has_derivative_in_compose[where f="(\<lambda>xa. (xa, x xa))" and g = f, derivative_intros]
    note has_derivative_subset[OF _ image_subset, derivative_intros]
    note f'[derivative_intros]
    note x'[simplified has_vector_derivative_def, derivative_intros]
    have [simp]: "\<And>c x'. c *\<^sub>R f' (ta, x ta) x' = f' (ta, x ta) (c *\<^sub>R x')"
      using mta ht assms by (auto intro!: f' linear_cmul[symmetric] has_derivative_linear)
    have "((\<lambda>t. f (t, x t)) has_vector_derivative f' (ta, x ta) (1, f (ta, x ta))) (at ta within {t..u})"
      unfolding has_vector_derivative_def
      using assms ht mta by (auto intro!: derivative_eq_intros)
    hence "(diff m has_vector_derivative diff (Suc m) ta) (at ta within {t..t + h})"
      using mta ht
      by (auto simp: diff_def intro!: has_vector_derivative_within_subset[OF _ subset] x')
  } note diff = this
  from taylor_up_within_vector[of 2 t "t + h" diff x t, OF _ _ diff] ht `h\<noteq>0`
  obtain tt where tt: "tt \<in> Basis \<rightarrow> {t <..< t + h}"
    and taylor: "x (t + h) = x t + h *\<^sub>R f (t, x t) + (h\<^sup>2/2) *\<^sub>R (\<Sum>i\<in>Basis. ((?p (tt i)) \<bullet> i) *\<^sub>R i)"
    by (auto simp: Pi_iff numeral_2_eq_2 diff_def 
      scaleR_setsum_right ac_simps power2_eq_square inverse_eq_divide)
  hence "x (t + h) - discrete_evolution (euler_increment f) (t + h) t (x t) =
    (h\<^sup>2 / 2) *\<^sub>R (\<Sum>i\<in>Basis. ((?p (tt i)) \<bullet> i) *\<^sub>R i)" (is "?d = _")
    by (auto simp: discrete_evolution_def euler_increment)
  also have "\<dots> \<in> op *\<^sub>R (h\<^sup>2 / 2) ` F'"
    apply (rule image_eqI[OF refl mem_box_componentwiseI[OF f'_ivl_bounded(1)]])
    using T tt ht
    apply (force simp: Pi_iff intro: f_set_bounded x image_eqI[OF refl f'_ivl_bounded(3)])
    done
  finally show ?thesis .
qed

end

locale derivative_norm_bounded = derivative_on_convex +
  fixes B B'
  assumes X_bounded: "bounded X"
  assumes f_bounded: "\<And>t x. t\<in>T \<Longrightarrow> x\<in>X \<Longrightarrow> norm (f (t,x)) \<le> B"
  assumes f'_bounded: "\<And>t x. t\<in>T \<Longrightarrow> x\<in>X \<Longrightarrow> onorm (f' (t,x)) \<le> B'"
begin

lemma f_bound_nonneg: "0 \<le> B"
proof -
  from nonempty obtain t x where "t \<in> T" "x \<in> X" by auto
  have "0 \<le> norm (f (t, x))" by simp
  also have "\<dots> \<le> B" by (rule f_bounded) fact+
  finally show ?thesis .
qed

lemma f'_bound_nonneg: "0 \<le> B'"
proof -
  from nonempty f_bounded ex_norm_eq_1[where 'a="real*'a"]
    obtain t x and d::"real*'a" where tx: "t \<in> T" "x \<in> X" "norm d = 1" by auto
  have "0 \<le> norm (f' (t, x) d)" by simp
  also have "... \<le> B'"
    apply (rule order_trans)
     apply (rule onorm[OF has_derivative_bounded_linear[OF f']])
       using tx
       apply (auto intro!: f'_bounded f' has_derivative_linear)
    done
  finally show ?thesis .
qed

sublocale g?: global_lipschitz _ _ _ B'
proof
  show "0 \<le> B'" using f'_bound_nonneg .
  fix t assume "t \<in> T"
  show "lipschitz X (\<lambda>x. f (t, x)) B'"
  proof (rule lipschitzI)
    fix x y
    let ?I = "T \<times> X"
    have "convex ?I" by (intro convex convex_Times)
    moreover have "\<forall>x\<in>?I. (f has_derivative f' x) (at x within ?I)" "\<forall>x\<in>?I. onorm (f' x) \<le> B'"
      using f' f'_bounded
      by (auto simp add: intro!: f'_bounded has_derivative_linear)
    moreover assume "x \<in> X" "y \<in> X"
    with `t \<in> T` have "(t, x) \<in> ?I" "(t, y) \<in> ?I" by simp_all
    ultimately have "norm (f (t, x) - f (t, y)) \<le> B' * norm ((t, x) - (t, y))"
      by (rule differentiable_bound)
    thus "dist (f (t, x)) (f (t, y)) \<le> B' * dist x y"
      by (simp add: dist_norm norm_Pair)
  qed
qed

definition euler_C::"real" where "euler_C = (sqrt DIM('a) * (B' * (B + 1) / 2))"

lemma euler_C_nonneg: "euler_C \<ge> 0"
 using f_bounded f_bound_nonneg f'_bound_nonneg
 by (simp add: euler_C_def)

sublocale derivative_set_bounded T X f f' "X \<times> cball 0 B"
    "{- (B' * (B + 1)) *\<^sub>R One.. (B' * (B + 1)) *\<^sub>R One}"
proof
  show "bounded (X \<times> cball 0 B)" using X_bounded by (auto intro!: bounded_Times)
  show "is_interval {-(B' * (B + 1)) *\<^sub>R One.. (B' * (B + 1)) *\<^sub>R One::'a}"
    "bounded {-(B' * (B + 1)) *\<^sub>R One.. (B' * (B + 1)) *\<^sub>R One::'a}"
    by (auto intro!: is_interval_closed_interval bounded_closed_interval)
  fix t x assume "t \<in> T" "x \<in> X"
  thus "(x, f (t, x)) \<in> X \<times> cball 0 B"
    by (auto simp: dist_norm f_bounded)
next
  fix t and x d::'a assume "t \<in> T" "(x, d) \<in> X \<times> cball 0 B"
  hence "x \<in> X" "norm d \<le> B" by (auto simp: dist_norm)
  have "norm (f' (t, x) (1, d)) \<le> onorm (f' (t, x)) * norm (1::real, d)"
    by (auto intro!: onorm has_derivative_bounded_linear f' `t \<in> T` `x \<in> X`)
  also have "\<dots> \<le> B' * (B + 1)"
    by (auto intro!: mult_mono f'_bounded f_bounded `t \<in> T` `x \<in> X` f'_bound_nonneg
      order_trans[OF norm_Pair_le] `norm d \<le> B`)
  finally have "f' (t, x) (1, d) \<in> cball 0 (B' * (B + 1))"
    by (auto simp: dist_norm)
  also note cball_in_cube
  finally show "f' (t, x) (1, d) \<in> {- (B' * (B + 1)) *\<^sub>R One..(B' * (B + 1)) *\<^sub>R One}" by simp
qed

lemma euler_consistent_traj:
  fixes t
  assumes T: "{t..u} \<subseteq> T"
  assumes x': "\<And>s. s \<in> {t..u} \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within {t..u})"
  assumes x: "\<And>s. s \<in> {t..u} \<Longrightarrow> x s \<in> X"
  shows "consistent x t u euler_C 1 (euler_increment f)"
proof
  fix h::real
  assume ht: "0 < h" "t + h \<le> u" hence "t < u" "0 < h\<^sup>2 / 2" by simp_all
  from euler_consistent_traj_set ht T x' x
  have "x (t + h) - discrete_evolution (euler_increment f) (t + h) t (x t) \<in>
      op *\<^sub>R (h\<^sup>2 / 2) ` {- (B' * (B + 1)) *\<^sub>R One..(B' * (B + 1)) *\<^sub>R One}"
    by auto
  also have "\<dots> = {- ((h\<^sup>2 / 2) * (B' * (B + 1))) *\<^sub>R One.. ((h\<^sup>2 / 2) * (B' * (B + 1))) *\<^sub>R One}"
    by (simp add: scaleR_image_atLeastAtMost[OF `0 < h\<^sup>2 / 2`])
  also
  note centered_cube_in_cball
  finally show "dist (x (t + h)) (discrete_evolution (euler_increment f) (t + h) t (x t))
      \<le> euler_C * h ^ (1 + 1)"
    by (auto simp: euler_C_def dist_norm algebra_simps norm_minus_commute power2_eq_square)
qed

end

locale grid_from = grid +
  fixes t0
  assumes grid_min: "t0 = t 0"

locale euler_consistent =
  has_solution i +
  ivp_on_interval i t1 +
  derivative_norm_bounded T X' f B f' B'
  for i::"'a::ordered_euclidean_space ivp" and t t1 X' B f' B' +
  fixes r
  assumes domain_subset: "X \<subseteq> X'"
  assumes lipschitz_area: "\<And>t. t \<in> T \<Longrightarrow> cball (solution t) \<bar>r\<bar> \<subseteq> X'"
begin

lemma euler_consistent_solution:
  fixes t'
  assumes t': "t' \<in> T"
  shows "consistent solution t' t1 euler_C 1 (euler_increment f)"
proof (rule euler_consistent_traj)
  show "{t'..t1} \<subseteq> T" using t' interval by simp
  fix s
  assume "s \<in> {t'..t1}" hence "s \<in> T" using `{t'..t1} \<subseteq> T` by auto
  show "(solution has_vector_derivative f (s, solution s)) (at s within {t'..t1})"
    by (rule has_vector_derivative_within_subset[OF _ `{t'..t1} \<subseteq> T`]) (rule solution(2)[OF `s \<in> T`])
  have "solution s \<in> ivp_X i" by (rule solution(3)[OF `s \<in> T`])
  thus "solution s \<in> X'" using domain_subset ..
qed

end

sublocale euler_consistent \<subseteq>
  consistent_one_step t0 t1 solution "euler_increment f" 1 euler_C r B'
proof
  show "0 < (1::nat)" by simp
  show "0 \<le> euler_C" using euler_C_nonneg by simp
  show "0 \<le> B'" using lipschitz by simp
  fix s x assume s: "s \<in> {t0..t1}"
  show "consistent solution s t1 euler_C 1 (euler_increment f)"
    using interval s f_bounded f'_bounded f'
      strip
    by (intro euler_consistent_solution) auto
  fix h
  assume "h\<in>{0..t1 - s}"
  have "lipschitz X' (euler_increment f h s) B'"
    using s lipschitz interval strip
    by (auto intro!: euler_lipschitz)
  thus "lipschitz (cball (solution s) \<bar>r\<bar>) (euler_increment f h s) B'"
    using lipschitz_area s interval
    by (force intro: lipschitz_subset)
qed

subsection {* Euler method is convergent *}
text{*\label{sec:rk-euler-conv}*}

locale max_step1 = grid +
  fixes t1 L B r
  assumes max_step: "\<And>j. t j \<le> t1 \<Longrightarrow> max_stepsize j \<le> \<bar>r\<bar> * L / B / (exp (L * (t1 - t 0) + 1) - 1)"

sublocale max_step1 < max_step?: max_step t t1 1 L B r
using max_step by unfold_locales simp_all

locale euler_convergent =
  euler_consistent + max_step1 t t1 B' euler_C r +
  assumes grid_from: "t0 = t 0"

sublocale euler_convergent \<subseteq>
  convergent_one_step t0 t1 solution "euler_increment f" 1 euler_C r B' t
  by unfold_locales (simp add: grid_from)

locale euler_on_strip =
  ivp_on_interval i t1 + continuous T X f +
  derivative_norm_bounded T UNIV f B f' B' +
  grid?: grid_from t t0 +
  max_step1 t t1 B' euler_C r
  for i::"'a::ordered_euclidean_space ivp" and t t1 r B f' B' +
  assumes strip: "X = UNIV"

sublocale euler_on_strip \<subseteq> unique_on_strip i t1 B'
  using lipschitz by unfold_locales (simp_all add: strip)

sublocale euler_on_strip \<subseteq> convergent?: euler_convergent i t t1 UNIV B f' B' r
  using lipschitz strip grid_min
  by unfold_locales simp_all

context euler_on_strip begin

lemma convergence:
  assumes "t j \<le> t1"
  shows "dist (solution (t j)) (euler f x0 t j)
    \<le> euler_C / B' * (exp (B' * (t1 - t0) + 1) - 1) * max_stepsize j"
  using assms convergence
  by (simp add: euler_def grid_min[symmetric] solution_t0)

end

subsection {* Euler method on Rectangle is convergent *}
text{*\label{sec:rk-euler-conv-on-rect}*}

locale ivp_rectangle_bounded_derivative = solution_in_rectangle i t1 b B +
  derivative_norm_bounded T "{x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}" f f' B B' for i t1 b r B f' B'

sublocale ivp_rectangle_bounded_derivative \<subseteq> unique_on_rectangle i t1 b B B'
  "{x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}"
  using b_pos by unfold_locales (auto simp: rectangle intro!: scaleR_mono One_nonneg)

sublocale ivp_rectangle_bounded_derivative \<subseteq>
  euler_consistent i t t1 "{x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}" f' B B'
proof
  show "X \<subseteq> {x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}" using lipschitz_on_domain .
  fix t assume "t \<in> T"
  from cball_in_cube
  have "cball (solution t) \<bar>r\<bar> \<subseteq> {solution t - setsum (op *\<^sub>R \<bar>r\<bar>) Basis..solution t + setsum (op *\<^sub>R \<bar>r\<bar>) Basis}"
    by (simp add: scaleR_setsum_right)
  also have "\<dots> \<subseteq> {x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}"
    using rectangle interval solution_in_D[of t] `t \<in> T`
    by (auto simp: scaleR_setsum_right algebra_simps setsum.distrib)
  finally show "cball (solution t) \<bar>r\<bar> \<subseteq> {x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}" .
qed

locale euler_on_rectangle =
  ivp_rectangle_bounded_derivative i t1 b r B f' B' +
  grid_from t t0 +
  max_step1 t t1 B' euler_C r
  for i::"'a::ordered_euclidean_space ivp" and t t1 b r B f' B'

sublocale euler_on_rectangle \<subseteq>
  convergent?: euler_convergent i t t1 "{x0 - (b + \<bar>r\<bar>) *\<^sub>R One..x0 + (b + \<bar>r\<bar>) *\<^sub>R One}" f' B B'
proof unfold_locales
qed (rule grid_min)

lemma "B \<ge> (0::real) \<Longrightarrow> 0 \<le> (exp (B + 1) - 1)" by (simp add: algebra_simps)

context euler_on_rectangle begin

lemma convergence:
  assumes "t j \<le> t1"
  shows "dist (solution (t j)) (euler f x0 t j)
    \<le> sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1 - t0) + 1) - 1) * max_stepsize j"
proof -
  have "dist (solution (t j)) (euler f x0 t j)
    \<le> sqrt DIM('a) * (B + 1) / 2 * B' / B' * ((exp (B' * (t1 - t0) + 1) - 1) * max_stepsize j)"
    using assms convergence f'_bound_nonneg
    unfolding euler_C_def
    by (simp add: euler_def grid_min[symmetric] solution_t0 ac_simps)
  also have "\<dots> \<le> sqrt DIM('a) * (B + 1) / 2 * ((exp (B' * (t1 - t0) + 1) - 1) * max_stepsize j)"
    using f_bound_nonneg f'_bound_nonneg
    by (auto intro!: mult_right_mono mult_nonneg_nonneg max_stepsize_nonneg add_nonneg_nonneg
      simp: le_diff_eq)
  finally show ?thesis by simp
qed

end

subsection {* Stability and Convergence of Approximate Euler *}
text{*\label{sec:rk-euler-stable}*}

locale euler_rounded_on_rectangle =
  ivp_rectangle_bounded_derivative i t1' b r B f' B' +
  grid?: grid_from t t0' +
  max_step_r_2?: max_step1 t t2' B' euler_C "r/2"
  for i::"'a::executable_euclidean_space ivp" and t :: "nat \<Rightarrow> real" and t0' t1' t2'::real and x0' :: 'a
  and b r B f' B' +
  fixes g::"(real\<times>'a)\<Rightarrow>'a" and e::int
  assumes t0_float: "t0 = t0'"
  assumes ordered_bounds: "t1' \<le> t2'"
  assumes approx_f_e: "\<And>j x. t j \<le> t1' \<Longrightarrow> dist (f (t j, x)) ((g (t j, x))) \<le> sqrt (DIM('a)) * 2 powr -e"
  assumes initial_error: "dist x0 (x0') \<le> euler_C / B' * (exp 1 - 1) * stepsize 0"
  assumes rounding_error: "\<And>j. t j \<le> t1' \<Longrightarrow> sqrt (DIM('a)) * 2 powr -e \<le> euler_C / 2 * stepsize j"
begin

lemma approx_f: "t j \<le> t1' \<Longrightarrow> dist (f (t j, x)) ((g (t j, x)))
    \<le> euler_C / 2 * stepsize j"
  using approx_f_e[of j x] rounding_error[of j] by auto

lemma t0_le: "t 0 \<le> t1'"
  unfolding grid_min[symmetric] t0_float[symmetric]
  by (metis interval_notempty)

end

sublocale euler_rounded_on_rectangle \<subseteq> grid'?: grid_from t t0'
  using grid t0_float grid_min by unfold_locales auto

sublocale euler_rounded_on_rectangle \<subseteq> max_step_r?: max_step1 t t2' B' euler_C r
proof unfold_locales
  fix j
  assume "(t j) \<le> t2'"
  moreover with grid_mono[of 0 j] have "t 0 \<le> t2'" by (simp add: less_eq_float_def)
  ultimately show "One_Step_Method.grid.max_stepsize (\<lambda>x. (t x)) j
        \<le> \<bar>r\<bar> * B' / euler_C / (exp (B' * (t2' - (t 0)) + 1) - 1)"
    using max_step_mono_r lipschitz B_nonneg interval_notempty f'_bound_nonneg
    by (auto simp: less_eq_float_def euler_C_def)
qed

lemma max_step1_mono:
  assumes "t 0 \<le> t1"
  assumes "t1 \<le> t2"
  assumes "0 \<le> a"
  assumes "0 \<le> b"
  assumes ms2: "max_step1 t t2 a b c"
  shows "max_step1 t t1 a b c"
proof -
  interpret t2: max_step1 t t2 a b c using ms2 .
  show ?thesis
  proof
    fix j
    assume "t j \<le> t1" hence "t j \<le> t2" using assms by simp
    hence "t2.max_stepsize j \<le> \<bar>c\<bar> * a / b / (exp (a * (t2 - t 0) + 1) - 1)" (is "_ \<le> ?x t2")
      by (rule t2.max_step)
    also have "\<dots> \<le> ?x t1"
      using assms
      by (cases "b = 0") (auto intro!: divide_left_mono mult_mono abs_ge_zero add_increasing
        mult_pos_pos add_strict_increasing2 simp: le_diff_eq less_diff_eq)
    finally show "t2.max_stepsize j \<le> ?x t1" .
  qed
qed

sublocale euler_rounded_on_rectangle \<subseteq> max_step_r1?: max_step1 t t1' B' euler_C r
  by (rule max_step1_mono[of t, OF t0_le ordered_bounds f'_bound_nonneg euler_C_nonneg])
    unfold_locales

sublocale euler_rounded_on_rectangle \<subseteq> c?: euler_on_rectangle i t t1' b r B f' B'
  using t0_float grid_min by unfold_locales simp

sublocale euler_rounded_on_rectangle \<subseteq>
  consistent_one_step "t 0" t1' solution "euler_increment f" 1 euler_C r B'
  using consistent_nonneg consistent lipschitz_nonneg lipschitz_incr t0_float grid_min
  by unfold_locales simp_all

sublocale euler_rounded_on_rectangle \<subseteq> max_step1 t t1' B' euler_C "r / 2"
  by (rule max_step1_mono[of t, OF t0_le ordered_bounds f'_bound_nonneg euler_C_nonneg])
    unfold_locales

sublocale euler_rounded_on_rectangle \<subseteq>
  one_step?:
  rounded_one_step t t1' solution "euler_increment f" 1 euler_C r B' "euler_increment' e g" x0'
proof
  fix h j x assume "t j \<le> t1'"
  have "dist (euler_increment f (h) (t j) (x))
        ((euler_increment' e g h (t j) x)) =
    dist (f (t j, x)) ((eucl_down e (g (t j, x))))"
    by (simp add: euler_increment euler_float_increment)
  also
  have "... \<le>
    dist (f (t j, x)) ((g (t j, x))) +
    dist ((g (t j, x))) ((eucl_down e (g (t j, x))))"
    by (rule dist_triangle)
  also
  from approx_f[OF `t j \<le> t1'`]
  have "dist (f (t j, x)) ((g (t j, x))) \<le>
    euler_C / 2 * stepsize j" .
  also
  from eucl_truncate_down_correct[of "g (t j, x)" e]
  have "dist ((g (t j, x))) ((eucl_down e (g (t j, x)))) \<le> sqrt (DIM('a)) * 2 powr - e" by simp
  also
  have "sqrt (DIM('a)) * 2 powr -e \<le> euler_C / 2 * stepsize j"
    using rounding_error `t j \<le> t1'` .
  finally
  have "dist (euler_increment f (h) (t j) (x)) ((euler_increment' e g h (t j) x)) \<le> euler_C * stepsize j"
    by arith
  thus "dist (euler_increment f h (t j) (x)) ((euler_increment' e g h (t j) x)) \<le> euler_C * stepsize j ^ 1"
    by simp
qed (insert initial_error grid_min solution_t0, simp_all)

context euler_rounded_on_rectangle begin

lemma stability:
  assumes "t j \<le> t1'"
  shows "dist (euler' e g x0' t j) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j"
proof -
  have "dist ((euler' e g x0' t j)) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * B' / B' * (exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j"
    using assms stability
    unfolding grid_min[symmetric] solution_t0 euler_C_def
    by (auto simp add: euler_def euler'_def t0_float)
  also have "\<dots> \<le> sqrt DIM('a) * (B + 1) / 2 * ((exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j)"
    using f_bound_nonneg f'_bound_nonneg
    by (auto intro!: mult_right_mono mult_nonneg_nonneg max_stepsize_nonneg add_nonneg_nonneg
      simp: le_diff_eq)
  finally show ?thesis by simp
qed

lemma convergence_float:
  assumes "t j \<le> t1'"
  shows "dist (solution (t j)) (euler' e g x0' t j) \<le>
    sqrt DIM('a) * (B + 1) * (exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j"
proof -
  have "dist (solution ((t j))) ((euler' e g x0' t j)) \<le>
    dist (solution ((t j)))
    (euler f x0 t j) +
    dist ((euler' e g x0' t j)) (euler f x0 t j)"
    by (rule dist_triangle2)
  also have "dist (solution ((t j)))
     (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j"
    using assms convergence t0_float by simp
  also have "dist ((euler' e g x0' t j)) (euler f x0 t j) \<le>
    sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1' - t0') + 1) - 1) * max_stepsize j"
    using assms stability by simp
  finally
  have "dist (solution ((t j))) ((euler' e g x0' t j))
     \<le> sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1' - t0') + 1) - 1) *
       max_stepsize j +
       sqrt DIM('a) * (B + 1) / 2 * (exp (B' * (t1' - t0') + 1) - 1) *
       max_stepsize j" by simp
  thus ?thesis by (simp add: field_simps)
qed

end

end
