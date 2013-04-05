header{* Runge-Kutta methods*}
theory Runge_Kutta
imports
  One_Step_Method "~~/src/HOL/Library/FrechetDeriv" "~~/src/HOL/Library/Float"
begin
text{*\label{sec:rk}*}

subsection {* Definitions *}
text{*\label{sec:rk-definition}*}

declare setsum_cong[fundef_cong]
fun rk_eval :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real\<times>'a::real_vector \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "rk_eval A c f t h x j =
  f (t + h * c j, x + h *\<^sub>R (\<Sum>l=1 ..< j. A j l *\<^sub>R rk_eval A c f t h x l))"

primrec rk_eval_dynamic :: "(nat\<Rightarrow>nat\<Rightarrow>real) \<Rightarrow> (nat\<Rightarrow>real) \<Rightarrow> (real\<times>'a::real_vector \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "rk_eval_dynamic A c f t h x 0 = (\<lambda>i. 0)"
| "rk_eval_dynamic A c f t h x (Suc j) =
  (let K = rk_eval_dynamic A c f t h x j in
  K(Suc j:=f (t + h * c (Suc j), x + h *\<^sub>R (\<Sum>l=1..j. A (Suc j) l *\<^sub>R K l))))"

fun rk_eval_float :: "(nat\<Rightarrow>nat\<Rightarrow>float) \<Rightarrow> (nat\<Rightarrow>float) \<Rightarrow> (float\<times>float \<Rightarrow> float) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float" where
  "rk_eval_float A c f t h x j =
  f (t + h * c j, x + h * setsum (\<lambda>l. A j l * rk_eval_float A c f t h x l) {1..<j})"

definition rk_increment where
  "rk_increment f s A b c h t x = (\<Sum>j=1..s. b j *\<^sub>R rk_eval A c f t h x j)"

definition rk_increment_float where
  "rk_increment_float error f s A b c h t x =
  float_down error (\<Sum>j=1..s. b j * rk_eval_float A c f t h x j)"

definition euler_increment where
  "euler_increment f = rk_increment f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler where
  "euler f = grid_function (discrete_evolution (euler_increment f))"

definition euler_float_increment where
"euler_float_increment e f = rk_increment_float e f 1 (\<lambda>i j. 0) (\<lambda>i. 1) (\<lambda>i. 0)"

definition euler_float where
  "euler_float e f =
    grid_function (discrete_evolution_scalar (euler_float_increment e f))"

definition heun where
  "heun f = grid_function (discrete_evolution (rk_increment f 2
    (\<lambda>i j. if i = 2 \<and> j = 1 then 1 else 0)
    (\<lambda>i. 1/2)
    (\<lambda>i. if i = 2 then 1 else 0)))"

definition heun_float where
  "heun_float error f = grid_function (discrete_evolution_scalar (rk_increment_float error f 2
    (\<lambda>i j. if i = 2 \<and> j = 1 then 1 else 0)
    (\<lambda>i. Float 1 -1)
    (\<lambda>i. if i = 2 then 1 else 0)))"

definition runge_kutta where
  "runge_kutta f = grid_function (discrete_evolution (rk_increment f 4
    (\<lambda>i j. if (i, j) = (2,1) \<or> (i, j) = (3, 2) then 1/2 else if (i, j) = (4, 3) then 1 else 0)
    ((\<lambda>i. 0)(1:=1/6, 2:=1/3, 3:=1/3, 4:=1/6))
    ((\<lambda>i. 0)(1:=0, 2:=1/2, 3:=1/2, 4:=1))))"

text {* The error for the approximations (e.g. @{term "float_divl 20 1 6"}) of the rational
  coefficients will need to be adapted for verification*}

definition runge_kutta_float where
  "runge_kutta_float error f =
  grid_function (discrete_evolution_scalar (rk_increment_float error f 4
    (\<lambda>i j. if (i, j) = (2,1) \<or> (i, j) = (3, 2) then Float 1 (-1) else if (i, j) = (4, 3) then 1 else 0)
    ((\<lambda>i. 0)(1:=float_divl 20 1 6, 2:=float_divl 20 1 3, 3:=float_divl 20 1 3, 4:=float_divl 20 1 6))
    ((\<lambda>i. 0)(1:=0, 2:= Float 1 -1, 3:=Float 1 -1, 4:=1))))"

subsection {* Euler method is consistent *}
text{*\label{sec:rk-euler-cons}*}

lemma euler_increment:
  shows "euler_increment f h t x = f (t, x)"
  unfolding euler_increment_def rk_increment_def
  by (subst rk_eval.simps) (simp del: rk_eval.simps)

lemma euler_float_increment:
  shows "euler_float_increment e f h t x = float_down e (f (t, x))"
  unfolding euler_float_increment_def rk_increment_float_def
  by (subst rk_eval_float.simps) (simp del: rk_eval_float.simps)

lemma euler_consistent_traj:
  fixes t
  assumes "B \<ge> 0"
  assumes "\<forall>s\<in>{t..T}. (x has_vector_derivative f (s, x s)) (at s)"
  assumes "\<forall>s\<in>{t..T}. ((\<lambda>s. f (s, x s)) has_vector_derivative f' s) (at s)"
  assumes "\<forall>s\<in>{t..T}. \<bar>f' s\<bar> \<le> 2 * B"
  shows "consistent x t T B 1 (euler_increment f)"
  unfolding consistent_def
proof (safe, cases)
  fix h::real
  assume "h = 0"
  thus "dist (x (t + h))
            (discrete_evolution (euler_increment f)
              (t + h) t (x t))
           \<le> B * h ^ (1 + 1)" by (simp add: discrete_evolution_def)
next
  fix h
  assume h: "0 \<le> h" "t + h \<le> T" "h \<noteq> 0"
  have deriv1: "\<forall>s\<in>{t..t+h}. DERIV x s :> f (s, x s)" using assms h
    unfolding DERIV_conv_has_vector_derivative by auto
  have deriv2: "\<forall>s\<in>{t..t+h}. DERIV (\<lambda>s. f (s, x s)) s :> f' s" using assms h
    unfolding DERIV_conv_has_vector_derivative by auto

  def B2 \<equiv> "2*B"
  def diff \<equiv> "\<lambda>i::nat. if i = 0 then x else if i = 1 then (\<lambda>t. f (t, x t)) else f'"
  have rewrite_2: "2 = real (Suc (Suc 0))" by simp
  {
    fix m::nat and s
    assume H:"m < 2" "t \<le> s" "s \<le> t + h"
    with deriv1 diff_def have "DERIV (diff m) s :> diff (Suc m) s"
    proof (cases "m=0")
      case False thus ?thesis using H deriv2 diff_def by (cases "m=1") auto
    qed simp
  }
  with assms h have "0 < (2::nat)" "diff 0 = x" "\<forall>m ta. m < 2 \<and> t \<le> ta \<and> ta \<le> t + h \<longrightarrow> DERIV (diff m) ta :> diff (Suc m) ta" "t \<le> t" "t \<le> t + h" "t \<le> t + h" "t + h \<le> t + h" "t + h \<noteq> t" by (auto simp add: diff_def)
  from taylor[where n=2 and f=x and c=t and x="t + h" and diff=diff and a=t and b="t+h", OF this]
  have "\<exists>s. (if t + h < t then t + h < s \<and> s < t else t < s \<and> s < t + h) \<and>
          x (t + h) =
          (\<Sum>m = 0..<2. diff m t / real (fact m) * (t + h - t) ^ m) +
          diff 2 s / real (fact (2::nat)) * (t + h - t)\<twosuperior>" by simp
  moreover have "2 = Suc (Suc 0)" by simp
  ultimately have "\<exists>s\<in>{t..t + h}. x (t + h) = x t + h * f (t, x t) + f' s * (h * h) / real (Suc (Suc 0))"
    using assms h by (auto simp add: diff_def)
  hence "\<exists>s\<in>{t..t+h}. x (t + h) = (x t) + h * f (t, x t) + h^2 * f' s / 2"
    by (simp add: ac_simps power2_eq_square rewrite_2)
  then guess s .. note s = this
  
  have "dist (x (t + h))
      (discrete_evolution (euler_increment f) (t + h) t (x t)) \<le>
    \<bar>h\<twosuperior> * f' s / 2\<bar>" using s unfolding discrete_evolution_def euler_increment
    by (simp add: dist_real_def)
  also have "... \<le> \<bar>(h\<twosuperior> / 2) * f' s\<bar>" by simp
  also have "... = \<bar>h\<twosuperior> / 2\<bar>  * \<bar>f' s\<bar>" by (rule abs_mult)
  also have "... \<le> h\<twosuperior> / 2 * \<bar>f' s\<bar>" by simp
  also have "... \<le> h\<twosuperior> / 2 * B2" using assms s h unfolding B2_def[symmetric] by simp
  finally show "dist (x (t + h))
    (discrete_evolution (euler_increment f) (t + h) t (x t))
      \<le> B * h ^ (1 + 1)" by (simp add: ac_simps power2_eq_square B2_def)
qed

lemma euler_lipschitz:
  fixes x::"real \<Rightarrow> real"
  assumes t: "t \<in> {t0..T}"
  assumes lipschitz: "\<forall>t\<in>{t0..T}. lipschitz D' (\<lambda>x. f (t, x)) L"
  shows "lipschitz D' (euler_increment f h t) L"
  using t lipschitz
  by (simp add: lipschitz_def euler_increment del: One_nat_def)

locale bounded_derivative = 
  fixes I D f B f' B'
  assumes f_bounded: "\<And>t x. t\<in>I \<Longrightarrow> x\<in>D \<Longrightarrow> \<bar>f (t,x) \<bar> \<le> B"
  assumes f': "\<And>t x. t\<in>I \<Longrightarrow> x\<in>D \<Longrightarrow> (f has_derivative f'(tx)) (at tx)"
  assumes f'_bounded: "\<And>t x dx. t\<in>I \<Longrightarrow> x\<in>D \<Longrightarrow> \<bar>dx\<bar> \<le> B \<Longrightarrow>
    \<bar>f' (t,x) (1, dx)\<bar> \<le> 2 * B'"

locale ivp_bounded_derivative =
  ivp i + bounded_derivative I D f B f' B' for i::"real ivp" and B f' B'
begin

lemma Bf'_nonneg: "B' \<ge> 0"
proof -
  have "0 \<le> abs(f (t0, x0))" by simp
  also have "... \<le> B" using f_bounded iv_defined by auto
  finally have Bf_nonneg: "B \<ge> 0" .
  have "0 \<le> abs(f' (t0, x0) (1, B))" by simp
  also have "... \<le> 2 * B'"
    using Bf_nonneg iv_defined by (auto intro: f'_bounded)
  finally show ?thesis by simp
qed

end

locale grid_from = grid +
  fixes t0
  assumes grid_min: "t0 = t 0"

locale euler_consistent =
  has_solution i +
  ivp_on_interval i T +
  global_lipschitz I D' f L + 
  grid: grid_from t t0 +
  bounded_derivative I D f B f' B'
  for i::"real ivp" and t T D' L B f' B' +
  fixes r
  assumes lipschitz_area: "\<And>t. t \<in> I \<Longrightarrow> cball (solution t) \<bar>r\<bar> \<subseteq> D'"
begin

lemma euler_consistent_solution:
  fixes t'
  assumes t': "t' \<in> I"
  shows "consistent solution t' T B' 1 (euler_increment f)"
proof -
  from obtain_linear_continuation_at[of t0 T solution "\<lambda>t. f (t, solution t)"]
    solution
  obtain xc where xc':
    "\<And>t. t \<in> I \<Longrightarrow> (xc has_vector_derivative f (t, solution t)) (at t)"
    "\<And>t. t \<in> I \<Longrightarrow> xc t = solution t" unfolding interval by blast
  
  def g \<equiv> "\<lambda>t. (t, xc t)"
  def g' \<equiv> "\<lambda>t. (1::real, f (t, xc t))"

  have consistent_xc: "consistent xc t' T B' 1 (euler_increment f)"
  proof (intro euler_consistent_traj, safe)
    fix s assume s: "s \<in> {t'..T}" hence s': "s \<in> I" using t' interval by simp
    with xc' have xc_x: "xc s = solution s" by simp
    from s' xc' show xc': "(xc has_vector_derivative f (s, xc s)) (at s)" by simp
    from solution(3) s' have x_defined: "solution s \<in> D" by (simp add: interval)
    hence xc_defined: "xc s \<in> D" using s' xc_x by simp
    
    from f' have f': "(f has_derivative f' (s, xc s)) (at (g s))"
      using x_defined xc' xc_x g_def s t' by (force simp: interval)
    have norm_unfold: "\<And>x. norm (0::real, x) = \<bar>x\<bar>" by (simp add: norm_Pair)
    have "(g has_vector_derivative g' s) (at s)" using xc'
      by (auto intro: bounded_linear_ident bounded_linear_Pair
        simp add: norm_unfold has_vector_derivative_def has_derivative_at'
        g'_def g_def)
    hence g': "(g has_derivative (\<lambda>x. x *\<^sub>R g' s)) (at s)"
      by (simp add: has_vector_derivative_def)
    have "(\<lambda>s. f (s, xc s)) = f o g" unfolding g_def by auto
    with linear_cmul[OF derivative_is_linear[OF f']]
    show "((\<lambda>s. f (s, xc s)) has_vector_derivative f' (s, xc s) (g' s)) (at s)"
      using diff_chain_at[OF g', OF f', folded g_def] 
      by (auto simp: has_vector_derivative_def o_def)

    from xc_defined show " \<bar>f' (s, xc s) (g' s)\<bar> \<le> 2*B'"
      using f_bounded f'_bounded s t' interval
      by (auto simp add: g'_def)
  next
    interpret ivp_bounded_derivative by default
    show "B' \<ge> 0" using Bf'_nonneg by simp
  qed
  
  show ?thesis unfolding consistent_def
  proof safe
    fix h assume h: "0 \<le> h" "t' + h \<le> T"
    hence "dist (xc (t' + h))
            (discrete_evolution (euler_increment f) (t' + h) t'
              (xc t'))
           \<le> B' * h ^ (1 + 1)"
      using consistent_xc by (auto simp: consistent_def)
    thus "dist (solution (t' + h))
            (discrete_evolution (euler_increment f) (t' + h) t'
              (solution t'))
           \<le> B' * h ^ (1 + 1)"
      using h t' by (simp add: xc' interval)
  qed
qed

end

sublocale euler_consistent \<subseteq>
  consistent_one_step t T solution "euler_increment f" 1 B'
proof
  have "0 \<le> abs(f (t0, x0))" by simp
  also have "... \<le> B" using f_bounded iv_defined by auto
  finally have "B \<ge> 0" .
  have "0 \<le> abs(f' (t0, x0) (1, B))" by simp
  also have "... \<le> 2 * B'" apply (rule f'_bounded)
    using interval f'_bounded `B \<ge> 0` iv_defined by auto
  finally show "B' \<ge> 0" by simp
  fix s x assume s: "s \<in> {t 0..T}"
  show "consistent solution s T B' 1 (euler_increment f)"
    using interval s f_bounded f'_bounded f'
      strip grid_min
    by (intro euler_consistent_solution) auto
  fix h
  assume "h\<in>{0..T - s}"
  have "lipschitz D' (euler_increment f h s) L"
    using s lipschitz interval strip grid_min
    by (auto intro!: euler_lipschitz)
  thus "lipschitz (cball (solution s) \<bar>r\<bar>) (euler_increment f h s) L"
    using lipschitz_area s interval grid_min
    by (force intro: lipschitz_subset)
qed (insert lipschitz, auto)

subsection {* Euler method is convergent *}
text{*\label{sec:rk-euler-conv}*}

locale max_step1 = grid +
  fixes T L B r
  assumes max_step: "\<And>j. t j \<le> T \<Longrightarrow> max_stepsize j \<le> \<bar>r\<bar> * L / B / (exp (L * (T - t 0) + 1) - 1)"

sublocale max_step1 < max_step: max_step t T 1 L B r
using max_step by unfold_locales simp_all

locale euler_convergent =
  euler_consistent + max_step1 t T L B' r

sublocale euler_convergent \<subseteq>
  convergent_one_step t T solution "euler_increment f" 1 B' by default

locale euler_on_strip = 
  unique_on_strip i T L + bounded_derivative I D f B f' B' +
  grid: grid_from t t0 +
  max_step1 t T L B' r
  for i::"real ivp" and t T r L B f' B'

sublocale euler_on_strip \<subseteq> convergent: euler_convergent i t T UNIV L B f' B' r
  using lipschitz strip
  by unfold_locales auto

context euler_on_strip begin

lemma convergence:
  assumes "t j \<le> T"
  shows "dist (solution (t j)) (euler f x0 t j)
    \<le> B' / L * (exp (L * (T - t0) + 1) - 1) * max_stepsize j"
  using assms convergence
  by (simp add: euler_def grid_min[symmetric] solution_t0)

end

subsection {* Euler method on Rectangle is convergent *}
text{*\label{sec:rk-euler-conv-on-rect}*}

locale euler_on_rectangle =
  unique: unique_on_rectangle i T b B L "{ivp_x0 i - b - \<bar>r\<bar>..ivp_x0 i + b + \<bar>r\<bar>}" +
  bounded_derivative I D f B f' B' +
  grid_from t t0 +
  max_step1 t T L B' r
  for i::"real ivp" and t T b r L B f' B'

sublocale euler_on_rectangle \<subseteq>
  convergent: euler_convergent i t T "{x0 - b - \<bar>r\<bar>..x0 + b + \<bar>r\<bar>}"
  using solution_in_D rectangle grid_min
  by unfold_locales (force simp: dist_real_def)

context euler_on_rectangle begin

lemma convergence:
  assumes "t j \<le> T"
  shows "dist (solution (t j)) (euler f x0 t j)
    \<le> B' / L * (exp (L * (T - t0) + 1) - 1) * max_stepsize j"
  using assms convergence
  by (simp add: euler_def grid_min[symmetric] solution_t0)

end

subsection {* Stability and Convergence of Approximate Euler *}
text{*\label{sec:rk-euler-stable}*}

locale euler_rounded_on_rectangle =
  unique_on_rectangle i T b B L
    "{ivp_x0 i - b - \<bar>r\<bar>..ivp_x0 i + b + \<bar>r\<bar>}" +
  bounded_deriv: bounded_derivative I D f B f' B' +
  grid: grid_from t t0' +
  max_step_r_2: max_step1 t T L B' "r/2"
  for i::"real ivp" and t :: "nat \<Rightarrow> float" and t0' x0' :: float and
  T b r L B B' f' +
  fixes g::"(float\<times>float)\<Rightarrow>float" and e::int
  assumes t0_float: "t0 = real t0'"
  assumes approx_f: "\<And>j x. dist (f (t j, real x)) (real (g (t j, x)))
    \<le> B' / 2 * stepsize j"
  assumes initial_error: "dist x0 (real x0')
    \<le> B' / L * (exp 1 - 1) * stepsize 0"
  assumes rounding_error: "\<And>j. t j \<le> T \<Longrightarrow> 2 powr -e \<le> B' / 2 * stepsize j"

sublocale euler_rounded_on_rectangle \<subseteq> grid': grid_from t t0'
  using grid t0_float grid_min by unfold_locales auto

sublocale euler_rounded_on_rectangle \<subseteq> ivp_bounded_derivative by default

sublocale euler_rounded_on_rectangle \<subseteq> max_step_r: max_step1 t T L B' r
proof unfold_locales
  fix j
  assume "real (t j) \<le> T"
  moreover with grid_mono[of 0 j] have "t 0 \<le> T" by (simp add: less_eq_float_def)
  ultimately show "One_Step_Method.grid.max_stepsize (\<lambda>x. real (t x)) j
        \<le> \<bar>r\<bar> * L / B' / (exp (L * (real T - real (t 0)) + 1) - 1)"
    using max_step_mono_r lipschitz B_nonneg interval_notempty Bf'_nonneg
    by (auto simp: less_eq_float_def)
qed

sublocale euler_rounded_on_rectangle \<subseteq> euler_on_rectangle i t T b r L B f' B'
  using max_step t0_float grid_min by unfold_locales simp_all

sublocale euler_rounded_on_rectangle \<subseteq>
  consistent_one_step t T solution "euler_increment f" 1 B' r L
  using consistent_nonneg consistent lipschitz_nonneg lipschitz_incr t0_float
  by unfold_locales simp_all

sublocale euler_rounded_on_rectangle \<subseteq>
  one_step:
  rounded_one_step t T solution "euler_increment f" 1 B' r L "euler_float_increment e g" x0' 
proof
  fix h j x assume "t j \<le> T"
  have "dist (euler_increment f (real h) (t j) (real x))
        (real (euler_float_increment e g h (t j) x)) =
    dist (f (t j, real x)) (real (float_down e (g (t j, x))))"
    by (simp add: euler_increment euler_float_increment)
  also
  have "... \<le>
    dist (f (t j, real x)) (real (g (t j, x))) +
    dist (real (g (t j, x))) (real (float_down e (g (t j, x))))"
    by (rule dist_triangle)
  also
  from approx_f
  have "dist (f (t j, real x)) (real (g (t j, x))) \<le>
    B' / 2 * stepsize j" .
  also
  have "dist (real (g (t j, x))) (real (float_down e (g (t j, x)))) =
    real (g (t j, x)) - real (float_down e (g (t j, x)))"
    using round_down by (simp add: dist_real_def abs_real_def float_down_def not_less)
  also from float_down_correct[of "g (t j, x)"]
  have "\<dots> \<le> 2 powr - e" by simp
  also
  have "2 powr -e \<le> B' / 2 * stepsize j"
    using rounding_error `t j \<le> T` .
  finally
  have "dist (euler_increment f (real h) (t j) (real x))
        (real (euler_float_increment e g h (t j) x))  \<le>
    B' * stepsize j" by arith
  thus "dist (euler_increment f h (t j) x)
        (real (euler_float_increment e g h (t j) x))
    \<le> B' * stepsize j ^ 1" by simp
qed (insert initial_error grid_min solution_t0, simp)

context euler_rounded_on_rectangle begin


lemma convergence_float:
  assumes "t j \<le> T"
  shows "dist (solution (t j)) (real (euler_float e g x0' t j)) \<le>
    2 * B' / L * (exp (L * (T - t0') + 1) - 1) * max_stepsize j"
proof -
  have "dist (solution (real (t j))) (real (euler_float e g x0' t j)) \<le>
    dist (solution (real (t j)))
    (euler f x0 t j) + 
    dist (real (euler_float e g x0' t j)) (euler f x0 t j)"
    by (rule dist_triangle2)
  also have "dist (solution (real (t j)))
     (euler f x0 t j) \<le>
    B' / L * (exp (L * (T - real t0') + 1) - 1) * max_stepsize j"
    using assms convergence t0_float by (simp add: less_eq_float_def)
  also have "dist (real (euler_float e g x0' t j))
            (euler f x0 t j) \<le>
    B' / L * (exp (L * (real T - real t0') + 1) - 1) * max_stepsize j"
    using assms stability
    unfolding grid_min[symmetric] solution_t0
    by (simp add: euler_def euler_float_def t0_float[symmetric])
  finally
  have "dist (solution (real (t j))) (real (euler_float e g x0' t j))
     \<le> B' / L * (exp (L * (real T - real t0') + 1) - 1) *
       max_stepsize j +
       B' / L * (exp (L * (real T - real t0') + 1) - 1) *
       max_stepsize j" by simp
  thus ?thesis by (simp add: field_simps)
qed

end

end
