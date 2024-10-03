theory Perron_Formula
imports
  "PNT_Remainder_Library"
  "PNT_Subsummable"
begin
unbundle pnt_syntax

section \<open>Perron's formula\<close>

text \<open>This version of Perron's theorem is referenced to:
  \<open>Perron's Formula and the Prime Number Theorem for Automorphic L-Functions, Jianya Liu, Y. Ye\<close>\<close>

text \<open>A contour integral estimation lemma that will be used
  both in proof of Perron's formula and the prime number theorem.\<close>

lemma perron_aux_3':
  fixes f :: "complex \<Rightarrow> complex" and a b B T :: real
  assumes Ha: "0 < a" and Hb: "0 < b" and hT: "0 < T"
    and Hf: "\<And>t. t \<in> {-T..T} \<Longrightarrow> \<parallel>f (Complex b t)\<parallel> \<le> B"
    and Hf': "(\<lambda>s. f s * a powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
  shows "\<parallel>1 / (2 * pi * \<i>) * contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. f s * a powr s / s)\<parallel>
       \<le> B * a powr b * ln (1 + T / b)"
proof -
  define path where "path \<equiv> linepath (Complex b (-T)) (Complex b T)"
  define t' where "t' t \<equiv> Complex (Re (Complex b (-T))) t" for t
  define g where "g t \<equiv> f (Complex b t) * a powr (Complex b t) / Complex b t * \<i>" for t
  have "\<parallel>f (Complex b 0)\<parallel> \<le> B" using hT by (auto intro: Hf [of 0])
  hence hB: "0 \<le> B" using hT by (smt (verit) norm_ge_zero)
  have "((\<lambda>t. f (t' t) * a powr (t' t) / (t' t) * \<i>)
        has_integral contour_integral path (\<lambda>s. f s * a powr s / s)) {Im (Complex b (-T))..Im (Complex b T)}"
    unfolding t'_def using hT
    by (intro integral_linepath_same_Re, unfold path_def)
       (auto intro: has_contour_integral_integral Hf')
  hence h_int: "(g has_integral contour_integral path (\<lambda>s. f s * a powr s / s)) {-T..T}"
    unfolding g_def t'_def by auto
  hence int: "g integrable_on {-T..T}" by (rule has_integral_integrable)
  have "contour_integral path (\<lambda>s. f s * a powr s / s) = integral {-T..T} g"
    using h_int by (rule integral_unique [symmetric])
  also have "\<parallel>\<dots>\<parallel> \<le> integral {-T..T} (\<lambda>t. 2 * B * a powr b / (b + \<bar>t\<bar>))"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1 from int show ?case .
    case 2 show ?case
      by (intro integrable_continuous_interval continuous_intros)
         (use Hb in auto)
  next
    fix t assume *: "t \<in> {-T..T}"
    have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) = - 3 * (b - \<bar>t\<bar>)\<^sup>2 + - 4 * b * \<bar>t\<bar>"
      by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<le> 0" using Hb by (intro add_nonpos_nonpos) auto
    finally have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) \<le> 0" .
    hence "b + \<bar>t\<bar> \<le> 2 * \<parallel>Complex b t\<parallel>"
      unfolding cmod_def by (auto intro: power2_le_imp_le)
    hence "a powr b / \<parallel>Complex b t\<parallel> \<le> a powr b / ((b + \<bar>t\<bar>) / 2)"
      using Hb by (intro divide_left_mono) (auto intro!: mult_pos_pos)
    hence "a powr b / \<parallel>Complex b t\<parallel> * \<parallel>f (Complex b t)\<parallel> \<le> a powr b / ((b + \<bar>t\<bar>) / 2) * B"
      by (insert Hf [OF *], rule mult_mono) (use Hb in auto)
    thus "\<parallel>g t\<parallel> \<le> 2 * B * a powr b / (b + \<bar>t\<bar>)"
      unfolding g_def
      by (auto simp add: norm_mult norm_divide)
         (subst norm_powr_real_powr, insert Ha, auto simp add: mult_ac)
  qed
  also have "\<dots> = 2 * B * a powr b * integral {-T..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
    by (subst divide_inverse, subst integral_mult_right) (simp add: inverse_eq_divide)
  also have "\<dots> = 4 * B * a powr b * integral {0..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
  proof -
    let ?f = "\<lambda>t. 1 / (b + \<bar>t\<bar>)"
    have "integral {-T..0} ?f + integral {0..T} ?f = integral {-T..T} ?f"
      by (intro Henstock_Kurzweil_Integration.integral_combine
                integrable_continuous_interval continuous_intros)
         (use Hb hT in auto)
    moreover have "integral {-T..-0} (\<lambda>t. ?f (-t)) = integral {0..T} ?f"
      by (rule Henstock_Kurzweil_Integration.integral_reflect_real)
    hence "integral {-T..0} ?f = integral {0..T} ?f" by auto
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = 4 * B * a powr b * ln (1 + T / b)"
  proof -
    have "((\<lambda>t. 1 / (b + \<bar>t\<bar>)) has_integral (ln (b + T) - ln (b + 0))) {0..T}"
    proof (rule fundamental_theorem_of_calculus, goal_cases)
      case 1 show ?case using hT by auto
    next
      fix x assume *: "x \<in> {0..T}"
      have "((\<lambda>x. ln (b + x)) has_real_derivative 1 / (b + x) * (0 + 1)) (at x within {0..T})"
        by (intro derivative_intros) (use Hb * in auto)
      thus "((\<lambda>x. ln (b + x)) has_vector_derivative 1 / (b + \<bar>x\<bar>)) (at x within {0..T})"
        using * by (subst has_real_derivative_iff_has_vector_derivative [symmetric]) auto
    qed
    moreover have "ln (b + T) - ln (b + 0) = ln (1 + T / b)"
      using Hb hT by (simp add: ln_div field_simps)
    ultimately show ?thesis by auto
  qed
  finally have "\<parallel>1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. f s * a powr s / s)\<parallel>
    \<le> 1 / (2*pi) * 4 * B * a powr b * ln (1 + T / b)"
    by (simp add: norm_divide norm_mult field_simps)
  also have "\<dots> \<le> 1 * B * a powr b * ln (1 + T / b)"
  proof -
    have "1 / (2*pi) * 4 \<le> 1" using pi_gt3 by auto
    thus ?thesis by (intro mult_right_mono) (use hT Hb hB in auto)
  qed
  finally show ?thesis unfolding path_def by auto
qed

locale perron_locale =
  fixes b B H T x :: real and f :: "complex fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "1 < H" and hH': "b + 1 \<le> H" and Hx: "0 < x"
    and hB: "(\<Sum>`n \<ge> 1. \<parallel>fds_nth f n\<parallel> / n nat_powr b) \<le> B"
begin
definition r where "r a \<equiv>
  if a \<noteq> 1 then min (1 / (2 * T * \<bar>ln a\<bar>)) (2 + ln (T / b))
  else (2 + ln (T / b))"
definition path where "path \<equiv> linepath (Complex b (-T)) (Complex b T)"
definition img_path where "img_path \<equiv> path_image path"
definition \<sigma>\<^sub>a where "\<sigma>\<^sub>a \<equiv> abs_conv_abscissa f"
definition region where "region = {n :: nat. x - x / H \<le> n \<and> n \<le> x + x / H}"
definition F where "F (a :: real) \<equiv>
  1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s) - (if 1 \<le> a then 1 else 0)"
definition F' where "F' (n :: nat) \<equiv> F (x / n)"

lemma hT': "0 < T" using Hb hT by auto
lemma cond: "0 < b" "b \<le> T" "0 < T" using Hb hT hT' by auto

lemma perron_integrable:
  assumes "(0 :: real) < a"
  shows "(\<lambda>s. a powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
using cond assms
by (intro contour_integrable_continuous_linepath continuous_intros)
   (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

lemma perron_aux_1':
  fixes U :: real
  assumes hU: "0 < U" and Ha: "1 < a"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr -U * T / (pi * U)"
proof -
  define f where "f \<equiv> \<lambda>s :: complex. a powr s / s"
  note assms' = cond assms this
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (Complex (-U) (-T)) (Complex b (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (Complex b (-T)) (Complex b T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (Complex b T) (Complex (-U) T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (Complex (-U) T) (Complex (-U) (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> contour_integral P\<^sub>1 f" and "I\<^sub>2 \<equiv> contour_integral P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> contour_integral P\<^sub>3 f" and "I\<^sub>4 \<equiv> contour_integral P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (Complex (-U) (-T)) (Complex b T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have 1: "\<And>A B x. A \<subseteq> B \<Longrightarrow> x \<notin> A \<Longrightarrow> A \<subseteq> B - {x}" by auto
  have "path_image (rectpath (Complex (- U) (- T)) (Complex b T))
        \<subseteq> cbox (Complex (- U) (- T)) (Complex b T) - {0}"
    using assms'
    by (intro 1 path_image_rectpath_subset_cbox)
       (auto simp add: path_image_rectpath)
  moreover have "0 \<in> box (Complex (- U) (- T)) (Complex b T)"
    using assms' by (simp add: mem_box Basis_complex_def)
  ultimately have
    "((\<lambda>s. a powr s / (s - 0)) has_contour_integral
      2 * pi * \<i> * winding_number rpath 0 * a powr (0 :: complex)) rpath"
    "winding_number rpath 0 = 1"
    unfolding rpath_def
    by (intro Cauchy_integral_formula_convex_simple
              [where S = "cbox (Complex (-U) (-T)) (Complex b T)"])
       (auto intro!: assms' holomorphic_on_powr_right winding_number_rectpath
             simp add: mem_box Basis_complex_def)
  hence "(f has_contour_integral 2 * pi * \<i>) rpath" unfolding f_def using Ha by auto
  hence 2: "(f has_contour_integral 2 * pi * \<i>) P"
    unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f contour_integrable_on P" by (intro has_contour_integral_integrable) (use 2 in auto)
  hence 3: "f contour_integrable_on P\<^sub>1" "f contour_integrable_on P\<^sub>2"
           "f contour_integrable_on P\<^sub>3" "f contour_integrable_on P\<^sub>4" unfolding P_defs by auto
  from 2 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 2 * pi * \<i>" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>2 - 2 * pi * \<i> = - (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)" by (simp add: field_simps)
  hence "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> = \<parallel>- (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)\<parallel>" by auto
  also have "\<dots> = \<parallel>I\<^sub>1 + I\<^sub>3 + I\<^sub>4\<parallel>" by (rule norm_minus_cancel)
  also have "\<dots> \<le> \<parallel>I\<^sub>1 + I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" using norm_triangle_ineq by auto
  finally have *: "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" .
  have I\<^sub>2_val: "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
  proof -
    have "I\<^sub>2 - 2 * pi * \<i> = (I\<^sub>2 / (2 * pi * \<i>) - 1) * (2 * pi * \<i>)" by (auto simp add: field_simps)
    hence "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> = \<parallel>(I\<^sub>2 / (2 * pi * \<i>) - 1) * (2 * pi * \<i>)\<parallel>" by auto
    also have "\<dots> = \<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> * (2*pi)" by (auto simp add: norm_mult)
    finally have "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> = 1 / (2*pi) * \<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel>" by auto
    also have "\<dots> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
      using * by (subst mult_le_cancel_left_pos) auto
    finally show ?thesis .
  qed
  define Q where "Q t \<equiv> linepath (Complex (-U) t) (Complex b t)" for t
  define g where "g t \<equiv> contour_integral (Q t) f" for t
  have Q_1: "(f has_contour_integral I\<^sub>1) (Q (-T))"
    using 3(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f has_contour_integral -I\<^sub>3) (Q T)"
    using 3(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "\<parallel>g t\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f has_contour_integral g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f contour_integrable_on Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a powr (x + Im (Complex (-U) t) * \<i>) / (x + Im (Complex (-U) t) * \<i>)) has_integral (g t))
          {Re (Complex (-U) t) .. Re (Complex b t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use hU Hb in auto)
    hence *: "((\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) has_integral g t) {-U..b}" by auto
    hence "\<parallel>g t\<parallel> = \<parallel>integral {-U..b} (\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>))\<parallel>" by (auto simp add: integral_unique)
    also have "\<dots> \<le> integral {-U..b} (\<lambda>x. a powr x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) integrable_on {-U..b}" using * by auto
      have "(\<lambda>x. a powr x / (of_real T)) integrable_on {-U..b}"
        by (intro iffD2 [OF integrable_on_cdivide_iff] powr_integrable) (use hU Ha Hb hT' in auto)
      thus "(\<lambda>x. a powr x / T) integrable_on {-U..b}" by auto
    next
      fix x assume "x \<in> {-U..b}"
      have "\<parallel>a powr (x + t * \<i>)\<parallel> = Re a powr Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a powr x" by auto
      finally have *: "\<parallel>a powr (x + t * \<i>)\<parallel> = a powr x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> \<parallel>x + t * \<i>\<parallel>" by (rule abs_Im_le_cmod)
      finally have "T \<le> \<parallel>x + t * \<i>\<parallel>" .
      with * show "\<parallel>a powr (x + t * \<i>) / (x + t * \<i>)\<parallel> \<le> a powr x / T"
        by (subst norm_divide) (rule frac_le, use assms' in auto)
    qed
    also have "\<dots> = integral {-U..b} (\<lambda>x. a powr x) / T" by auto
    also have "\<dots> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    proof -
      have "integral {-U..b} (\<lambda>x. a powr x) \<le> a powr b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_gt_1) (use hU Ha Hb in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "\<parallel>I\<^sub>4\<parallel> \<le> a powr -U / U * \<parallel>Complex (- U) (- T) - Complex (- U) T\<parallel>"
  proof -
    have "f contour_integrable_on P\<^sub>4" by (rule 3)
    moreover have "0 \<le> a powr - U / U" using hU by auto
    moreover have "\<parallel>f z\<parallel> \<le> a powr - U / U"
      when *: "z \<in> closed_segment (Complex (- U) T) (Complex (- U) (- T))" for z
    proof -
      from * have Re_z: "Re z = - U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> \<parallel>z\<parallel>" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> \<parallel>z\<parallel>" .
      have "\<parallel>f z\<parallel> = \<parallel>a powr z\<parallel> / \<parallel>z\<parallel>" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a powr - U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>4_def P\<^sub>4_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> = a powr -U / U * (2 * T)"
  proof -
    have "sqrt ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' by (auto simp add: field_simps legacy_Complex_simps)
  qed
  finally have I\<^sub>4_bound: "\<parallel>I\<^sub>4\<parallel> \<le> a powr -U / U * (2 * T)" .
  have "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> \<le> 1 / (2*pi) * (\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
    using I\<^sub>2_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 1 / (2*pi) * (2 * a powr b / (T * \<bar>ln a\<bar>) + a powr -U / U * (2*T))"
  proof -
    have "\<parallel>g T\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
         "\<parallel>g (- T)\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>4\<parallel> \<le> 2 * a powr b / (T * \<bar>ln a\<bar>) + a powr -U / U * (2*T)"
      using I\<^sub>4_bound by auto
    thus ?thesis by (auto simp add: field_simps)
  qed
  also have "\<dots> = 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr -U * T / (pi * U)"
    using hT' by (auto simp add: field_simps)
  finally show ?thesis
    using Ha unfolding I\<^sub>2_def P\<^sub>2_def f_def F_def path_def by auto
qed

lemma perron_aux_1:
  assumes Ha: "1 < a"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)" (is "_ \<le> ?x")
proof -
  let ?y = "\<lambda>U :: real. a powr -U * T / (pi * U)"
  have "((\<lambda>U :: real. ?x) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "((\<lambda>U. ?y U) \<longlongrightarrow> 0) at_top" using Ha by real_asymp
  ultimately have "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x + 0) at_top" by (rule tendsto_add)
  hence "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "\<parallel>F a\<parallel> \<le> ?x + ?y U" when hU: "0 < U" for U
    by (subst perron_aux_1' [OF hU Ha], standard)
  hence "\<forall>\<^sub>F U in at_top. \<parallel>F a\<parallel> \<le> ?x + ?y U"
    by (rule eventually_at_top_linorderI')
  ultimately show ?thesis
    by (intro tendsto_lowerbound) auto
qed

lemma perron_aux_2':
  fixes U :: real
  assumes hU: "0 < U" "b < U" and Ha: "0 < a \<and> a < 1"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
proof -
  define f where "f \<equiv> \<lambda>s :: complex. a powr s / s"
  note assms' = cond assms hU
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (Complex b (-T)) (Complex U (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (Complex U (-T)) (Complex U T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (Complex U T) (Complex b T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (Complex b T) (Complex b (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> contour_integral P\<^sub>1 f" and "I\<^sub>2 \<equiv> contour_integral P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> contour_integral P\<^sub>3 f" and "I\<^sub>4 \<equiv> contour_integral P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (Complex b (- T)) (Complex U T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have "path_image (rectpath (Complex b (- T)) (Complex U T)) \<subseteq> cbox (Complex b (- T)) (Complex U T)"
    by (intro path_image_rectpath_subset_cbox) (use assms' in auto)
  moreover have "0 \<notin> cbox (Complex b (- T)) (Complex U T)"
    using Hb unfolding cbox_def by (auto simp add: Basis_complex_def)
  ultimately have "((\<lambda>s. a powr s / (s - 0)) has_contour_integral 0) rpath"
    unfolding rpath_def
    by (intro Cauchy_theorem_convex_simple
              [where S = "cbox (Complex b (- T)) (Complex U T)"])
       (auto intro!: holomorphic_on_powr_right holomorphic_on_divide)
  hence "(f has_contour_integral 0) rpath" unfolding f_def using Ha by auto
  hence 1: "(f has_contour_integral 0) P" unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f contour_integrable_on P" by (intro has_contour_integral_integrable) (use 1 in auto)
  hence 2: "f contour_integrable_on P\<^sub>1" "f contour_integrable_on P\<^sub>2"
           "f contour_integrable_on P\<^sub>3" "f contour_integrable_on P\<^sub>4" unfolding P_defs by auto
  from 1 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 0" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>4 = - (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)" by (metis neg_eq_iff_add_eq_0)
  hence "\<parallel>I\<^sub>4\<parallel> = \<parallel>- (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)\<parallel>" by auto
  also have "\<dots> = \<parallel>I\<^sub>1 + I\<^sub>2 + I\<^sub>3\<parallel>" by (rule norm_minus_cancel)
  also have "\<dots> \<le> \<parallel>I\<^sub>1 + I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" using norm_triangle_ineq by auto
  finally have "\<parallel>I\<^sub>4\<parallel> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" .
  hence I\<^sub>4_val: "\<parallel>I\<^sub>4 / (2 * pi * \<i>)\<parallel> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>)"
    by (auto simp add: norm_divide norm_mult field_simps)
  define Q where "Q t \<equiv> linepath (Complex b t) (Complex U t)" for t
  define g where "g t \<equiv> contour_integral (Q t) f" for t
  have Q_1: "(f has_contour_integral I\<^sub>1) (Q (-T))"
    using 2(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f has_contour_integral -I\<^sub>3) (Q T)"
    using 2(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "\<parallel>g t\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f has_contour_integral g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f contour_integrable_on Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a powr (x + Im (Complex b t) * \<i>) / (x + Im (Complex b t) * \<i>)) has_integral (g t))
          {Re (Complex b t) .. Re (Complex U t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use assms' in auto)
    hence *: "((\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) has_integral g t) {b..U}" by auto
    hence "\<parallel>g t\<parallel> = \<parallel>integral {b..U} (\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>))\<parallel>" by (auto simp add: integral_unique)
    also have "\<dots> \<le> integral {b..U} (\<lambda>x. a powr x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) integrable_on {b..U}" using * by auto
      have "(\<lambda>x. a powr x / (of_real T)) integrable_on {b..U}"
        by (intro iffD2 [OF integrable_on_cdivide_iff] powr_integrable) (use assms' in auto)
      thus "(\<lambda>x. a powr x / T) integrable_on {b..U}" by auto
    next
      fix x assume "x \<in> {b..U}"
      have "\<parallel>a powr (x + t * \<i>)\<parallel> = Re a powr Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a powr x" by auto
      finally have 1: "\<parallel>a powr (x + t * \<i>)\<parallel> = a powr x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> \<parallel>x + t * \<i>\<parallel>" by (rule abs_Im_le_cmod)
      finally have 2: "T \<le> \<parallel>x + t * \<i>\<parallel>" .
      from 1 2 show "\<parallel>a powr (x + t * \<i>) / (x + t * \<i>)\<parallel> \<le> a powr x / T"
        by (subst norm_divide) (rule frac_le, use hT' in auto)
    qed
    also have "\<dots> = integral {b..U} (\<lambda>x. a powr x) / T" by auto
    also have "\<dots> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    proof -
      have "integral {b..U} (\<lambda>x. a powr x) \<le> a powr b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_lt_1) (use assms' in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "\<parallel>I\<^sub>2\<parallel> \<le> a powr U / U * \<parallel>Complex U T - Complex U (- T)\<parallel>"
  proof -
    have "f contour_integrable_on P\<^sub>2" by (rule 2)
    moreover have "0 \<le> a powr U / U" using hU by auto
    moreover have "\<parallel>f z\<parallel> \<le> a powr U / U"
      when *: "z \<in> closed_segment (Complex U (- T)) (Complex U T)" for z
    proof -
      from * have Re_z: "Re z = U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> \<parallel>z\<parallel>" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> \<parallel>z\<parallel>" .
      have "\<parallel>f z\<parallel> = \<parallel>a powr z\<parallel> / \<parallel>z\<parallel>" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a powr U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>2_def P\<^sub>2_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> \<le> a powr U / U * (2 * T)"
  proof -
    have "sqrt ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' by (simp add: field_simps legacy_Complex_simps)
  qed
  finally have I\<^sub>2_bound: "\<parallel>I\<^sub>2\<parallel> \<le> a powr U / U * (2 * T)" .
  have "\<parallel>I\<^sub>4 / (2 * pi * \<i>)\<parallel> \<le> 1 / (2*pi) * (\<parallel>g (- T)\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>- g T\<parallel>)"
    using I\<^sub>4_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 1 / (2*pi) * (2 * a powr b / (T * \<bar>ln a\<bar>) + a powr U / U * (2*T))"
  proof -
    have "\<parallel>g T\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
         "\<parallel>g (- T)\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>2\<parallel> \<le> 2 * a powr b / (T * \<bar>ln a\<bar>) + a powr U / U * (2*T)"
      using I\<^sub>2_bound by auto
    thus ?thesis by (auto simp add: field_simps)
  qed
  also have "\<dots> = 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
    using hT' by (auto simp add: field_simps)
  finally have "\<parallel>1 / (2 * pi * \<i>) * contour_integral (reversepath P\<^sub>4) f\<parallel>
    \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
    unfolding I\<^sub>4_def P\<^sub>4_def by (subst contour_integral_reversepath) auto
  thus ?thesis using Ha unfolding I\<^sub>4_def P\<^sub>4_def f_def F_def path_def by auto
qed

lemma perron_aux_2:
  assumes Ha: "0 < a \<and> a < 1"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)" (is "_ \<le> ?x")
proof -
  let ?y = "\<lambda>U :: real. a powr U * T / (pi * U)"
  have "((\<lambda>U :: real. ?x) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "((\<lambda>U. ?y U) \<longlongrightarrow> 0) at_top" using Ha by real_asymp
  ultimately have "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x + 0) at_top" by (rule tendsto_add)
  hence "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "\<parallel>F a\<parallel> \<le> ?x + ?y U" when hU: "0 < U" "b < U" for U
    by (subst perron_aux_2' [OF hU Ha], standard)
  hence "\<forall>\<^sub>F U in at_top. \<parallel>F a\<parallel> \<le> ?x + ?y U"
    by (rule eventually_at_top_linorderI') (use Hb in auto)
  ultimately show ?thesis
    by (intro tendsto_lowerbound) auto
qed

lemma perron_aux_3:
  assumes Ha: "0 < a"
  shows "\<parallel>1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s)\<parallel> \<le> a powr b * ln (1 + T / b)"
proof -
  have "\<parallel>1 / (2 * pi * \<i>) * contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. 1 * a powr s / s)\<parallel>
       \<le> 1 * a powr b * ln (1 + T / b)"
    by (rule perron_aux_3') (auto intro: Ha cond perron_integrable)
  thus ?thesis unfolding path_def by auto
qed

lemma perron_aux':
  assumes Ha: "0 < a"
  shows "\<parallel>F a\<parallel> \<le> a powr b * r a"
proof -
  note assms' = assms cond
  define P where "P \<equiv> 1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s)"
  have lm_1: "1 + ln (1 + T / b) \<le> 2 + ln (T / b)"
  proof -
    have "1 \<le> T / b" using hT Hb by auto
    hence "1 + T / b \<le> 2 * (T / b)" by auto
    hence "ln (1 + T / b) \<le> ln 2 + ln (T / b)"
      by (subst ln_mult_pos [symmetric]) auto
    thus ?thesis using ln_2_less_1 by auto
  qed
  have *: "\<parallel>F a\<parallel> \<le> a powr b * (2 + ln (T / b))"
  proof (cases "1 \<le> a")
    assume Ha': "1 \<le> a"
    have "\<parallel>P - 1\<parallel> \<le> \<parallel>P\<parallel> + 1" by (simp add: norm_triangle_le_diff)
    also have "\<dots> \<le> a powr b * ln (1 + T / b) + 1"
    proof -
      have "\<parallel>P\<parallel> \<le> a powr b * ln (1 + T / b)"
        unfolding P_def by (intro perron_aux_3 assms')
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> a powr b * (2 + ln (T / b))"
    proof -
      have "1 = a powr 0" using Ha' by auto
      also have "a powr 0 \<le> a powr b" using Ha' Hb by (intro powr_mono) auto
      finally have "a powr b * ln (1 + T / b) + 1 \<le> a powr b * (1 + ln (1 + T / b))"
        by (auto simp add: algebra_simps)
      also have "\<dots> \<le> a powr b * (2 + ln (T / b))" using Ha' lm_1 by auto
      finally show ?thesis .
    qed
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  next
    assume Ha': "\<not> 1 \<le> a"
    hence "\<parallel>P\<parallel> \<le> a powr b * ln (1 + T / b)"
      unfolding P_def by (intro perron_aux_3 assms')
    also have "\<dots> \<le> a powr b * (2 + ln (T / b))"
      by (rule mult_left_mono) (use lm_1 in auto)
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  qed
  consider "0 < a \<and> a \<noteq> 1" | "a = 1" using Ha by linarith
  thus ?thesis proof cases
    define c where "c = 1 / 2 * a powr b / (T * \<bar>ln a\<bar>)"
    assume Ha': "0 < a \<and> a \<noteq> 1"
    hence "(0 < a \<and> a < 1) \<or> a > 1" by auto
    hence "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)"
      using perron_aux_1 perron_aux_2 by auto
    also have "\<dots> \<le> c" unfolding c_def
      using Ha' hT' pi_gt3 by (auto simp add: field_simps)
    finally have "\<parallel>F a\<parallel> \<le> c" .
    hence "\<parallel>F a\<parallel> \<le> min c (a powr b * (2 + ln (T / b)))" using * by auto
    also have "\<dots> = a powr b * r a"
      unfolding r_def c_def using Ha' by auto (subst min_mult_distrib_left, auto)
    finally show ?thesis using Ha' unfolding P_def by auto
  next
    assume Ha': "a = 1"
    with * show ?thesis unfolding r_def by auto
  qed
qed

lemma r_bound:
  assumes Hn: "1 \<le> n"
  shows "r (x / n) \<le> H / T + (if n \<in> region then 2 + ln (T / b) else 0)"
proof (cases "n \<in> region")
  assume *: "n \<notin> region"
  then consider "n < x - x / H" | "x + x / H < n" unfolding region_def by auto
  hence "1 / \<bar>ln (x / n)\<bar> \<le> 2 * H"
  proof cases
    have hH': "1 / (1 - 1 / H) > 1" using hH by auto
    case 1 hence "x / n > x / (x - x / H)"
      using Hx hH Hn by (intro divide_strict_left_mono) auto
    also have "x / (x - x / H) = 1 / (1 - 1 / H)"
      using Hx hH by (auto simp add: field_simps)
    finally have xn: "x / n > 1 / (1 - 1 / H)" .
    moreover have xn': "x / n > 1" using xn hH' by linarith
    ultimately have "\<bar>ln (x / n)\<bar> > ln (1 / (1 - 1 / H))"
      using hH Hx Hn by auto
    hence "1 / \<bar>ln (x / n)\<bar> < 1 / ln (1 / (1 - 1 / H))"
      using xn' hH' by (intro divide_strict_left_mono mult_pos_pos ln_gt_zero) auto
    also have "\<dots> \<le> H" proof -
      have "ln (1 - 1 / H) \<le> - (1 / H)"
        using hH by (intro ln_one_minus_pos_upper_bound) auto
      hence "-1 / ln (1 - 1 / H) \<le> -1 / (- (1 / H))"
        using hH by (intro divide_left_mono_neg) (auto intro: divide_neg_pos)
      also have "... = H" by auto
      finally show ?thesis
        by (subst (2) inverse_eq_divide [symmetric])
           (subst ln_inverse, use hH in auto)
    qed
    finally show ?thesis using hH by auto
  next
    case 2 hence "x / n < x / (x + x / H)"
      using Hx hH Hn by (auto intro!: divide_strict_left_mono mult_pos_pos add_pos_pos)
    also have "\<dots> = 1 / (1 + 1 / H)"
    proof -
      have "0 < x + x * H" using Hx hH by (auto intro: add_pos_pos)
      thus ?thesis using Hx hH by (auto simp add: field_simps)
    qed
    finally have xn: "x / n < 1 / (1 + 1 / H)" .
    also have hH': "\<dots> < 1" using hH by (auto simp add: field_simps)
    finally have xn': "0 < x / n \<and> x / n < 1" using Hx Hn by auto
    have "1 / \<bar>ln (x / n)\<bar> = -1 / ln (x / n)"
      using xn' by (auto simp add: field_simps)
    also have "\<dots> \<le> 2 * H" proof -
      have "ln (x / n) < ln (1 / (1 + 1 / H))"
        using xn xn' by (subst ln_less_cancel_iff) (blast, linarith)
      also have "\<dots> = - ln (1 + 1 / H)"
        by (simp add: divide_inverse ln_inverse)
      also have "\<dots> \<le> - 1 / (2 * H)"
      proof -
        have "- ln (1 + 1 / H) = ln (inverse (1 + 1 / H))"
          by (simp add: ln_inverse)
        also have "\<dots> = ln (1 - 1 / (H + 1))"
          using hH by (auto simp: field_simps)
        also have "\<dots> \<le> - (1 / (H + 1))"
          using hH by (auto intro: ln_one_minus_pos_upper_bound)
        also have "\<dots> \<le> - 1 / (2 * H)"
          using hH by (auto simp: field_simps)
        finally show ?thesis .
      qed
      finally have "-1 / ln (x / n) \<le> -1 / (-1 / (2 * H))"
        by (intro divide_left_mono_neg) (insert xn' hH, auto simp add: field_simps)
      thus ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "(1 / \<bar>ln (x / n)\<bar>) / (2 * T) \<le> (2 * H) / (2 * T)"
    using hT' by (intro divide_right_mono) auto
  hence "1 / (2 * T * \<bar>ln (x / n)\<bar>) \<le> H / T"
    by (simp add: field_simps)
  moreover have "x / n \<noteq> 1" using * hH unfolding region_def by auto
  ultimately show ?thesis unfolding r_def using * by auto
next
  assume *: "n \<in> region"
  moreover have "2 + ln (T / b) \<le> H / T + (2 + ln (T / b))"
    using hH hT' by auto
  ultimately show ?thesis unfolding r_def by auto
qed

lemma perron_aux:
  assumes Hn: "0 < n"
  shows "\<parallel>F' n\<parallel> \<le> 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then 3 * (2 + ln (T / b)) else 0)" (is "?P \<le> ?Q")
proof -
  have "\<parallel>F (x / n)\<parallel> \<le> (x / n) powr b * r (x / n)"
    by (rule perron_aux') (use Hx Hn in auto)
  also have "\<dots> \<le> (x / n) powr b * (H / T + (if n \<in> region then 2 + ln (T / b) else 0))"
    by (intro mult_left_mono r_bound) (use Hn in auto)
  also have "\<dots> \<le> ?Q"
  proof -
    have *: "(x / n) powr b * (H / T) = 1 / n nat_powr b * (x powr b * H / T)"
      using Hx Hn by (subst powr_divide) (auto simp add: field_simps)
    moreover have "(x / n) powr b * (H / T + (2 + ln (T / b)))
      \<le> 1 / n nat_powr b * (x powr b * H / T) + 3 * (2 + ln (T / b))"
      when Hn': "n \<in> region"
    proof -
      have "(x / n) powr b \<le> 3"
      proof -
        have "x - x / H \<le> n" using Hn' unfolding region_def by auto
        moreover have "x / H < x / 1" using hH Hx by (intro divide_strict_left_mono) auto
        ultimately have "x / n \<le> x / (x - x / H)"
          using Hx hH Hn by (intro divide_left_mono mult_pos_pos) auto
        also have "\<dots> = 1 + 1 / (H - 1)"
          using Hx hH by (auto simp add: field_simps)
        finally have "(x / n) powr b \<le> (1 + 1 / (H - 1)) powr b"
          using Hx Hn Hb by (intro powr_mono2) auto
        also have "\<dots> \<le> exp (b / (H - 1))"
        proof -
          have "ln (1 + 1 / (H - 1)) \<le> 1 / (H - 1)"
            using hH by (intro ln_add_one_self_le_self) auto
          hence "b * ln (1 + 1 / (H - 1)) \<le> b * (1 / (H - 1))"
            using Hb by (intro mult_left_mono) auto
          thus ?thesis unfolding powr_def by auto
        qed
        also have "\<dots> \<le> exp 1" using Hb hH' by auto
        also have "\<dots> \<le> 3" by (rule exp_le)
        finally show ?thesis .
      qed
      moreover have "0 \<le> ln (T / b)" using hT Hb by (auto intro!: ln_ge_zero)
      ultimately show ?thesis using hT
        by (subst ring_distribs, subst *, subst add_le_cancel_left)
           (intro mult_right_mono, auto intro!: add_nonneg_nonneg)
    qed
    ultimately show ?thesis by auto
  qed
  finally show ?thesis unfolding F'_def .
qed

definition a where "a n \<equiv> fds_nth f n"

lemma finite_region: "finite region"
  unfolding region_def by (subst nat_le_real_iff) auto

lemma zero_notin_region: "0 \<notin> region"
  unfolding region_def using hH Hx by (auto simp add: field_simps)

lemma path_image_conv:
  assumes "s \<in> img_path"
  shows "conv_abscissa f < s \<bullet> 1"
proof -
  from assms have "Re s = b"
    unfolding img_path_def path_def
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  thus ?thesis using Hb' conv_le_abs_conv_abscissa [of f] by auto
qed

lemma converge_on_path:
  assumes "s \<in> img_path"
  shows "fds_converges f s"
  by (intro fds_converges path_image_conv assms)

lemma summable_on_path:
  assumes "s \<in> img_path"
  shows "(\<lambda>n. a n / n nat_powr s) subsummable {1..}"
  unfolding a_def by (intro eval_fds_complex_subsum(2) converge_on_path assms)

lemma zero_notin_path:
  shows "0 \<notin> closed_segment (Complex b (- T)) (Complex b T)"
  using Hb unfolding img_path_def path_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

lemma perron_bound:
  "\<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel> \<le> x powr b * H * B / T
    + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
proof -
  define M where "M \<equiv> 3 * (2 + ln (T / b))"
  have sum_1: "(\<lambda>n. \<parallel>a n / n nat_powr (b :: complex)\<parallel>) subsummable {1..}"
    unfolding a_def
    by (fold nat_power_complex_def)
       (fastforce intro: Hb' fds_abs_subsummable fds_abs_converges)
  hence sum_2: "(\<lambda>n. \<parallel>a n\<parallel> * 1 / n nat_powr b) subsummable {1..}"
  proof -
    have "\<parallel>a n / n nat_powr (b :: complex)\<parallel> = \<parallel>a n\<parallel> * 1 / n nat_powr b" for n
      by (auto simp add: norm_divide field_simps norm_powr_real_powr')
    thus ?thesis using sum_1 by auto
  qed
  hence sum_3: "(\<lambda>n. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)) subsummable {1..}"
    by (rule subsummable_mult2)
  moreover have sum_4: "(\<lambda>n. if n \<in> region then M * \<parallel>a n\<parallel> else 0) subsummable {1..}"
    by (intro has_subsum_summable, rule has_subsum_If_finite)
       (insert finite_region, auto)
  moreover have "\<parallel>a n * F' n\<parallel>
    \<le> \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then M * \<parallel>a n\<parallel> else 0)" (is "?x' \<le> ?x")
    when "n \<in> {1..}" for n
  proof -
    have "\<parallel>a n * F' n\<parallel> \<le> \<parallel>a n\<parallel> *
      (1 / n nat_powr b * (x powr b * H / T) + (if n \<in> region then M else 0))"
      unfolding M_def
      by (subst norm_mult)
         (intro mult_left_mono perron_aux, use that in auto)
    also have "\<dots> = ?x" by (simp add: field_simps)
    finally show ?thesis .
  qed
  ultimately have "\<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel>
    \<le> (\<Sum>`n \<ge> 1. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then M * \<parallel>a n\<parallel> else 0))"
    by (intro subsum_norm_bound subsummable_add)
  also have "\<dots> \<le> x powr b * H * B / T + M * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
  proof -
    have "(\<Sum>`n \<ge> 1. (if n \<in> region then M * \<parallel>a n\<parallel> else 0))
        = (\<Sum>n \<in> region \<inter> {1..}. M * \<parallel>a n\<parallel>)"
      by (intro subsumI [symmetric] has_subsum_If_finite_set finite_region)
    also have "\<dots> = M * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
    proof -
      have "region \<inter> {1..} = region"
        using zero_notin_region zero_less_iff_neq_zero by (auto intro: Suc_leI)
      thus ?thesis by (subst sum_distrib_left) (use zero_notin_region in auto)
    qed
    also have
      "(\<Sum>`n \<ge> 1. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T))
      \<le> x powr b * H * B / T"
      by (subst subsum_mult2, rule sum_2, insert hB hH hT', fold a_def)
         (auto simp add: field_simps, subst (1) mult.commute, auto intro: mult_right_mono)
    ultimately show ?thesis
      by (subst subsum_add [symmetric]) ((rule sum_3 sum_4)+, auto)
  qed
  finally show ?thesis unfolding M_def .
qed

lemma perron:
  "(\<lambda>s. eval_fds f s * x powr s / s) contour_integrable_on path"
  "\<parallel>sum_upto a x - 1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. eval_fds f s * x powr s / s)\<parallel>
    \<le> x powr b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
proof (goal_cases)
  define g where "g s \<equiv> eval_fds f s * x powr s / s" for s :: complex
  define h where "h s n \<equiv> a n / n nat_powr s * (x powr s / s)" for s :: complex and n :: nat
  define G where "G n \<equiv> contour_integral path (\<lambda>s. (x / n) powr s / s)" for n :: nat
  define H where "H n \<equiv> 1 / (2 * pi * \<i>) * G n" for n :: nat
  have h_integrable: "(\<lambda>s. h s n) contour_integrable_on path" when "0 < n" for n
    using Hb Hx unfolding path_def h_def
    by (intro contour_integrable_continuous_linepath continuous_intros)
       (use that zero_notin_path in auto)
  have "contour_integral path g = contour_integral path (\<lambda>s. \<Sum>`n \<ge> 1. h s n)"
  proof (rule contour_integral_eq, fold img_path_def)
    fix s assume *: "s \<in> img_path"
    hence "g s = (\<Sum>`n \<ge> 1. a n / n nat_powr s) * (x powr s / s)"
      unfolding g_def a_def
      by (subst eval_fds_complex_subsum) (auto intro!: converge_on_path)
    also have "\<dots> = (\<Sum>`n \<ge> 1. a n / n nat_powr s * (x powr s / s))"
      by (intro subsum_mult2 [symmetric] summable) (intro summable_on_path *)
    finally show "g s = (\<Sum>`n \<ge> 1. h s n)" unfolding h_def .
  qed
  also have
    sum_1: "(\<lambda>n. contour_integral path (\<lambda>s. h s n)) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. contour_integral path (\<lambda>s. h s n))"
  proof (goal_cases)
    have "((\<lambda>N. contour_integral path (\<lambda>s. sum (h s) {1..N}))
      \<longlongrightarrow> contour_integral path (\<lambda>s. subsum (h s) {1..})) at_top"
    proof (rule contour_integral_uniform_limit)
      show "valid_path path" unfolding path_def by auto
      show "sequentially \<noteq> bot" by auto
    next
      fix t :: real
      show "\<parallel>vector_derivative path (at t)\<parallel> \<le> sqrt (4 * T\<^sup>2)"
        unfolding path_def by (auto simp add: legacy_Complex_simps)
    next
      from path_image_conv
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n\<le>N. fds_nth f n / nat_power n s)"
        by (intro uniformly_convergent_eval_fds) (unfold path_def img_path_def, auto)
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)"
      proof -
        have "(\<Sum>n\<le>N. fds_nth f n / nat_power n s) = (\<Sum>n = 1..N. a n / n nat_powr s)" for N s
        proof -
          have "(\<Sum>n\<le>N. fds_nth f n / nat_power n s) = (\<Sum>n\<le>N. a n / n nat_powr s)"
            unfolding a_def nat_power_complex_def by auto
          also have "\<dots> = (\<Sum>n\<in>{..N} - {0}. a n / n nat_powr s)"
            by (subst sum_diff1) auto
          also have "\<dots> = (\<Sum>n = 1..N. a n / n nat_powr s)"
          proof -
            have "{..N} - {0} = {1..N}" by auto
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
        thus ?thesis using * by auto
      qed
      hence "uniform_limit img_path
        (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)
        (\<lambda>s. \<Sum>`n \<ge> 1. a n / n nat_powr s) at_top"
      proof -
        have "uniform_limit img_path
          (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)
          (\<lambda>s. lim (\<lambda>N. \<Sum>n = 1..N. a n / n nat_powr s)) at_top"
          using * by (subst (asm) uniformly_convergent_uniform_limit_iff)
        moreover have "lim (\<lambda>N. \<Sum>n = 1..N. a n / n nat_powr s) = (\<Sum>`n \<ge> 1. a n / n nat_powr s)" for s
          by (rule subsum_ge_limit)
        ultimately show ?thesis by auto
      qed
      moreover have "bounded ((\<lambda>s. subsum (\<lambda>n. a n / n nat_powr s) {1..}) ` img_path)" (is "bounded ?A")
      proof -
        have "bounded (eval_fds f ` img_path)"
          by (intro compact_imp_bounded compact_continuous_image continuous_on_eval_fds)
             (use path_image_conv img_path_def path_def in auto)
        moreover have "\<dots> = ?A"
          unfolding a_def by (intro image_cong refl eval_fds_complex_subsum(1) converge_on_path)
        ultimately show ?thesis by auto
      qed
      moreover have "0 \<notin> closed_segment (Complex b (- T)) (Complex b T)"
        using Hb by (auto simp: closed_segment_def legacy_Complex_simps algebra_simps)
      hence "bounded ((\<lambda>s. x powr s / s) ` img_path)"
        unfolding img_path_def path_def using Hx Hb
        by (intro compact_imp_bounded compact_continuous_image continuous_intros) auto
      ultimately have "uniform_limit img_path
        (\<lambda>N s. (\<Sum>n = 1..N. a n / n nat_powr s) * (x powr s / s))
        (\<lambda>s. (\<Sum>`n \<ge> 1. a n / n nat_powr s) * (x powr s / s)) at_top" (is ?P)
        by (intro uniform_lim_mult uniform_limit_const)
      moreover have "?P = uniform_limit (path_image path)
        (\<lambda>N s. sum (h s) {1..N}) (\<lambda>s. subsum (h s) {1..}) at_top" (is "?P = ?Q")
        unfolding h_def
        by (fold img_path_def, rule uniform_limit_cong', subst sum_distrib_right [symmetric], rule refl)
           (subst subsum_mult2, intro summable_on_path, auto)
      ultimately show ?Q by blast
    next
      from h_integrable
      show "\<forall>\<^sub>F N in at_top. (\<lambda>s. sum (h s) {1..N}) contour_integrable_on path"
        unfolding h_def by (intro eventuallyI contour_integrable_sum) auto
    qed
    hence *: "has_subsum (\<lambda>n. contour_integral path (\<lambda>s. h s n)) {1..} (contour_integral path (\<lambda>s. subsum (h s) {1..}))"
      using h_integrable by (subst (asm) contour_integral_sum) (auto intro: has_subsum_ge_limit)
    case 1 from * show ?case unfolding h_def by (intro has_subsum_summable)
    case 2 from * show ?case unfolding h_def by (rule subsumI)
  qed
  note this(2) also have
    sum_2: "(\<lambda>n. a n * G n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n)"
  proof (goal_cases)
    have *: "a n * G n = contour_integral path (\<lambda>s. h s n)" when Hn: "n \<in> {1..}" for n :: nat
    proof -
      have "(\<lambda>s. (x / n) powr s / s) contour_integrable_on path"
        unfolding path_def by (rule perron_integrable) (use Hn Hx hT in auto)
      moreover have "contour_integral path (\<lambda>s. h s n) = contour_integral path (\<lambda>s. a n * ((x / n) powr s / s))"
      proof (intro contour_integral_cong refl)
        fix s :: complex
        have "(x / n) powr s * n powr s = ((x / n :: complex) * n) powr s"
          by (rule powr_times_real [symmetric]) (use Hn Hx in auto)
        also have "\<dots> = x powr s" using Hn by auto
        finally have "(x / n) powr s = x powr s / n powr s" using Hn by (intro eq_divide_imp) auto
        thus "h s n = a n * ((x / n) powr s / s)" unfolding h_def by (auto simp add: field_simps)
      qed
      ultimately show ?thesis unfolding G_def by (subst (asm) contour_integral_lmul) auto
    qed
    case 1 show ?case by (subst subsummable_cong) (use * sum_1 in auto)
    case 2 show ?case by (intro subsum_cong * [symmetric])
  qed
  note this(2) finally have
    "1 / (2 * pi * \<i>) * contour_integral path g = (\<Sum>`n \<ge> 1. a n * G n) * (1 / (2 * pi * \<i>))" by auto
  also have
    sum_3: "(\<lambda>n. a n * G n * (1 / (2 * pi * \<i>))) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n * (1 / (2 * pi * \<i>)))"
    by (intro subsummable_mult2 subsum_mult2 [symmetric] sum_2)+
  note this(2) also have
    sum_4: "(\<lambda>n. a n * H n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * H n)"
    unfolding H_def using sum_3 by auto
  note this(2) also have
    "\<dots> - (\<Sum>`n \<ge> 1. if n \<le> x then a n else 0)
      = (\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0))"
    using sum_4
    by (rule subsum_minus(1), unfold subsummable_def)
       (auto simp add: if_if_eq_conj nat_le_real_iff)
  moreover have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = sum_upto a x"
  proof -
    have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = (\<Sum>n :: nat|n \<in> {1..} \<and> n \<le> x. a n)"
      by (intro subsumI [symmetric] has_subsum_If_finite) (auto simp add: nat_le_real_iff)
    also have "\<dots> = sum_upto a x"
    proof -
      have "{n :: nat. n \<in> {1..} \<and> n \<le> x} = {n. 0 < n \<and> n \<le> x}" by auto
      thus ?thesis unfolding sum_upto_def by auto
    qed
    finally show ?thesis .
  qed
  moreover have "(\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0)) = (\<Sum>`n \<ge> 1. a n * F' n)"
    unfolding F_def F'_def G_def H_def by (rule subsum_cong) (auto simp add: algebra_simps)
  ultimately have result: "\<parallel>sum_upto a x - 1 / (2 * pi * \<i>) * contour_integral path g\<parallel> = \<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel>"
    by (subst norm_minus_commute) auto
  case 1 show ?case
  proof -
    have "closed_segment (Complex b (- T)) (Complex b T) \<subseteq> {s. conv_abscissa f < ereal (s \<bullet> 1)}"
      using path_image_conv unfolding img_path_def path_def by auto
    thus ?thesis unfolding path_def
      by (intro contour_integrable_continuous_linepath continuous_intros)
         (use Hx zero_notin_path in auto)
  qed
  case 2 show ?case using perron_bound result unfolding g_def by linarith
qed
end

theorem perron_formula:
  fixes b B H T x :: real and f :: "complex fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "1 < H" and hH': "b + 1 \<le> H" and Hx: "0 < x"
    and hB: "(\<Sum>`n \<ge> 1. \<parallel>fds_nth f n\<parallel> / n nat_powr b) \<le> B"
  shows "(\<lambda>s. eval_fds f s * x powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
        "\<parallel>sum_upto (fds_nth f) x - 1 / (2 * pi * \<i>) *
          contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. eval_fds f s * x powr s / s)\<parallel>
         \<le> x powr b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n | x - x / H \<le> n \<and> n \<le> x + x / H. \<parallel>fds_nth f n\<parallel>)"
proof (goal_cases)
  interpret z: perron_locale using assms unfolding perron_locale_def by auto
  case 1 show ?case using z.perron(1) unfolding z.path_def .
  case 2 show ?case using z.perron(2) unfolding z.path_def z.region_def z.a_def .
qed

theorem perron_asymp:
  fixes b x :: real
  assumes b: "b > 0" "ereal b > abs_conv_abscissa f"
  assumes x: "0 < x" "x \<notin> \<nat>"
  defines "L \<equiv> (\<lambda>T. linepath (Complex b (-T)) (Complex b T))"
  shows   "((\<lambda>T. contour_integral (L T) (\<lambda>s. eval_fds f s * of_real x powr s / s))
               \<longlongrightarrow> 2 * pi * \<i> * sum_upto (\<lambda>n. fds_nth f n) x) at_top"
proof -
  define R where "R = (\<lambda>H. {n. x - x / H \<le> real n \<and> real n \<le> x + x / H})"
  have R_altdef: "R H = {n. dist (of_nat n) x \<le> x / H}" for H
    unfolding R_def by (intro Collect_cong) (auto simp: dist_norm)
  obtain H where H: "H > 1" "H \<ge> b + 1" "R H = (if x \<in> \<nat> then {nat \<lfloor>x\<rfloor>} else {})"
  proof (cases "x \<in> \<nat>")
    case True thus ?thesis using x by auto
  next
    case False
    define d where "d = setdist {x} \<nat>"
    have "0 \<in> (\<nat> :: real set)" by auto
    hence "(\<nat> :: real set) \<noteq> {}" by blast
    hence "d > 0"
      unfolding d_def using False by (subst setdist_gt_0_compact_closed) auto
    define H where "H = Max {2, b + 1, 2 * x / d}"
    have H: "H \<ge> 2" "H \<ge> b + 1" "H \<ge> 2 * x / d"
      unfolding H_def by (rule Max.coboundedI; simp)+
    
    show ?thesis
    proof (rule that[of H])
      have "n \<notin> R H" for n :: nat
      proof -
        have "x / H \<le> x / (2 * x / d)"
          using H x \<open>d > 0\<close> 
          by (intro divide_left_mono) (auto intro!: mult_pos_pos)
        also have "\<dots> < d"
          using x \<open>d > 0\<close> by simp
        also have "d \<le> dist (of_nat n) x"
          unfolding d_def by (subst dist_commute, rule setdist_le_dist) auto
        finally show "n \<notin> R H"
          by (auto simp: R_altdef)
      qed
      thus "R H = (if x \<in> \<nat> then {nat \<lfloor>x\<rfloor>} else {})"
        using False by auto
    qed (use H in auto)
  qed

  define g where "g = (\<lambda>s. eval_fds f s * of_real x powr s / s)"
  define I where "I = (\<lambda>T. contour_integral (L T) g)"
  define c where "c = 2 * pi * \<i>"
  define A where "A = sum_upto (fds_nth f)"
  define B where "B = subsum (\<lambda>n. norm (fds_nth f n) / n nat_powr b) {0\<^sub>+..}"
  define X where "X = (if x \<in> \<int> then {nat \<lfloor>x\<rfloor>} else {})"
  
  have norm_le: "norm (A x - I T / c) \<le> x powr b * H * B / T" if T: "T \<ge> b" for T
  proof -
    interpret perron_locale b B H T x f
      by standard (use b T x H(1,2) in \<open>auto simp: B_def\<close>)
    from perron
    have "norm (A x - I T / c) \<le> x powr b * H * B / T
        + 3 * (\<Sum>n\<in>R H. norm (fds_nth f n)) * (2 + ln (T / b))"
      by (simp add: I_def A_def g_def a_def local.path_def L_def c_def R_def 
                    region_def algebra_simps)
    also have "(\<Sum>n\<in>R H. norm (fds_nth f n)) = 0"
      using x H by auto
    finally show "norm (A x - I T / c) \<le> x powr b * H * B / T"
      by simp
  qed
  have "eventually (\<lambda>T. norm (A x - I T / c) \<le> x powr b * H * B / T) at_top"
    using eventually_ge_at_top[of b] by eventually_elim (use norm_le in auto)
  moreover have "((\<lambda>T. x powr b * H * B / T) \<longlongrightarrow> 0) at_top"
    by real_asymp
  ultimately have lim: "((\<lambda>T. A x - I T / c) \<longlongrightarrow> 0) at_top"
    using Lim_null_comparison by fast
  have "((\<lambda>T. -c * (A x - I T / c) + c * A x) \<longlongrightarrow> -c * 0 + c * A x) at_top"
    by (rule tendsto_intros lim)+
  also have "(\<lambda>T. -c * (A x - I T / c) + c * A x) = I"
    by (simp add: algebra_simps c_def)
  finally show ?thesis
    by (simp add: c_def A_def I_def g_def)
qed

unbundle no_pnt_syntax
end
