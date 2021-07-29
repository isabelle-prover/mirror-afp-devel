(*  Title:       Preliminaries for hybrid systems verification
    Author:      Jonathan Julián Huerta y Munive, 2021
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Hybrid Systems Preliminaries \<close>

text \<open>Hybrid systems combine continuous dynamics with discrete control. This section contains
auxiliary lemmas for verification of hybrid systems.\<close>

theory HS_Preliminaries
  imports "Ordinary_Differential_Equations.Picard_Lindeloef_Qualitative"
begin

\<comment> \<open> Notation \<close>

bundle derivative_notation
begin

no_notation has_vderiv_on (infix "(has'_vderiv'_on)" 50)

notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
     and has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)

end

bundle derivative_no_notation
begin

notation has_vderiv_on (infix "(has'_vderiv'_on)" 50)

no_notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
     and has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)

end

unbundle derivative_notation

notation norm ("\<parallel>_\<parallel>")

subsection \<open> Real numbers \<close>

lemma abs_le_eq:
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
  by linarith+

lemma real_ivl_eqs:
  assumes "0 < r"
  shows "ball x r = {x-r<--< x+r}"         and "{x-r<--< x+r} = {x-r<..< x+r}"
    and "ball (r / 2) (r / 2) = {0<--<r}"  and "{0<--<r} = {0<..<r}"
    and "ball 0 r = {-r<--<r}"             and "{-r<--<r} = {-r<..<r}"
    and "cball x r = {x-r--x+r}"           and "{x-r--x+r} = {x-r..x+r}"
    and "cball (r / 2) (r / 2) = {0--r}"   and "{0--r} = {0..r}"
    and "cball 0 r = {-r--r}"              and "{-r--r} = {-r..r}"
  unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
  using assms by (auto simp: cball_def ball_def dist_norm field_simps)

lemma is_interval_real_nonneg[simp]: "is_interval (Collect ((\<le>) (0::real)))"
  by (auto simp: is_interval_def)

lemma norm_rotate_eq[simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq)
  thus "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: add.commute add.left_commute power2_diff power2_sum)
qed

lemma sum_eq_Sum:
  assumes "inj_on f A"
  shows "(\<Sum>x\<in>A. f x) = (\<Sum> {f x |x. x \<in> A})"
proof-
  have "(\<Sum> {f x |x. x \<in> A}) = (\<Sum> (f ` A))"
    apply(auto simp: image_def)
    by (rule_tac f=Sum in arg_cong, auto)
  also have "... = (\<Sum>x\<in>A. f x)"
    by (subst sum.image_eq[OF assms], simp)
  finally show "(\<Sum>x\<in>A. f x) = (\<Sum> {f x |x. x \<in> A})"
    by simp
qed

lemma triangle_norm_vec_le_sum: "\<parallel>x\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>x $ i\<parallel>)"
  by (simp add: L2_set_le_sum norm_vec_def)


subsection \<open> Single variable derivatives \<close>

named_theorems poly_derivatives "compilation of optimised miscellaneous derivative rules."

declare has_vderiv_on_const [poly_derivatives]
    and has_vderiv_on_id [poly_derivatives]
    and has_vderiv_on_add[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_diff[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_mult[THEN has_vderiv_on_eq_rhs, poly_derivatives]
    and has_vderiv_on_ln[poly_derivatives]

lemma vderiv_on_composeI:
  assumes "D f = f' on g ` T" 
    and " D g = g' on T"
    and "h = (\<lambda>t. g' t *\<^sub>R f' (g t))"
  shows "D (\<lambda>t. f (g t)) = h on T"
  apply(subst ssubst[of h], simp)
  using assms has_vderiv_on_compose by auto

lemma vderiv_uminusI[poly_derivatives]:
  "D f = f' on T \<Longrightarrow> g = (\<lambda>t. - f' t) \<Longrightarrow> D (\<lambda>t. - f t) = g on T"
  using has_vderiv_on_uminus by auto

lemma vderiv_npowI[poly_derivatives]:
  fixes f::"real \<Rightarrow> real"
  assumes "n \<ge> 1" and "D f = f' on T" and "g = (\<lambda>t. n * (f' t) * (f t)^(n-1))"
  shows "D (\<lambda>t. (f t)^n) = g on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro: derivative_eq_intros simp: field_simps)

lemma vderiv_divI[poly_derivatives]:
  assumes "\<forall>t\<in>T. g t \<noteq> (0::real)" and "D f = f' on T"and "D g = g' on T" 
    and "h = (\<lambda>t. (f' t * g t - f t * (g' t)) / (g t)^2)"
  shows "D (\<lambda>t. (f t)/(g t)) = h on T"
  apply(subgoal_tac "(\<lambda>t. (f t)/(g t)) = (\<lambda>t. (f t) * (1/(g t)))")
   apply(erule ssubst, rule poly_derivatives(5)[OF assms(2)])
  apply(rule vderiv_on_composeI[where g=g and f="\<lambda>t. 1/t" and f'="\<lambda>t. - 1/t^2", OF _ assms(3)])
  apply(subst has_vderiv_on_def, subst has_vector_derivative_def, clarsimp)
   using assms(1) apply(force intro!: derivative_eq_intros simp: fun_eq_iff power2_eq_square)
   using assms by (auto simp: field_simps power2_eq_square)

lemma vderiv_cosI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. - (f' t) * sin (f t))"
  shows "D (\<lambda>t. cos (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. cos t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

lemma vderiv_sinI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * cos (f t))"
  shows "D (\<lambda>t. sin (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. sin t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

lemma vderiv_expI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * exp (f t))"
  shows "D (\<lambda>t. exp (f t)) = g on T"
  apply(rule vderiv_on_composeI[OF _ assms(1), of "\<lambda>t. exp t"])
  unfolding has_vderiv_on_def has_vector_derivative_def 
  by (auto intro!: derivative_eq_intros simp: assms)

\<comment> \<open>Examples for checking derivatives\<close>

lemma "D (*) a = (\<lambda>t. a) on T"
  by (auto intro!: poly_derivatives)

lemma "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "(a::real) \<noteq> 0 \<Longrightarrow> D f = f' on T \<Longrightarrow> g = (\<lambda>t. (f' t)/a) \<Longrightarrow> D (\<lambda>t. (f t)/a) = g on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "\<forall>t\<in>T. f t \<noteq> (0::real) \<Longrightarrow> D f = f' on T \<Longrightarrow> g = (\<lambda>t. - a * f' t / (f t)^2) \<Longrightarrow> 
  D (\<lambda>t. a/(f t)) = g on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  by(auto intro!: poly_derivatives)

lemma "D x = x' on (\<lambda>\<tau>. \<tau> + t) ` T \<Longrightarrow> D (\<lambda>\<tau>. x (\<tau> + t)) = (\<lambda>\<tau>. x' (\<tau> + t)) on T"
  by (rule vderiv_on_composeI, auto intro: poly_derivatives)

lemma "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  by (auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. a5 * t^5 + a3 * (t^3 / c) - a2 * exp (t^2) + a1 * cos t + a0) = 
  (\<lambda>t. 5 * a5 * t^4 + 3 * a3 * (t^2 / c) - 2 * a2 * t * exp (t^2) - a1 * sin t) on T"
  by(auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. - a3 * exp (t^3 / c) + a1 * sin t + a2 * t^2) = 
  (\<lambda>t. a1 * cos t + 2 * a2 * t - 3 * a3 * t^2 / c * exp (t^3 / c)) on T"
  by(auto intro!: poly_derivatives simp: power2_eq_square)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. exp (a * sin (cos (t^4) / c))) = 
  (\<lambda>t. - 4 * a * t^3 * sin (t^4) / c * cos (cos (t^4) / c) * exp (a * sin (cos (t^4) / c))) on T"
  by (intro poly_derivatives) (auto intro!: poly_derivatives simp: power2_eq_square)


subsection \<open> Intermediate Value Theorem \<close>

lemma IVT_two_functions:
  fixes f :: "('a::{linear_continuum_topology, real_vector}) \<Rightarrow> 
  ('b::{linorder_topology,real_normed_vector,ordered_ab_group_add})"
  assumes conts: "continuous_on {a..b} f" "continuous_on {a..b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b " and "a \<le> b"
    shows "\<exists>x\<in>{a..b}. f x = g x"
proof-
  let "?h x" = "f x - g x"
  have "?h a \<le> 0" and "?h b \<ge> 0"
    using ahyp bhyp by simp_all
  also have "continuous_on {a..b} ?h"
    using conts continuous_on_diff by blast 
  ultimately obtain x where "a \<le> x" "x \<le> b" and "?h x = 0"
    using IVT'[of "?h"] \<open>a \<le> b\<close> by blast
  thus ?thesis
    using \<open>a \<le> b\<close> by auto
qed

lemma IVT_two_functions_real_ivl:
  fixes f :: "real \<Rightarrow> real"
  assumes conts: "continuous_on {a--b} f" "continuous_on {a--b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b "
    shows "\<exists>x\<in>{a--b}. f x = g x"
proof(cases "a \<le> b")
  case True
  then show ?thesis 
    using IVT_two_functions assms 
    unfolding closed_segment_eq_real_ivl by auto
next
  case False
  hence "a \<ge> b"
    by auto
  hence "continuous_on {b..a} f" "continuous_on {b..a} g"
    using conts False unfolding closed_segment_eq_real_ivl by auto
  hence "\<exists>x\<in>{b..a}. g x = f x"
    using IVT_two_functions[of b a g f] assms(3,4) False by auto
  then show ?thesis  
    using \<open>a \<ge> b\<close> unfolding closed_segment_eq_real_ivl by auto force
qed


subsection \<open> Filters \<close>

lemma eventually_at_within_mono:
  assumes "t \<in> interior T" and "T \<subseteq> S"
    and "eventually P (at t within T)"
  shows "eventually P (at t within S)"
  by (meson assms eventually_within_interior interior_mono subsetD)

lemma netlimit_at_within_mono:
  fixes t::"'a::{perfect_space,t2_space}"
  assumes "t \<in> interior T" and "T \<subseteq> S"
  shows "netlimit (at t within S) = t"
  using assms(1) interior_mono[OF \<open>T \<subseteq> S\<close>] netlimit_within_interior by auto

lemma has_derivative_at_within_mono:
  assumes "(t::real) \<in> interior T" and "T \<subseteq> S"
    and "D f \<mapsto> f' at t within T"
  shows "D f \<mapsto> f' at t within S"
  using assms(3) apply(unfold has_derivative_def tendsto_iff, safe)
  unfolding netlimit_at_within_mono[OF assms(1,2)] netlimit_within_interior[OF assms(1)]
  by (rule eventually_at_within_mono[OF assms(1,2)]) simp

lemma eventually_all_finite2:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h:"\<forall>i. eventually (P i) F"
  shows "eventually (\<lambda>x. \<forall>i. P i x) F"
proof(unfold eventually_def)
  let ?F = "Rep_filter F"
  have obs: "\<forall>i. ?F (P i)"
    using h by auto
  have "?F (\<lambda>x. \<forall>i \<in> UNIV. P i x)"
    apply(rule finite_induct)
    by(auto intro: eventually_conj simp: obs h)
  thus "?F (\<lambda>x. \<forall>i. P i x)"
    by simp
qed

lemma eventually_all_finite_mono:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h1: "\<forall>i. eventually (P i) F"
      and h2: "\<forall>x. (\<forall>i. (P i x)) \<longrightarrow> Q x"
  shows "eventually Q F"
proof-
  have "eventually (\<lambda>x. \<forall>i. P i x) F"
    using h1 eventually_all_finite2 by blast
  thus "eventually Q F"
    unfolding eventually_def
    using h2 eventually_mono by auto
qed


subsection \<open> Multivariable derivatives \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

lemma vec_upd_eq: "vec_upd s i a = (\<chi> j. if j = i then a else s$j)"
  by (simp add: vec_upd_def)

lemma has_derivative_vec_nth[derivative_intros]: 
  "D (\<lambda>s. s $ i) \<mapsto> (\<lambda>s. s $ i) (at x within S)"
  by (clarsimp simp: has_derivative_within) standard

lemma bounded_linear_component:
  "(bounded_linear f) \<longleftrightarrow> (\<forall>i. bounded_linear (\<lambda>x. (f x) $ i))" (is "?lhs = ?rhs")
proof
  assume ?lhs 
  thus ?rhs
    apply(clarsimp, rule_tac f="(\<lambda>x. x $ i)" in bounded_linear_compose)
     apply(simp_all add: bounded_linear_def bounded_linear_axioms_def linear_iff)
    by (rule_tac x=1 in exI, clarsimp) (meson Finite_Cartesian_Product.norm_nth_le)
next
  assume ?rhs
  hence "(\<forall>i. \<exists>K. \<forall>x. \<parallel>f x $ i\<parallel> \<le> \<parallel>x\<parallel> * K)" "linear f"
    by (auto simp: bounded_linear_def bounded_linear_axioms_def linear_iff vec_eq_iff)
  then obtain F where F: "\<And>i x. \<parallel>f x $ i\<parallel> \<le> \<parallel>x\<parallel> * F i"
    by metis
  have "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * sum F UNIV" for x
  proof -
    have "norm (f x) \<le> (\<Sum>i\<in>UNIV. \<parallel>f x $ i\<parallel>)"
      by (simp add: L2_set_le_sum norm_vec_def)
    also have "... \<le> (\<Sum>i\<in>UNIV. norm x * F i)"
      by (metis F sum_mono)
    also have "... = norm x * sum F UNIV"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  then show ?lhs
    by (force simp: bounded_linear_def bounded_linear_axioms_def \<open>linear f\<close>)
qed

lemma open_preimage_nth:
  "open S \<Longrightarrow> open {s::('a::real_normed_vector^'n::finite). s $ i \<in> S}"
  unfolding open_contains_ball apply clarsimp
  apply(erule_tac x="x$i" in ballE; clarsimp)
  apply(rule_tac x=e in exI; clarsimp simp: dist_norm subset_eq ball_def)
  apply(rename_tac x e y, erule_tac x="y$i" in allE)
  using Finite_Cartesian_Product.norm_nth_le
  by (metis le_less_trans vector_minus_component)

lemma tendsto_nth_iff: \<comment> \<open> following @{thm tendsto_componentwise_iff} \<close>
  fixes l::"'a::real_normed_vector^'n::finite"
  defines "m \<equiv> real CARD('n)"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i. ((\<lambda>x. f x $ i) \<longlongrightarrow> l $ i) F)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    unfolding tendsto_def
    by (clarify, drule_tac x="{s. s $ i \<in> S}" in spec) (auto simp: open_preimage_nth)
next
  assume ?rhs
  thus ?lhs
  proof(unfold tendsto_iff dist_norm, clarify)
    fix \<epsilon>::real assume "0 < \<epsilon>"
    assume evnt_h: "\<forall>i \<epsilon>. 0 < \<epsilon> \<longrightarrow> (\<forall>\<^sub>F x in F. \<parallel>f x $ i - l $ i\<parallel> < \<epsilon>)"
    {fix x assume hyp: "\<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m)"
      have "\<parallel>f x - l\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>f x $ i - l $ i\<parallel>)"
        using triangle_norm_vec_le_sum[of "f x - l"] by auto
      also have "... < (\<Sum>(i::'n)\<in>UNIV. (\<epsilon>/m))"
        apply(rule sum_strict_mono[of UNIV "\<lambda>i. \<parallel>f x $ i - l $ i\<parallel>" "\<lambda>i. \<epsilon>/m"])
        using hyp by auto
      also have "... = m * (\<epsilon>/m)"
        unfolding assms by simp
      finally have "\<parallel>f x - l\<parallel> < \<epsilon>" 
        unfolding assms by simp}
    hence key: "\<And>x. \<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m) \<Longrightarrow> \<parallel>f x - l\<parallel> < \<epsilon>"
      by blast
    have obs: "\<forall>\<^sub>F x in F. \<forall>i. \<parallel>f x $ i - l $ i\<parallel> < (\<epsilon>/m)"
      apply(rule eventually_all_finite)
      using \<open>0 < \<epsilon>\<close> evnt_h unfolding assms by auto
    thus "\<forall>\<^sub>F x in F. \<parallel>f x - l\<parallel> < \<epsilon>"
      by (rule eventually_mono[OF _ key], simp)
  qed
qed

lemma has_derivative_component[simp]: \<comment> \<open> following @{thm has_derivative_componentwise_within} \<close>
  "(D f \<mapsto> f' at x within S) \<longleftrightarrow> (\<forall>i. D (\<lambda>s. f s $ i) \<mapsto> (\<lambda>s. f' s $ i) at x within S)"
  by (simp add: has_derivative_within tendsto_nth_iff 
      bounded_linear_component all_conj_distrib)

lemma has_vderiv_on_component[simp]:
  fixes x::"real \<Rightarrow> ('a::banach)^('n::finite)"
  shows "(D x = x' on T) = (\<forall>i. D (\<lambda>t. x t $ i) = (\<lambda>t. x' t $ i) on T)"
  unfolding has_vderiv_on_def has_vector_derivative_def by auto

lemma frechet_tendsto_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)" and x::real and T::"real set"
  defines "x\<^sub>0 \<equiv> netlimit (at x within T)" and "m \<equiv> real CARD('m)"
  assumes "\<forall>i. ((\<lambda>y. (f y $ i - f x\<^sub>0 $ i - (y - x\<^sub>0) *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  shows "((\<lambda>y. (f y - f x\<^sub>0 - (y - x\<^sub>0) *\<^sub>R f' x) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  using assms by (simp add: tendsto_nth_iff)

lemma tendsto_norm_bound:
  "\<forall>x. \<parallel>G x - L\<parallel> \<le> \<parallel>F x - L\<parallel> \<Longrightarrow> (F \<longlongrightarrow> L) net \<Longrightarrow> (G \<longlongrightarrow> L) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x - L\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma tendsto_zero_norm_bound:
  "\<forall>x. \<parallel>G x\<parallel> \<le> \<parallel>F x\<parallel> \<Longrightarrow> (F \<longlongrightarrow> 0) net \<Longrightarrow> (G \<longlongrightarrow> 0) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma frechet_tendsto_vec_nth:
  fixes f::"real \<Rightarrow> ('a::real_normed_vector)^'m"
  assumes "((\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  shows "((\<lambda>x. (f x $ i - f x\<^sub>0 $ i - (x - x\<^sub>0) *\<^sub>R f' t $ i) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  apply(rule_tac F="(\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>))" in tendsto_zero_norm_bound)
   apply(clarsimp, rule mult_left_mono)
    apply (metis Finite_Cartesian_Product.norm_nth_le vector_minus_component vector_scaleR_component)
  using assms by simp_all

end