theory Preliminaries
  imports "HOL-Analysis.Analysis"
begin

notation powr (infixr ".^" 80)


section \<open>Preliminary Definitions and Lemmas\<close>

lemma seq_part_multiple: fixes m n :: nat assumes "m \<noteq> 0" defines "A \<equiv> \<lambda>i::nat. {i*m ..< (i+1)*m}"
  shows "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" and "(\<Union>i<n. A i) = {..< n*m}"
proof -
  { fix i j :: nat
    have "i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    proof (erule contrapos_np)
      assume "A i \<inter> A j \<noteq> {}"
      then obtain k where "k \<in> A i \<inter> A j" by blast
      hence "i*m < (j+1)*m \<and> j*m < (i+1)*m" unfolding A_def by force
      hence "i < j+1 \<and> j < i+1" using mult_less_cancel2 by blast
      thus "i = j" by force
    qed }
  thus "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" by blast
next
  show "(\<Union>i<n. A i) = {..< n*m}"
  proof
    show "(\<Union>i<n. A i) \<subseteq> {..< n*m}"
    proof
      fix x::nat
      assume "x \<in> (\<Union>i<n. A i)"
      then obtain i where i_n: "i < n" and i_x: "x < (i+1)*m" unfolding A_def by force
      hence "i+1 \<le> n" by linarith
      hence "x < n*m" by (meson less_le_trans mult_le_cancel2 i_x)
      thus "x \<in> {..< n*m}"
        using diff_mult_distrib mult_1 i_n by auto
    qed
  next
    show "{..< n*m} \<subseteq> (\<Union>i<n. A i)"
    proof
      fix x::nat
      let ?i = "x div m"
      assume "x \<in> {..< n*m}"
      hence "?i < n" by (simp add: less_mult_imp_div_less)
      moreover have "?i*m \<le> x \<and> x < (?i+1)*m"
        using assms div_times_less_eq_dividend dividend_less_div_times by auto
      ultimately show "x \<in> (\<Union>i<n. A i)" unfolding A_def by force
    qed
  qed
qed

lemma(in field) divide_mult_cancel[simp]: fixes a b assumes "b \<noteq> 0"
  shows "a / b * b = a"
  by (simp add: assms)

lemma inverse_powr: "(1/a).^b = a.^-b" if "a > 0" for a b :: real
  by (smt that powr_divide powr_minus_divide powr_one_eq_one)

lemma powr_eq_one_iff_gen[simp]: "a.^x = 1 \<longleftrightarrow> x = 0" if "a > 0" "a \<noteq> 1" for a x :: real
  by (metis powr_eq_0_iff powr_inj powr_zero_eq_one that)

lemma powr_less_cancel2: "0 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x.^a < y.^a \<Longrightarrow> x < y"
  for a x y ::real
proof -
  assume a_pos: "0 < a" and x_pos: "0 < x" and y_pos: "0 < y"
  show "x.^a < y.^a \<Longrightarrow> x < y"
  proof (erule contrapos_pp)
    assume "\<not> x < y"
    hence "x \<ge> y" by fastforce
    hence "x.^a \<ge> y.^a"
    proof (cases "x = y")
      case True
      thus ?thesis by simp
    next
      case False
      hence "x.^a > y.^a"
        using \<open>x \<ge> y\<close> powr_less_mono2 a_pos y_pos by auto
      thus ?thesis by auto
    qed
    thus "\<not> x.^a < y.^a" by fastforce
  qed
qed

lemma geometric_increasing_sum_aux: "(1-r)^2 * (\<Sum>k<n. (k+1)*r^k) = 1 - (n+1)*r^n + n*r^(n+1)"
  for n::nat and r::real
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thus ?case
    by (simp add: distrib_left power2_diff field_simps power2_eq_square)
qed

lemma geometric_increasing_sum: "(\<Sum>k<n. (k+1)*r^k) = (1 - (n+1)*r^n + n*r^(n+1)) / (1-r)^2"
  if "r \<noteq> 1" for n::nat and r::real
  by (subst geometric_increasing_sum_aux[THEN sym], simp add: that)

lemma Reals_UNIV[simp]: "\<real> = {x::real. True}"
  unfolding Reals_def by auto

lemma DERIV_fun_powr2:
  fixes a::real
  assumes a_pos: "a > 0"
    and f: "DERIV f x :> r"
  shows "DERIV (\<lambda>x. a.^(f x)) x :> a.^(f x) * r * ln a"
proof -
  let ?g = "(\<lambda>x. a)"
  have g: "DERIV ?g x :> 0" by simp
  have pos: "?g x > 0" by (simp add: a_pos)
  show ?thesis
    using DERIV_powr[OF g pos f] a_pos by (auto simp add: field_simps)
qed

lemma has_real_derivative_powr2:
  assumes a_pos: "a > 0"
  shows "((\<lambda>x. a.^x) has_real_derivative a.^x * ln a) (at x)"
proof -
  let ?f = "(\<lambda>x. x::real)"
  have f: "DERIV ?f x :> 1" by simp
  thus ?thesis using DERIV_fun_powr2[OF a_pos f] by simp
qed

lemma has_integral_powr2_from_0:
  fixes a c :: real
  assumes a_pos: "a > 0" and a_neq_1: "a \<noteq> 1" and c_nneg: "c \<ge> 0"
  shows "((\<lambda>x. a.^x) has_integral ((a.^c - 1) / (ln a))) {0..c}"
proof -
  have "((\<lambda>x. a.^x) has_integral ((a.^c)/(ln a) - (a.^0)/(ln a))) {0..c}"
  proof (rule fundamental_theorem_of_calculus[OF c_nneg])
    fix x::real
    assume "x \<in> {0..c}"
    show "((\<lambda>y. a.^y / ln a) has_vector_derivative a.^x) (at x within {0..c})"
      using has_real_derivative_powr2[OF a_pos, of x]
      apply -
      apply (drule DERIV_cdivide[where c = "ln a"], simp add: assms)
      apply (rule has_vector_derivative_within_subset[where S=UNIV and T="{0..c}"], auto)
      by (rule iffD1[OF has_real_derivative_iff_has_vector_derivative])
  qed
  thus ?thesis
    using assms powr_zero_eq_one by (simp add: field_simps)
qed

lemma integrable_on_powr2_from_0:
  fixes a c :: real
  assumes a_pos: "a > 0" and a_neq_1: "a \<noteq> 1" and c_nneg: "c \<ge> 0"
  shows "(\<lambda>x. a.^x) integrable_on {0..c}"
  using has_integral_powr2_from_0[OF assms] unfolding integrable_on_def by blast

lemma integrable_on_powr2_from_0_general:
  fixes a c :: real
  assumes a_pos: "a > 0" and c_nneg: "c \<ge> 0"
  shows "(\<lambda>x. a.^x) integrable_on {0..c}"
proof (cases "a = 1")
  case True
  thus ?thesis
    using has_integral_const_real by auto
next
  case False
  thus ?thesis
    using has_integral_powr2_from_0 False assms by auto
qed

lemma has_integral_null_interval: fixes a b :: real and f::"real \<Rightarrow> real" assumes "a \<ge> b"
  shows "(f has_integral 0) {a..b}"
  using assms content_real_eq_0 by blast

lemma has_integral_interval_reverse: fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b"
    and "continuous_on {a..b} f"
  shows "((\<lambda>x. f (a+b-x)) has_integral (integral {a..b} f)) {a..b}"
proof -
  let ?g = "\<lambda>x. a + b - x"
  let ?g' = "\<lambda>x. -1"
  have g_C0: "continuous_on {a..b} ?g" using continuous_on_op_minus by simp
  have Dg_g': "\<And>x. x\<in>{a..b} \<Longrightarrow> (?g has_field_derivative ?g' x) (at x within {a..b})"
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    using has_integral_substitution_general
      [of "{}" a b ?g a b f, simplified, OF assms g_C0 Dg_g', simplified]
    apply (simp add: has_integral_null_interval[OF assms(1), THEN integral_unique])
    by (simp add: has_integral_neg_iff)
qed

end
