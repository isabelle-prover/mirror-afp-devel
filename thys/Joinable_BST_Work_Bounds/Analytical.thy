section \<open>Real Analysis Prerequisites\<close>

text \<open>
  This first part collects the real-analysis groundwork for the complexity analysis of
  the joinable-tree operations, independent of trees and algorithms. It provides
  \<^item> elementary logarithm estimates
  \<^item> strict monotonicity of $x \cdot \log_2(1 + n/x)$
  \<^item> closed forms and bounds for geometric and arithmetic-geometric series
  \<^item> a finite, uniformly weighted instance of Jensen's inequality
\<close>

theory Analytical
imports
  "HOL-Analysis.Convex"
begin

subsection \<open>Logarithm estimates\<close>

lemma log_split:
  assumes "a \<ge> 0" "b \<ge> 0"
  shows "log 2 (a * b + 1) \<le> log 2 (a + 1) + log 2 (b + 1)"
proof -
  have "a * b + 1 > 0"
    using assms by (metis zero_le_mult_iff abs_add_one_gt_zero abs_of_nonneg add.commute)
  moreover have "a * b + 1 \<le> (a + 1) * (b + 1)"
    using assms by argo
  ultimately have "log 2 (a * b + 1) \<le> log 2 ((a + 1) * (b + 1))"
    using log_mono by auto
  then show ?thesis
    using assms log_mult_pos by force
qed

lemma log_2powr_plus_1_le:
  fixes x :: real
  assumes "x \<ge> 0"
  shows "log 2 (2 powr x + 1) \<le> 1 + x"
proof -
  have "2 powr x + 1 \<le> 2 * (2 powr x)"
    using assms ge_one_powr_ge_zero by simp
  then have "2 powr x + 1 \<le> 2 powr (x + 1)" 
    by (simp add: add.commute powr_mult_base)
  then have "log 2 (2 powr x + 1) \<le> log 2 (2 powr (x + 1))"
    by (intro log_mono) (auto intro: add_pos_nonneg)
  also have "... = x + 1"
    by (simp add: log_powr)
  finally show ?thesis
    by force
qed

subsection \<open>Monotonicity of \texorpdfstring{$x \cdot \log_2(1 + n/x)$}{x * log 2 (1 + n/x)}\<close>

corollary ln_diff_less: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x \<noteq> y \<Longrightarrow> ln x - ln y < (x - y) / y" for
x :: real
using ln_eq_minus_one[of "x/y"] ln_diff_le[of x y]
by (fastforce simp: diff_divide_distrib ln_divide_pos)

lemma ln_mono_1:
  fixes n :: real
  assumes n_pos: "n > 0" 
  defines "f \<equiv> (\<lambda>x::real. x * ln (1 + n/x))"
  shows   "strict_mono_on {0<..} f"
proof -
  have "(f has_real_derivative ln (x + n) - ln x - n / (x + n)) (at x)"
    if "x > 0" for x
    unfolding f_def using \<open>x>0\<close> n_pos
    by(auto intro!: derivative_eq_intros) (force simp add: ln_div divide_simps)+
  moreover have "0 < ln (x + n) - ln x - n / (x + n)" if "x > 0" for x
    using ln_diff_less[of x "x + n"] \<open>x>0\<close> n_pos 
    by auto 
  ultimately have "\<exists>y. (f has_real_derivative y) (at x) \<and> 0 < y" if "x > 0" for x
    using \<open>x>0\<close> by blast
  then show ?thesis
    by (metis DERIV_pos_imp_increasing greaterThan_iff order.strict_trans2 strict_mono_onI)
qed

corollary log_mono_1:
   fixes n :: real
   assumes n_pos: "n > 0"
   defines "f \<equiv> (\<lambda>x::real. x * log 2 (1 + n/x))"
   shows   "strict_mono_on {0<..} f"
using ln_mono_1[OF n_pos] unfolding f_def strict_mono_on_def log_def
  by (simp add: divide_less_eq)

corollary xlog_mono:
  fixes n x z :: real
  assumes "n > 0" "0 < x" "x \<le> z"
  shows "x * log 2 (n / x + 1) \<le> z * log 2 (n / z + 1)"
proof -
  let ?f = "\<lambda>x::real. x * log 2 (1 + n / x)"
  have "?f x \<le> ?f z"
  proof (cases "x = z")
    case False
    have "strict_mono_on {0<..} ?f"
      using assms(1) log_mono_1 by simp
    then show ?thesis
      using assms False strict_mono_onD[of "{0<..}" ?f x z] by auto
  qed simp
  then show ?thesis
    by argo
qed

corollary xlog_term_mono:
  fixes n x z k c :: real
  assumes "0 < x" "x \<le> z" "0 < n" "0 \<le> k" "0 \<le> c"
  shows "x * (k + c * log 2 (n / x + 1)) \<le> z * (k + c * log 2 (n / z + 1))"
proof -
  have "k * x \<le> k * z"
    using assms(2,4) by (rule mult_left_mono)
  moreover have "c * (x * log 2 (n / x + 1)) \<le> c * (z * log 2 (n / z + 1))"
    using xlog_mono[OF assms(3,1,2)] assms(5) by (rule mult_left_mono)
  ultimately show ?thesis
    by argo
qed

subsection \<open>Geometric and arithmetic-geometric series\<close>

text \<open>
  The following lemmas derive the limit $\sum_{k} k\,c^k = \frac{c}{(1-c)^2}$ 
  together with summability for $|c| < 1$.
\<close>
lemma arith_geometric_sums:
  fixes z :: "real"
  assumes z: "norm z < 1"
  shows   "(\<lambda>n. of_nat n * z ^ n) sums (z / (1 - z)\<^sup>2)"
proof -
  have "(\<Sum>n. of_nat (Suc n) * z ^ n) = 1 / (1 - z) ^ 2"
  proof (rule DERIV_unique)
    have "((\<lambda>z. \<Sum>n. 1 * z ^ n) has_field_derivative (\<Sum>n. of_nat (Suc n) * z ^ n)) (at z)"
      using termdiffs_strong'[of 1 "\<lambda>_. 1" z] z by (simp add: diffs_def)
    also have "?this \<longleftrightarrow> ((\<lambda>z. 1 / (1 - z)) has_field_derivative (\<Sum>n. of_nat (Suc n) * z ^ n)) (at z)"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>x. x \<in> {x. dist 0 x < 1}) (nhds z)"
        by (rule eventually_nhds_in_open, rule open_ball) (use z in auto)
      then show "eventually (\<lambda>x. (\<Sum>n. 1 * x ^ n) = 1 / (1 - x)) (nhds z)"
        by eventually_elim (auto simp: suminf_geometric)
    qed (auto simp: diffs_def)
    finally show "((\<lambda>z. 1 / (1 - z)) has_field_derivative (\<Sum>n. of_nat (Suc n) * z ^ n)) (at z)" .
  next
    show "((\<lambda>z. 1 / (1 - z)) has_field_derivative (1 / (1 - z) ^ 2)) (at z)"
      using z by (auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)
  qed
  hence "(\<lambda>n. of_nat (Suc n) * z ^ n) sums (1 / (1 - z) ^ 2)"
    using termdiff_converges[of z 1 "\<lambda>_. 1"] z by (simp add: diffs_def sums_iff)
  hence "(\<lambda>n. of_nat (Suc n) * z ^ n - z ^ n) sums (1 / (1 - z) ^ 2 - 1 / (1 - z))"
    using z by (intro sums_diff geometric_sums)
  also have "(\<lambda>n. of_nat (Suc n) * z ^ n - z ^ n) = (\<lambda>n. of_nat n * z ^ n)"
    by (simp add: algebra_simps)
  also have "(1 / (1 - z) ^ 2 - 1 / (1 - z)) = z / (1 - z) ^ 2"
    using assms by (simp add: divide_simps) (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

corollary arith_geometric_summable:
  fixes c :: "real"
  assumes "norm c < 1"
  shows   "summable (\<lambda>n. n * c^n) "
using arith_geometric_sums assms summable_def by fastforce

text \<open>
  The analysis eventually instantiates the series with the geometric ratio
  $q(c_u) = 2^{-1/c_u}$, which lies strictly between $0$ and $1$ for $c_u > 0$.
  The constant definitions $S_1(c_u)$ and $S_2(c_u)$ bound the geometric and
  arithmetic-geometric series in this ratio over any finite index set. 
\<close>

lemma powr_split_nat:
  fixes a :: real and cu :: real and i :: nat
  assumes "a > 0"
  shows "a powr (real i / cu) = (a powr (1 / cu)) ^ i"
   by (metis assms(1) div_by_1 divide_divide_eq_right powr_eq_0_iff 
    powr_eq_one_iff_gen powr_power times_divide_eq_right zero_neq_one)

definition geom_ratio where "geom_ratio cu = 1 / (2 powr (1 / cu))"

lemma geom_ratio_range:
  fixes cu :: "real"
  assumes cu_pos:"cu > 0"
  shows "0 < geom_ratio cu \<and> geom_ratio cu < 1"
using assms by (simp add: geom_ratio_def)

lemma inv_powr_geom_ratio:
  fixes cu :: real and i :: nat
  assumes "cu > 0"
  shows "1 / (2 powr (real i / cu)) = geom_ratio cu ^ i"
by (simp add: power_one_over powr_split_nat geom_ratio_def)

definition S1 where "S1 cu = (2 powr (1 / cu)) / ((2 powr (1 / cu)) - 1)"
definition S2 where "S2 cu = (geom_ratio cu) / (1 - geom_ratio cu)^2"

lemma geom_ratio_sum_le:
  fixes cu :: "real"
  assumes "cu > 0" "finite A"
  shows "(\<Sum>i\<in>A. (geom_ratio cu) ^ i) \<le> S1 cu"
proof -
  have qr: "0 < geom_ratio cu \<and> geom_ratio cu < 1"
    using geom_ratio_range[OF assms(1)] .
  have "(\<Sum>i\<in>A. (geom_ratio cu) ^ i) < 1 / (1 - geom_ratio cu)"
    by (metis qr assms(2) geometric_sum_less)
  also have "1 / (1 - geom_ratio cu) = S1 cu"
    using qr by (simp add: S1_def geom_ratio_def field_simps)
  finally show ?thesis
    by force
qed

lemma geom_ratio_arith_sum_le:
  assumes "cu > 0" "finite A"
  shows "(\<Sum>i\<in>A. real i * (geom_ratio cu) ^ i) \<le> S2 cu"
proof -
  have qr:"0 < geom_ratio cu \<and> geom_ratio cu < 1"
    using geom_ratio_range[OF assms(1)] .
  have "summable (\<lambda>i::nat. real i * (geom_ratio cu)^i)"
    using qr arith_geometric_summable by fastforce
  moreover have "0 \<le> (real i * (geom_ratio cu)^i)" for i
    using qr by simp
  ultimately have "(\<Sum>i\<in>A. real i * (geom_ratio cu)^i) \<le> (\<Sum>i. real i * (geom_ratio cu)^i)"
    using assms(2) sum_le_suminf summable by blast
  also have "... = S2 cu"
  proof -
    have "(\<lambda>i::nat. real i * (geom_ratio cu)^i) sums ((geom_ratio cu) / (1 - geom_ratio cu)^2)"
      using qr by (simp add: arith_geometric_sums)
    then show ?thesis
      by (metis S2_def sums_unique)
  qed
  finally show ?thesis .
qed

text \<open>Both instantiations below use $c_u = 2$, for which the series constants have
  closed forms in $\sqrt 2$.\<close>

lemma sqrt2_bounds: "sqrt 2 * sqrt 2 = 2" "1 < sqrt 2" "sqrt 2 \<le> 1.415"
proof -
  show "sqrt 2 * sqrt 2 = 2"
    by fastforce
  show "1 < sqrt 2"
    by simp
  show "sqrt 2 \<le> 1.415"
    by (rule real_le_lsqrt) (simp_all add: power2_eq_square)
qed

lemma S1_two: "S1 2 = 2 + sqrt 2"
proof -
  have "S1 2 = sqrt 2 / (sqrt 2 - 1)"
    by (simp add: S1_def powr_half_sqrt)
  also have "\<dots> = 2 + sqrt 2"
    using sqrt2_bounds(1,2) by (simp add: field_simps)
  finally show ?thesis .
qed

lemma S2_two: "S2 2 = 4 + 3 * sqrt 2"
proof -
  have "geom_ratio 2 = 1 / sqrt 2"
    by (simp add: geom_ratio_def powr_half_sqrt)
  then have "S2 2 = (1 / sqrt 2) / (1 - 1 / sqrt 2)\<^sup>2"
    by (simp add: S2_def)
  also have "\<dots> = 2 / (3 * sqrt 2 - 4)"
    using sqrt2_bounds(1,2) by (simp add: power2_eq_square field_simps)
  also have "\<dots> = 4 + 3 * sqrt 2"
  proof -
    have "4 / 3 < sqrt 2"
      by (rule real_less_rsqrt) (simp add: power2_eq_square)
    then show ?thesis
      using sqrt2_bounds(1) by (simp add: field_simps)
  qed
  finally show ?thesis .
qed

subsection \<open>Jensen's inequality for finite sets\<close>

text \<open>
  Jensen's inequality relates the value of a concave function at a weighted average to
  the average of its values. The below is a special case of 
  @{thm [source] concave_on_sum}.
\<close>
corollary jensen_finite:
  fixes  S :: "'b set"
  defines "a \<equiv> (\<lambda>i::'b. 1 / card S)" 
  assumes "finite S" "S \<noteq> {}"
      and "concave_on D f"
      and "\<And>i. i \<in> S \<Longrightarrow> x i \<in> D"
  shows "f ((1 / card S) *\<^sub>R (\<Sum>i\<in>S. x i))
        \<ge> (1 / card S) * (\<Sum>i\<in>S. f (x i))"
proof -
  have weights: "\<And>i. i \<in> S \<Longrightarrow> a i \<ge> 0" "(\<Sum>i\<in>S. a i) = 1"
    unfolding a_def using assms by auto
  show ?thesis
    using concave_on_sum[OF assms(2,3,4) weights(2) weights(1) assms(5)]
    unfolding a_def by (simp add: sum_distrib_left scaleR_right.sum)
qed

corollary jensen_list:
  assumes "xs \<noteq> []"
      and "concave_on C f"
      and "\<And>x. x \<in> set xs \<Longrightarrow> x \<in> C"
  shows "f ((1 / length xs) *\<^sub>R sum_list xs)
        \<ge> (1 / length xs) * sum_list (map f xs)"
proof -
  let ?S = "{..<length xs}"
  let ?x = "\<lambda>i. xs ! i"

  have "f ((1 / card ?S) *\<^sub>R (\<Sum>i\<in>?S. xs ! i)) \<ge> (1 / card ?S) * (\<Sum>i\<in>?S. f (xs ! i))"
  proof - 
    have "finite ?S" 
      by simp
    moreover have "?S \<noteq> {}" 
      using assms(1) by blast
    moreover have in_C: "\<And>i. i \<in> ?S \<Longrightarrow> xs ! i \<in> C"
      by (simp add: assms(3))
    ultimately show ?thesis using assms jensen_finite by blast
  qed

  moreover have "card ?S = length xs" 
    by simp
  moreover have "sum_list xs = (\<Sum>i\<in>?S. xs ! i)"
    by (simp add: lessThan_atLeast0 sum_list_sum_nth)
  moreover have "sum_list (map f xs) = (\<Sum>i\<in>?S. f (xs ! i))"
    by (metis (mono_tags, lifting) length_map lessThan_atLeast0 
      lessThan_iff nth_map sum.cong sum.list_conv_set_nth)
  ultimately show ?thesis
    by force
qed

end