section \<open>The theta nullwert functions\<close>
theory Theta_Nullwert
  imports "Sum_Of_Squares_Count.Sum_Of_Squares_Count" Jacobi_Triple_Product
begin

text \<open>
  The theta nullwert function (nullwert being German for ``zero value'') are the 
  four functions $\vartheta_{xy}(z; \tau)$ with $z = 0$. However, they are very commonly
  denoted in terms of the nome instead, corresponding to $\vartheta_{xy}(w, q)$ with $w = 1$.

  It is easy to see that $\vartheta_{11}(0; \tau) = \vartheta_{11}(1, q)$ is identically zero 
  and therefore uninteresting. The remaining three functions $\vartheta_{10}(0, q)$,
  $\vartheta_{00}(0, q)$, and $\vartheta_{01}(0, q)$ are denoted $\vartheta_2(q)$, 
  $\vartheta_3(q)$, and $\vartheta_4(q)$.

  It is also not hard to see that in fact $\vartheta_4(q) = \vartheta_3(-q)$, but we still
  introduce separate notation for $\vartheta_4$ since it is very commonly used in the literature.
\<close>

lemma jacobi_theta_nome_11_1_left [simp]: "jacobi_theta_nome_11 1 q = 0"
  using jacobi_theta_nome_minus_same[of q] by (auto simp: jacobi_theta_nome_11_def)

abbreviation jacobi_theta_nw_10 :: "'a :: {real_normed_field, banach, ln} \<Rightarrow> 'a" where
  "jacobi_theta_nw_10 q \<equiv> jacobi_theta_nome_10 1 q"

abbreviation jacobi_theta_nw_00 :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a" where
  "jacobi_theta_nw_00 q \<equiv> jacobi_theta_nome_00 1 q"

abbreviation jacobi_theta_nw_01 :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a" where
  "jacobi_theta_nw_01 q \<equiv> jacobi_theta_nome_01 1 q"


bundle jacobi_theta_nw_notation
begin
notation jacobi_theta_nw_10 ("\<theta>\<^sub>2")
notation jacobi_theta_nw_00 ("\<theta>\<^sub>3")
notation jacobi_theta_nw_01 ("\<theta>\<^sub>4")
end

bundle no_jacobi_theta_nw_notation
begin
no_notation jacobi_theta_nw_10 ("\<theta>\<^sub>2")
no_notation jacobi_theta_nw_00 ("\<theta>\<^sub>3")
no_notation jacobi_theta_nw_01 ("\<theta>\<^sub>4")
end

unbundle jacobi_theta_nw_notation


lemma jacobi_theta_nw_10_0 [simp]: "\<theta>\<^sub>2 0 = 0"
  and jacobi_theta_nw_00_0 [simp]: "\<theta>\<^sub>3 0 = 1"
  and jacobi_theta_nw_01_0 [simp]: "\<theta>\<^sub>4 0 = 1"
  by simp_all

lemma jacobi_theta_nw_01_conv_00: "\<theta>\<^sub>4 q = \<theta>\<^sub>3 (-q)"
  by (simp add: jacobi_theta_nome_01_conv_00)


lemma jacobi_theta_nw_10_of_real:
        "y \<ge> 0 \<Longrightarrow> \<theta>\<^sub>2 (complex_of_real y) = of_real (\<theta>\<^sub>2 y)"
  and jacobi_theta_nw_00_of_real: "\<theta>\<^sub>3 (of_real x) = of_real (\<theta>\<^sub>3 x)"
  and jacobi_theta_nw_01_of_real: "\<theta>\<^sub>4 (of_real x) = of_real (\<theta>\<^sub>4 x)"
  by (simp_all flip: jacobi_theta_nome_10_complex_of_real jacobi_theta_nome_00_of_real
                     jacobi_theta_nome_01_of_real)

lemma jacobi_theta_nw_10_cnj:
        "(Im q = 0 \<Longrightarrow> Re q \<ge> 0) \<Longrightarrow> \<theta>\<^sub>2 (cnj q) = cnj (\<theta>\<^sub>2 q)"
  and jacobi_theta_nw_00_cnj: "\<theta>\<^sub>3 (cnj q) = cnj (\<theta>\<^sub>3 q)"
  and jacobi_theta_nw_01_cnj: "\<theta>\<^sub>4 (cnj q) = cnj (\<theta>\<^sub>4 q)"
  by (simp_all flip: jacobi_theta_nome_10_cnj jacobi_theta_nome_00_cnj jacobi_theta_nome_01_cnj)


text \<open>
  The nullwerte have the following definitions as infinite sums:
  \begin{align*}
    \vartheta_2(q) &= \sum\limits_{-\infty}^\infty q^{(n+\frac{1}{2})^2}\\
    \vartheta_3(q) &= \sum\limits_{-\infty}^\infty q^{n^2}\\
    \vartheta_4(q) &= \sum\limits_{-\infty}^\infty (-1)^n q^{n^2}
  \end{align*}
\<close>

lemma has_sum_jacobi_theta_nw_10_complex:
  assumes "norm (q :: complex) < 1"
  shows   "((\<lambda>n. q powr ((of_int n + 1 / 2) ^ 2)) has_sum \<theta>\<^sub>2 q) UNIV"
proof (cases "q = 0")
  case [simp]: False
  show ?thesis
    using has_sum_jacobi_theta_nome_10[of q 1] assms by simp
qed auto

lemma has_sum_jacobi_theta_nw_10_real:
  assumes "q \<in> {0<..<1::real}"
  shows   "((\<lambda>n. q powr ((of_int n + 1 / 2) ^ 2)) has_sum \<theta>\<^sub>2 q) UNIV"
proof (cases "q = 0")
  case [simp]: False
  show ?thesis
    using has_sum_jacobi_theta_nome_10[of q 1] assms by simp
qed auto

lemma has_sum_jacobi_theta_nw_00:
  assumes "norm q < 1"
  shows   "((\<lambda>n. q powi (n ^ 2)) has_sum \<theta>\<^sub>3 q) UNIV"
  using has_sum_jacobi_theta_nome_00[of q 1] assms by simp

lemma has_sum_jacobi_theta_nw_01:
  assumes "norm q < 1"
  shows   "((\<lambda>n. (-1) powi n * q powi (n ^ 2)) has_sum \<theta>\<^sub>4 q) UNIV"
  using has_sum_jacobi_theta_nome_01[of q 1] assms by simp

text \<open>
  The theta nullwert functions do not vanish (except for \<open>\<theta>\<^sub>2(0) = 0\<close>).
\<close>
lemma jacobi_theta_00_nw_nonzero_complex: "norm (q::complex) < 1 \<Longrightarrow> \<theta>\<^sub>3 q \<noteq> 0"
  by (simp add: jacobi_theta_nome_00_def jacobi_theta_nome_1_left_nonzero_complex)

lemma jacobi_theta_01_nw_nonzero_complex: "norm (q::complex) < 1 \<Longrightarrow> \<theta>\<^sub>4 q \<noteq> 0"
  by (simp add: jacobi_theta_nw_01_conv_00 jacobi_theta_00_nw_nonzero_complex)

lemma jacobi_theta_10_nw_nonzero_complex:
  assumes "q \<noteq> 0" "norm (q::complex) < 1"
  shows   "\<theta>\<^sub>2 q \<noteq> 0"
  using jacobi_theta_nome_q_q_nonzero_complex[of q] assms
  by (auto simp: jacobi_theta_nome_10_def)

lemma jacobi_theta_00_nw_nonzero_real: "\<bar>q::real\<bar> < 1 \<Longrightarrow> \<theta>\<^sub>3 q \<noteq> 0"
  and jacobi_theta_01_nw_nonzero_real: "\<bar>q::real\<bar> < 1 \<Longrightarrow> \<theta>\<^sub>4 q \<noteq> 0"
  and jacobi_theta_10_nw_nonzero_real: "q \<in> {0..<1} \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> \<theta>\<^sub>2 q \<noteq> 0"
  using jacobi_theta_00_nw_nonzero_complex[of "of_real q"]
        jacobi_theta_01_nw_nonzero_complex[of "of_real q"]
        jacobi_theta_10_nw_nonzero_complex[of "of_real q"]
  by (simp_all add: jacobi_theta_nw_00_of_real jacobi_theta_nw_01_of_real
                    jacobi_theta_nw_10_of_real)


subsection \<open>The Maclaurin series of $\vartheta_3$ and $\vartheta_4$\<close>

text \<open>
  It is easy to see from the above infinite sums that $\vartheta_3(q)$ and $\vartheta_4(q)$ have the 
  Maclaurin series
  \[1 + 2\sum_{n=1}^\infty [\exists i.\ n = i^2] c^n q^n\]
  for $c = 1$ and $c = -1$, respectively.

  In other words, $\vartheta_3(q)$ is the generating function of the number $r_1(n)$ of ways to write 
  an integer $n$ as a square of an integer -- 1 for $n = 0$, 2 if $n$ is a non-zero perfect square,
  and $0$ otherwise.

  Consequently, $\vartheta_3(q)^k$ is the generating function of the number $r_k(n)$ of ways to write
  an integer $n$ as a square of $k$ integers. The function $r_k(n)$ is written as 
  \<^const>\<open>count_sos\<close> \<open>k\<close> \<open>n\<close> in Isabelle.
\<close>
definition fps_jacobi_theta_nw :: "'a :: field \<Rightarrow> 'a fps" where
  "fps_jacobi_theta_nw c = Abs_fps (\<lambda>n. if n = 0 then 1 else if is_square n then 2 * c ^ n else 0)"

theorem fps_jacobi_theta_power_eq:
  "fps_jacobi_theta_nw c ^ k = Abs_fps (\<lambda>n. of_nat (count_sos k n) * c ^ n)"
proof (induction k)
  case (Suc k)
  have "fps_jacobi_theta_nw (c::'a) ^ Suc k =
          fps_jacobi_theta_nw c * Abs_fps (\<lambda>n. of_nat (count_sos k n) * c ^ n)"
    by (simp add: Suc.IH mult.commute)
  also have "\<dots> = Abs_fps (\<lambda>n. of_nat (count_sos (Suc k) n) * c ^ n)" (is "?lhs = ?rhs")
  proof (rule fps_ext)
    fix n :: nat
    have "fps_nth (fps_jacobi_theta_nw (c::'a) * Abs_fps (\<lambda>n. of_nat (count_sos k n) * c ^ n)) n =
            (\<Sum>i=0..n. fps_nth (fps_jacobi_theta_nw c) i * of_nat (count_sos k (n - i)) * c ^ (n - i))"
      by (simp add: fps_mult_nth sum_distrib_left sum_distrib_right algebra_simps)
    also have "\<dots> = of_nat (count_sos k n) * c ^ n + 
                   (\<Sum>i\<in>{0<..n}. fps_nth (fps_jacobi_theta_nw c) i * 
                                 of_nat (count_sos k (n - i)) * c ^ (n - i))"
      (is "_ = _ + ?S")
      by (subst sum.head) (auto simp: fps_jacobi_theta_nw_def)
    also have "?S =  (\<Sum>i | i \<in> {0<..n} \<and> is_square i. 
                       2 * of_nat (count_sos k (n - i)) * c ^ n)"
      by (rule sum.mono_neutral_cong_right) (auto simp: fps_jacobi_theta_nw_def simp flip: power_add)
    also have "\<dots> = (\<Sum>i \<in> {1..floor_sqrt n}. 
                       2 * of_nat (count_sos k (n - i ^ 2)) * c ^ n)"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i ^ 2" floor_sqrt])
         (auto elim!: is_nth_powerE simp: le_floor_sqrt_iff)
    also have "of_nat (count_sos k n) * c ^ n + \<dots> = of_nat (count_sos (Suc k) n) * c ^ n"
      by (simp add: count_sos_Suc sum_distrib_left sum_distrib_right power_add algebra_simps)
    finally show "fps_nth ?lhs n = fps_nth ?rhs n"
      by simp
  qed
  finally show ?case .
qed (auto intro!: fps_ext)

corollary fps_jacobi_theta_altdef:
  "fps_jacobi_theta_nw c = Abs_fps (\<lambda>n. of_nat (count_sos 1 n) * c ^ n)"
  using fps_jacobi_theta_power_eq[of c 1] by simp

lemma norm_summable_fps_jacobi_theta:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes "norm (c * q) < 1"
  shows   "summable (\<lambda>n. norm (fps_nth (fps_jacobi_theta_nw c) n * q ^ n))"
proof (rule summable_comparison_test)
  show "summable (\<lambda>n. 2 * norm (c * q) ^ n)"
    by (intro summable_mult summable_geometric) (use assms in auto)
  show "\<exists>N. \<forall>n\<ge>N. norm (norm (fps_nth (fps_jacobi_theta_nw c) n * q ^ n)) \<le> 2 * norm (c * q) ^ n"
    by (rule exI[of _ 0]) (auto simp: fps_jacobi_theta_nw_def norm_mult norm_power power_mult_distrib)
qed

lemma summable_fps_jacobi_theta:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes "norm (c * q) < 1"
  shows   "summable (\<lambda>n. fps_nth (fps_jacobi_theta_nw c) n * q ^ n)"
  using norm_summable_fps_jacobi_theta[OF assms] by (rule summable_norm_cancel)

lemma summable_ints_symmetric:
  fixes f :: "int \<Rightarrow> 'a :: {real_normed_vector, banach}"
  assumes "summable (\<lambda>n. norm (f (int n)))"
  assumes "\<And>n. f (-n) = f n"
  shows   "f abs_summable_on UNIV" and "summable (\<lambda>n. norm ((if n = 0 then 1 else 2) *\<^sub>R f (int n)))"
proof -
  show "summable (\<lambda>n. norm ((if n = 0 then 1 else 2) *\<^sub>R f (int n)))"
  proof (rule summable_comparison_test)
    show "summable (\<lambda>n. 2 * norm (f n))"
      by (intro summable_mult assms)
  qed (auto intro!: exI[of _ 0])
next
  have "(\<lambda>n. f (int n)) abs_summable_on UNIV"
    using assms by (subst summable_on_UNIV_nonneg_real_iff) auto
  also have "?this \<longleftrightarrow> f abs_summable_on {0..}"
    by (rule summable_on_reindex_bij_witness[of _ nat int]) auto
  finally have 1: "f abs_summable_on {0<..}"
    by (rule summable_on_subset) auto
  also have "?this \<longleftrightarrow> f abs_summable_on {..<0}"
    by (rule summable_on_reindex_bij_witness[of _ uminus uminus]) (use assms(2) in auto)
  finally have "f abs_summable_on ({..<0} \<union> {0} \<union> {0<..})"
    by (intro summable_on_Un_disjoint 1) auto
  also have "({..<(0::int)} \<union> {0} \<union> {0<..}) = UNIV"
    by auto
  finally show "f abs_summable_on UNIV" .
qed

lemma has_sum_ints_symmetric_iff:
  fixes f :: "int \<Rightarrow> 'a :: {banach, real_normed_vector}"
  assumes "\<And>n. f (-n) = f n"
  shows   "(f has_sum S) UNIV \<longleftrightarrow> ((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f (int n)) has_sum S) UNIV"
proof
  assume *: "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f (int n)) has_sum S) UNIV"
  have "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f (int n)) has_sum (S - f 0)) (UNIV - {0})"
    using has_sum_Diff[OF * has_sum_finite[of "{0}"]] by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f n) has_sum (S - f 0)) {0<..}"
    by (intro has_sum_reindex_bij_witness[of _ nat int]) auto
  finally have "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f n) has_sum S - f 0) {0<..}" .
  also have "?this \<longleftrightarrow> ((\<lambda>n. 2 *\<^sub>R f n) has_sum (S - f 0)) {0<..}"
    by (intro has_sum_cong) auto
  also have "\<dots> \<longleftrightarrow> (f has_sum (S - f 0) /\<^sub>R 2) {0<..}"
    by (rule has_sum_scaleR_iff) auto
  finally have 1: "(f has_sum (S - f 0) /\<^sub>R 2) {0<..}" .

  have "(f has_sum (S - f 0) /\<^sub>R 2) {0<..} \<longleftrightarrow> (f has_sum (S - f 0) /\<^sub>R 2) {..<0}"
    by (intro has_sum_reindex_bij_witness[of _ uminus uminus]) (use assms in auto)
  with 1 have 2: "(f has_sum (S - f 0) /\<^sub>R 2) {..<0}"
    by simp

  have "(f has_sum ((S - f 0) /\<^sub>R 2 + (S - f 0) /\<^sub>R 2 + f 0)) ({..<0} \<union> {0<..} \<union> {0})"
    by (intro has_sum_Un_disjoint 1 2) (auto simp: has_sum_finite_iff)
  also have "{..<0} \<union> {0<..} \<union> {0::int} = UNIV"
    by auto
  also have "(S - f 0) /\<^sub>R 2 + (S - f 0) /\<^sub>R 2 + f 0 = S"
    by (simp flip: mult_2 scaleR_2)
  finally show "(f has_sum S) UNIV" .
next
  assume *: "(f has_sum S) UNIV"
  define S' where "S' = (\<Sum>\<^sub>\<infinity>n\<in>{0<..}. f n)"
  have "f summable_on {0<..}"
    by (rule summable_on_subset_banach[of _ UNIV]) (use * in \<open>auto dest: has_sum_imp_summable\<close>)
  hence 1: "(f has_sum S') {0<..}"
    unfolding S'_def by (rule has_sum_infsum)
  
  have "(f has_sum S') {0<..} \<longleftrightarrow> (f has_sum S') {..<0}"
    by (rule has_sum_reindex_bij_witness[of _ uminus uminus]) (use assms in auto)
  with 1 have 2: "(f has_sum S') {..<0}"
    by simp

  have "(f has_sum (S' + S' + f 0)) ({..<0} \<union> {0<..} \<union> {0})"
    by (intro has_sum_Un_disjoint 1 2) (auto simp: has_sum_finite_iff)
  also have "({..<0} \<union> {0<..} \<union> {0::int}) = UNIV"
    by auto
  also have "S' + S' + f 0 = 2 *\<^sub>R S' + f 0"
    by (simp add: algebra_simps flip: scaleR_2)
  finally have 3: "S = 2 *\<^sub>R S' + f 0"
    using * has_sum_unique by blast

  have "((\<lambda>n. 2 *\<^sub>R f n) has_sum (2 *\<^sub>R S')) {0<..}"
    by (intro has_sum_scaleR 1)
  also have "?this \<longleftrightarrow> ((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f n) has_sum (2 *\<^sub>R S')) {0<..}"
    by (intro has_sum_cong) auto
  finally have "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f n) has_sum (f 0 + 2 *\<^sub>R S')) ({0} \<union> {0<..})"
    by (intro has_sum_Un_disjoint) (auto simp: has_sum_finite_iff)
  also have "?this \<longleftrightarrow> ((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f (int n)) has_sum (f 0 + 2 *\<^sub>R S')) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ int nat]) auto
  finally show "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R f (int n)) has_sum S) UNIV"
    using 3 by (simp add: add.commute)
qed

lemma sums_jacobi_theta_nw_00:
  assumes "norm q < 1"
  shows   "(\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * q ^ n) sums \<theta>\<^sub>3 q"
proof -
  define S where "S = (\<Sum>n. if is_square n \<and> n > 0 then q ^ n else 0)"
  have "((\<lambda>n. (if n = 0 then 1 else 2) *\<^sub>R q powi (int n ^ 2)) has_sum (\<theta>\<^sub>3 q)) UNIV"
  proof (subst has_sum_ints_symmetric_iff [symmetric])
    show "((\<lambda>n. q powi n\<^sup>2) has_sum \<theta>\<^sub>3 q) UNIV"
      by (rule has_sum_jacobi_theta_nw_00) fact
  qed auto
  also have "?this \<longleftrightarrow> ((\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * q ^ n) has_sum
                          \<theta>\<^sub>3 q) {n. is_square n}"
    by (rule has_sum_reindex_bij_witness[of _ floor_sqrt "\<lambda>i. i ^ 2"])
       (auto simp: fps_jacobi_theta_nw_def power_int_def scaleR_conv_of_real nat_power_eq
             elim!: is_nth_powerE)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * q ^ n) has_sum
                          \<theta>\<^sub>3 q) UNIV"
    by (intro has_sum_cong_neutral) (auto simp: fps_jacobi_theta_nw_def intro: Nat.gr0I)
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma sums_jacobi_theta_nw_01:
  assumes "norm q < 1"
  shows   "(\<lambda>n. fps_nth (fps_jacobi_theta_nw (-1)) n * q ^ n) sums \<theta>\<^sub>4 q"
proof -
  have "(\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * (-q) ^ n) sums \<theta>\<^sub>3 (-q)"
    by (rule sums_jacobi_theta_nw_00) (use assms in auto)
  also have "(\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * (-q) ^ n) =
             (\<lambda>n. fps_nth (fps_jacobi_theta_nw (-1)) n * q ^ n)"
    by (auto simp: fun_eq_iff fps_jacobi_theta_nw_def power_minus')
  also have "\<theta>\<^sub>3 (-q) = \<theta>\<^sub>4 q"
    by (simp add: jacobi_theta_nw_01_conv_00)
  finally show ?thesis .
qed

lemma has_fps_expansion_jacobi_theta_3 [fps_expansion_intros]:
  "\<theta>\<^sub>3 has_fps_expansion fps_jacobi_theta_nw 1"
proof (rule has_fps_expansionI)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (nhds (0 :: 'a))"
    by (rule eventually_nhds_in_open) auto
  thus "eventually (\<lambda>q. (\<lambda>n. fps_nth (fps_jacobi_theta_nw 1) n * q ^ n :: 'a) sums \<theta>\<^sub>3 q) (nhds 0)"
    by eventually_elim (rule sums_jacobi_theta_nw_00, auto)
qed

lemma has_fps_expansion_jacobi_theta_4 [fps_expansion_intros]:
  "\<theta>\<^sub>4 has_fps_expansion fps_jacobi_theta_nw (-1)"
proof (rule has_fps_expansionI)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (nhds (0 :: 'a))"
    by (rule eventually_nhds_in_open) auto
  thus "eventually (\<lambda>q. (\<lambda>n. fps_nth (fps_jacobi_theta_nw (-1)) n * q ^ n :: 'a) sums \<theta>\<^sub>4 q) (nhds 0)"
    by eventually_elim (rule sums_jacobi_theta_nw_01, auto)
qed

lemma fps_conv_radius_jacobi_theta_nw [simp]:
  fixes c :: "'a :: {banach, real_normed_field}"
  shows "fps_conv_radius (fps_jacobi_theta_nw c) = 1 / ereal (norm c)"
proof -
  have "fps_conv_radius (fps_jacobi_theta_nw c) = 
          inverse (limsup (\<lambda>n. ereal (root n (norm (fps_nth (fps_jacobi_theta_nw c) n)))))"
    by (simp add: fps_conv_radius_def conv_radius_def)
  also have "limsup (\<lambda>n. ereal (root n (norm (fps_nth (fps_jacobi_theta_nw c) n)))) = norm c"
    (is "?lhs = _")
  proof (rule antisym)
    have "?lhs \<le> limsup (\<lambda>n. root n 2 * norm c)"
      by (intro Limsup_mono always_eventually)
         (auto simp: fps_jacobi_theta_nw_def norm_power real_root_mult real_root_power)
    also have "(\<lambda>n. ereal (root n 2 * norm c)) \<longlonglongrightarrow> ereal (1 * norm c)"
      by (intro tendsto_intros LIMSEQ_root_const) auto
    hence "limsup (\<lambda>n. root n 2 * norm c) = ereal (1 * norm c)" 
      by (intro lim_imp_Limsup) auto
    finally show "?lhs \<le> norm c"
      by simp
  next
    have "limsup ((\<lambda>n. ereal (root n (norm (fps_nth (fps_jacobi_theta_nw c) n)))) \<circ> (\<lambda>n. n ^ 2)) \<le> ?lhs"
      by (rule limsup_subseq_mono) (auto intro!: strict_monoI power_strict_mono)
    also have "limsup ((\<lambda>n. ereal (root n (norm (fps_nth (fps_jacobi_theta_nw c) n)))) \<circ> (\<lambda>n. n ^ 2)) =
               limsup ((\<lambda>n. ereal (root (n^2) 2 * norm c)))"
      by (rule Limsup_eq, rule eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: o_def fps_jacobi_theta_nw_def norm_power real_root_mult real_root_power)
    also have "(\<lambda>n. ereal (root (n^2) 2 * norm c)) \<longlonglongrightarrow> ereal (1 * norm c)"
      by (intro tendsto_intros filterlim_compose[OF LIMSEQ_root_const]
                filterlim_subseq[of "\<lambda>n. n ^ 2"] strict_monoI power_strict_mono) auto
    hence "limsup (\<lambda>n. ereal (root (n^2) 2 * norm c)) = ereal (1 * norm c)"
      by (intro lim_imp_Limsup) auto
    finally show "norm c \<le> ?lhs"
      by simp
  qed
  finally show ?thesis
    by (simp add: divide_ereal_def)
qed


text \<open>
  Recall that $\vartheta_2(q) = q^{1/4} \vartheta(q, q)$. Since the factor $q^{1/4}$ has a branch cut,
  it is somewhat unpleasant to deal with and we will concentrate only on the factor $\vartheta(q,q)$
  for now. This is a holomorphic function on the unit disc except for a removable singularity
  at $q = 0$.

  For $q\neq 0$ and $|q|<1$, $\vartheta(q,q)$ has following the power series expansion:
  \[ \vartheta(q,q) = \sum_{n=-\infty}^{\infty} q^{n(n+1)} = \sum_{n=0}^{\infty} 2 q^{n(n+1)} \]
  Note that $n(n+1)$ is twice the triangular number $n(n+1)/2$, so we can also see this as a
  series expansion in terms of powers of $q^2$.
\<close>
lemma has_sum_jacobi_theta_nw_10_aux:
  assumes q: "norm q < 1" "q \<noteq> 0"
  shows   "((\<lambda>n. 2 * q ^ (n*(n+1))) has_sum jacobi_theta_nome q q) UNIV"
proof -
  define S where "S = jacobi_theta_nome q q"
  have 1: "((\<lambda>n. q powi (n*(n+1))) has_sum S) UNIV"
    using has_sum_jacobi_theta_nome[of q q]
    using q by (simp add: algebra_simps power2_eq_square power_int_add S_def)
  have summable: "(\<lambda>n. q powi (n * (n + 1))) summable_on I" for I
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF 1]) auto

  define S1 where "S1 = (\<Sum>\<^sub>\<infinity>n\<in>{0..}. q powi (n*(n+1)))"
  have S1: "((\<lambda>n. q powi (n*(n+1))) has_sum S1) {0..}"
    unfolding S1_def by (rule has_sum_infsum[OF summable])
  have "((\<lambda>n. q powi (n*(n+1))) has_sum S1) {0..} \<longleftrightarrow>
        ((\<lambda>n. q powi (n*(n+1))) has_sum S1) {..<0}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. -n-1" "\<lambda>n. -n-1"])
       (auto simp: algebra_simps)
  with S1 have S1': "((\<lambda>n. q powi (n*(n+1))) has_sum S1) {..<0}"
    by simp
  have "((\<lambda>n. q powi (n*(n+1))) has_sum (S1 + S1)) ({..<0} \<union> {0..})"
    by (intro has_sum_Un_disjoint S1 S1') auto
  also have "{..<(0::int)} \<union> {0..} = UNIV"
    by auto
  finally have 2: "((\<lambda>n. q powi (n*(n+1))) has_sum (2 * S1)) UNIV"
    by simp
  
  from this and 1 have 3: "2 * S1 = S"
    using has_sum_unique by blast

  have "((\<lambda>n. q powi (n*(n+1))) has_sum S1) {0..} \<longleftrightarrow> ((\<lambda>n. q ^ (n*(n+1))) has_sum S1) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ int nat]) 
       (auto simp: power_int_def algebra_simps power_add nat_add_distrib nat_mult_distrib)
  with S1 show "((\<lambda>n. 2 * q ^ (n*(n+1))) has_sum S) UNIV"
    unfolding 3 [symmetric] by (intro has_sum_cmult_right) auto
qed

lemma sums_jacobi_theta_nw_10_aux:
  assumes q: "norm q < 1" "q \<noteq> 0"
  shows   "(\<lambda>n. if \<exists>i. n = i*(i+1) then 2 * q ^ n else 0) sums jacobi_theta_nome q q"
proof -
  have inj: "inj (\<lambda>i::nat. i * (i + 1))"
    by (rule strict_mono_imp_inj_on) (auto simp: strict_mono_Suc_iff)
  have "((\<lambda>n. 2 * q ^ (n*(n+1))) has_sum jacobi_theta_nome q q) UNIV"
    by (rule has_sum_jacobi_theta_nw_10_aux) fact+
  also have "?this \<longleftrightarrow> ((\<lambda>n. 2 * q ^ n) has_sum jacobi_theta_nome q q) (range (\<lambda>i. i*(i+1)))"
    by (subst has_sum_reindex[OF inj]) (auto simp: o_def)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n. if \<exists>i. n = i*(i+1) then 2 * q ^ n else 0) has_sum jacobi_theta_nome q q) UNIV"
    by (rule has_sum_cong_neutral) auto
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

definition fps_jacobi_theta_nw_10 :: "'a :: field fps" where
  "fps_jacobi_theta_nw_10 = Abs_fps (\<lambda>n. if \<exists>i. n = i*(i+1) then 2 else 0)"

lemma fps_conv_radius_jacobi_theta_2 [simp]: "fps_conv_radius fps_jacobi_theta_nw_10 = 1"
proof -
  have "fps_conv_radius (fps_jacobi_theta_nw_10 :: 'a fps) =
          inverse (limsup (\<lambda>n. ereal (root n (norm (fps_nth fps_jacobi_theta_nw_10 n :: 'a)))))"
    unfolding fps_conv_radius_def conv_radius_def ..
  also have "limsup (\<lambda>n. ereal (root n (norm (fps_nth fps_jacobi_theta_nw_10 n :: 'a)))) = 1"
    (is "?lhs = _")
  proof (rule antisym)
    have "?lhs \<le> limsup (\<lambda>n. root n 2)"
      by (intro Limsup_mono always_eventually)
         (auto simp: fps_jacobi_theta_nw_10_def norm_power real_root_ge_zero)
    also have "(\<lambda>n. ereal (root n 2)) \<longlonglongrightarrow> ereal 1"
      by (intro tendsto_intros LIMSEQ_root_const) auto
    hence "limsup (\<lambda>n. root n 2) = ereal 1" 
      by (intro lim_imp_Limsup) auto
    finally show "?lhs \<le> 1"
      by (simp add: one_ereal_def)
  next
    define h where "h = (\<lambda>n::nat. n * (n + 1))"
    have h: "strict_mono h"
      by (rule strict_monoI_Suc) (auto simp: algebra_simps h_def)
    have "limsup ((\<lambda>n. ereal (root n (norm (fps_nth fps_jacobi_theta_nw_10 n :: 'a)))) \<circ> h) \<le> ?lhs"
      using h by (rule limsup_subseq_mono)
    also have "limsup ((\<lambda>n. ereal (root n (norm (fps_nth fps_jacobi_theta_nw_10 n :: 'a)))) \<circ> h) =
               limsup ((\<lambda>n. ereal (root (h n) 2)))"
      by (rule Limsup_eq, rule eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: o_def fps_jacobi_theta_nw_10_def h_def algebra_simps)
    also have "(\<lambda>n. ereal (root (h n) 2)) \<longlonglongrightarrow> ereal 1"
      by (intro tendsto_intros filterlim_compose[OF LIMSEQ_root_const]
                filterlim_subseq[of h] h) auto
    hence "limsup (\<lambda>n. ereal (root (h n) 2)) = ereal 1"
      by (intro lim_imp_Limsup) auto
    finally show "1 \<le> ?lhs"
      by (simp add: one_ereal_def)
  qed
  finally show ?thesis
    by simp
qed

lemma has_laurent_expansion_jacobi_theta_2 [laurent_expansion_intros]:
  "(\<lambda>q. jacobi_theta_nome q q) has_laurent_expansion fps_to_fls fps_jacobi_theta_nw_10"
  unfolding has_laurent_expansion_def
proof safe
  show "fls_conv_radius (fps_to_fls fps_jacobi_theta_nw_10 :: complex fls) > 0"
    unfolding fls_conv_radius_fps_to_fls by simp
next
  have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at (0 :: complex))"
    by (rule eventually_at_in_open) auto
  thus "eventually (\<lambda>q. eval_fls (fps_to_fls fps_jacobi_theta_nw_10) q = 
         jacobi_theta_nome q q) (at (0::complex))"
  proof eventually_elim
    case q: (elim q)
    have "eval_fls (fps_to_fls fps_jacobi_theta_nw_10) q = eval_fps fps_jacobi_theta_nw_10 q"
      by (subst eval_fps_to_fls) (use q in auto)
    also have "eval_fps fps_jacobi_theta_nw_10 q = (\<Sum>n. fps_nth fps_jacobi_theta_nw_10 n * q ^ n)"
      by (simp add: eval_fps_def)
    also have "(\<lambda>n. fps_nth fps_jacobi_theta_nw_10 n * q ^ n) = 
               (\<lambda>n. if \<exists>i. n = i*(i+1) then 2 * q ^ n else 0)"
      by (auto simp: fun_eq_iff fps_jacobi_theta_nw_10_def)
    also have "(\<Sum>n. \<dots> n) = jacobi_theta_nome q q"
      using sums_jacobi_theta_nw_10_aux[of q] q by (simp add: sums_iff)
    finally show ?case .
  qed
qed

text \<open>
  For $\vartheta(q,q)^2$, we can find the following expansion into a double sum:
  \[\vartheta(q,q)^2 = \sum_{n=-\infty}^\infty \sum_{n=-\infty}^\infty q^{i(i+1) + j(j+1)}\]
\<close>
lemma has_sum_jacobi_theta_nw_10_aux_square:
  fixes q :: complex
  assumes q: "norm q < 1" "q \<noteq> 0"
  shows "((\<lambda>(i,j). q powi (i*(i+1) + j*(j+1))) has_sum jacobi_theta_nome q q ^ 2) UNIV"
proof -
  define S where "S = jacobi_theta_nome q q"
  have 1: "((\<lambda>n. q powi (n*(n+1))) has_sum S) UNIV"
    using has_sum_jacobi_theta_nome[of q q]
    using q by (simp add: algebra_simps power2_eq_square power_int_add S_def)
  have summable: "(\<lambda>n. q powi (n * (n + 1))) summable_on I" for I
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF 1]) auto

  define S' where "S' = jacobi_theta_nome (norm q) (norm q)"
  have 2: "((\<lambda>n. norm q powi (n*(n+1))) has_sum S') UNIV"
    using has_sum_jacobi_theta_nome[of "norm q" "norm q"]
    using q by (simp add: algebra_simps power2_eq_square power_int_add S'_def)

  have "((\<lambda>(i,j). q powi (i*(i+1) + j*(j+1))) has_sum S\<^sup>2) (UNIV \<times> UNIV)"
  proof (rule has_sum_SigmaI; (unfold prod.case)?)
    show "((\<lambda>i. S * q powi (i*(i+1))) has_sum S^2) UNIV"
      unfolding power2_eq_square by (intro has_sum_cmult_right 1)
  next
    fix i :: int
    show "((\<lambda>j. q powi (i * (i + 1) + j * (j + 1))) has_sum S * q powi (i * (i + 1))) UNIV"
      using has_sum_cmult_left[OF 1, of "q powi (i * (i + 1))"] q
      by (simp add: power_int_add mult_ac)
  next
    have "(\<lambda>ij. norm (case ij of (i,j) \<Rightarrow> q powi (i * (i + 1) + j * (j + 1)))) summable_on UNIV \<times> UNIV"
    proof (rule summable_on_SigmaI; (unfold prod.case)?)
      show "(\<lambda>j. S' * norm q powi (j * (j + 1))) summable_on UNIV"
        using has_sum_imp_summable[OF 2] by (intro summable_on_cmult_right)
    next
      fix i :: int
      show "((\<lambda>j. norm (q powi (i*(i+1) + j*(j+1)))) has_sum (S' * norm q powi (i*(i+1)))) UNIV"
        using has_sum_cmult_left[OF 2, of "norm q powi (i*(i+1))"] q
        by (simp add: norm_power_int norm_mult power_int_add mult_ac)
    qed auto
    thus "(\<lambda>(i, j). q powi (i * (i + 1) + j * (j + 1))) summable_on UNIV \<times> UNIV"
      by (rule abs_summable_summable)
  qed
  thus ?thesis
    by (simp add: S_def)
qed

text \<open>
  With some creative reindexing, we find the following power series expansion:
  \[ q \vartheta(q^2, q^2)^2 = \sum_{n=0}^\infty r_2(2n+1) q^{2n+1} \]
\<close>
lemma sums_q_times_jacobi_theta_nw_10_aux_square_square:
  fixes q :: complex
  assumes q: "q \<noteq> 0" "norm q < 1"
  shows "(\<lambda>n. (if odd n then of_nat (count_sos 2 n) else 0) * q ^ n) sums
           (q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2)"
proof -
  define IJ where "IJ = (\<lambda>n. {(i, j). i\<^sup>2 + j\<^sup>2 = int n})"
  have [simp, intro]: "finite (IJ n)" for n
    using bij_betw_finite[OF bij_betw_sos_decomps_2[of n]] by (simp add: IJ_def)

  have aux: "1 + x \<noteq> y" if "even x" "even y" for x y :: int
    using that by presburger

  define S where "S = q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2"
  have "((\<lambda>(i,j). (q^2) powi (i*(i+1) + j*(j+1))) has_sum jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2) UNIV"
    by (intro has_sum_jacobi_theta_nw_10_aux_square) 
       (use q in \<open>auto simp: norm_power power_less_one_iff\<close>)
  hence "((\<lambda>(i,j). q * (q^2) powi (i*(i+1) + j*(j+1))) has_sum S) (UNIV \<times> UNIV)"
    unfolding S_def case_prod_unfold by (intro has_sum_cmult_right) auto
  also have "((\<lambda>(i,j). q * (q^2) powi (i*(i+1) + j*(j+1)))) =
             ((\<lambda>(i,j). q powi (1 + 2 * (i*(i+1) + j*(j+1)))))" using q
    by (auto simp: power_int_add power2_eq_square fun_eq_iff power_int_mult_distrib algebra_simps)
       (auto simp flip: power_int_add simp: algebra_simps)?
  also have "(\<dots> has_sum S) (UNIV \<times> UNIV) \<longleftrightarrow>
             ((\<lambda>(i,j). q powi (i ^ 2 + j ^ 2)) has_sum S) {(i,j). odd (i^2+j^2)}"
    by (rule has_sum_reindex_bij_witness[of _ 
             "\<lambda>(i,j). ((j+i-1) div 2, (j-i-1) div 2)" "\<lambda>(i,j). (i-j, i+j+1)"])
       (auto elim!: evenE oddE simp: algebra_simps power2_eq_square aux
             intro!: arg_cong[of _ _ "\<lambda>a. q powi a"])
  also have "\<dots> \<longleftrightarrow> ((\<lambda>(n,(i,j)). q powi n) has_sum S) (SIGMA n:{n. odd n}. IJ n)"
  proof (rule has_sum_reindex_bij_witness[of _ snd "\<lambda>(i,j). (nat (i^2+j^2), (i,j))"])
    fix nij assume nij: "nij \<in> Sigma {n. odd n} IJ"
    obtain n i j where [simp]: "nij = (n, (i, j))"
      using prod_cases3 by blast
    from nij have n: "odd n" and ij: "i ^ 2 + j ^ 2 = int n"
      by (auto simp: IJ_def)
    have "odd (int n)"
      using n by simp
    also have "int n = i ^ 2 + j ^ 2"
      by (rule ij [symmetric])
    finally show "snd nij \<in> {(i, j). odd (i\<^sup>2 + j\<^sup>2)}"
      by auto
  qed (auto simp: IJ_def even_nat_iff)    
  finally have *: "((\<lambda>(n,(i,j)). q powi n) has_sum S) (SIGMA n:{n. odd n}. IJ n)" .
  have "((\<lambda>n. count_sos 2 n * q ^ n) has_sum S) {n. odd n}"
  proof (rule has_sum_SigmaD[OF *]; unfold prod.case)
    fix n :: nat assume n: "n \<in> {n. odd n}"
    have "count_sos 2 n = card (IJ n)"
      by (simp add: IJ_def count_sos_2)
    thus "((\<lambda>(i,j). q powi int n) has_sum complex_of_nat (count_sos 2 n) * q ^ n) (IJ n)"
      using q by (simp add: has_sum_finite_iff)
  qed
  also have "?this \<longleftrightarrow> ((\<lambda>n. (if odd n then of_nat (count_sos 2 n) else 0) * q ^ n) has_sum S) UNIV"
    by (intro has_sum_cong_neutral) auto
  finally show "(\<lambda>n. (\<lambda>n. if odd n then of_nat (count_sos 2 n) else 0) n * q ^ n) sums S"
    by (rule has_sum_imp_sums)
qed

lemma has_laurent_expansion_q_times_jacobi_theta_nw_10_aux_square_square:
  defines "F \<equiv> Abs_fps (\<lambda>n. if odd n then of_nat (count_sos 2 n) else 0)"
  shows "(\<lambda>q. q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2) has_laurent_expansion fps_to_fls F"
  unfolding has_laurent_expansion_def
proof
  have "0 < norm (1/2::complex)"
    by simp
  also have "fls_conv_radius (fps_to_fls F) \<ge> norm (1 / 2 :: complex)"
    unfolding fls_conv_radius_fps_to_fls fps_conv_radius_def
    by (rule conv_radius_geI) (use sums_q_times_jacobi_theta_nw_10_aux_square_square[of "1/2"] 
        in  \<open>auto simp: sums_iff F_def\<close>)
  finally show "fls_conv_radius (fps_to_fls F) > 0" 
    by - (simp_all add: zero_ereal_def)
next
  have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at (0::complex))"
    by (rule eventually_at_in_open) auto
  thus "\<forall>\<^sub>F q in at 0. eval_fls (fps_to_fls F) q = q * (jacobi_theta_nome (q\<^sup>2) (q\<^sup>2))\<^sup>2"
  proof eventually_elim
    case q: (elim q)
    have "(\<lambda>n. fps_nth F n * q ^ n) sums (q * (jacobi_theta_nome (q\<^sup>2) (q\<^sup>2))\<^sup>2)"
      using sums_q_times_jacobi_theta_nw_10_aux_square_square[of q] q by (simp add: F_def)
    thus "eval_fls (fps_to_fls F) q = q * (jacobi_theta_nome (q\<^sup>2) (q\<^sup>2))\<^sup>2"
      using eval_fls_eq[of 0 "fps_to_fls F" q "q * (jacobi_theta_nome (q\<^sup>2) (q\<^sup>2))\<^sup>2"]
      by (simp add: fls_subdegree_fls_to_fps_gt0)
  qed
qed


subsection \<open>Identities\<close>

text \<open>
  Lastly, we derive a variety of identities between the different theta functions.
\<close>

theorem jacobi_theta_nw_00_plus_01_complex: "\<theta>\<^sub>3 q + \<theta>\<^sub>4 q = 2 * \<theta>\<^sub>3 (q ^ 4 :: complex)"
proof (cases "norm q < 1")
  case q: True
  define f :: "complex \<Rightarrow> complex" where "f = (\<lambda>q. \<theta>\<^sub>3 q + \<theta>\<^sub>4 q - 2 * \<theta>\<^sub>3 (q ^ 4))"
  define F :: "complex fps" 
    where "F = fps_jacobi_theta_nw 1 + fps_jacobi_theta_nw (-1) - 
               2 * (fps_jacobi_theta_nw 1 oo fps_X ^ 4)"
  have [simp]: "is_square (4 :: nat)"
    unfolding is_nth_power_def by (rule exI[of _ 2]) auto
  have "fps_jacobi_theta_nw 1 + fps_jacobi_theta_nw (-1 :: complex) =
        2 * Abs_fps (\<lambda>n. if n = 0 then 1 else if even n \<and> is_square n then 2 else 0)"
    by (intro fps_ext) (auto simp: fps_jacobi_theta_nw_def intro: Nat.gr0I)
  also have "Abs_fps (\<lambda>n. if n = 0 then 1 else if even n \<and> is_square n then 2 else 0) =
               fps_compose (fps_jacobi_theta_nw 1) (fps_X ^ 4)"
    by (auto simp: fps_eq_iff fps_jacobi_theta_nw_def fps_nth_compose_X_power is_square_mult2_nat_iff
                   is_nth_power_mult_cancel_left elim!: dvdE)
  finally have "F = 0"
    by (simp add: F_def)

  have "f q = 0"
  proof (rule has_fps_expansion_0_analytic_continuation[of f])
    have "(\<lambda>q. \<theta>\<^sub>3 q + \<theta>\<^sub>4 q - 2 * (\<theta>\<^sub>3 \<circ> (\<lambda>q. q ^ 4)) q) has_fps_expansion F"
      unfolding F_def by (intro fps_expansion_intros has_fps_expansion_compose) auto
    also have "F = 0"
      by fact
    finally show "f has_fps_expansion 0"
      by (simp add: f_def)
  next
    show "f holomorphic_on ball 0 1"
      unfolding f_def by (auto intro!: holomorphic_intros simp: norm_power power_less_one_iff)
  qed (use q in auto)
  thus ?thesis
    by (simp add: f_def)
qed (auto simp: norm_power power_less_one_iff)

lemma jacobi_theta_nw_00_plus_01_real: "\<theta>\<^sub>3 q + \<theta>\<^sub>4 q = 2 * \<theta>\<^sub>3 (q ^ 4 :: real)"
  by (subst of_real_eq_iff [where ?'a = complex, symmetric],
         unfold of_real_add of_real_mult of_real_diff)
     (use jacobi_theta_nw_00_plus_01_complex[of q] 
      in  \<open>simp_all flip: jacobi_theta_nome_00_of_real jacobi_theta_nome_01_of_real\<close>)


theorem jacobi_theta_nw_00_plus_01_square_complex:
  "\<theta>\<^sub>3 q ^ 2 + \<theta>\<^sub>4 q ^ 2 = 2 * \<theta>\<^sub>3 (q ^ 2 :: complex) ^ 2"
proof (cases "norm q < 1")
  case q: True
  define F :: "complex fps"
    where "F = 2 * fps_compose (fps_jacobi_theta_nw 1 ^ 2) (fps_X ^ 2) - 
               fps_jacobi_theta_nw 1 ^ 2 - fps_jacobi_theta_nw (-1) ^ 2"
  have "(\<lambda>z. 2 * ((\<lambda>z. \<theta>\<^sub>3 z ^ 2) \<circ> (\<lambda>z. z ^ 2)) z - \<theta>\<^sub>3 z ^ 2 - \<theta>\<^sub>4 z ^ 2) has_fps_expansion F"
    unfolding F_def by (intro fps_expansion_intros has_fps_expansion_compose) auto
  also have "F = 0"
  proof -
    have "2 * fps_compose (Abs_fps (\<lambda>n. of_nat (count_sos 2 n) :: complex)) (fps_X ^ 2) =
            Abs_fps (\<lambda>n. if even n then of_nat (2 * count_sos 2 n) else 0)"
      by (auto elim!: evenE simp: fps_nth_compose_X_power fps_eq_iff count_sos_2_double)
    also have "\<dots> = fps_jacobi_theta_nw 1 ^ 2 + fps_jacobi_theta_nw (-1) ^ 2"
      by (auto simp: fps_eq_iff fps_jacobi_theta_power_eq)
    also have "Abs_fps (\<lambda>n. of_nat (count_sos 2 n)) = fps_jacobi_theta_nw 1 ^ 2"
      by (simp add: fps_jacobi_theta_power_eq)
    finally show "F = 0" 
      by (simp add: algebra_simps F_def)
  qed
  finally have "(\<lambda>z::complex. 2 * \<theta>\<^sub>3 (z\<^sup>2) ^ 2 - \<theta>\<^sub>3 z ^ 2 - \<theta>\<^sub>4 z ^ 2) has_fps_expansion 0"
    by simp
  hence "2 * (\<theta>\<^sub>3 (q\<^sup>2))\<^sup>2 - (\<theta>\<^sub>3 q)\<^sup>2 - (\<theta>\<^sub>4 q)\<^sup>2 = 0"
    by (rule has_fps_expansion_0_analytic_continuation[where A = "ball 0 1"])
       (use q in \<open>auto intro!: holomorphic_intros simp: norm_power power_less_one_iff\<close>)
  thus ?thesis
    by (simp add: algebra_simps)
qed (auto simp: norm_power power_less_one_iff)

corollary midpoint_jacobi_theta_nw_00_01_square_complex:
  "midpoint (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2) = \<theta>\<^sub>3 (q ^ 2 :: complex) ^ 2"
  using jacobi_theta_nw_00_plus_01_square_complex[of q] by (simp add: midpoint_def)

lemma jacobi_theta_nw_00_plus_01_square_real: "\<theta>\<^sub>3 q ^ 2 + \<theta>\<^sub>4 q ^ 2 = 2 * \<theta>\<^sub>3 (q ^ 2 :: real) ^ 2"
  by (subst of_real_eq_iff [where ?'a = complex, symmetric],
         unfold of_real_add of_real_mult of_real_diff)
     (use jacobi_theta_nw_00_plus_01_square_complex[of q] 
      in  \<open>simp_all flip: jacobi_theta_nome_00_of_real jacobi_theta_nome_01_of_real\<close>)

theorem jacobi_theta_nw_00_times_01_complex: "\<theta>\<^sub>3 q * \<theta>\<^sub>4 q = (\<theta>\<^sub>4 (q ^ 2) ^ 2 :: complex)"
proof -
  have "2 * \<theta>\<^sub>3 q * \<theta>\<^sub>4 q = (\<theta>\<^sub>3 q + \<theta>\<^sub>4 q) ^ 2 - (\<theta>\<^sub>3 q ^ 2 + \<theta>\<^sub>4 q ^ 2)"
    by Groebner_Basis.algebra
  also have "\<dots> = 2 * (2 * \<theta>\<^sub>3 (q ^ 4) ^ 2 - \<theta>\<^sub>3 (q\<^sup>2) ^ 2)"
    unfolding jacobi_theta_nw_00_plus_01_complex jacobi_theta_nw_00_plus_01_square_complex
    by Groebner_Basis.algebra
  also have "2 * \<theta>\<^sub>3 (q ^ 4) ^ 2 - \<theta>\<^sub>3 (q\<^sup>2) ^ 2 = \<theta>\<^sub>4 (q\<^sup>2) ^ 2"
    using jacobi_theta_nw_00_plus_01_square_complex[of "q ^ 2"]
    by (simp add: algebra_simps)
  finally show ?thesis
    by simp
qed

lemma jacobi_theta_nw_00_times_01_real: "\<theta>\<^sub>3 q * \<theta>\<^sub>4 q = (\<theta>\<^sub>4 (q ^ 2) ^ 2 :: real)"
  by (subst of_real_eq_iff [where ?'a = complex, symmetric],
         unfold of_real_add of_real_mult of_real_diff)
     (use jacobi_theta_nw_00_times_01_complex[of q] 
      in  \<open>simp_all flip: jacobi_theta_nome_00_of_real jacobi_theta_nome_01_of_real\<close>)

lemma jacobi_theta_nw_00_plus_10_square_square_aux:
  fixes q :: complex
  shows "\<theta>\<^sub>3 q ^ 2 - \<theta>\<^sub>3 (q\<^sup>2) ^ 2 = q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2"
proof (cases "q \<noteq> 0 \<and> norm q < 1")
  case True
  define f :: "complex \<Rightarrow> complex"
    where "f = (\<lambda>q. \<theta>\<^sub>3 q ^ 2 - ((\<lambda>q. \<theta>\<^sub>3 q ^ 2) \<circ> (\<lambda>q. q ^ 2)) q - q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2)"
  define F where "F = (fps_to_fls (fps_jacobi_theta_nw 1))\<^sup>2 -
    fps_to_fls ((fps_jacobi_theta_nw 1)\<^sup>2 oo fps_X\<^sup>2) -
    fps_to_fls (Abs_fps (\<lambda>n. if odd n then complex_of_nat (count_sos 2 n) else 0))"
  have "f has_laurent_expansion F"
    unfolding F_def f_def
    by (intro laurent_expansion_intros fps_expansion_intros
              has_laurent_expansion_q_times_jacobi_theta_nw_10_aux_square_square
              has_laurent_expansion_fps) auto
  also have "F = fps_to_fls 0"
    unfolding F_def fps_to_fls_power [symmetric] fps_to_fls_minus [symmetric] fps_to_fls_eq_iff
    by (auto simp: fps_eq_iff fps_jacobi_theta_power_eq fps_nth_compose_X_power count_sos_2_double 
             elim!: evenE)
  finally have "f has_laurent_expansion 0" 
    by simp

  have "f q = 0"
  proof (rule has_laurent_expansion_0_analytic_continuation[of f])
    show "f has_laurent_expansion 0"
      by fact
    show "f holomorphic_on ball 0 1 - {0}"
      by (auto simp: f_def o_def norm_power power_less_one_iff intro!: holomorphic_intros)
  qed (use True in auto)
  thus ?thesis
    by (simp add: f_def)
qed (auto simp: norm_power power_less_one_iff)

theorem jacobi_theta_nw_00_plus_10_square_square_complex:
  fixes q :: complex
  assumes "Re q \<ge> 0 \<and> (Re q = 0 \<longrightarrow> Im q \<ge> 0)"
  shows   "\<theta>\<^sub>3 (q\<^sup>2) ^ 2 + \<theta>\<^sub>2 (q\<^sup>2) ^ 2 = \<theta>\<^sub>3 q ^ 2"
proof -
  have "\<theta>\<^sub>3 q ^ 2 - \<theta>\<^sub>3 (q\<^sup>2) ^ 2 = q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2"
    by (rule jacobi_theta_nw_00_plus_10_square_square_aux)
  also have "q = ((q ^ 2) powr (1 / 4)) ^ 2"
  proof -
    have "((q ^ 2) powr (1 / 4)) ^ 2 = csqrt (q ^ 2)"
      using assms by (auto simp add: powr_def csqrt_exp_Ln simp flip: exp_of_nat_mult)
    also have "csqrt (q ^ 2) = q"
      by (rule csqrt_unique) (use assms in \<open>auto simp: not_less\<close>)
    finally show ?thesis ..
  qed
  hence "q * jacobi_theta_nome (q\<^sup>2) (q\<^sup>2) ^ 2 = \<theta>\<^sub>2 (q ^ 2) ^ 2"
    by (simp add: jacobi_theta_nome_10_def power_mult_distrib)
  finally show ?thesis by (Groebner_Basis.algebra)
qed

lemma jacobi_theta_nw_00_plus_10_square_square_real:
  assumes "q \<ge> (0::real)"
  shows   "\<theta>\<^sub>3 (q\<^sup>2) ^ 2 + \<theta>\<^sub>2 (q\<^sup>2) ^ 2 = \<theta>\<^sub>3 q ^ 2"
  by (subst of_real_eq_iff [where ?'a = complex, symmetric],
         unfold of_real_add of_real_mult of_real_diff)
     (use jacobi_theta_nw_00_plus_10_square_square_complex[of q] assms 
      in  \<open>simp_all flip: jacobi_theta_nome_00_of_real jacobi_theta_nome_10_complex_of_real\<close>)


theorem jacobi_theta_nw_00_minus_10_square_square_complex:
  assumes "0 \<le> Re q \<and> (Re q = 0 \<longrightarrow> 0 \<le> Im q)"
  shows   "\<theta>\<^sub>3 (q\<^sup>2) ^ 2 - \<theta>\<^sub>2 (q\<^sup>2) ^ 2 = \<theta>\<^sub>4 (q :: complex) ^ 2"
  using jacobi_theta_nw_00_plus_01_square_complex[of q]
        jacobi_theta_nw_00_plus_10_square_square_complex[OF assms]
  by Groebner_Basis.algebra

lemma jacobi_theta_nw_00_minus_10_square_square_real:
  assumes "q \<ge> (0::real)"
  shows   "\<theta>\<^sub>3 (q\<^sup>2) ^ 2 - \<theta>\<^sub>2 (q\<^sup>2) ^ 2 = \<theta>\<^sub>4 q ^ 2"
  using jacobi_theta_nw_00_plus_01_square_real[of q]
        jacobi_theta_nw_00_plus_10_square_square_real[OF assms]
  by Groebner_Basis.algebra

text \<open>
  The following shows that the theta nullwerte provide a parameterisation of the
  Fermat curve $X^4 + Y^4 = Z^4$:
\<close>
theorem jacobi_theta_nw_pow4_complex: "\<theta>\<^sub>2 q ^ 4 + \<theta>\<^sub>4 q ^ 4 = (\<theta>\<^sub>3 q ^ 4 :: complex)"
proof (cases "norm q < 1")
  case q: True
  define r where "r = csqrt q"
  have q_eq: "q = r ^ 2"
    by (simp add: r_def)
  have "norm r < 1"
    using q by (auto simp: r_def)
  have "0 \<le> Re r \<and> (Re r = 0 \<longrightarrow> 0 \<le> Im r)"
    using csqrt_principal[of q] by (auto simp: r_def simp del: csqrt.sel)
  note r = \<open>norm r < 1\<close> this

  have "\<theta>\<^sub>3 q ^ 4 - \<theta>\<^sub>2 q ^ 4 = (\<theta>\<^sub>3 q ^ 2 + \<theta>\<^sub>2 q ^ 2) * (\<theta>\<^sub>3 q ^ 2 - \<theta>\<^sub>2 q ^ 2)"
    by Groebner_Basis.algebra
  also have "\<dots> = (\<theta>\<^sub>3 r * \<theta>\<^sub>4 r) ^ 2"
    using jacobi_theta_nw_00_plus_10_square_square_complex[OF r(2)]
          jacobi_theta_nw_00_minus_10_square_square_complex[OF r(2)]
    unfolding q_eq by Groebner_Basis.algebra
  also have "\<theta>\<^sub>3 r * \<theta>\<^sub>4 r = \<theta>\<^sub>4 q ^ 2"
    unfolding q_eq using jacobi_theta_nw_00_times_01_complex[of r] .
  finally have "\<theta>\<^sub>3 q ^ 4 - \<theta>\<^sub>2 q ^ 4 = \<theta>\<^sub>4 q ^ 4"
    by simp
  thus ?thesis
    by Groebner_Basis.algebra
qed auto

lemma jacobi_theta_nw_pow4_real: "q \<ge> 0 \<Longrightarrow> \<theta>\<^sub>2 q ^ 4 + \<theta>\<^sub>4 q ^ 4 = (\<theta>\<^sub>3 q ^ 4 :: real)"
  by (subst of_real_eq_iff [where ?'a = complex, symmetric],
         unfold of_real_add of_real_mult of_real_diff)
      (use jacobi_theta_nw_pow4_complex[of q] 
       in  \<open>simp_all flip: jacobi_theta_nome_00_of_real jacobi_theta_nome_01_of_real 
                           jacobi_theta_nome_10_complex_of_real\<close>)




subsection \<open>Properties of the nullwert functions on the real line\<close>

lemma has_field_derivative_jacobi_theta_nw_00:
  fixes q :: "'a :: {real_normed_field,banach}"
  assumes q: "norm q < 1"
  defines "a \<equiv> (\<lambda>n. 2 * (of_nat n + 1)\<^sup>2 * q ^ (n * (n + 2)))"
  shows "summable a" "(\<theta>\<^sub>3 has_field_derivative (\<Sum>n. a n)) (at q)"
proof -
  define F :: "'a fps" where "F = fps_jacobi_theta_nw 1"
  define F' where [simp]: "F' = fps_deriv F"
  define f' :: "'a \<Rightarrow> 'a" where "f' = eval_fps F"
  have [simp]: "fps_conv_radius F = 1"
    unfolding F_def using fps_conv_radius_jacobi_theta_nw[of "1::'a"] 
    by (simp add: one_ereal_def)

  have "(\<lambda>n. fps_nth F' n * q ^ n) sums eval_fps F' q"
    by (rule sums_eval_fps)
       (use q in \<open>auto intro!: less_le_trans[OF _ fps_conv_radius_deriv]\<close>)
  moreover have "bij_betw (\<lambda>n. (n+1)^2 - 1) UNIV {n. is_square (Suc n)}"
    by (rule bij_betwI[of _ _ _ "\<lambda>n. floor_sqrt (n+1) - 1"]) (auto elim!: is_nth_powerE)
  moreover have "strict_mono (\<lambda>n::nat. (n+1)^2 - 1)"
    by (intro strict_monoI_Suc) (auto simp: power2_eq_square)
  ultimately have "(\<lambda>n. fps_nth (fps_deriv F) ((n+1)^2 - 1) * q ^ ((n+1)^2 - 1)) sums 
                     eval_fps (fps_deriv F) q"
    by (subst sums_mono_reindex) (auto simp: F_def fps_jacobi_theta_nw_def bij_betw_def)
  also have "(\<lambda>n. fps_nth (fps_deriv F) ((n+1)^2 - 1) * q ^ ((n+1)^2 - 1)) = 
             (\<lambda>n. 2 * (of_nat n + 1)^2 * q ^ ((n+1)^2-1))"
    by (auto simp: F_def fps_jacobi_theta_nw_def add_ac)
  also have "(\<lambda>n::nat. (n+1) ^ 2 - 1) = (\<lambda>n. n * (n + 2))"
    by (simp add: algebra_simps power2_eq_square)
  finally have "a sums eval_fps (fps_deriv F) q"
    by (simp only: a_def)

  moreover have "(\<theta>\<^sub>3 has_field_derivative (eval_fps F' q)) (at q)"
  proof -
    have "ereal (norm q) < fps_conv_radius F"
      using q by (auto simp: one_ereal_def)
    hence "(eval_fps F has_field_derivative (eval_fps F' q)) (at q)"
      unfolding F'_def by (rule has_field_derivative_eval_fps)
    also have "?this \<longleftrightarrow> ?thesis"
    proof (intro DERIV_cong_ev)
      have "eventually (\<lambda>t. t \<in> ball 0 1) (nhds q)"
        by (rule eventually_nhds_in_open) (use q in auto)
      thus "eventually (\<lambda>t. eval_fps F t = \<theta>\<^sub>3 t) (nhds q)"
      proof eventually_elim
        case (elim t)
        thus ?case
          using sums_jacobi_theta_nw_00[of t] by (simp add: sums_iff eval_fps_def F_def)
      qed
    qed auto
    finally show ?thesis .
  qed

  ultimately show "summable a" "(\<theta>\<^sub>3 has_field_derivative (\<Sum>n. a n)) (at q)"
    by (simp_all add: sums_iff)
qed

lemma jacobi_theta_nw_10_le_00:
  assumes "q \<ge> (0::real)"
  shows   "\<theta>\<^sub>2 q \<le> \<theta>\<^sub>3 q"
proof (cases "q < 1")
  case True
  with assms have q: "q \<ge> 0" "q < 1"
    by auto
  define r where "r = sqrt q"
  have "0 \<le> \<theta>\<^sub>3 q"
    using has_sum_jacobi_theta_nw_00[of q] by (rule has_sum_nonneg) (use q in auto)
  have "(\<theta>\<^sub>3 q)\<^sup>2 - (\<theta>\<^sub>2 q)\<^sup>2 = (\<theta>\<^sub>4 r)\<^sup>2"
    using jacobi_theta_nw_00_minus_10_square_square_real[of r] q
    by (simp add: r_def)
  also have "\<dots> \<ge> 0"
    by simp
  finally have "(\<theta>\<^sub>3 q)\<^sup>2 \<ge> (\<theta>\<^sub>2 q)\<^sup>2"
    by simp
  thus "\<theta>\<^sub>3 q \<ge> \<theta>\<^sub>2 q"
    by (rule power2_le_imp_le) (fact \<open>\<theta>\<^sub>3 q \<ge> 0\<close>)
qed auto

lemma jacobi_theta_nw_00_pos:
  fixes q :: real
  assumes "q \<in> {-1<..<1}"
  shows   "\<theta>\<^sub>3 q > 0"
proof -
  have pos: "\<theta>\<^sub>3 q > 0" if "q \<in> {0..<1}" for q :: real
    using has_sum_0 has_sum_jacobi_theta_nw_00
  proof (rule has_sum_strict_mono)
    show "0 < q powi 0 ^ 2"
      by auto
  qed (use that in auto)

  have "\<theta>\<^sub>4 q > 0" if q: "q \<in> {0..<1}" for q :: real
  proof - 
    have eq: "\<theta>\<^sub>3 q * \<theta>\<^sub>4 q = (\<theta>\<^sub>4 (q ^ 2) ^ 2)"
      by (rule jacobi_theta_nw_00_times_01_real)
    have "\<theta>\<^sub>3 q * \<theta>\<^sub>4 q \<ge> 0"
      by (subst eq) auto
    with pos[of q] q have "\<theta>\<^sub>4 q \<ge> 0"
      by (simp add: zero_le_mult_iff)
  
    have zero_iff: "\<theta>\<^sub>4 q = 0 \<longleftrightarrow> \<theta>\<^sub>4 (q ^ 2) = 0" if "q \<in> {0..<1}" for q :: real
      using jacobi_theta_nw_00_times_01_real[of q] pos[of q] that by auto
  
    have "\<theta>\<^sub>4 q \<noteq> 0"
    proof
      assume "\<theta>\<^sub>4 q = 0"
      have "\<theta>\<^sub>4 (q ^ (2 ^ n)) = 0" for n
      proof (induction n)
        case (Suc n)
        have "\<theta>\<^sub>4 (q ^ (2 ^ Suc n)) = \<theta>\<^sub>4 ((q ^ (2 ^ n)) ^ 2)"
          by (simp flip: power_mult add: mult_ac)
        also have "\<dots> = 0 \<longleftrightarrow> \<theta>\<^sub>4 (q ^ (2 ^ n)) = 0"
          by (subst zero_iff [symmetric]) (use q in \<open>auto simp: power_less_one_iff\<close>)
        finally show ?case
          using Suc.IH by simp
      qed (use \<open>\<theta>\<^sub>4 q = 0\<close> in auto)
      hence "(\<lambda>n. \<theta>\<^sub>4 (q ^ (2 ^ n))) \<longlonglongrightarrow> 0"
        by simp
      moreover have "(\<lambda>n. \<theta>\<^sub>4 (q ^ (2 ^ n))) \<longlonglongrightarrow> \<theta>\<^sub>4 0"
      proof (rule continuous_on_tendsto_compose[of _ \<theta>\<^sub>4])
        show "continuous_on {0..<1::real} \<theta>\<^sub>4"
          by (intro continuous_intros) auto
        show "(\<lambda>n. q ^ (2 ^ n)) \<longlonglongrightarrow> 0"
        proof (cases "q = 0")
          case False
          thus ?thesis
            using q by real_asymp
        qed (auto simp: power_0_left)
      qed (use q in \<open>auto simp: power_less_one_iff\<close>)
      ultimately have "\<theta>\<^sub>4 (0::real) = 0"
        using LIMSEQ_unique by blast
      thus False
        by simp
    qed
    with \<open>\<theta>\<^sub>4 q \<ge> 0\<close> show "\<theta>\<^sub>4 q > 0"
      by simp
  qed
  from this[of "-q"] and pos[of q] show ?thesis
    using assms by (cases "q \<ge> 0") (auto simp: jacobi_theta_nw_01_conv_00)
qed

lemma jacobi_theta_nw_01_pos: "q \<in> {-1<..<1} \<Longrightarrow> \<theta>\<^sub>4 q > (0::real)"
  using jacobi_theta_nw_00_pos[of "-q"]
  by (simp add: jacobi_theta_nw_01_conv_00)

lemma jacobi_theta_nw_00_nonneg: "\<theta>\<^sub>3 q \<ge> (0::real)"
  using jacobi_theta_nw_00_pos[of q] by (cases "norm q < 1") (auto simp: abs_less_iff)

lemma jacobi_theta_nw_01_nonneg: "\<theta>\<^sub>4 q \<ge> (0::real)"
  by (simp add: jacobi_theta_nw_01_conv_00 jacobi_theta_nw_00_nonneg)

lemma strict_mono_jacobi_theta_nw_00: "strict_mono_on {-1<..<1::real} \<theta>\<^sub>3"
proof -
  have theta3_less: "\<theta>\<^sub>3 x < \<theta>\<^sub>3 y" if xy: "0 \<le> x" "x < y" "y < 1" for x y :: real
  proof (rule has_sum_strict_mono)
    show "((\<lambda>n. x powi n\<^sup>2) has_sum \<theta>\<^sub>3 x) UNIV" "((\<lambda>n. y powi n\<^sup>2) has_sum \<theta>\<^sub>3 y) UNIV"
      by (rule has_sum_jacobi_theta_nw_00; use xy in simp)+
    show "x powi (n^2) \<le> y powi (n^2)" for n :: int
      by (intro power_int_mono) (use xy in auto)
    show "x powi (1^2) < y powi (1^2)"
      using xy by auto
  qed auto    

  have theta4_less: "\<theta>\<^sub>4 x < \<theta>\<^sub>4 y" if xy: "0 \<le> y" "y < x" "x < 1" for x y :: real
  proof -
    include qpochhammer_inf_notation
    have "\<theta>\<^sub>4 x = jacobi_theta_nome (-1) x"
      by (simp add: jacobi_theta_nome_01_def)
    also have "\<dots> = (x\<^sup>2 ; x\<^sup>2)\<^sub>\<infinity> * ((x ; x\<^sup>2)\<^sub>\<infinity>) ^ 2"
      by (subst jacobi_theta_nome_triple_product_real) (use xy in \<open>simp_all add: power2_eq_square\<close>)
    also have "\<dots> < (x\<^sup>2 ; x\<^sup>2)\<^sub>\<infinity> * ((y ; y\<^sup>2)\<^sub>\<infinity>) ^ 2"
    proof (intro mult_strict_left_mono power_strict_mono)
      show "(x\<^sup>2 ; x\<^sup>2)\<^sub>\<infinity> > 0" "(x ; x\<^sup>2)\<^sub>\<infinity> \<ge> 0"
        using xy by (auto intro!: qpochhammer_inf_pos qpochhammer_inf_nonneg simp: power_less_one_iff)
    next
      show "(x ; x\<^sup>2)\<^sub>\<infinity> < (y ; y\<^sup>2)\<^sub>\<infinity>"
      proof (rule has_prod_less)
        show "(\<lambda>n. 1 - x * (x^2)^n) has_prod (x ; x\<^sup>2)\<^sub>\<infinity>"
             "(\<lambda>n. 1 - y * (y^2)^n) has_prod (y ; y\<^sup>2)\<^sub>\<infinity>"
          by (rule has_prod_qpochhammer_inf; use xy in \<open>simp add: power_less_one_iff\<close>)+
      next
        show "1 - x * (x^2)^0 < 1 - y * (y^2)^0"
          using xy by simp
      next
        fix n :: nat
        have "x * (x\<^sup>2)^n = x^(2*n+1)"
          by (simp add: power_mult power_add)
        also have "\<dots> < 1"
          by (subst power_less_one_iff) (use xy in auto)
        finally show "1 - x * (x\<^sup>2)^n > 0"
          by simp
      next
        fix n :: nat
        have "x^(2*n+1) \<ge> y^(2*n+1)"
          by (intro power_mono) (use xy in auto)
        thus "1 - x * (x\<^sup>2) ^ n \<le> 1 - y * (y\<^sup>2) ^ n"
          by (simp add: power_mult)
      qed      
    qed auto
    also have "\<dots> \<le> (y\<^sup>2 ; y\<^sup>2)\<^sub>\<infinity> * ((y ; y\<^sup>2)\<^sub>\<infinity>) ^ 2"
    proof (intro mult_right_mono zero_le_power)
      show "(y ; y\<^sup>2)\<^sub>\<infinity> \<ge> 0"
        by (intro qpochhammer_inf_nonneg) (use xy in \<open>auto simp: power_less_one_iff\<close>)
    next
      show "(x\<^sup>2 ; x\<^sup>2)\<^sub>\<infinity> \<le> (y\<^sup>2 ; y\<^sup>2)\<^sub>\<infinity>"
      proof (rule has_prod_le[OF _ _ conjI])
        show "(\<lambda>n. 1 - x\<^sup>2 * (x^2)^n) has_prod (x\<^sup>2 ; x\<^sup>2)\<^sub>\<infinity>"
             "(\<lambda>n. 1 - y\<^sup>2 * (y^2)^n) has_prod (y\<^sup>2 ; y\<^sup>2)\<^sub>\<infinity>"
          by (rule has_prod_qpochhammer_inf; use xy in \<open>simp add: power_less_one_iff\<close>)+
      next
        fix n :: nat
        have "x\<^sup>2 * (x\<^sup>2)^n = x^(2*n+2)"
          by (simp add: power_mult power_add power2_eq_square)
        also have "\<dots> \<le> 1"
          by (subst power_le_one_iff) (use xy in auto)
        finally show "1 - x\<^sup>2 * (x\<^sup>2)^n \<ge> 0"
          by simp
      next
        fix n :: nat
        have "x^(2*n+2) \<ge> y^(2*n+2)"
          by (intro power_mono) (use xy in auto)
        thus "1 - x\<^sup>2 * (x\<^sup>2) ^ n \<le> 1 - y\<^sup>2 * (y\<^sup>2) ^ n"
          by (simp add: power_mult power2_eq_square)
      qed
    qed
    also have "\<dots> = jacobi_theta_nome (-1) y"
      by (subst jacobi_theta_nome_triple_product_real) (use xy in \<open>simp_all add: power2_eq_square\<close>)
    also have "\<dots> = \<theta>\<^sub>4 y"
      by (simp add: jacobi_theta_nome_01_def)
    finally show "\<theta>\<^sub>4 x < \<theta>\<^sub>4 y" .
  qed

  show "strict_mono_on {-1<..<1::real} \<theta>\<^sub>3"
  proof (rule strict_mono_onI)
    fix x y :: real
    assume xy: "x \<in> {-1<..<1}" "y \<in> {-1<..<1}" "x < y"
    consider "x \<ge> 0" | "y \<le> 0" | "x < 0" "y > 0"
      using xy by linarith
    thus "\<theta>\<^sub>3 x < \<theta>\<^sub>3 y"
    proof cases
      assume "x \<ge> 0"
      thus ?thesis by (intro theta3_less) (use xy in auto)
    next
      assume "y \<le> 0"
      hence "\<theta>\<^sub>4 (-x) < \<theta>\<^sub>4 (-y)"
        by (intro theta4_less) (use xy in auto)
      thus ?thesis
        by (simp add: jacobi_theta_nw_01_conv_00)
    next
      assume xy': "x < 0" "y > 0"
      have "\<theta>\<^sub>4 (-x) < \<theta>\<^sub>4 0"
        by (rule theta4_less) (use xy xy' in auto)
      moreover have "\<theta>\<^sub>3 0 < \<theta>\<^sub>3 y"
        by (rule theta3_less) (use xy xy' in auto)
      ultimately show ?thesis
        by (simp add: jacobi_theta_nw_01_conv_00)
    qed
  qed
qed

lemma strict_antimono_jacobi_theta_nw_01: "strict_antimono_on {-1<..<1::real} \<theta>\<^sub>4"
  by (auto intro!: monotone_onI strict_mono_onD[OF strict_mono_jacobi_theta_nw_00] 
           simp: jacobi_theta_nw_01_conv_00)

lemma jacobi_theta_nw_10_nonneg:
  assumes "x \<ge> 0"
  shows   "\<theta>\<^sub>2 x \<ge> (0::real)"
proof -
  consider "x = 0" | "x \<ge> 1" | "x \<in> {0<..<1}"
    using assms by force
  thus ?thesis
  proof cases
    assume x: "x \<in> {0<..<1}"
    show ?thesis
      using has_sum_jacobi_theta_nw_10_real
      by (rule has_sum_nonneg) (use x in auto)
  qed auto
qed

lemma strict_mono_jacobi_theta_nw_10: "strict_mono_on {0::real..<1} \<theta>\<^sub>2"
proof (rule strict_mono_onI)
  fix x y :: real
  assume xy: "x \<in> {0..<1}" "y \<in> {0..<1}" "x < y"
  note mono_rules = strict_mono_jacobi_theta_nw_00 strict_antimono_jacobi_theta_nw_01

  have "\<theta>\<^sub>2 x ^ 4 = \<theta>\<^sub>3 x ^ 4 - \<theta>\<^sub>4 x ^ 4"
    by (subst jacobi_theta_nw_pow4_real [symmetric]) (use xy in auto)
  also have "\<dots> < \<theta>\<^sub>3 y ^ 4 - \<theta>\<^sub>4 y ^ 4"
    by (intro diff_strict_mono power_strict_mono mono_rules[THEN monotone_onD]
             jacobi_theta_nw_00_nonneg jacobi_theta_nw_01_nonneg)
       (use xy in auto)
  also have "\<dots> = \<theta>\<^sub>2 y ^ 4"
    by (subst jacobi_theta_nw_pow4_real [symmetric]) (use xy in auto)
  finally show "\<theta>\<^sub>2 x < \<theta>\<^sub>2 y"
    by (rule power_less_imp_less_base) (use xy in \<open>auto intro!: jacobi_theta_nw_10_nonneg\<close>)
qed

lemma jacobi_theta_nw_10_pos:
  assumes "x \<in> {0<..<1}"
  shows   "\<theta>\<^sub>2 x > (0::real)"
  using strict_mono_onD[OF strict_mono_jacobi_theta_nw_10, of 0 x] assms by simp

end