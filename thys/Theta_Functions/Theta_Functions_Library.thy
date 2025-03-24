theory Theta_Functions_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

subsection \<open>Infinite sums\<close>

(* TODO: notation for the "old" deprecated infinite sums; why is this even still active *)
no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)

lemma has_sum_iff: "(f has_sum S) A \<longleftrightarrow> f summable_on A \<and> infsum f A = S"
  using infsumI summable_iff_has_sum_infsum by blast

lemma summable_on_of_real:
  "f summable_on A \<Longrightarrow> (\<lambda>x. of_real (f x) :: 'a :: real_normed_algebra_1) summable_on A"
  using summable_on_bounded_linear[of "of_real :: real \<Rightarrow> 'a", OF bounded_linear_of_real, of f A]
  by simp

lemma has_sum_of_real_iff:
  "((\<lambda>x. of_real (f x) :: 'a :: real_normed_div_algebra) has_sum (of_real c)) A \<longleftrightarrow> 
   (f has_sum c) A"
proof -
  have "((\<lambda>x. of_real (f x) :: 'a) has_sum (of_real c)) A \<longleftrightarrow>
        (sum (\<lambda>x. of_real (f x) :: 'a) \<longlongrightarrow> of_real c) (finite_subsets_at_top A)"
    by (simp add: has_sum_def)
  also have "sum (\<lambda>x. of_real (f x) :: 'a) = (\<lambda>X. of_real (sum f X))"
    by simp
  also have "((\<lambda>X. of_real (sum f X) :: 'a) \<longlongrightarrow> of_real c) (finite_subsets_at_top A) \<longleftrightarrow> 
             (f has_sum c) A"
    unfolding has_sum_def tendsto_of_real_iff ..
  finally show ?thesis .
qed

lemma has_sum_of_real:
  "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. of_real (f x) :: 'a :: real_normed_algebra_1) has_sum of_real S) A"
  using has_sum_bounded_linear[of "of_real :: real \<Rightarrow> 'a", OF bounded_linear_of_real, of f A S]
  by simp

lemma has_sum_finite_iff: 
  fixes S :: "'a :: {topological_comm_monoid_add,t2_space}"
  assumes "finite A"
  shows   "(f has_sum S) A \<longleftrightarrow> S = (\<Sum>x\<in>A. f x)"
proof
  assume "S = (\<Sum>x\<in>A. f x)"
  thus "(f has_sum S) A"
    by (intro has_sum_finiteI assms)
next
  assume "(f has_sum S) A"
  moreover have "(f has_sum (\<Sum>x\<in>A. f x)) A"
    by (intro has_sum_finiteI assms) auto
  ultimately show "S = (\<Sum>x\<in>A. f x)"
    using has_sum_unique by blast
qed

lemma has_sum_finite_neutralI:
  assumes "finite B" "B \<subseteq> A" "\<And>x. x \<in> A - B \<Longrightarrow> f x = 0" "c = (\<Sum>x\<in>B. f x)"
  shows   "(f has_sum c) A"
proof -
  have "(f has_sum c) B"
    by (rule has_sum_finiteI) (use assms in auto)
  also have "?this \<longleftrightarrow> (f has_sum c) A"
    by (intro has_sum_cong_neutral) (use assms in auto)
  finally show ?thesis .
qed

lemma has_sum_strict_mono_neutral:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_ab_group_add, topological_ab_group_add, linorder_topology}"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  assumes \<open>x \<in> B\<close> \<open>if x \<in> A then f x < g x else 0 < g x\<close>
  shows "a < b"
proof -
  define y where "y = (if x \<in> A then f x else 0)"
  have "a - y \<le> b - g x"
  proof (rule has_sum_mono_neutral)
    show "(f has_sum (a - y)) (A - (if x \<in> A then {x} else {}))"
      by (intro has_sum_Diff assms has_sum_finiteI) (auto simp: y_def)
    show "(g has_sum (b - g x)) (B - {x})"
      by (intro has_sum_Diff assms has_sum_finiteI) (use assms in auto)
  qed (use assms in \<open>auto split: if_splits\<close>)
  moreover have "y < g x"
    using assms(3,4,5)[of x] assms(6-) by (auto simp: y_def split: if_splits)
  ultimately show ?thesis
    by (metis diff_strict_left_mono diff_strict_mono leD neqE)
qed

lemma has_sum_strict_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_ab_group_add, topological_ab_group_add, linorder_topology}"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>x \<in> A\<close> \<open>f x < g x\<close>
  shows "a < b"
  by (rule has_sum_strict_mono_neutral[OF assms(1,2), where x = x])
     (use assms(3-) in auto)

lemma has_sum_scaleR:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes "(f has_sum S) A"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_sum (c *\<^sub>R S)) A"
  using has_sum_bounded_linear[OF bounded_linear_scaleR_right[of c], of f A S] assms by simp

lemma has_sum_scaleR_iff:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_sum S) A \<longleftrightarrow> (f has_sum (S /\<^sub>R c)) A"
  using has_sum_scaleR[of f A "S /\<^sub>R c" c] has_sum_scaleR[of "\<lambda>x. c *\<^sub>R f x" A S "inverse c"] assms
  by auto

lemma summable_on_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows   "g summable_on S \<longleftrightarrow> h summable_on T"
  using has_sum_reindex_bij_witness[of S i j T h g, OF assms]
  by (simp add: summable_on_def)

lemma sums_nonneg_imp_has_sum_strong:
  assumes "f sums (S::real)" "eventually (\<lambda>n. f n \<ge> 0) sequentially"
  shows   "(f has_sum S) UNIV"
proof -
  from assms(2) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> f n \<ge> 0"
    by (auto simp: eventually_at_top_linorder)
  from assms(1) have "summable f"
    by (simp add: sums_iff)
  hence "summable (\<lambda>n. f (n + N))"
    by (rule summable_ignore_initial_segment)
  hence "summable (\<lambda>n. norm (f (n + N)))"
    using N by simp
  hence "summable (\<lambda>n. norm (f n))"
    using summable_iff_shift by blast
  with assms(1) show ?thesis
    using norm_summable_imp_has_sum by blast
qed

lemma sums_nonneg_imp_has_sum:
  assumes "f sums (S::real)" and "\<And>n. f n \<ge> 0"
  shows   "(f has_sum S) UNIV"
  by (rule sums_nonneg_imp_has_sum_strong) (use assms in auto)

lemma summable_nonneg_imp_summable_on_strong:
  assumes "summable f" "eventually (\<lambda>n. f n \<ge> (0::real)) sequentially"
  shows   "f summable_on UNIV"
  using sums_nonneg_imp_has_sum_strong[OF _ assms(2)] assms(1) has_sum_imp_summable by blast 

lemma summable_nonneg_imp_summable_on:
  assumes "summable f" "\<And>n. f n \<ge> (0::real)"
  shows   "f summable_on UNIV"
  by (rule summable_nonneg_imp_summable_on_strong) (use assms in auto)

lemma Weierstrass_m_test_general':
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: banach"
  fixes M :: "'a \<Rightarrow> real"
  assumes norm_le:  "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> norm (f x y) \<le> M x"
  assumes has_sum: "\<And>y. y \<in> Y \<Longrightarrow> ((\<lambda>x. f x y) has_sum S y) X"
  assumes summable: "M summable_on X"
  shows "uniform_limit Y (\<lambda>X y. \<Sum>x\<in>X. f x y) S (finite_subsets_at_top X)"
proof -
  have "uniform_limit Y (\<lambda>X y. \<Sum>x\<in>X. f x y) (\<lambda>y. \<Sum>\<^sub>\<infinity>x\<in>X. f x y) (finite_subsets_at_top X)"
    using norm_le summable by (rule Weierstrass_m_test_general)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro uniform_limit_cong refl always_eventually allI ballI)
       (use has_sum in \<open>auto simp: has_sum_iff\<close>)
  finally show ?thesis .
qed



subsection \<open>Miscellanea\<close>

(* some rules to simplify away annoying things like "1/2 \<in> \<int>" *)
lemma fraction_numeral_not_in_Ints [simp]:
  assumes "\<not>(numeral b :: int) dvd numeral a"
  shows   "numeral a / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" "numeral a", where ?'a = 'a] assms by simp

lemma fraction_numeral_not_in_Ints' [simp]:
  assumes "b \<noteq> Num.One"
  shows   "1 / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" 1, where ?'a = 'a] assms by simp

lemmas [simp] = not_in_Ints_imp_not_in_nonpos_Ints minus_in_Ints_iff



lemma power_int_power: "(a ^ b :: 'a :: division_ring) powi c = a powi (int b * c)"
  by (subst power_int_mult) simp

lemma power_int_power': "(a powi b :: 'a :: division_ring) ^ c = a powi (b * int c)"
  by (simp add: power_int_mult)



lemma real_sqrt_abs': "sqrt (abs x) = abs (sqrt x)"
  by (metis real_sqrt_abs2 real_sqrt_mult)

lemma power_int_nonneg_exp: "n \<ge> 0 \<Longrightarrow> x powi n = x ^ nat n"
  by (simp add: power_int_def)

lemma sin_npi_complex' [simp]: "sin (of_nat n * of_real pi) = 0"
  by (metis of_real_0 of_real_mult of_real_of_nat_eq sin_npi sin_of_real)

lemma cos_npi_complex' [simp]: "cos (of_nat n * of_real pi) = (-1) ^ n" for n
proof -
  have "cos (of_nat n * of_real pi :: 'a) = of_real (cos (real n * pi))"
    by (subst cos_of_real [symmetric]) simp
  also have "cos (real n * pi) = (-1) ^ n"
    by simp
  finally show ?thesis by simp
qed

lemma cis_power_int: "cis x powi n = cis (of_int n * x)"
  by (auto simp: power_int_def Complex.DeMoivre)  

lemma complex_cnj_power_int [simp]: "cnj (x powi n) = cnj x powi n"
  by (auto simp: power_int_def)


lemma uniform_limit_singleton: "uniform_limit {x} f g F \<longleftrightarrow> ((\<lambda>n. f n x) \<longlongrightarrow> g x) F"
  by (simp add: uniform_limit_iff tendsto_iff)

lemma uniform_limit_compose':
  assumes "uniform_limit A f g F" and "h ` B \<subseteq> A"
  shows   "uniform_limit B (\<lambda>n x. f n (h x)) (\<lambda>x. g (h x)) F"
  unfolding uniform_limit_iff
proof safe
  fix e :: real
  assume e: "e > 0"
  from e and assms(1) have "\<forall>\<^sub>F n in F. \<forall>x\<in>A. dist (f n x) (g x) < e"
    by (auto simp: uniform_limit_iff)
  thus "\<forall>\<^sub>F n in F. \<forall>x\<in>B. dist (f n (h x)) (g (h x)) < e"
    by eventually_elim (use assms(2) in blast)
qed


lemma is_square_mult_prime_left_iff:
  assumes "prime p"
  shows   "is_square (p * x) \<longleftrightarrow> p dvd x \<and> is_square (x div p)"
proof
  assume *: "p dvd x \<and> is_square (x div p)"
  have [simp]: "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "x = y ^ 2 * p"
    by (auto elim!: dvdE is_nth_powerE simp: mult_ac)
  have "is_square ((p * y) ^ 2)"
    by auto
  also have "(p * y) ^ 2 = p * x"
    by (simp add: y power2_eq_square algebra_simps)
  finally show "is_square (p * x)" .
next
  assume *: "is_square (p * x)"
  have "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "p * x = y ^ 2"
    by (elim is_nth_powerE)
  have "p dvd y ^ 2"
    by (simp flip: y)
  hence "p dvd y"
    using \<open>prime p\<close> using prime_dvd_power by blast
  then obtain z where z: "y = p * z "
    by (elim dvdE)
  have "p * x = p * (p * z ^ 2)"
    by (simp add: y z algebra_simps power2_eq_square)
  hence x_eq: "x = p * z ^ 2"
    using \<open>p \<noteq> 0\<close> by simp
  show "p dvd x \<and> is_square (x div p)"
    using \<open>p \<noteq> 0\<close> by (simp add: x_eq)
qed

lemma is_square_mult2_nat_iff:
  "is_square (2 * b :: nat) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_square_mult2_int_iff:
  "is_square (2 * b :: int) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_nth_power_mult_cancel_left:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n a" "a \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n b"
proof (cases "n > 0")
  case True
  show ?thesis
  proof
    assume "is_nth_power n (a * b)"
    then obtain x where x: "a * b = x ^ n"
      by (elim is_nth_powerE)
    obtain y where y: "a = y ^ n"
      using assms by (elim is_nth_powerE)
    have "y ^ n dvd x ^ n"
      by (simp flip: x y)
    hence "y dvd x"
      using \<open>n > 0\<close> by simp
    then obtain z where z: "x = y * z"
      by (elim dvdE)
    have "x ^ n = y ^ n * z ^ n"
      by (simp add: z power_mult_distrib)
    hence "b = z ^ n"
      using \<open>a \<noteq> 0\<close> by (simp flip: x y)
    thus "is_nth_power n b"
      by auto
  qed (use assms in \<open>auto intro: is_nth_power_mult\<close>)
qed (use assms in auto)

lemma is_nth_power_mult_cancel_right:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n b" "b \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n a"
  by (subst mult.commute, subst is_nth_power_mult_cancel_left) (use assms in auto)

end