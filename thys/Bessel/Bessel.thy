(*
  File:     Bessel.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Bessel functions\<close>
theory Bessel
  imports "Incomplete_Gamma.Incomplete_Gamma"
begin

subsection \<open>Auxiliary material\<close>

(* TODO: Move to HOL-Analysis.Gamma_Function *)
lemma rGamma_real_nonneg [simp]:
  assumes "x \<ge> (0::real)"
  shows   "rGamma x \<ge> 0"
  using Gamma_real_pos[of x] assms by (cases "x = 0") (auto simp: rGamma_inverse_Gamma)

(* TODO: Move to HOL.Transcendental, near the definition of sinh, probably *)
lemma sinh_of_real: "sinh (of_real x :: 'a :: {real_normed_field, banach}) = of_real (sinh x)"
  by (simp add: sinh_def scaleR_conv_of_real flip: exp_of_real)

(* TODO: Move to HOL.Transcendental, near the definition of cosh, probably *)
lemma cosh_of_real: "cosh (of_real x :: 'a :: {real_normed_field, banach}) = of_real (cosh x)"
  by (simp add: cosh_def scaleR_conv_of_real flip: exp_of_real)

(* TODO: move to HOL-Library.Nonpos_Ints *)
lemma plus_of_nat_in_nonpos_IntsD:
  assumes "x + of_nat n \<in> \<int>\<^sub>\<le>\<^sub>0"
  shows   "x \<in> \<int>\<^sub>\<le>\<^sub>0"
proof -
  from assms obtain k where "k \<le> 0" "x + of_nat n = of_int k"
    by (elim nonpos_Ints_cases) auto
  hence "x = of_int (k - int n)" "k - int n \<le> 0"
    by (auto simp: algebra_simps)
  thus ?thesis
    using nonpos_Ints_of_int by blast
qed

(* TODO: move to HOL-Library.Nonpos_Ints *)
lemma plus_of_nat_notin_nonpos_Ints:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "x + of_nat n \<notin> \<int>\<^sub>\<le>\<^sub>0"
  using assms plus_of_nat_in_nonpos_IntsD by blast

(* TODO: move to HOL-Library.Nonpos_Ints *)
lemma plus1_notin_nonpos_Ints:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "x + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  using plus_of_nat_notin_nonpos_Ints[OF assms, of 1] by simp

(* TODO: move to HOL-Library.Nonpos_ints *)
lemma plus_numeral_notin_nonpos_Ints:
  assumes "x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "x + numeral n \<notin> \<int>\<^sub>\<le>\<^sub>0"
  using plus_of_nat_notin_nonpos_Ints[OF assms, of "numeral n"] by simp


subsection \<open>Hyperbolic sine and cosine as formal power series\<close>

(* TODO Move to HOL-Computational_Algebra.Formal_Power_Series *)
definition fps_sinh :: "'a :: {inverse, ring_1} \<Rightarrow> 'a fps" where
  "fps_sinh c = fps_const (1/2) * (fps_exp c - fps_exp (-c))"

(* TODO Move to HOL-Computational_Algebra.Formal_Power_Series *)
definition fps_cosh :: "'a :: {inverse, ring_1} \<Rightarrow> 'a fps" where
  "fps_cosh c = fps_const (1/2) * (fps_exp c + fps_exp (-c))"

(* TODO Move to HOL-Computational_Algebra.Formal_Power_Series *)
lemma fps_nth_cosh: 
  fixes c :: "'a :: field_char_0"
  shows "fps_nth (fps_cosh c) n = (if even n then c ^ n / of_nat (fact n) else 0)"
  by (auto simp: fps_cosh_def)

(* TODO: Move to HOL-Analysis.FPS_Convergence *)
lemma has_fps_expansion_sinh [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "(\<lambda>x. sinh (c * x)) has_fps_expansion fps_sinh c"
proof -
  have "(\<lambda>x. (1/2) * (exp (c*x) - exp ((-c) * x))) has_fps_expansion fps_sinh c"
    unfolding sinh_def fps_sinh_def by (intro fps_expansion_intros)
  thus ?thesis
    by (simp add: sinh_def scaleR_conv_of_real)
qed

(* TODO: Move to HOL-Analysis.FPS_Convergence *)
lemma has_fps_expansion_sinh' [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. sinh x) has_fps_expansion fps_sinh 1"
  using has_fps_expansion_sinh[of 1] by simp

(* TODO: Move to HOL-Analysis.FPS_Convergence *)
lemma has_fps_expansion_cosh [fps_expansion_intros]:
  fixes c :: "'a :: {banach, real_normed_field, field_char_0}"
  shows "(\<lambda>x. cosh (c * x)) has_fps_expansion fps_cosh c"
proof -
  have "(\<lambda>x. (1/2) * (exp (c*x) + exp ((-c) * x))) has_fps_expansion fps_cosh c"
    unfolding cosh_def fps_cosh_def by (intro fps_expansion_intros)
  thus ?thesis
    by (simp add: cosh_def scaleR_conv_of_real)
qed

(* TODO: Move to HOL-Analysis.FPS_Convergence *)
lemma has_fps_expansion_cosh' [fps_expansion_intros]:
  "(\<lambda>x::'a :: {banach, real_normed_field}. cosh x) has_fps_expansion fps_cosh 1"
  using has_fps_expansion_cosh[of 1] by simp


subsection \<open>The cardinal hyperbolic sine\<close>

(* TODO: Move\<dots> somewhere? HOL-Analysis maybe? Or maybe just leave it here I guess. *)
definition sinch :: "'a \<Rightarrow> 'a :: {banach, real_normed_field, field_char_0}" where
  "sinch z = hypergeo_F [] [3 / 2] (z\<^sup>2 / 4)"

lemma sinch_altdef: "sinch z = (if z = 0 then 1 else sinh z / z)"
  using sinh_conv_hypergeo_F[of z] by (auto simp: sinch_def)

lemma sinch_0 [simp]: "sinch 0 = 1"
  by (simp add: sinch_altdef)

lemma sinch_of_real: "sinch (of_real x) = of_real (sinch x)"
  by (simp add: sinch_def of_real_hypergeo_F)

lemma sums_sinch': "(\<lambda>n. x ^ (2*n) / fact (2 * n + 1)) sums sinch x"
proof -
  have "(3 / 2 :: 'a) \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by auto
  thus ?thesis
    using sums_hypergeo_F[of "[3/2]" "[]" "x\<^sup>2 / 4"]
    by (simp add: sinch_def fps_hypergeo_nth pochhammer_three_halves 
                  power_divide power_mult fact_reduce[of "2 * _ + 1"] add_ac)
qed

lemma sums_sinch: "(\<lambda>n. if even n then x ^ n / fact (n+1) else 0) sums sinch x"
proof -
  have "(\<lambda>n. x ^ (2*n) / fact (2 * n + 1)) sums sinch x"
    by (rule sums_sinch')
  also have "?this \<longleftrightarrow> (\<lambda>n. if even n then x ^ n / fact (n+1) else 0) sums sinch x"
    by (subst (2) sums_mono_reindex[of "\<lambda>n. 2 * n", symmetric]) (auto intro!: strict_monoI)
  finally show ?thesis .
qed

lemma has_field_derivative_sinch:
  assumes "x \<noteq> 0"
  shows   "(sinch has_field_derivative (cosh x / x - sinh x / x ^ 2)) (at x within A)"
proof -
  have "((\<lambda>x. sinh x / x) has_field_derivative (cosh x / x - sinh x / x ^ 2)) (at x within A)"
    using assms by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps)
  also have "?this \<longleftrightarrow> (sinch has_field_derivative (cosh x / x - sinh x / x ^ 2)) (at x within A)"
  proof (rule has_field_derivative_cong_eventually)
    have "eventually (\<lambda>x. x \<noteq> 0) (at x within A)"
      by (rule eventually_neq_at_within)
    thus "eventually (\<lambda>x. sinh x / x = sinch x) (at x within A)"
      by eventually_elim (auto simp: sinch_altdef)
  qed (use assms in \<open>auto simp: sinch_altdef\<close>)
  finally show ?thesis .
qed  

lemma analytic_on_sinch [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>z. sinch (f z)) analytic_on A"
  unfolding sinch_def
proof (intro analytic_intros)
  show "set [3 / 2 :: complex] \<inter> \<int>\<^sub>\<le>\<^sub>0 = {}"
    by auto
qed auto

lemma holomorphic_on_sinch [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. sinch (f z)) holomorphic_on A"
  unfolding sinch_def
proof (intro holomorphic_intros)
  show "set [3 / 2 :: complex] \<inter> \<int>\<^sub>\<le>\<^sub>0 = {}"
    by auto
qed auto

lemma continuous_on_sinch [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>z. sinch (f z))"
  unfolding sinch_def
proof (intro continuous_intros)
  show "set [3 / 2 :: 'b] \<inter> \<int>\<^sub>\<le>\<^sub>0 = {}"
    by auto
qed auto

lemma subdegree_fps_sinh [simp]: "(c :: 'a :: field_char_0) \<noteq> 0 \<Longrightarrow> subdegree (fps_sinh c) = 1"
  by (rule subdegreeI) (auto simp: fps_sinh_def)

lemma has_fps_expansion_sinch [fps_expansion_intros]:
  assumes [simp]: "c \<noteq> 0"
  shows   "(\<lambda>z. sinch (c * z)) has_fps_expansion fps_sinh c / (fps_const c * fps_X)"
proof -
  have [simp]: "fps_nth (fps_sinh c) (Suc 0) = c"
    by (simp add: fps_sinh_def)
  have "(\<lambda>x. if x = 0 then 1 else sinh (c * x) / (c * x)) has_fps_expansion 
          fps_sinh c / (fps_const c * fps_X)"
    by (intro has_fps_expansion_divide fps_expansion_intros) auto
  thus ?thesis
    unfolding sinch_altdef by simp
qed

lemma has_fps_expansion_sinch' [fps_expansion_intros]:
  "sinch has_fps_expansion fps_sinh 1 / fps_X"
  using has_fps_expansion_sinch[of 1] by simp

lemma has_laurent_expansion_sinch [laurent_expansion_intros]:
  assumes [simp]: "c \<noteq> 0"
  shows "(\<lambda>z. sinch (c * z)) has_laurent_expansion fps_to_fls (fps_sinh c) / (fls_const c * fls_X)"
proof -
  have "(\<lambda>z. sinh (c * z) / (c * z)) has_laurent_expansion 
          fps_to_fls (fps_sinh c) / (fls_const c * fls_X)"
    by (intro laurent_expansion_intros has_laurent_expansion_fps fps_expansion_intros)
  also have "?this \<longleftrightarrow> (\<lambda>z. sinch (c * z)) 
                has_laurent_expansion (fps_to_fls (fps_sinh c) / (fls_const c * fls_X))"
  proof (rule has_laurent_expansion_cong)
    have "eventually (\<lambda>x. x \<noteq> (0::complex)) (at 0)"
      by (rule eventually_neq_at_within)
    thus "eventually (\<lambda>z. sinh (c * z) / (c * z) = sinch (c * z)) (at 0)"
      by eventually_elim (auto simp: sinch_altdef)
  qed auto
  finally show ?thesis
    by simp
qed

lemma has_laurent_expansion_sinch' [laurent_expansion_intros]:
  "sinch has_laurent_expansion fps_to_fls (fps_sinh 1) / fls_X"
  using has_laurent_expansion_sinch[of 1] by simp


subsection \<open>Bessel polynomials\<close>

text \<open>
  The Bessel polynomials $y_n(X)$ are defined by the following recurrence:
  \begin{align*}
  y_0(X) &= 1\\
  y_1(X) &= 1 + X\\
  y_n(X) &= (2n-1)X y_{n-1}(X) + y_{n-2}(X)
  \intertext{Later, we will additionally show the following alternative recurrence:}
  y_n(X) &= (1 + n X) y_{n-1}(X) + X^2 y_{n-1}'(X)
  \end{align*}
\<close>

fun bessel_poly :: "nat \<Rightarrow> 'a :: semidom poly" where
  "bessel_poly 0 = 1"
| "bessel_poly (Suc 0) = [:1, 1:]"
| "bessel_poly (Suc (Suc n)) = monom (of_nat (2*n+3)) 1 * bessel_poly (Suc n) + bessel_poly n"

lemma coeff_bessel_poly_eq_0_aux:
  "m > n \<Longrightarrow> coeff (bessel_poly n) m = 0"
  by (induction n arbitrary: m rule: bessel_poly.induct)
     (simp_all add: monom_altdef coeff_pCons split: nat.splits)

lemma bessel_poly_conv_bessel_poly_of_nat:
  "bessel_poly n = map_poly of_nat (bessel_poly n)"
proof (induction n rule: bessel_poly.induct)
  case (3 n)
  thus ?case
    by (auto simp: poly_eq_iff monom_altdef coeff_pCons coeff_map_poly split: nat.splits)
qed (auto simp: map_poly_pCons)

text \<open>
  Their coefficients (\oeiscite{A001498} on OEIS) have the following closed form:
    \[[X^m]y_m(X) = \frac{(n+m)!}{2^m m! (n-m)!}\]
\<close>
lemma coeff_bessel_poly_conv_fact_aux1:
  "m \<le> n \<Longrightarrow> real (coeff (bessel_poly n) m) = fact (n+m) / (fact m * fact (n-m) * 2^m)"
proof (induction n  arbitrary: m rule: bessel_poly.induct)
  case (3 n m)
  consider "m = 0" | "m \<in> {0<..n}" | "m = Suc n" | "m = Suc (Suc n)"
    using "3.prems" by force
  thus ?case
  proof cases
    assume "m = 0"
    thus ?thesis
      by (induction n rule: bessel_poly.induct)
         (simp_all add: monom_altdef coeff_pCons)
  next
    assume m_eq: "m = Suc (Suc n)"
    hence "m > Suc n"
      by auto
    have "real (coeff (bessel_poly (Suc (Suc n))) m) = fact (2 * n + 3) / (fact (n + 1)* 2 ^ Suc n)"
      using "3.prems" 
      by (simp add: monom_altdef "3.IH" m_eq coeff_bessel_poly_eq_0_aux fact_reduce flip: mult_2)
    also have "\<dots> = fact (Suc (Suc n) + m) / (fact m * fact (Suc (Suc n) - m) * 2^m)"
      unfolding m_eq
      apply (simp del: fact_Suc add: add_ac eval_nat_numeral)
      apply (simp add: divide_simps)?
      done
    finally show ?case .
  next
    assume m_eq: "m = Suc n"
    hence "m > n"
      by auto
    have "real (coeff (bessel_poly (Suc (Suc n))) m) = 
            (2 * real n + 3) * (2 * real n + 1) * fact (2 * n) / (fact n * 2 ^ n)"
      using "3.prems" 
      by (simp add: monom_altdef "3.IH" m_eq coeff_bessel_poly_eq_0_aux flip: mult_2)
    also have "\<dots> = fact (Suc (Suc n) + m) / (fact m * fact (Suc (Suc n) - m) * 2^m)"
      apply (simp del: fact_Suc add: add_ac eval_nat_numeral m_eq)
      apply (simp add: divide_simps flip: mult_2)?
      done
    finally show ?case .
  next
    assume m: "m \<in> {0<..n}"
    define k where "k = m - 1"
    have m_eq: "m = Suc k" and k: "k < n"
      using m by (auto simp: k_def)
    define D where "D = fact (n + k) / (fact (Suc k) * fact (Suc n - k) * 2 ^ Suc k :: real)"
    have "real (coeff (bessel_poly (Suc (Suc n))) m) = 
            (2 * real n + 3) * (1 + real n + real k) * fact (n + k) / 
               (fact k * fact (Suc n - k) * 2 ^ k) +
            (1 + real n + real k) * fact (n + k) /
               (fact (Suc k) * fact (n - Suc k) * 2 ^ Suc k)"
      unfolding m_eq using k by (simp add: "3.IH" monom_altdef mult_ac add_ac)
    also have "(2 * real n + 3) * (1 + real n + real k) * fact (n + k) / 
                 (fact k * fact (Suc n - k) * 2 ^ k) =
               2 * (real k + 1) * (2 * real n + 3) * (1 + real n + real k) * D"
      by (simp add: divide_simps D_def)
    also have "(1 + real n + real k) * fact (n + k) /
                 (fact (Suc k) * fact (n - Suc k) * 2 ^ Suc k) =
               (1 + real n + real k) * (real n - real k + 1) * (real n - real k) * (fact (n + k) /
                 (fact (Suc k) * fact (Suc (Suc (n - Suc k))) * 2 ^ Suc k))"
      using k unfolding fact_Suc by (simp add: divide_simps)
    also have "Suc (Suc (n - Suc k)) = Suc n - k"
      using k by (simp add: Suc_diff_le)
    also have "fact (n + k) / (fact (Suc k) * fact \<dots> * 2 ^ Suc k) = D"
      by (simp add: D_def)
    also have "2 * (real k + 1) * (2 * real n + 3) * (1 + real n + real k) * D +
               (1 + real n + real k) * (real n - real k + 1) * (real n - real k) * D =
               (real n + real k + 1) * (real n + real k + 2) * (real n + real k + 3) * D"
      by Groebner_Basis.algebra
    also have "\<dots> = fact (n + k + 3) / (fact (Suc k) * fact (Suc (Suc (n - Suc k))) * 2 ^ Suc k)"
      using k by (simp add: D_def fact_reduce divide_simps add_ac Suc_diff_le)
    also have "\<dots> = fact (Suc (Suc n) + m) / (fact m * fact (Suc (Suc n) - m) * 2 ^ m)"
      using k by (simp add: m_eq divide_simps Suc_diff_le eval_nat_numeral Suc_diff_Suc del: fact_Suc)
    finally show ?case .
  qed
qed (auto simp: coeff_pCons split: nat.splits)   

lemma degree_bessel_poly: "degree (bessel_poly n :: 'a :: {semidom, semiring_char_0} poly) = n"
proof -
  have "coeff (bessel_poly n) n \<noteq> (0::'a)"
  proof -
    have "coeff (bessel_poly n) n = (of_nat (coeff (bessel_poly n) n) :: 'a)"
      by (subst bessel_poly_conv_bessel_poly_of_nat) (simp_all add: coeff_map_poly)
    moreover have "real (coeff (bessel_poly n) n) \<noteq> 0"
      by (subst coeff_bessel_poly_conv_fact_aux1) auto
    hence "coeff (bessel_poly n) n \<noteq> (0 :: nat)"
      by auto
    ultimately show ?thesis
      by auto
  qed
  moreover have "coeff (bessel_poly n) m = (0 :: 'a)" if "m > n" for m
    using that by (simp add: coeff_bessel_poly_eq_0_aux)
  ultimately show ?thesis
    by (meson coeff_eq_0 less_degree_imp nat_neq_iff)
qed


text \<open>
  The coefficients of the Bessel polynomials also satisfy the following recurrence:
\<close>
fun bessel_poly_coeff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bessel_poly_coeff n 0 = 1"
| "bessel_poly_coeff 0 (Suc m) = 0"
| "bessel_poly_coeff (Suc n) (Suc m) = bessel_poly_coeff n (Suc m) + (n + m + 1) * bessel_poly_coeff n m"

lemma bessel_poly_coeff_eq_0 [simp]: "m > n \<Longrightarrow> bessel_poly_coeff n m = 0"
  by (induction n m rule: bessel_poly_coeff.induct) auto

lemma bessel_poly_coeff_pos: "m \<le> n \<Longrightarrow> bessel_poly_coeff n m > 0"
  by (induction n m rule: bessel_poly_coeff.induct) auto

lemma bessel_poly_coeff_eq_0_iff: "bessel_poly_coeff n m = 0 \<longleftrightarrow> m > n"
  using bessel_poly_coeff_eq_0 bessel_poly_coeff_pos by (metis linorder_not_le order_less_irrefl)

lemma bessel_poly_coeff_0_left: "m > 0 \<Longrightarrow> bessel_poly_coeff 0 m = 0"
  by (cases m) auto

lemma bessel_poly_coeff_conv_fact_aux2:
  "m \<le> n \<Longrightarrow> real (bessel_poly_coeff n m) = fact (n+m) / (fact m * fact (n-m) * 2^m)"
proof (induction n m rule: bessel_poly_coeff.induct)
  case (3 n m)
  show ?case
  proof (cases "n = m")
    case True
    hence "real (bessel_poly_coeff (Suc n) (Suc m)) = fact (2*m+1) / (fact m * 2 ^ m)"
      by (simp add: add_divide_distrib ring_distribs "3.IH"[unfolded True] flip: mult_2)
    also have "\<dots> = fact (Suc n + Suc m) / (fact (Suc m) * fact (Suc n - Suc m) * 2 ^ Suc m)"
      by (simp add: divide_simps True flip: mult_2)
    finally show ?thesis .
  next
    case False
    hence "m < n"
      using "3.prems" by simp
    hence "real (bessel_poly_coeff (Suc n) (Suc m)) =
             fact (n + m + 1) / (fact (Suc m) * fact (n - Suc m) * 2 ^ Suc m) +
             fact (n + m) / (fact m * fact (n - m) * 2 ^ m) +
             fact (n + m) * (n + m) / (fact m * fact (n - m) * 2 ^ m)"
      by (simp add: "3.IH")
    also have "fact (n + m + 1) = fact (n + m) * real (n + m + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> / (fact (Suc m) * fact (n - Suc m) * 2 ^ Suc m) =
               fact (n + m) * (n + m + 1) * (n - m) / (fact (Suc m) * fact (Suc (n - Suc m)) * 2 ^ Suc m)"
      unfolding fact_Suc
      using \<open>m < n\<close> apply (simp add: divide_simps del: of_nat_Suc)
      apply (simp add: algebra_simps)
      done
    also have "Suc (n - Suc m) = n - m"
      using \<open>m < n\<close> by simp
    also have "fact (n + m) / (fact m * fact (n - m) * 2 ^ m) = 
               2 * (m + 1) * fact (n + m) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m)"
      apply (simp add: divide_simps del: of_nat_Suc)
      apply (simp add: algebra_simps)?
      done
    also have "fact (n + m) * (n + m) / (fact m * fact (n - m) * 2 ^ m) = 
               2 * fact (n + m) * (m + 1) * (n + m) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m)"
      apply (simp add: divide_simps del: of_nat_Suc)
      apply (simp add: algebra_simps)?
      done
    also have "fact (n + m) * (n + m + 1) * (n - m) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m) +
               2 * (m + 1) * fact (n + m) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m) + 
               2 * fact (n + m) * (m + 1) * (n + m) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m) =
               (fact (n + m) * (n + m + 1) * (n - m) + 2 * (m + 1) * fact (n + m) + 
                   2 * fact (n + m) * (m + 1) * (n + m)) / 
                 (fact (Suc m) * fact (n - m) * 2 ^ Suc m)"
      by (simp only: add_divide_distrib mult_ac of_nat_mult of_nat_add)
    also have "(fact (n + m) * (n + m + 1) * (n - m) + 2 * (m + 1) * fact (n + m) + 
                   2 * fact (n + m) * (m + 1) * (n + m)) =
               fact (n + m) * real ((n + m + 1) * (n - m) + 2 * (m + 1) * (n + m + 1))"
      unfolding of_nat_mult of_nat_add ring_distribs of_nat_numeral of_nat_1 of_nat_fact
      by Groebner_Basis.algebra
    also have "real ((n + m + 1) * (n - m) + 2 * (m + 1) * (n + m + 1)) = (m + n + 1) * (m + n + 2)"
      using \<open>m < n\<close> unfolding of_nat_mult of_nat_add by (simp add: algebra_simps)
    also have "fact (n + m) * real ((m + n + 1) * (m + n + 2)) / (fact (Suc m) * fact (n - m) * 2 ^ Suc m) =
                 fact (Suc n + Suc m) / (fact (Suc m) * fact (Suc n - Suc m) * 2 ^ Suc m)"
      apply (simp add: divide_simps del: of_nat_Suc)
      apply (simp add: algebra_simps)?
      done
    finally show ?thesis .
  qed
qed auto

lemma bessel_poly_coeff_conv_fact:
  assumes "m \<le> n"
  shows   "bessel_poly_coeff n m = fact (n+m) div (fact m * fact (n-m) * 2^m)"
proof -
  have "real (fact m * fact (n-m) * 2^m * bessel_poly_coeff n m) = real (fact (n + m))"
    unfolding of_nat_mult by (subst bessel_poly_coeff_conv_fact_aux2) (use assms in auto)
  hence *: "fact m * fact (n-m) * 2^m * bessel_poly_coeff n m = fact (n + m)"
    by (simp only: of_nat_eq_iff)
  show ?thesis
    by (subst * [symmetric]) simp_all
qed

lemma bessel_poly_coeff_conv_fact':
  "bessel_poly_coeff n m = (if m \<le> n then fact (n+m) div (fact m * fact (n-m) * 2^m) else 0)"
  using bessel_poly_coeff_conv_fact[of m n] by auto

lemma coeff_bessel_poly: "coeff (bessel_poly n) m = of_nat (bessel_poly_coeff n m)"
proof -
  have "coeff (bessel_poly n) m = (of_nat (coeff (bessel_poly n) m) :: 'a)"
    by (subst bessel_poly_conv_bessel_poly_of_nat) (simp_all add: coeff_map_poly)
  also have "coeff (bessel_poly n) m = bessel_poly_coeff n m"
  proof (cases "m \<le> n")
    case True
    show ?thesis
      using coeff_bessel_poly_conv_fact_aux1[OF True] bessel_poly_coeff_conv_fact_aux2[OF True]
      by simp
  qed (simp_all add: coeff_bessel_poly_eq_0_aux)
  finally show ?thesis .
qed

text \<open>
  The Bessel polynomials also satisfy the following recurrence with respect to their derivative:
  \[y_n(X) = (1 + nX) y_{n-1}(X) + X^2 y_{n-1}'(X)\]
\<close>
lemma bessel_poly_Suc_conv_pderiv:
  "bessel_poly (Suc n) = [:1, of_nat n + 1:] * bessel_poly n + [:0,0,1:] * pderiv (bessel_poly n)"
  by (rule poly_eqI)
     (auto simp: coeff_bessel_poly coeff_pCons algebra_simps coeff_pderiv split: nat.splits)



subsection \<open>Spherical Bessel and Hankel functions\<close>


subsubsection \<open>The spherical Bessel function of the first kind\<close>

text \<open>
  The spherical Bessel functions of the first kind $j_n(z)$ are defined by letting
  $j_0(z) = \sin z / z$ and $j_{-1} = \cos z / z$ and then extending the definition to
  all integers $n$ via the following recurrence:
  \[(2n+1) j_n(z) = z (j_{n+1}(z) + j_{n-1}(z))\]
\<close>

function SBessel_J :: "int \<Rightarrow> 'a :: {banach, real_normed_field} \<Rightarrow> 'a" where
  "SBessel_J 0 = (\<lambda>z. sin z / z)"
| "SBessel_J (-1) = (\<lambda>z. cos z / z)"
| "n > 0 \<Longrightarrow> SBessel_J n = (\<lambda>z. (2 * of_int n - 1) / z * SBessel_J (n-1) z - SBessel_J (n-2) z)"
| "n < -1 \<Longrightarrow> SBessel_J n = (\<lambda>z. (2 * of_int n + 3) / z * SBessel_J (n+1) z - SBessel_J (n+2) z)"
  by force+
termination 
  by (relation "Wellfounded.measure (\<lambda>n. nat (abs (2 * n + 1)))") (auto simp: abs_if)

lemmas [simp del] = SBessel_J.simps(3,4)

lemma SBessel_J_induct:
  "P 0 \<Longrightarrow> P (-1) \<Longrightarrow> 
    (\<And>n. 0 < n \<Longrightarrow> (P (n - 1)) \<Longrightarrow> (P (n - 2)) \<Longrightarrow> P n) \<Longrightarrow>
    (\<And>n. n < - 1 \<Longrightarrow> (P (n + 1)) \<Longrightarrow> (P (n + 2)) \<Longrightarrow> P n) \<Longrightarrow>
  P (n :: int)"
  by (induction n rule: SBessel_J.induct; metis)

lemma SBessel_J_0_right [simp]: "SBessel_J n 0 = 0"
  by (induction n rule: SBessel_J_induct) (auto simp: SBessel_J.simps)

lemma SBessel_J_of_real: "SBessel_J n (of_real x) = of_real (SBessel_J n x)"
  by (induction n rule: SBessel_J_induct) (simp_all add: SBessel_J.simps sin_of_real cos_of_real)

lemma SBessel_J_minus_right: "SBessel_J n (-z) = (-1) powi n * SBessel_J n z"
  by (induction n rule: SBessel_J_induct)
     (auto simp: power_int_minus_left SBessel_J.simps)

lemma SBessel_J_contiguous:
  assumes "z \<noteq> 0"
  shows   "(2 * of_int n + 1) * SBessel_J n z = z * (SBessel_J (n+1) z + SBessel_J (n-1) z)"
proof (cases n rule: SBessel_J.cases)
  case 1
  thus ?thesis using assms
    by (simp add: SBessel_J.simps field_simps)
next
  case 2
  thus ?thesis using assms
    by (simp add: SBessel_J.simps field_simps)
next
  case (3 n)
  thus ?thesis using assms
    by (simp add: SBessel_J.simps field_simps)
next
  case (4 n)
  thus ?thesis using assms
    by (simp add: SBessel_J.simps field_simps)
qed


subsubsection \<open>The spherical Bessel function of the second kind\<close>

text \<open>
  For convenience, we also define the closely related spherical Bessel functions of the 
  second kind $y_n(z)$. They satisfy the same recurrence, but with the initial conditions
  $y_0(z) = -\cos z / z$ and $y_{-1}(z) = \sin z / z$. They can easily be expressed in terms of
  $j_n(z)$ and vice versa.
\<close>
definition SBessel_Y :: "int \<Rightarrow> 'a :: {real_normed_field,banach} \<Rightarrow> 'a"
  where "SBessel_Y n z = (-1) powi (n+1) * SBessel_J (-n-1) z"

lemma SBessel_Y_0_right [simp]: "SBessel_Y n 0 = 0"
  by (simp add: SBessel_Y_def)

lemma SBessel_Y_conv_J: "SBessel_Y n z = (-1) powi (n+1) * SBessel_J (-n-1) z"
  unfolding SBessel_Y_def ..

lemma SBessel_J_conv_Y: "SBessel_J n z = (-1) powi n * SBessel_Y (-n-1) z"
  unfolding SBessel_Y_conv_J by (simp add: power_int_minus)

lemma SBessel_Y_minus_left: "SBessel_Y (-n) z = (-1) powi (n+1) * SBessel_J (n - 1) z"
  by (subst SBessel_Y_conv_J) (simp_all add: power_int_minus_left)

lemma SBessel_J_minus_left: "SBessel_J (-n) z = (-1) powi n * SBessel_Y (n - 1) z"
  by (subst SBessel_Y_conv_J) (simp_all add: power_int_minus_left)

lemma SBessel_Y_minus_right: "SBessel_Y n (-z) = (-1) powi (n+1) * SBessel_Y n z"
  by (simp add: SBessel_Y_conv_J SBessel_J_minus_right power_int_minus_left)

lemma SBessel_Y_of_real: "SBessel_Y n (of_real x) = of_real (SBessel_Y n x)"
  by (simp add: SBessel_Y_conv_J SBessel_J_of_real)

lemma SBessel_Y_contiguous:
  assumes "z \<noteq> 0"
  shows   "(2 * of_int n + 1) * SBessel_Y n z = z * (SBessel_Y (n - 1) z + SBessel_Y (n + 1) z)"
proof -
  have "z * SBessel_Y (n - 1) z = (-1) powi n * (z * SBessel_J (-n) z)"
    unfolding SBessel_Y_conv_J by simp
  also have "z * SBessel_J (-n) z = -(2 * of_int n + 1) * SBessel_J (-n-1) z - z * SBessel_J (-n-2) z"
    using SBessel_J_contiguous[of z "-n-1"] assms by (simp add: power_int_add algebra_simps)
  also have "(-1) powi n * \<dots> = (2 * of_int n + 1) * SBessel_Y n z  - z * SBessel_Y (1 + n) z"
    unfolding SBessel_J_conv_Y
    by (simp_all add: power_int_diff power_int_minus algebra_simps flip: power_int_inverse)
  finally show ?thesis
    by (simp add: algebra_simps)
qed


subsubsection \<open>The modified spherical Bessel function of the first kind\<close>

text \<open>
  The modified spherical Bessel functions of the first kind are the hyperbolic versions of $j_n(z)$.
  They satisfy a slightly different recurrence and, in the complex case, can easily be written in
  terms of $j_n$ and vice versa.
\<close>
function SBessel_I :: "int \<Rightarrow> 'a :: {banach, real_normed_field} \<Rightarrow> 'a" where
  "SBessel_I 0 = (\<lambda>z. sinh z / z)"
| "SBessel_I (-1) = (\<lambda>z. cosh z / z)"
| "n > 0 \<Longrightarrow> SBessel_I n = (\<lambda>z. -(2 * of_int n - 1) / z * SBessel_I (n-1) z + SBessel_I (n-2) z)"
| "n < -1 \<Longrightarrow> SBessel_I n = (\<lambda>z. (2 * of_int n + 3) / z * SBessel_I (n+1) z + SBessel_I (n+2) z)"
  by force+
termination 
  by (relation "Wellfounded.measure (\<lambda>n. nat (abs (2 * n + 1)))") (auto simp: abs_if)

lemmas [simp del] = SBessel_I.simps(3,4)

lemma SBessel_I_0_right [simp]: "SBessel_I n 0 = 0"
  by (induction n rule: SBessel_J_induct) (auto simp: SBessel_I.simps)

lemma SBessel_I_of_real: "SBessel_I n (of_real x) = of_real (SBessel_I n x)"
  by (induction n rule: SBessel_J_induct) (simp_all add: SBessel_I.simps sinh_of_real cosh_of_real)

lemma SBessel_I_minus_right: "SBessel_I n (-z) = (-1) powi n * SBessel_I n z"
  by (induction n rule: SBessel_J_induct)
     (auto simp: power_int_minus_left SBessel_I.simps)

lemma SBessel_I_contiguous:
  assumes "z \<noteq> 0"
  shows   "(2 * of_int n + 1) * SBessel_I n z = z * (SBessel_I (n-1) z - SBessel_I (n+1) z)"
proof (cases n rule: SBessel_I.cases)
  case 1
  thus ?thesis using assms
    by (simp add: SBessel_I.simps field_simps)
next
  case 2
  thus ?thesis using assms
    by (simp add: SBessel_I.simps field_simps)
next
  case (3 n)
  thus ?thesis using assms
    by (simp add: SBessel_I.simps field_simps)
next
  case (4 n)
  thus ?thesis using assms
    by (simp add: SBessel_I.simps field_simps)
qed

lemma SBessel_I_conv_J: "SBessel_I n z = (-\<i>) powi n * SBessel_J n (\<i> * z)"
proof (cases "z = 0")
  case False
  thus ?thesis
    by (induction n rule: SBessel_J_induct)
       (simp_all add: SBessel_I.simps SBessel_J.simps sin_conv_sinh cos_conv_cosh
                      power_int_add power_int_diff field_simps)
qed auto

lemma SBessel_J_conv_I: "SBessel_J n z = \<i> powi n * SBessel_I n (-\<i> * z)"
  by (subst SBessel_I_conv_J) (auto simp flip: mult.assoc power_int_mult_distrib)



subsubsection \<open>Spherical Hankel functions\<close>

text \<open>
  The spherical Hankel functions are complex functions that can be written as linear combinations 
  of the spherical Bessel functions. Therefore, they also satisfy the same contiguous relations.
\<close>

definition SHankel_1 :: "int \<Rightarrow> complex \<Rightarrow> complex"
  where "SHankel_1 n z = SBessel_J n z + \<i> * SBessel_Y n z"

definition SHankel_2 :: "int \<Rightarrow> complex \<Rightarrow> complex"
  where "SHankel_2 n z = SBessel_J n z - \<i> * SBessel_Y n z"

lemma SHankel_1_minus_left: "SHankel_1 (-n) z = -\<i> * (-1) powi n * SHankel_1 (n-1) z"
  unfolding SHankel_1_def SHankel_2_def SBessel_J_minus_left SBessel_Y_minus_left
  by (simp add: power_int_add algebra_simps)

lemma SHankel_2_minus_left: "SHankel_2 (-n) z = \<i> * (-1) powi n * SHankel_2 (n-1) z"
  unfolding SHankel_1_def SHankel_2_def SBessel_J_minus_left SBessel_Y_minus_left
  by (simp add: power_int_add algebra_simps)

lemma SHankel_1_minus_right: "SHankel_1 n (-z) = (-1) powi n * SHankel_2 n z"
  by (simp add: SHankel_1_def SHankel_2_def SBessel_J_minus_right 
                SBessel_Y_minus_right power_int_add algebra_simps)

lemma SHankel_2_minus_right: "SHankel_2 n (-z) = (-1) powi n * SHankel_1 n z"
  by (simp add: SHankel_1_def SHankel_2_def SBessel_J_minus_right 
                SBessel_Y_minus_right power_int_add algebra_simps)

lemma SBessel_J_conv_SHankel: "SBessel_J n z = (SHankel_1 n z + SHankel_2 n z) / 2"
  by (simp add: SHankel_1_def SHankel_2_def)

lemma SBessel_Y_conv_SHankel: "SBessel_Y n z = (SHankel_1 n z - SHankel_2 n z) / (2 * \<i>)"
  by (simp add: SHankel_1_def SHankel_2_def)


lemma SHankel_1_contiguous:
  assumes "z \<noteq> 0"
  shows   "(2 * of_int n + 1) * SHankel_1 n z = z * (SHankel_1 (n - 1) z + SHankel_1 (n + 1) z)"
proof -
  have "(2 * of_int n + 1) * SHankel_1 n z =
        (2 * of_int n + 1) * SBessel_J n z + \<i> * ((2 * of_int n + 1) * SBessel_Y n z)"
    unfolding SHankel_1_def by algebra
  also have "\<dots> = z * (SHankel_1 (n-1) z + SHankel_1 (n+1) z)"
    unfolding SHankel_1_def SBessel_J_contiguous[OF assms] SBessel_Y_contiguous[OF assms]
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma SHankel_2_contiguous:
  assumes "z \<noteq> 0"
  shows   "(2 * of_int n + 1) * SHankel_2 n z = z * (SHankel_2 (n - 1) z + SHankel_2 (n + 1) z)"
proof -
  have "(2 * of_int n + 1) * SHankel_2 n z =
        (2 * of_int n + 1) * SBessel_J n z - \<i> * ((2 * of_int n + 1) * SBessel_Y n z)"
    unfolding SHankel_2_def by algebra
  also have "\<dots> = z * (SHankel_2 (n-1) z + SHankel_2 (n+1) z)"
    unfolding SHankel_2_def SBessel_J_contiguous[OF assms] SBessel_Y_contiguous[OF assms]
    by (simp add: algebra_simps)
  finally show ?thesis .
qed


text \<open>
  The spherical Hankel functions have a simple closed form in terms of the exponential and the
  Bessel polynomials.
\<close>
lemma SHankel_1_nonneg_eq: 
  assumes "z \<noteq> 0"
  shows   "SHankel_1 (int n) z = (-\<i>)^(n+1) * exp (\<i>*z) * poly (bessel_poly n) (\<i>/z) / z"
proof (induction n rule: induct_nat_012)
  case 0
  thus ?case
    using assms by (simp add: SHankel_1_def SBessel_Y_def sin_exp_eq cos_exp_eq field_simps)
next
  case 1
  thus ?case
    using assms by (simp add: SHankel_1_def SBessel_Y_def sin_exp_eq cos_exp_eq field_simps SBessel_J.simps)
next
  case (ge2 n)
  have "(-\<i>) ^ (Suc (Suc n) + 1) * exp (\<i>*z) * poly (bessel_poly (Suc (Suc n))) (\<i>/z) / z = 
           (2 * of_nat n + 3) * ((-\<i>)^(Suc n + 1) * exp (\<i>*z) * poly (bessel_poly (Suc n)) (\<i>/z) / z) / z -
           (-\<i>)^(n+1) * exp (\<i>*z) * poly (bessel_poly n) (\<i>/z) / z"
    using assms by (simp add: poly_monom field_simps)
  also have "\<dots> = ((2 * of_nat n + 3) * SHankel_1 (int (Suc n)) z) / z - SHankel_1 (int n) z"
    unfolding ge2.IH [symmetric] ..
  also have "(2 * of_nat n + 3) * SHankel_1 (int (Suc n)) z = 
               z * (SHankel_1 (int n) z + SHankel_1 (2 + int n) z)"
    using SHankel_1_contiguous[of z "int (Suc n)"] assms by (simp add: algebra_simps)
  also have "\<dots> / z - SHankel_1 (int n) z = SHankel_1 (Suc (Suc n)) z"
    using assms by simp
  finally show ?case ..
qed

lemma SHankel_2_nonneg_eq: 
  assumes "z \<noteq> 0"
  shows   "SHankel_2 (int n) z = \<i>^(n+1) * exp (-\<i>*z) * poly (bessel_poly n) (-\<i>/z) / z"
proof -
  have "SHankel_2 (int n) z = (-1) powi n * SHankel_1 (int n) (-z)"
    by (simp add: SHankel_1_minus_right)
  also have "\<dots> = \<i>^(n+1) * exp (-\<i>*z) * poly (bessel_poly n) (-\<i>/z) / z"
    using assms by (subst SHankel_1_nonneg_eq) (auto simp: uminus_power_if)
  finally show ?thesis .
qed

lemma SHankel_1_neg_eq: 
  assumes "z \<noteq> 0"
  shows   "SHankel_1 (-int (n+1)) z = \<i> ^ n * exp (\<i> * z) * poly (bessel_poly n) (\<i> / z) / z"
proof -
  have "SHankel_1 (-int (n+1)) z = -\<i> * (-1) ^ (n+1) * SHankel_1 (int n) z"
    by (subst SHankel_1_minus_left) (auto simp: power_int_add)
  also have "\<dots> = \<i> ^ n * exp (\<i> * z) * poly (bessel_poly n) (\<i> / z) / z"
    by (subst SHankel_1_nonneg_eq[OF assms]) (auto simp: power_minus' mult_ac)
  finally show ?thesis .
qed

lemma SHankel_2_neg_eq: 
  assumes "z \<noteq> 0"
  shows   "SHankel_2 (-int (n+1)) z = (-\<i>) ^ n * exp (-\<i> * z) * poly (bessel_poly n) (-\<i> / z) / z"
proof -
  have "SHankel_2 (-int (n+1)) z = \<i> * (-1) ^ (n+1) * SHankel_2 (int n) z"
    by (subst SHankel_2_minus_left) (auto simp: power_int_add)
  also have "\<dots> = (-\<i>) ^ n * exp (-\<i> * z) * poly (bessel_poly n) (-\<i> / z) / z"
    by (subst SHankel_2_nonneg_eq[OF assms]) (auto simp: power_minus' mult_ac)
  finally show ?thesis .
qed


subsubsection \<open>Closed form expressions\<close>

text \<open>
  We can now give closed-form expressions for all the spherical Bessel functions in terms
  of $\sin$, $\cos$, $\sinh$, and $\cosh$.
\<close>

lemma SBessel_J_conv_sin_cos_nonneg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_J (int n) z =
            (\<Sum>k\<le>n. (-1)^((n+k+1) div 2 + k) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sin z else cos z))"
proof (cases "z = 0")
  case [simp]: False
  define c :: "nat \<Rightarrow> complex" where "c = coeff (bessel_poly n)"
  have "SBessel_J (int n) z = 
          ((-\<i>) ^ (n+1) * exp (\<i>*z) * poly (bessel_poly n) (\<i>/z) +
           \<i> ^ (n+1) * exp (-\<i>*z) * poly (bessel_poly n) (-\<i>/z)) / (2 * z)"
    unfolding SBessel_J_conv_SHankel SHankel_1_nonneg_eq[OF False] SHankel_2_nonneg_eq[OF False]
    by (simp add: field_simps)
  also have "\<dots> = (\<Sum>k\<le>n. (-\<i>)^(n+1) * exp (\<i>*z) * c k * (\<i>/z)^k + 
                           \<i>^(n+1) * exp (-\<i>*z) * c k * (-\<i>/z) ^ k) / (2*z)"
    unfolding poly_altdef degree_bessel_poly sum.distrib [symmetric] sum_distrib_left
    by (simp add: c_def mult_ac)
  also have "\<dots> = (\<Sum>k\<le>n. (-1)^((n+k+1) div 2 + k) * c k / z^(k+1) * 
                          (if even (n + k) then sin z else cos z))"
    unfolding sum_divide_distrib
  proof (intro sum.cong, goal_cases)
    case (2 k)
    have "(-\<i>)^(n+1) * exp (\<i>*z) * c k * (\<i>/z)^k / (2*z) + \<i>^(n+1) * exp (-\<i>*z) * c k * (-\<i>/z) ^ k / (2*z) =
          c k / z ^ Suc k * (\<i>^(n+k+1) * (-1)^k * (((-1)^(n+k+1) * exp (\<i>*z) + exp (-\<i>*z)) / 2))"
      by (auto simp: power_minus' field_simps power_add)
    also have "((-1)^(n+k+1) * exp (\<i>*z) + exp (-\<i>*z)) / 2 = (if even (n+k) then -\<i> * sin z else cos z)"
      by (auto simp: cos_exp_eq sin_exp_eq field_simps)
    also have "\<i>^(n+k+1) * (-1)^k * \<dots> = (-1) ^ ((n+k+1) div 2 + k) * (if even (n+k) then sin z else cos z)"
      by (cases "even n"; cases "even k")
         (auto elim!: evenE oddE simp: uminus_power_if split: if_splits)
    finally show ?case
      by (simp add: field_simps)
  qed auto
  finally show ?thesis
    by (simp add: coeff_bessel_poly c_def)
qed auto

lemma SBessel_Y_conv_sin_cos_nonneg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_Y (int n) z =
            (\<Sum>k\<le>n. (-1)^((n+k) div 2 + k + 1) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cos z else sin z))"
proof (cases "z = 0")
  case [simp]: False
  define c :: "nat \<Rightarrow> complex" where "c = coeff (bessel_poly n)"
  have "SBessel_Y (int n) z = 
          ((-\<i>) ^ (n+1) * exp (\<i>*z) * poly (bessel_poly n) (\<i>/z) -
           \<i> ^ (n+1) * exp (-\<i>*z) * poly (bessel_poly n) (-\<i>/z)) / (2 * \<i> * z)"
    unfolding SBessel_Y_conv_SHankel SHankel_1_nonneg_eq[OF False] SHankel_2_nonneg_eq[OF False]
    by (simp add: field_simps)
  also have "\<dots> = (\<Sum>k\<le>n. (-\<i>)^(n+1) * exp (\<i>*z) * c k * (\<i>/z)^k - 
                           \<i>^(n+1) * exp (-\<i>*z) * c k * (-\<i>/z) ^ k) / (2*\<i>*z)"
    unfolding poly_altdef degree_bessel_poly sum_subtractf sum_distrib_left
    by (simp add: c_def mult_ac)                        
  also have "\<dots> = (\<Sum>k\<le>n. (-1)^((n+k) div 2 + k + 1) * c k / z^(k+1) * 
                          (if even (n + k) then cos z else sin z))"
    unfolding sum_divide_distrib
  proof (intro sum.cong, goal_cases)
    case (2 k)
    have "(-\<i>)^(n+1) * exp (\<i>*z) * c k * (\<i>/z)^k / (2*\<i>*z) - \<i>^(n+1) * exp (-\<i>*z) * c k * (-\<i>/z) ^ k / (2*\<i>*z) =
          c k / z ^ Suc k * (\<i>^(n+k) * (-1)^k * (((-1)^(n+k+1) * exp (\<i>*z) - exp (-\<i>*z)) / 2))"
      by (auto simp: power_minus' field_simps power_add)
    also have "((-1)^(n+k+1) * exp (\<i>*z) - exp (-\<i>*z)) / 2 = (if even (n+k) then -cos z else \<i> * sin z)"
      by (auto simp: cos_exp_eq sin_exp_eq field_simps)
    also have "\<i>^(n+k) * (-1)^k * \<dots> = (-1) ^ ((n+k) div 2 + k + 1) * (if even (n+k) then cos z else sin z)"
      by (cases "even n"; cases "even k")
         (auto elim!: evenE oddE simp: uminus_power_if split: if_splits)
    finally show ?case
      by (simp add: field_simps)
  qed auto
  finally show ?thesis
    by (simp add: coeff_bessel_poly c_def)
qed auto

lemma SBessel_J_conv_sin_cos_neg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_J (-int (n+1)) z =
            (\<Sum>k\<le>n. (-1)^(n + k + (n+k) div 2) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cos z else sin z))"
proof -
  have "SBessel_J (-int (n+1)) z = (-1)^(n+1) * SBessel_Y (int n) z"
    unfolding SBessel_J_conv_Y
    by (simp add: power_int_add minus_diff_commute power_int_minus uminus_power_if)
  also have "\<dots> = (\<Sum>j\<le>n. (-1)^(n+1) * ((-1) ^ ((n + j) div 2 + j + 1) *
                          of_nat (bessel_poly_coeff n j) / z^(j+1) * 
                          (if even (n+j) then cos z else sin z))) "
    unfolding SBessel_Y_conv_sin_cos_nonneg_complex sum_distrib_left ..
  also have "\<dots> = (\<Sum>j\<le>n. (-1) ^ (n + j + (n + j) div 2) *
                          of_nat (bessel_poly_coeff n j) / z^(j+1) * 
                          (if even (n+j) then cos z else sin z))"
    by (simp add: power_add mult_ac)
  finally show ?thesis .
qed

lemma SBessel_Y_conv_sin_cos_neg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_Y (-int (n+1)) z =
            (\<Sum>k\<le>n. (-1)^(n + k + (n+k+1) div 2) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sin z else cos z))"
proof -
  have "SBessel_Y (-int (n+1)) z = (-1)^n * SBessel_J (int n) z"
    unfolding SBessel_Y_conv_J 
    by (simp add: power_int_add minus_diff_commute power_int_minus uminus_power_if)
  also have "\<dots> = (\<Sum>j\<le>n. (-1)^n * ((-1) ^ ((n + j + 1) div 2 + j) *
                          of_nat (bessel_poly_coeff n j) / z^(j+1) * 
                          (if even (n+j) then sin z else cos z))) "
    unfolding SBessel_J_conv_sin_cos_nonneg_complex sum_distrib_left ..
  also have "\<dots> = (\<Sum>j\<le>n. (-1) ^ (n + j + (n + j + 1) div 2) *
                          of_nat (bessel_poly_coeff n j) / z^(j+1) * 
                          (if even (n+j) then sin z else cos z))"
    by (simp add: power_add mult_ac)
  finally show ?thesis .
qed

lemma SBessel_I_conv_sinh_cosh_nonneg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_I (int n) z =
            (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sinh z else cosh z))"
proof (cases "z = 0")
  case [simp]: False
  have "SBessel_I (int n) z = 
          (-\<i>) ^ n * (\<Sum>k\<le>n. (-1) ^ ((n + k + 1) div 2 + k) * of_nat (bessel_poly_coeff n k) /
                               (\<i> * z) ^ (k + 1) * (if even (n + k) then sin (\<i> * z) else cos (\<i> * z)))"
    by (subst SBessel_I_conv_J, subst SBessel_J_conv_sin_cos_nonneg_complex) auto
  also have "\<dots> = (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sinh z else cosh z))"
    unfolding sum_distrib_left
    by (intro sum.cong)
       (auto simp: cosh_conv_cos sinh_conv_sin field_simps power_add elim!: oddE evenE)
  finally show ?thesis .
qed auto

lemma SBessel_I_conv_sinh_cosh_neg_complex:
  fixes z :: complex and n :: nat
  shows  "SBessel_I (-int (n+1)) z =
            (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cosh z else sinh z))"
proof (cases "z = 0")
  case [simp]: False
  have "SBessel_I (-int (n+1)) z = 
          (-\<i>) powi (-1 - int n) * (\<Sum>k\<le>n. (-1) ^ (n + k + (n + k) div 2) *
          of_nat (bessel_poly_coeff n k) *
          (if even n = even k then cos (\<i> * z) else sin (\<i> * z)) / (\<i> * z * (\<i> * z) ^ k))"
    by (subst SBessel_I_conv_J, subst SBessel_J_conv_sin_cos_neg_complex) auto
  also have "\<dots> = (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cosh z else sinh z))"
    unfolding sum_distrib_left
    by (intro sum.cong)
       (auto simp: cosh_conv_cos sinh_conv_sin field_simps power_int_add power_int_diff
                   power_int_minus power_add elim!: oddE evenE)
  finally show ?thesis .
qed auto


text \<open>
  Variants of the above for the real-valued functions:
\<close>
lemma SBessel_J_conv_sin_cos_nonneg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_J (int n) z =
            (\<Sum>k\<le>n. (-1)^((n+k+1) div 2 + k) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sin z else cos z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_J (int n) z) = of_real ?rhs"
    unfolding SBessel_J_of_real [symmetric]
    by (subst SBessel_J_conv_sin_cos_nonneg_complex)
       (simp_all add: sin_of_real cos_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma SBessel_Y_conv_sin_cos_nonneg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_Y (int n) z =
            (\<Sum>k\<le>n. (-1)^((n+k) div 2 + k + 1) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cos z else sin z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_Y (int n) z) = of_real ?rhs"
    unfolding SBessel_Y_of_real [symmetric]
    by (subst SBessel_Y_conv_sin_cos_nonneg_complex)
       (simp_all add: sin_of_real cos_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma SBessel_J_conv_sin_cos_neg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_J (-int (n+1)) z =
             (\<Sum>k\<le>n. (-1)^(n + k + (n+k) div 2) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cos z else sin z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_J (-int (n+1)) z) = of_real ?rhs"
    unfolding SBessel_J_of_real [symmetric]
    by (subst SBessel_J_conv_sin_cos_neg_complex)
       (simp_all add: sin_of_real cos_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma SBessel_Y_conv_sin_cos_neg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_Y (-int (n+1)) z =
            (\<Sum>k\<le>n. (-1)^(n + k + (n+k+1) div 2) * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sin z else cos z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_Y (-int (n+1)) z) = of_real ?rhs"
    unfolding SBessel_Y_of_real [symmetric]
    by (subst SBessel_Y_conv_sin_cos_neg_complex)
       (simp_all add: sin_of_real cos_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma SBessel_I_conv_sinh_cosh_nonneg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_I (int n) z =
            (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then sinh z else cosh z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_I (int n) z) = of_real ?rhs"
    unfolding SBessel_I_of_real [symmetric]
    by (subst SBessel_I_conv_sinh_cosh_nonneg_complex)
       (simp_all add: sinh_of_real cosh_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma SBessel_I_conv_sinh_cosh_neg_real:
  fixes z :: real and n :: nat
  shows  "SBessel_I (-int (n+1)) z =
            (\<Sum>k\<le>n. (-1)^k * of_nat (bessel_poly_coeff n k) / z^(k+1) * 
                      (if even (n + k) then cosh z else sinh z))" (is "_ = ?rhs")
proof -
  have "complex_of_real (SBessel_I (-int (n+1)) z) = of_real ?rhs"
    unfolding SBessel_I_of_real [symmetric]
    by (subst SBessel_I_conv_sinh_cosh_neg_complex)
       (simp_all add: sinh_of_real cosh_of_real if_distrib[of of_real] cong: if_cong)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed


experiment
begin

text \<open>
  As an example: the close form of $j_3(z)$:
\<close>
lemma "SBessel_J 3 (z :: complex) = 
          15 * sin z / z ^ 4 + cos z / z - 6 * sin z / z ^ 2 - 15 * cos z / z ^ 3"
  using SBessel_J_conv_sin_cos_nonneg_complex[of 3 z]
  by (simp add: atMost_nat_numeral bessel_poly_coeff_conv_fact' fact_numeral 
                power_numeral_reduce mult_ac)

end


subsection \<open>The Bessel--Clifford function\<close>

text \<open>
  The Bessel--Clifford function $C_a$ is a useful building block to construct the Bessel functions.
  It is a holomorphic function in two variables and therefore very well-behaved. It can be
  defined most easily via the regularised hypergeometric function.

  Two important properties are that it is is that it satisfies $\frac{d}{dz} C_a(z) = C_{a+1}(z)$
  and the contiguous relation $C_a(z) = (a+1) C_{a+1}(z) + z C_{a+2}(z)$, which already hints at
  its connection to the Bessel functions.

  A direct consequence of this (which we do not show here) is that it is a solution of the ODE
  $y = (a+1)y' + xy''$.

  We get these properties mostly for free using the development on hypergeometric functions.
\<close>
definition Bessel_Clifford :: "'a :: Gamma \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Bessel_Clifford a = reg_hypergeo_F [] [a+1]"

lemma Bessel_Clifford_altdef: "Bessel_Clifford a = eval_fps (fps_bessel a)"
  by (simp add: fps_bessel_def Bessel_Clifford_def reg_hypergeo_F_def)

lemma Bessel_Clifford_conv_hypergeo_F:
  "a + 1 \<notin> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Bessel_Clifford a z = rGamma (a+1) * hypergeo_F [] [a+1] z"
  unfolding Bessel_Clifford_def by (subst reg_hypergeo_F_conv_hypergeo_F) auto

lemma Bessel_Clifford_complex_of_real:
  "Bessel_Clifford (of_real a) (of_real z) = complex_of_real (Bessel_Clifford a z)"
  unfolding Bessel_Clifford_def by (subst complex_of_real_reg_hypergeo_F) auto

lemma sums_Bessel_Clifford:
  "(\<lambda>n. rGamma (a + of_nat (Suc n)) * z ^ n / fact n) sums Bessel_Clifford a z"
  using sums_reg_hypergeo_F[of "[]" "[a+1]" z] by (simp add: Bessel_Clifford_def add_ac)

lemma Bessel_Clifford_contiguous:
  "Bessel_Clifford a z = (a+1) * Bessel_Clifford (a+1) z + z * Bessel_Clifford (a+2) z"
proof -
  have conv1: "fps_conv_radius (fps_const (a + 1) * fps_bessel (a + 1)) \<ge> \<infinity>"
    by (rule fps_conv_radius_mult_ge) auto
  have conv2: "fps_conv_radius (fps_X * fps_bessel (a + 2)) \<ge> \<infinity>"
    by (rule fps_conv_radius_mult_ge) auto

  have "Bessel_Clifford a z = eval_fps (fps_bessel a) z"
    by (simp add: Bessel_Clifford_altdef)
  also have "fps_bessel a = fps_const (a+1) * fps_bessel (a+1) + fps_X * fps_bessel (a+2)"
    using fps_bessel_contiguous[of "a+1"] by (simp add: add_ac)
  also have "eval_fps \<dots> z = eval_fps (fps_const (a+1) * fps_bessel (a+1)) z +
                             eval_fps (fps_X * fps_bessel (a+2)) z"
    by (subst eval_fps_add) (use conv1 conv2 in auto)
  also have "\<dots> = (a+1) * Bessel_Clifford (a+1) z + z * Bessel_Clifford (a+2) z"
    unfolding Bessel_Clifford_altdef by (subst (1 2) eval_fps_mult) auto
  finally show ?thesis .
qed    

lemma Bessel_Clifford_0_right [simp]: "Bessel_Clifford a 0 = rGamma (a + 1)"
  by (simp add: Bessel_Clifford_def reg_hypergeo_F_0)

lemma Bessel_Clifford_minus_of_nat:
  "Bessel_Clifford (-of_nat n) z = z ^ n * Bessel_Clifford (of_nat n) z"
proof (cases "z = 0")
  case True
  show ?thesis
  proof (cases "n > 0")
    case True
    have "rGamma (of_int (1 - int n)) = 0"
      by (subst rGamma_of_int) (use \<open>n > 0\<close> in auto)
    thus ?thesis using \<open>z = 0\<close> \<open>n > 0\<close>
      by (auto simp: power_0_left)
  qed auto
next
  case False
  show ?thesis
  proof (induction "n + 1" arbitrary: n rule: less_induct)
    case (less n)
    consider "n = 0" | "n = 1" | "n \<ge> 2"
      by linarith
    thus ?case
    proof cases
      assume [simp]: "n = 1"
      show ?case
        by (subst Bessel_Clifford_contiguous) simp_all
    next
      assume n: "n \<ge> 2"
      have "Bessel_Clifford (-of_nat n) z =
               (-of_nat n + 1) * Bessel_Clifford (-of_nat (n-1)) z + z * Bessel_Clifford (-of_nat (n-2)) z"
        by (subst Bessel_Clifford_contiguous) (use n in \<open>simp_all add: add_ac\<close>)
      also have "\<dots> = (- of_nat n + 1) * z^(n-1) * Bessel_Clifford (of_nat (n - 1)) z + 
                      z * z^(n-2) * Bessel_Clifford (of_nat (n - 2)) z"
        by (subst (1 2) less) (use n in \<open>auto simp: algebra_simps\<close>)
      also have "\<dots> = z ^ n * Bessel_Clifford (of_nat n) z"
        by (subst (2) Bessel_Clifford_contiguous)
           (use n \<open>z \<noteq> 0\<close> in \<open>auto simp: field_simps power_diff power2_eq_square\<close>)
      finally show ?thesis .
    qed auto
  qed
qed

lemma Bessel_Clifford_minus_of_int:
  assumes "n \<ge> 0 \<or> z \<noteq> 0"
  shows   "Bessel_Clifford (-of_int n) z = z powi n * Bessel_Clifford (of_int n) z"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis
    using Bessel_Clifford_minus_of_nat[of "nat n" z] by (simp add: power_int_def)
next
  case False
  hence "z \<noteq> 0"
    using assms by auto
  show ?thesis
    using Bessel_Clifford_minus_of_nat[of "nat (-n)" z] \<open>z \<noteq> 0\<close> False
    by (simp add: power_int_def field_simps)
qed

lemma analytic_Bessel_Clifford [analytic_intros]:
  assumes "a analytic_on A" "b analytic_on A"
  shows   "(\<lambda>x. Bessel_Clifford (a x) (b x)) analytic_on A"
  unfolding Bessel_Clifford_def
  by (rule analytic_reg_hypergeo_F[where as = "[]" and bs = "[\<lambda>x. a x + 1]"])
     (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma has_field_derivative_Bessel_Clifford [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. Bessel_Clifford a (f x)) has_field_derivative 
                   (Bessel_Clifford (a+1) (f x) * f')) (at x within A)"
  unfolding Bessel_Clifford_def
  by (rule DERIV_cong[OF has_field_derivative_reg_hypergeo_F'[OF assms]]) auto

lemma Bessel_Clifford_real_mono:
  assumes xy: "0 \<le> (x::real)" "x \<le> y" "a \<ge> -1"
  shows  "Bessel_Clifford a x \<le> Bessel_Clifford a y"
proof (rule sums_le)
  show "(\<lambda>n. rGamma (a + real (Suc n)) * x ^ n / fact n) sums Bessel_Clifford a x"
    by (rule sums_Bessel_Clifford)
  show "(\<lambda>n. rGamma (a + real (Suc n)) * y ^ n / fact n) sums Bessel_Clifford a y"
    by (rule sums_Bessel_Clifford)
  show "rGamma (a + real (Suc n)) * x ^ n / fact n \<le> 
          rGamma (a + real (Suc n)) * y ^ n / fact n" for n using assms
    by (intro mult_left_mono divide_right_mono power_mono)
       (auto intro!: rGamma_real_nonneg)
qed

lemma Bessel_Clifford_real_pos [simp]:
  assumes "x \<ge> (0::real)" "a > -1"
  shows   "Bessel_Clifford a x > 0"
proof -
  have "rGamma (a + 1) > 0"
    using assms by (auto simp: rGamma_inverse_Gamma intro!: Gamma_real_pos)
  also have "rGamma (a+1) = Bessel_Clifford a 0"
    by simp
  also have "Bessel_Clifford a 0 \<le> Bessel_Clifford a x"
    by (rule Bessel_Clifford_real_mono) (use assms in auto)
  finally show ?thesis
    by simp
qed

lemma Bessel_Clifford_real_nonneg [simp]: "x \<ge> (0::real) \<Longrightarrow> a \<ge> -1 \<Longrightarrow> Bessel_Clifford a x \<ge> 0"
  by (rule sums_le[OF _ sums_zero sums_Bessel_Clifford])
     (auto intro!: divide_nonneg_pos mult_nonneg_nonneg rGamma_real_nonneg)

lemma Bessel_Clifford_convex_real:
  assumes "a \<ge> -3"
  shows "convex_on {0..} (Bessel_Clifford (a::real))"
proof (rule f''_ge0_imp_convex)
  show "(Bessel_Clifford a has_real_derivative Bessel_Clifford (a+1) x) (at x)" for x
    by (auto intro!: derivative_eq_intros)
  show "(Bessel_Clifford (a+1) has_real_derivative Bessel_Clifford (a+2) x) (at x)" for x
    by (auto intro!: derivative_eq_intros simp: add_ac)
  show "Bessel_Clifford (a+2) x \<ge> 0" if x: "x \<in> {0..}" for x :: real
    by (rule Bessel_Clifford_real_nonneg) (use assms x in auto)
qed auto



subsection \<open>The Bessel function of the first kind\<close>

text \<open>
  The Bessel function of the first kind $J_a$(z) can now easily be derived from the Bessel--Clifford
  function with the change of variables $z\mapsto -z^2/4$ and multiplication with $(z/2)^a$
  (from which it gets its branch cut). All the basic properties follow directly from the ones
  we have for the Bessel--Clifford function.
\<close>
definition Bessel_J :: "'a :: {Gamma, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Bessel_J a z = (z / 2) powr' a * Bessel_Clifford a (-(z\<^sup>2/4))"

lemma Bessel_J_0_0 [simp]: "Bessel_J 0 0 = 1"
  by (simp add: Bessel_J_def)

lemma Bessel_J_0_right [simp]: "a \<noteq> 0 \<Longrightarrow> Bessel_J a 0 = 0"
  by (simp add: Bessel_J_def)

lemma Bessel_J_0_right': "Bessel_J a 0 = (if a = 0 then 1 else 0)"
  by (cases "a = 0") auto

lemma Bessel_J_complex_of_real:
  assumes "a \<in> \<int> \<or> z \<ge> 0"
  shows   "Bessel_J (complex_of_real a) (of_real z) = of_real (Bessel_J a z)"
  using assms unfolding Bessel_J_def 
  by (auto simp: powr'_def Bessel_Clifford_complex_of_real [symmetric]
           elim!: Ints_cases simp: powr_Reals_eq)

lemma Bessel_J_contiguous_complex:
  fixes a z :: complex
  shows "2 * a * Bessel_J a z = z * (Bessel_J (a-1) z + Bessel_J (a+1) z)"
proof (cases "z = 0")
  case False
  define a' where "a' = a - 1"
  have "z * (Bessel_J a' z + Bessel_J (a'+2) z) = 2 * (a' + 1) * Bessel_J (a'+1) z"
    unfolding Bessel_J_def using False
    by (subst Bessel_Clifford_contiguous)
       (simp add: field_simps power2_eq_square power3_eq_cube powr_add powr'_complex)
  thus ?thesis
    by (simp add: a'_def add_ac)
qed (auto simp: Bessel_J_0_right' add_eq_0_iff2)

lemma Bessel_J_contiguous_real:
  fixes a z :: real
  assumes "z \<ge> 0 \<or> a \<in> \<int>"
  shows   "2 * a * Bessel_J a z = z * (Bessel_J (a-1) z + Bessel_J (a+1) z)"
proof (cases "z = 0")
  case False
  define a' where "a' = a - 1"
  have [simp]: "a' \<in> \<int> \<longleftrightarrow> a \<in> \<int>"
    by (auto simp: a'_def)
  have "z * (Bessel_J a' z + Bessel_J (a'+2) z) = 2 * (a' + 1) * Bessel_J (a'+1) z"
    unfolding Bessel_J_def using False assms
    by (subst Bessel_Clifford_contiguous)
       (use assms in \<open>auto simp: field_simps power2_eq_square power3_eq_cube powr_add powr'_def 
          the_int_add power_int_add power_int_0_left_if add_eq_0_iff2 elim!: Ints_cases\<close>)
  thus ?thesis
    by (simp add: a'_def add_ac)
qed (auto simp: Bessel_J_0_right' add_eq_0_iff2)

lemma Bessel_J_minus_of_nat_complex:
  "Bessel_J (-of_nat n :: complex) z = (-1) ^ n * Bessel_J (of_nat n) z"
proof (cases "z = 0")
  case False
  thus ?thesis
    unfolding Bessel_J_def Bessel_Clifford_minus_of_nat power2_eq_square
    using power_mult_distrib[of 2 "2::complex" n]
    by (auto simp: powr'_complex powr_minus Bessel_Clifford_minus_of_nat field_simps power_minus')
qed (auto simp: Bessel_J_0_right')

lemma Bessel_J_minus_of_int_complex:
  "Bessel_J (-of_int n :: complex) z = (-1) powi n * Bessel_J (of_int n) z"
proof (cases "z = 0")
  case False
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis
      using Bessel_J_minus_of_nat_complex[of "nat n" z] by (simp add: power_int_def)
  next
    case False
    thus ?thesis
      using Bessel_J_minus_of_nat_complex[of "nat (-n)" z] by (simp add: power_int_def)
  qed
qed (auto simp: Bessel_J_0_right')

lemma Bessel_J_minus_of_int_real:
  "Bessel_J (-of_int n :: real) z = (-1) powi n * Bessel_J (of_int n) z"
proof -
  have "complex_of_real (Bessel_J (-of_int n) z) = of_real ((-1) powi n * Bessel_J (of_int n) z)"
    unfolding of_real_mult using Bessel_J_minus_of_int_complex[of n "of_real z"]
    by (simp flip: Bessel_J_complex_of_real)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma Bessel_J_minus_of_nat_real:
  "Bessel_J (-of_nat n :: real) z = (-1) powi n * Bessel_J (of_nat n) z"
  using Bessel_J_minus_of_int_real[of "int n" z] by simp

lemma sums_Bessel_J:
  fixes a z :: "'a :: {Gamma, ln}"
  shows  "(\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_J a z"
proof -
  have "(\<lambda>n. (z/2) powr' a * (rGamma (a + of_nat (Suc n)) * (-(z\<^sup>2/4)) ^ n / fact n)) sums
          (Bessel_J a z)"
    unfolding Bessel_J_def by (intro sums_mult sums_Bessel_Clifford)
  also have "(\<lambda>n. (z/2) powr' a * (rGamma (a + of_nat (Suc n)) * (-(z\<^sup>2/4)) ^ n / fact n)) =
             (\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n)))"
    unfolding power_mult power2_eq_square
    by (auto simp: fun_eq_iff powr_add power_minus' field_simps rGamma_inverse_Gamma)
  finally show ?thesis .
qed

lemma sums_Bessel_J_complex:
  fixes a z :: complex
  assumes "z \<noteq> 0 \<or> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows  "(\<lambda>n. (-1)^n * (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_J a z"
proof -
  have "(\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
           Bessel_J a z"
    by (rule sums_Bessel_J)
  also have "(\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) =
             (\<lambda>n. (-1)^n * (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n)))"
    (is "?lhs = ?rhs")
  proof
    fix n :: nat
    from assms have "z \<noteq> 0 \<or> (z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0)"
      by auto
    hence "(z/2) powr' (a + 2 * of_nat n) = (z/2) powr' a * (z/2) ^ (2*n)"
    proof
      assume "z \<noteq> 0"
      thus ?thesis using powr_nat'[of "z/2" "2 * n"]
        by (auto simp: powr'_complex powr_add)
    next
      assume *: "z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
      hence "a + 2 * complex_of_nat n \<noteq> 0"
        by (metis mult_2 of_nat_add plus_of_nat_eq_0_imp)
      thus ?thesis using *
        by (auto simp: powr'_0_left_if)
    qed
    thus "?lhs n = ?rhs n"
      by simp
  qed
  finally show ?thesis .
qed

lemma sums_Bessel_J_real:
  fixes a z :: real
  assumes "a \<in> \<int> \<or> z \<ge> 0" "z \<noteq> 0 \<or> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows  "(\<lambda>n. (-1)^n * (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_J a z"
proof -
  have "(\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
           Bessel_J a z"
    by (rule sums_Bessel_J)
  also have "(\<lambda>n. (-1)^n * (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) =
             (\<lambda>n. (-1)^n * (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n)))"
    (is "?lhs = ?rhs")
  proof
    fix n :: nat
    from assms have "z \<noteq> 0 \<or> (z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0)"
      by auto
    have "(z/2) powr' (a + 2 * of_nat n) = (z/2) powr' a * (z/2) ^ (2*n)"
    proof (cases "z = 0")
      case [simp]: True
      with assms(2) have "a + 2 * real n \<noteq> 0"
        by (metis mult.commute mult_2_right of_nat_add plus_of_nat_eq_0_imp)
      thus ?thesis
        using assms by (auto simp: powr'_0_left_if)
    next
      case nz: False
      show ?thesis
      proof (cases "a \<in> \<int>")
        case False
        thus ?thesis using powr_realpow[of "z/2" "2*n"] assms(1)
          using nz by (auto simp: powr'_def powr_add)
      next
        case True
        then obtain k where a_eq: "a = of_int k"
          by (auto elim!: Ints_cases)
        have "(z / 2) powi (int (2*n)) = (z / 2) ^ (2 * n)"
          by (subst power_int_of_nat) auto
        thus ?thesis using nz unfolding of_nat_mult
          by (auto simp: a_eq powr'_def the_int_add power_int_add the_int_mult)
      qed
    qed
    thus "?lhs n = ?rhs n"
      by simp
  qed
  finally show ?thesis .
qed

lemma has_field_derivative_Bessel_J_complex:
  assumes "a \<in> \<int> \<or> (z::complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(Bessel_J a has_field_derivative 
             ((Bessel_J (a-1) z - Bessel_J (a+1) z) / 2)) (at z within A)"
proof (cases "a \<in> \<int>")
  case False
  with assms have "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by auto
  moreover from this have "z \<noteq> 0"
    by auto
  ultimately have "(Bessel_J a has_field_derivative 
                     (a * Bessel_J a z / z - Bessel_J (a+1) z)) (at z within A)"
    unfolding Bessel_J_def
    by (auto intro!: derivative_eq_intros
             simp: complex_nonpos_Reals_iff powr'_complex powr_add field_simps)
  also have "a * Bessel_J a z / z - Bessel_J (a+1) z = (Bessel_J (a-1) z - Bessel_J (a+1) z) / 2"
    using Bessel_J_contiguous_complex[of a z] \<open>z \<noteq> 0\<close> by (auto simp: field_simps)
  finally show ?thesis .
next
  case True
  then obtain n where a: "a = of_int n"
    by (auto elim: Ints_cases)
  have *: "(Bessel_J a has_field_derivative
           (Bessel_J (a - 1) z - Bessel_J (a + 1) z) / 2) (at z within A)"
    if a: "a = of_int n" "n \<ge> 0" for a n
  proof -
    have a': "a - 1 = of_int (n - 1)" "a + 1 = of_int (n + 1)"
      by (auto simp: a)
    have "((\<lambda>z. (z / 2) powi n * Bessel_Clifford a (-(z^2/4))) has_field_derivative
            (a / 2 * (z / 2) powi (n-1) * Bessel_Clifford a (- (z\<^sup>2 / 4)) -
            (z / 2) powi (n+1) * Bessel_Clifford (a+1) (- (z\<^sup>2 / 4)))) (at z within A)"
      using a by (auto intro!: derivative_eq_intros simp: power_int_add)
    also have "(a / 2 * (z / 2) powi (n-1) * Bessel_Clifford a (- (z\<^sup>2 / 4)) -
                 (z / 2) powi (n+1) * Bessel_Clifford (a+1) (- (z\<^sup>2 / 4))) = 
              (Bessel_J (a-1) z - Bessel_J (a+1) z) / 2"
      unfolding Bessel_J_def a' powr'_of_int using a
      by (subst Bessel_Clifford_contiguous[of "of_int (n-1)" "-(z ^ 2 / 4)"], cases "z = 0")
         (auto simp: powr'_complex power_int_0_left_if add_eq_0_iff2 power_int_divide_distrib 
                     power_int_add power_int_diff power2_eq_square field_simps)
    also have "((\<lambda>z. (z / 2) powi n * Bessel_Clifford a (- (z\<^sup>2 / 4))) has_field_derivative
                 (Bessel_J (a - 1) z - Bessel_J (a + 1) z) / 2) (at z within A) \<longleftrightarrow>
               ((\<lambda>z. Bessel_J a z) has_field_derivative
                 (Bessel_J (a - 1) z - Bessel_J (a + 1) z) / 2) (at z within A)"
    proof (rule has_field_derivative_cong_eventually)
      have "eventually (\<lambda>x. x \<noteq> 0) (at z within A)"
        by (rule eventually_neq_at_within)
      thus "\<forall>\<^sub>F x in at z within A. (x / 2) powi n * Bessel_Clifford a (- (x\<^sup>2 / 4)) = Bessel_J a x"
        unfolding Bessel_J_def by eventually_elim (auto simp: powr'_complex a)
    next
      show "(z / 2) powi n * Bessel_Clifford a (- (z\<^sup>2 / 4)) = Bessel_J a z"
        by (auto simp: Bessel_J_def powr'_complex power_int_0_left_if a)
    qed
    finally show ?thesis .
  qed

  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis using *[of a n] a by simp
  next
    case False
    have "((\<lambda>z. (-1) powi n * Bessel_J (-of_int n) z) has_field_derivative
            (-1) powi n * ((Bessel_J ((-of_int n) - 1) z - Bessel_J ((-of_int n) + 1) z) / 2)) (at z within A)"
      by (rule DERIV_cmult, rule *[of "-of_int n" "-n"]) (use False in auto)
    also have "(\<lambda>z. (-1) powi n * Bessel_J (-of_int n) z) = Bessel_J a"
      unfolding a by (subst Bessel_J_minus_of_int_complex) auto
    also have "(-1) powi n * ((Bessel_J ((-of_int n) - 1) z - Bessel_J ((-of_int n) + 1) z) / 2) =
               (-1) powi n * ((Bessel_J (-(of_int (n+1))) z - Bessel_J (-(of_int (n-1))) z) / 2)"
      by simp
    also have "\<dots> = (Bessel_J (a-1) z - Bessel_J (a+1) z) / 2"
      unfolding a
      by (subst (1 2) Bessel_J_minus_of_int_complex) (auto simp: power_int_add power_int_minus_left)
    finally show ?thesis .
  qed
qed

lemma has_field_derivative_Bessel_J_complex' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "a \<in> \<int> \<or> (f x :: complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Bessel_J a (f x)) has_field_derivative 
             (f' * (Bessel_J (a-1) (f x) - Bessel_J (a+1) (f x)) / 2)) (at x within A)"
  using DERIV_chain[OF has_field_derivative_Bessel_J_complex[of a] assms(1)] assms(2)
  by (simp add: o_def mult_ac)

lemma has_field_derivative_Bessel_J_real:
  assumes "a \<in> \<int> \<or> (z :: real) > 0"
  shows   "(Bessel_J a has_field_derivative 
             ((Bessel_J (a-1) z - Bessel_J (a+1) z) / 2)) (at z within A)"
proof -
  have *: "complex_of_real a \<in> \<int> \<or> complex_of_real z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using assms by auto
  have "((\<lambda>x. Re (Bessel_J (of_real a) (of_real x))) has_field_derivative
           (Re (Bessel_J (of_real (a - 1)) (of_real z)) -
            Re (Bessel_J (of_real (a + 1)) (of_real z))) / 2) (at z within A)"
    by (rule derivative_eq_intros has_vector_derivative_real_field refl *)+ simp_all
  also have "(Re (Bessel_J (of_real (a - 1)) (of_real z)) -
              Re (Bessel_J (of_real (a + 1)) (of_real z))) / 2 =
             (Bessel_J (a-1) z - Bessel_J (a+1) z) / 2"
    by (subst (1 2) Bessel_J_complex_of_real) (use assms in auto)
  also have "((\<lambda>x. Re (Bessel_J (of_real a) (of_real x))) has_real_derivative
               (Bessel_J (a - 1) z - Bessel_J (a + 1) z) / 2) (at z within A) \<longleftrightarrow> ?thesis"
  proof (rule has_field_derivative_cong_eventually)
    have "eventually (\<lambda>x. x \<in> (if a \<in> \<int> then UNIV else {0<..})) (nhds z)"
      by (rule eventually_nhds_in_open) (use assms in auto)
    hence ev: "eventually (\<lambda>x. Re (Bessel_J (of_real a) (of_real x)) = Bessel_J a x) (nhds z)"
      by eventually_elim (auto simp: Bessel_J_complex_of_real split: if_splits)
    show "eventually (\<lambda>x. Re (Bessel_J (of_real a) (of_real x)) = Bessel_J a x) (at z within A)"
      using ev by (simp add: eventually_at_filter eventually_mono)
    show "Re (Bessel_J (complex_of_real a) (complex_of_real z)) = Bessel_J a z"
      using ev by (meson eventually_nhds)
  qed
  finally show ?thesis .
qed

lemma has_field_derivative_Bessel_J_real' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "a \<in> \<int> \<or> f x > (0 :: real)"
  shows   "((\<lambda>x. Bessel_J a (f x)) has_field_derivative 
             ((Bessel_J (a-1) (f x) - Bessel_J (a+1) (f x)) / 2) * f') (at x within A)"
  using DERIV_chain[OF has_field_derivative_Bessel_J_real assms(1), of a] assms
  by (simp add: o_def mult_ac)

lemma analytic_Bessel_J [analytic_intros]:
  assumes "a analytic_on A" "b analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> b x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Bessel_J (a x) (b x)) analytic_on A"
  unfolding Bessel_J_def
  by (auto intro!: analytic_intros assms(1,2))
     (use assms(3) in \<open>auto simp: complex_nonpos_Reals_iff\<close>)

lemma analytic_Bessel_J_Ints:
  assumes "b analytic_on A" "a \<in> \<int>"
  shows   "(\<lambda>x. Bessel_J a (b x)) analytic_on A"
proof -
  from \<open>a \<in> \<int>\<close> obtain n where a: "a = of_int n"
    by (elim Ints_cases)
  have *: "(\<lambda>x. Bessel_J (of_int n) (b x)) analytic_on A" if n: "n \<ge> 0" for n
    unfolding Bessel_J_def powr'_of_int by (intro analytic_intros assms(1)) (use n in auto)
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis using *[of n] by (simp add: a)
  next
    case False
    note [analytic_intros del] = analytic_Bessel_J
    have "(\<lambda>x. (-1) powi n * Bessel_J (of_int (-n)) (b x)) analytic_on A"
      by (intro analytic_intros *) (use False in auto)
    also have "(\<lambda>x. (-1) powi n * Bessel_J (of_int (-n)) (b x)) =
               (\<lambda>x. Bessel_J (of_int n) (b x))"
      unfolding of_int_minus by (subst Bessel_J_minus_of_int_complex) (simp flip: mult.assoc)
    finally show ?thesis by (simp add: a)
  qed
qed

text \<open>
  The half-integer case $J_{n+\frac{1}{2}}$ can be expressed in terms of spherical Bessel
  functions of the first kind $j_n$ and therefore has a closed form.
\<close>
theorem Bessel_J_conv_SBessel_J_complex:
  assumes z: "z \<noteq> (0 :: complex)"
  defines "C \<equiv> sqrt (2 / pi) * csqrt z"
  shows   "Bessel_J (of_int n + 1 / 2) z = C * SBessel_J n z"
proof (induction n rule: SBessel_J_induct)
  case 1
  have "Bessel_J (of_int 0 + 1 / 2) z = 
          (z / 2) powr' (1 / 2) * rGamma (3/2) * hypergeo_F [] [3 / 2] (- (z\<^sup>2 / 4))"
    unfolding Bessel_J_def by (subst Bessel_Clifford_conv_hypergeo_F) auto
  also have "rGamma (3 / 2 :: complex) = 2 * rGamma (1/2)"
    using rGamma_plus1[of "1/2 :: complex"] by simp
  also have "\<dots> = of_real (2 / sqrt pi)"
    unfolding rGamma_inverse_Gamma Gamma_one_half_complex by (simp add: field_simps)
  also have "(z / 2) powr' (1 / 2) = ((1/2) * z) powr (1 / 2)"
    by (auto simp: powr'_def)
  also have "\<dots> = csqrt z / sqrt 2"
    by (subst powr_times_real_left)
       (auto simp: powr_half_sqrt powr_Reals_eq real_sqrt_divide simp flip: csqrt_conv_powr)
  also have "hypergeo_F [] [3/2] (-(z\<^sup>2/4)) = sin z / z"
    using sin_conv_hypergeo_F[of z] z by simp
  also have "sin z / z = SBessel_J 0 z"
    by simp
  also have "csqrt z / complex_of_real (sqrt 2) * complex_of_real (2 / sqrt pi) =
             C"
    using z by (simp add: C_def real_sqrt_divide field_simps flip: power2_eq_square of_real_power)
  finally show ?case
    by simp
next
  case 2
  have "Bessel_J (of_int (-1) + 1 / 2) z = 
          (z / 2) powr' (-1 / 2) * rGamma (1/2) * hypergeo_F [] [1 / 2] (- (z\<^sup>2 / 4))"
    unfolding Bessel_J_def by (subst Bessel_Clifford_conv_hypergeo_F) auto
  also have "rGamma (1 / 2 :: complex) = of_real (1 / sqrt pi)"
    unfolding rGamma_inverse_Gamma Gamma_one_half_complex by (simp add: field_simps)
  also have "(z / 2) powr' (-1 / 2) = ((1/2) * z) powr (-1 / 2)"
    by (auto simp: powr'_def)
  also have "\<dots> = sqrt 2 * (1 / csqrt z)"
    by (subst powr_times_real_left) 
       (auto simp: powr_minus powr_half_sqrt powr_Reals_eq real_sqrt_divide field_simps 
             simp flip: csqrt_conv_powr)
  also have "1 / csqrt z = csqrt z / z"
    using z by (simp add: field_simps flip: power2_eq_square)
  also have "hypergeo_F [] [1/2] (-(z\<^sup>2/4)) = cos z"
    using cos_conv_hypergeo_F[of z] z by simp
  also have "of_real (sqrt 2) * (csqrt z / z) * of_real (1 / sqrt pi) * cos z =
             of_real (sqrt (2 / pi)) * csqrt z * (cos z / z)"
    using z by (simp add: field_simps real_sqrt_divide)
  also have "cos z / z = SBessel_J (-1) z"
    by simp
  finally show ?case
    by (simp add: C_def)
next
  case (3 n)
  have "Bessel_J (of_int n + 1 / 2) z =
          2 * (of_int n - 1 / 2) / z * Bessel_J (of_int (n - 1) + 1 / 2) z -
          Bessel_J (of_int (n - 2) + 1 / 2) z"
    using Bessel_J_contiguous_complex[of "of_int n - 1 / 2" z] using z
    by (simp add: field_simps)
  also have "2 * (of_int n - 1 / 2) = 2 * complex_of_int n - 1"
    by (simp add: field_simps)
  also have "Bessel_J (of_int (n - 1) + 1 / 2) z = C * SBessel_J (n - 1) z"
    by (subst "3.IH") auto
  also have "Bessel_J (of_int (n - 2) + 1 / 2) z = C * SBessel_J (n - 2) z"
    by (subst "3.IH") auto
  also have "(2 * of_int n - 1) / z * (C * SBessel_J (n - 1) z) - C * SBessel_J (n - 2) z = 
               C * SBessel_J n z"
    using "3.hyps" z by (subst (3) SBessel_J.simps) (auto simp: field_simps)
  finally show ?case .
next
  case (4 n)
  have "Bessel_J (of_int n + 1 / 2) z =
           2 * (of_int n + 3 / 2) / z * Bessel_J (of_int (n + 1) + 1 / 2) z -
           Bessel_J (of_int (n + 2) + 1 / 2) z"
    using Bessel_J_contiguous_complex[of "of_int n + 3 / 2" z] using z
    by (simp add: field_simps)
  also have "2 * (of_int n + 3 / 2) = 2 * complex_of_int n + 3"
    by (simp add: field_simps)
  also have "Bessel_J (of_int (n + 1) + 1 / 2) z = C * SBessel_J (n + 1) z"
    by (subst "4.IH") auto
  also have "Bessel_J (of_int (n + 2) + 1 / 2) z = C * SBessel_J (n + 2) z"
    by (subst "4.IH") auto
  also have "(2 * of_int n + 3) / z * (C * SBessel_J (n + 1) z) - C * SBessel_J (n + 2) z =
             C * ((2 * of_int n + 3) / z * SBessel_J (n + 1) z - SBessel_J (n + 2) z)"
    using z by (simp add: field_simps)
  also have "(2 * of_int n + 3) / z * SBessel_J (n + 1) z - SBessel_J (n + 2) z = SBessel_J n z"
    by (subst (2) SBessel_J.simps) (use "4.hyps" in \<open>simp_all add: add_ac\<close>)
  finally show ?case .
qed

lemma Bessel_J_conv_SBessel_J_real:
  assumes z: "z > (0 :: real)"
  shows   "Bessel_J (of_int n + 1 / 2) z = sqrt (2 * z / pi) * SBessel_J n z"
proof -
  have "complex_of_real (Bessel_J (of_int n + 1 / 2) z) = Bessel_J (of_int n + 1 / 2) (of_real z)"
    by (subst Bessel_J_complex_of_real [symmetric]) (use z in auto)
  also have "Bessel_J (of_int n + 1 / 2) (complex_of_real z) = 
               of_real (sqrt (2 * z / pi) * SBessel_J n z)"
    by (subst Bessel_J_conv_SBessel_J_complex) 
       (use z in \<open>auto simp: SBessel_J_of_real real_sqrt_divide real_sqrt_mult\<close>)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


subsection \<open>The modified Bessel function of the first kind\<close>

text \<open>
  Again, the modified Bessel function of the first kind $I_a$ is essentially the hyperbolic
  version of $J_a$. In the complex case, it can also easily be written in terms of $I_a$ and
  vice versa.
\<close>
definition Bessel_I :: "'a :: {Gamma, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Bessel_I a z = (z / 2) powr' a * Bessel_Clifford a (z\<^sup>2/4)"

lemma Bessel_I_0_0 [simp]: "Bessel_I 0 0 = 1"
  by (simp add: Bessel_I_def)

lemma Bessel_I_0_right [simp]: "a \<noteq> 0 \<Longrightarrow> Bessel_I a 0 = 0"
  by (simp add: Bessel_I_def)

lemma Bessel_I_0_right': "Bessel_I a 0 = (if a = 0 then 1 else 0)"
  by (cases "a = 0") auto

lemma Bessel_I_complex_of_real:
  assumes "a \<in> \<int> \<or> z \<ge> 0"
  shows   "Bessel_I (complex_of_real a) (of_real z) = of_real (Bessel_I a z)"
  using assms unfolding Bessel_I_def 
  by (auto simp: powr'_def Bessel_Clifford_complex_of_real [symmetric]
           elim!: Ints_cases simp: powr_Reals_eq)

lemma Bessel_I_contiguous_complex:
  fixes a z :: complex
  shows "z * Bessel_I a z = 2 * (a + 1) * Bessel_I (a+1) z + z * Bessel_I (a+2) z"
proof (cases "z = 0")
  case False
  show "z * Bessel_I a z = 2 * (a + 1) * Bessel_I (a+1) z + z * Bessel_I (a+2) z"
    unfolding Bessel_I_def using False
    by (subst Bessel_Clifford_contiguous)
       (simp add: field_simps power2_eq_square power3_eq_cube powr_add powr'_complex)
qed (auto simp: Bessel_I_0_right' add_eq_0_iff2)

lemma Bessel_I_contiguous_real:
  fixes a z :: real
  assumes "z \<ge> 0 \<or> a \<in> \<int>"
  shows   "z * Bessel_I a z = 2 * (a + 1) * Bessel_I (a+1) z + z * Bessel_I (a+2) z"
  unfolding Bessel_I_def
  by (subst Bessel_Clifford_contiguous; cases "z = 0")
     (use assms in \<open>auto simp: field_simps power2_eq_square power3_eq_cube powr_add powr'_def 
        the_int_add power_int_add power_int_0_left_if add_eq_0_iff2 elim!: Ints_cases\<close>)

lemma Bessel_I_minus_of_nat_complex:
  "Bessel_I (-of_nat n :: complex) z = Bessel_I (of_nat n) z"
proof (cases "z = 0")
  case False
  thus ?thesis
    unfolding Bessel_I_def Bessel_Clifford_minus_of_nat power2_eq_square
    using power_mult_distrib[of 2 "2::complex" n] False
    by (auto simp: powr'_complex powr_minus Bessel_Clifford_minus_of_nat field_simps power_minus')
qed (auto simp: Bessel_I_0_right')

lemma Bessel_I_minus_of_int_complex:
  "Bessel_I (-of_int n :: complex) z = Bessel_I (of_int n) z"
proof (cases "z = 0")
  case False
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis
      using Bessel_I_minus_of_nat_complex[of "nat n" z] by (simp add: power_int_def)
  next
    case False
    thus ?thesis
      using Bessel_I_minus_of_nat_complex[of "nat (-n)" z] by (simp add: power_int_def)
  qed
qed (auto simp: Bessel_I_0_right')

lemma Bessel_I_minus_of_int_real:
  "Bessel_I (-of_int n :: real) z = Bessel_I (of_int n) z"
proof -
  have "complex_of_real (Bessel_I (-of_int n) z) = of_real (Bessel_I (of_int n) z)"
    unfolding of_real_mult using Bessel_I_minus_of_int_complex[of n "of_real z"]
    by (simp flip: Bessel_I_complex_of_real)
  thus ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma Bessel_I_minus_of_nat_real:
  "Bessel_I (-of_nat n :: real) z = Bessel_I (of_nat n) z"
  using Bessel_I_minus_of_int_real[of "int n" z] by simp

lemma Bessel_I_conv_J:
  assumes "a \<in> \<int> \<or> Re z \<ge> 0 \<or> Im z < 0"
  shows "Bessel_I a z = \<i> powr (-a) * Bessel_J a (\<i> * z)"
proof (cases "z = 0")
  case [simp]: True
  show ?thesis
    by (cases "a = 0") (auto simp: Bessel_I_def Bessel_J_def)
next
  case z: False
  have "\<i> powr -a * (\<i> * (z / 2)) powr' a = (z / 2) powr' a"
    using assms
  proof
    assume "a \<in> \<int>"
    then obtain n where a: "a = of_int n"
      by (auto elim!: Ints_cases)
    show ?thesis
      by (simp add: a powr_minus complex_powr_of_int power_int_divide_distrib 
                    power_int_mult_distrib field_simps)
  next
    assume z': "Re z \<ge> 0 \<or> Im z < 0"
    have "(\<i> * (z / 2)) powr' a = (\<i> * (z / 2)) powr a"
      using z by (subst powr'_complex) auto
    also have "\<dots> = exp (Ln (\<i> * (z / 2)) * a)"
      using z by (simp add: powr_def mult_ac)
    also have "Ln (\<i> * (z / 2)) = Ln \<i> + Ln (z / 2)"
      by (subst Ln_times_ii) (use z' z in \<open>auto simp: not_le not_less mult_ac\<close>)
    also have "exp (\<dots> * a) = exp (Ln \<i> * a) * exp (Ln (z / 2) * a)"
      unfolding exp_add ring_distribs by simp
    also have "exp (Ln (z / 2) * a) = (z / 2) powr a"
      using z by (auto simp: powr_def mult_ac)
    also have "\<dots> = (z / 2) powr' a"
      using z by (subst powr'_complex) auto
    also have "exp (Ln \<i> * a) = \<i> powr a"
      by (auto simp: powr_def mult_ac)
    finally show ?thesis
      by (simp add: powr_minus field_simps)
  qed
  thus ?thesis
    using z by (simp add: Bessel_I_def Bessel_J_def power_mult_distrib powr'_complex powr_minus)
qed

lemma Bessel_J_conv_I:
  assumes "a \<in> \<int> \<or> Re x > 0 \<or> Im x \<ge> 0"
  shows "Bessel_J a x = \<i> powr a * Bessel_I a (-\<i> * x)"
  by (subst Bessel_I_conv_J) (use assms in \<open>auto simp: powr_minus\<close>)

lemma sums_Bessel_I:
  fixes a z :: "'a :: {Gamma, ln}"
  shows  "(\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_I a z"
proof -
  have "(\<lambda>n. (z/2) powr' a * (rGamma (a + of_nat (Suc n)) * (z\<^sup>2/4) ^ n / fact n)) sums
          (Bessel_I a z)"
    unfolding Bessel_I_def by (intro sums_mult sums_Bessel_Clifford)
  also have "(\<lambda>n. (z/2) powr' a * (rGamma (a + of_nat (Suc n)) * (z\<^sup>2/4) ^ n / fact n)) =
             (\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n)))"
    unfolding power_mult power2_eq_square
    by (auto simp: fun_eq_iff powr_add power_minus' field_simps rGamma_inverse_Gamma)
  finally show ?thesis .
qed

lemma sums_Bessel_I_complex:
  fixes a z :: complex
  assumes "z \<noteq> 0 \<or> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows  "(\<lambda>n. (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_I a z"
proof -
  have "(\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
           Bessel_I a z"
    by (rule sums_Bessel_I)
  also have "(\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) =
             (\<lambda>n. (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n)))"
    (is "?lhs = ?rhs")
  proof
    fix n :: nat
    from assms have "z \<noteq> 0 \<or> (z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0)"
      by auto
    hence "(z/2) powr' (a + 2 * of_nat n) = (z/2) powr' a * (z/2) ^ (2*n)"
    proof
      assume "z \<noteq> 0"
      thus ?thesis using powr_nat'[of "z/2" "2 * n"]
        by (auto simp: powr'_complex powr_add)
    next
      assume *: "z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
      hence "a + 2 * complex_of_nat n \<noteq> 0"
        by (metis mult_2 of_nat_add plus_of_nat_eq_0_imp)
      thus ?thesis using *
        by (auto simp: powr'_0_left_if)
    qed
    thus "?lhs n = ?rhs n"
      by simp
  qed
  finally show ?thesis .
qed

lemma sums_Bessel_I_real:
  fixes a z :: real
  assumes "a \<in> \<int> \<or> z \<ge> 0" "z \<noteq> 0 \<or> a \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows  "(\<lambda>n. (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n))) sums
            Bessel_I a z"
proof -
  have "(\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) sums
           Bessel_I a z"
    by (rule sums_Bessel_I)
  also have "(\<lambda>n. (z/2) powr' a * (z/2) ^ (2*n) / (fact n * Gamma (1 + a + of_nat n))) =
             (\<lambda>n. (z/2) powr' (a + 2 * of_nat n) / (fact n * Gamma (1 + a + of_nat n)))"
    (is "?lhs = ?rhs")
  proof
    fix n :: nat
    from assms have "z \<noteq> 0 \<or> (z = 0 \<and> a \<notin> \<int>\<^sub>\<le>\<^sub>0)"
      by auto
    have "(z/2) powr' (a + 2 * of_nat n) = (z/2) powr' a * (z/2) ^ (2*n)"
    proof (cases "z = 0")
      case [simp]: True
      with assms(2) have "a + 2 * real n \<noteq> 0"
        by (metis mult.commute mult_2_right of_nat_add plus_of_nat_eq_0_imp)
      thus ?thesis
        using assms by (auto simp: powr'_0_left_if)
    next
      case nz: False
      show ?thesis
      proof (cases "a \<in> \<int>")
        case False
        thus ?thesis using powr_realpow[of "z/2" "2*n"] assms(1)
          using nz by (auto simp: powr'_def powr_add)
      next
        case True
        then obtain k where a_eq: "a = of_int k"
          by (auto elim!: Ints_cases)
        have "(z / 2) powi (int (2*n)) = (z / 2) ^ (2 * n)"
          by (subst power_int_of_nat) auto
        thus ?thesis using nz unfolding of_nat_mult
          by (auto simp: a_eq powr'_def the_int_add power_int_add the_int_mult)
      qed
    qed
    thus "?lhs n = ?rhs n"
      by simp
  qed
  finally show ?thesis .
qed

lemma has_field_derivative_Bessel_I_complex:
  assumes "a \<in> \<int> \<or> (z::complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(Bessel_I a has_field_derivative 
             ((Bessel_I (a-1) z + Bessel_I (a+1) z) / 2)) (at z within A)"
proof (cases "a \<in> \<int>")
  case False
  with assms have "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by auto
  moreover from this have "z \<noteq> 0"
    by auto
  ultimately have "(Bessel_I a has_field_derivative 
                     (a * Bessel_I a z / z + Bessel_I (a+1) z)) (at z within A)"
    unfolding Bessel_I_def
    by (auto intro!: derivative_eq_intros
             simp: complex_nonpos_Reals_iff powr'_complex powr_add field_simps)
  also have "a * Bessel_I a z / z + Bessel_I (a+1) z = (Bessel_I (a-1) z + Bessel_I (a+1) z) / 2"
    using Bessel_I_contiguous_complex[of z "a-1"] \<open>z \<noteq> 0\<close> by (auto simp: field_simps)
  finally show ?thesis .
next
  case True
  then obtain n where a: "a = of_int n"
    by (auto elim: Ints_cases)
  have *: "(Bessel_I a has_field_derivative
           (Bessel_I (a - 1) z + Bessel_I (a + 1) z) / 2) (at z within A)"
    if a: "a = of_int n" "n \<ge> 0" for a n
  proof -
    have a': "a - 1 = of_int (n - 1)" "a + 1 = of_int (n + 1)"
      by (auto simp: a)
    have "((\<lambda>z. (z / 2) powi n * Bessel_Clifford a (z^2/4)) has_field_derivative
            (a / 2 * (z / 2) powi (n-1) * Bessel_Clifford a (z\<^sup>2 / 4) +
            (z / 2) powi (n+1) * Bessel_Clifford (a+1) (z\<^sup>2 / 4))) (at z within A)"
      using a by (auto intro!: derivative_eq_intros simp: power_int_add)
    also have "(a / 2 * (z / 2) powi (n-1) * Bessel_Clifford a (z\<^sup>2 / 4) +
                 (z / 2) powi (n+1) * Bessel_Clifford (a+1) (z\<^sup>2 / 4)) = 
              (Bessel_I (a-1) z + Bessel_I (a+1) z) / 2"
      unfolding Bessel_I_def a' powr'_of_int using a
      by (subst Bessel_Clifford_contiguous[of "of_int (n-1)" "z ^ 2 / 4"], cases "z = 0")
         (auto simp: powr'_complex power_int_0_left_if add_eq_0_iff2 power_int_divide_distrib 
                     power_int_add power_int_diff power2_eq_square field_simps)
    also have "((\<lambda>z. (z / 2) powi n * Bessel_Clifford a (z\<^sup>2 / 4)) has_field_derivative
                 (Bessel_I (a - 1) z + Bessel_I (a + 1) z) / 2) (at z within A) \<longleftrightarrow>
               ((\<lambda>z. Bessel_I a z) has_field_derivative
                 (Bessel_I (a - 1) z + Bessel_I (a + 1) z) / 2) (at z within A)"
    proof (rule has_field_derivative_cong_eventually)
      have "eventually (\<lambda>x. x \<noteq> 0) (at z within A)"
        by (rule eventually_neq_at_within)
      thus "\<forall>\<^sub>F x in at z within A. (x / 2) powi n * Bessel_Clifford a (x\<^sup>2 / 4) = Bessel_I a x"
        unfolding Bessel_I_def by eventually_elim (auto simp: powr'_complex a)
    next
      show "(z / 2) powi n * Bessel_Clifford a (z\<^sup>2 / 4) = Bessel_I a z"
        by (auto simp: Bessel_I_def powr'_complex power_int_0_left_if a)
    qed
    finally show ?thesis .
  qed

  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis using *[of a n] a by simp
  next
    case False
    have "((\<lambda>z. Bessel_I (-of_int n) z) has_field_derivative
            ((Bessel_I ((-of_int n) - 1) z + Bessel_I ((-of_int n) + 1) z) / 2)) (at z within A)"
      by (rule *[of "-of_int n" "-n"]) (use False in auto)
    also have "(\<lambda>z. Bessel_I (-of_int n) z) = Bessel_I a"
      unfolding a by (subst Bessel_I_minus_of_int_complex) auto
    also have "((Bessel_I ((-of_int n) - 1) z + Bessel_I ((-of_int n) + 1) z) / 2) =
               ((Bessel_I (-(of_int (n+1))) z + Bessel_I (-(of_int (n-1))) z) / 2)"
      by simp
    also have "\<dots> = (Bessel_I (a-1) z + Bessel_I (a+1) z) / 2"
      unfolding a
      by (subst (1 2) Bessel_I_minus_of_int_complex) (auto simp: power_int_add power_int_minus_left)
    finally show ?thesis .
  qed
qed

lemma has_field_derivative_Bessel_I_complex' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "a \<in> \<int> \<or> (f x :: complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Bessel_I a (f x)) has_field_derivative 
             (f' * (Bessel_I (a-1) (f x) + Bessel_I (a+1) (f x)) / 2)) (at x within A)"
  using DERIV_chain[OF has_field_derivative_Bessel_I_complex[of a] assms(1)] assms(2)
  by (simp add: o_def mult_ac)

lemma has_field_derivative_Bessel_I_real:
  assumes "a \<in> \<int> \<or> (z :: real) > 0"
  shows   "(Bessel_I a has_field_derivative 
             ((Bessel_I (a-1) z + Bessel_I (a+1) z) / 2)) (at z within A)"
proof -
  have *: "complex_of_real a \<in> \<int> \<or> complex_of_real z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using assms by auto
  have "((\<lambda>x. Re (Bessel_I (of_real a) (of_real x))) has_field_derivative
           (Re (Bessel_I (of_real (a - 1)) (of_real z)) +
            Re (Bessel_I (of_real (a + 1)) (of_real z))) / 2) (at z within A)"
    by (rule derivative_eq_intros has_vector_derivative_real_field refl *)+ simp_all
  also have "(Re (Bessel_I (of_real (a - 1)) (of_real z)) +
              Re (Bessel_I (of_real (a + 1)) (of_real z))) / 2 =
             (Bessel_I (a-1) z + Bessel_I (a+1) z) / 2"
    by (subst (1 2) Bessel_I_complex_of_real) (use assms in auto)
  also have "((\<lambda>x. Re (Bessel_I (of_real a) (of_real x))) has_real_derivative
               (Bessel_I (a - 1) z + Bessel_I (a + 1) z) / 2) (at z within A) \<longleftrightarrow> ?thesis"
  proof (rule has_field_derivative_cong_eventually)
    have "eventually (\<lambda>x. x \<in> (if a \<in> \<int> then UNIV else {0<..})) (nhds z)"
      by (rule eventually_nhds_in_open) (use assms in auto)
    hence ev: "eventually (\<lambda>x. Re (Bessel_I (of_real a) (of_real x)) = Bessel_I a x) (nhds z)"
      by eventually_elim (auto simp: Bessel_I_complex_of_real split: if_splits)
    show "eventually (\<lambda>x. Re (Bessel_I (of_real a) (of_real x)) = Bessel_I a x) (at z within A)"
      using ev by (simp add: eventually_at_filter eventually_mono)
    show "Re (Bessel_I (complex_of_real a) (complex_of_real z)) = Bessel_I a z"
      using ev by (meson eventually_nhds)
  qed
  finally show ?thesis .
qed

lemma has_field_derivative_Bessel_I_real' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "a \<in> \<int> \<or> f x > (0 :: real)"
  shows   "((\<lambda>x. Bessel_I a (f x)) has_field_derivative 
             ((Bessel_I (a-1) (f x) + Bessel_I (a+1) (f x)) / 2) * f') (at x within A)"
  using DERIV_chain[OF has_field_derivative_Bessel_I_real assms(1), of a] assms
  by (simp add: o_def mult_ac)

lemma analytic_Bessel_I [analytic_intros]:
  assumes "a analytic_on A" "b analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> b x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Bessel_I (a x) (b x)) analytic_on A"
  unfolding Bessel_I_def
  by (auto intro!: analytic_intros assms(1,2))
     (use assms(3) in \<open>auto simp: complex_nonpos_Reals_iff\<close>)

lemma analytic_Bessel_I_Ints:
  assumes "b analytic_on A" "a \<in> \<int>"
  shows   "(\<lambda>x. Bessel_I a (b x)) analytic_on A"
proof -
  from \<open>a \<in> \<int>\<close> obtain n where a: "a = of_int n"
    by (elim Ints_cases)
  have *: "(\<lambda>x. Bessel_I (of_int n) (b x)) analytic_on A" if n: "n \<ge> 0" for n
    unfolding Bessel_I_def powr'_of_int by (intro analytic_intros assms(1)) (use n in auto)
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis using *[of n] by (simp add: a)
  next
    case False
    note [analytic_intros del] = analytic_Bessel_I
    have "(\<lambda>x. Bessel_I (of_int (-n)) (b x)) analytic_on A"
      by (intro analytic_intros *) (use False in auto)
    also have "(\<lambda>x. Bessel_I (of_int (-n)) (b x)) = (\<lambda>x. Bessel_I (of_int n) (b x))"
      unfolding of_int_minus by (subst Bessel_I_minus_of_int_complex) (simp flip: mult.assoc)
    finally show ?thesis by (simp add: a)
  qed
qed

theorem Bessel_I_conv_SBessel_I_complex:
  assumes z: "z \<noteq> (0 :: complex)"
  defines "C \<equiv> sqrt (2 / pi) * csqrt z"
  shows   "Bessel_I (of_int n + 1 / 2) z = C * SBessel_I n z"
proof (induction n rule: SBessel_J_induct)
  case 1
  have "Bessel_I (of_int 0 + 1 / 2) z = 
          (z / 2) powr' (1 / 2) * rGamma (3/2) * hypergeo_F [] [3 / 2] (z\<^sup>2 / 4)"
    unfolding Bessel_I_def by (subst Bessel_Clifford_conv_hypergeo_F) auto
  also have "rGamma (3 / 2 :: complex) = 2 * rGamma (1/2)"
    using rGamma_plus1[of "1/2 :: complex"] by simp
  also have "\<dots> = of_real (2 / sqrt pi)"
    unfolding rGamma_inverse_Gamma Gamma_one_half_complex by (simp add: field_simps)
  also have "(z / 2) powr' (1 / 2) = ((1/2) * z) powr (1 / 2)"
    by (auto simp: powr'_def)
  also have "\<dots> = csqrt z / sqrt 2"
    by (subst powr_times_real_left)
       (auto simp: powr_half_sqrt powr_Reals_eq real_sqrt_divide simp flip: csqrt_conv_powr)
  also have "hypergeo_F [] [3/2] (z\<^sup>2/4) = sinh z / z"
    using sinh_conv_hypergeo_F[of z] z by simp
  also have "sinh z / z = SBessel_I 0 z"
    by simp
  also have "csqrt z / complex_of_real (sqrt 2) * complex_of_real (2 / sqrt pi) =
             C"
    using z by (simp add: C_def real_sqrt_divide field_simps flip: power2_eq_square of_real_power)
  finally show ?case
    by simp
next
  case 2
  have "Bessel_I (of_int (-1) + 1 / 2) z = 
          (z / 2) powr' (-1 / 2) * rGamma (1/2) * hypergeo_F [] [1 / 2] (z\<^sup>2 / 4)"
    unfolding Bessel_I_def by (subst Bessel_Clifford_conv_hypergeo_F) auto
  also have "rGamma (1 / 2 :: complex) = of_real (1 / sqrt pi)"
    unfolding rGamma_inverse_Gamma Gamma_one_half_complex by (simp add: field_simps)
  also have "(z / 2) powr' (-1 / 2) = ((1/2) * z) powr (-1 / 2)"
    by (auto simp: powr'_def)
  also have "\<dots> = sqrt 2 * (1 / csqrt z)"
    by (subst powr_times_real_left) 
       (auto simp: powr_minus powr_half_sqrt powr_Reals_eq real_sqrt_divide field_simps 
             simp flip: csqrt_conv_powr)
  also have "1 / csqrt z = csqrt z / z"
    using z by (simp add: field_simps flip: power2_eq_square)
  also have "hypergeo_F [] [1/2] (z\<^sup>2/4) = cosh z"
    using cosh_conv_hypergeo_F[of z] z by simp
  also have "of_real (sqrt 2) * (csqrt z / z) * of_real (1 / sqrt pi) * cosh z =
             of_real (sqrt (2 / pi)) * csqrt z * (cosh z / z)"
    using z by (simp add: field_simps real_sqrt_divide)
  also have "cosh z / z = SBessel_I (-1) z"
    by simp
  finally show ?case
    by (simp add: C_def)
next
  case (3 n)
  have "Bessel_I (of_int n + 1 / 2) z =
          -2 * (of_int n - 1 / 2) / z * Bessel_I (of_int (n - 1) + 1 / 2) z +
          Bessel_I (of_int (n - 2) + 1 / 2) z"
    using Bessel_I_contiguous_complex[of z "of_int n - 3 / 2"] using z
    by (simp add: field_simps)
  also have "-2 * (of_int n - 1 / 2) = -2 * complex_of_int n + 1"
    by (simp add: field_simps)
  also have "Bessel_I (of_int (n - 1) + 1 / 2) z = C * SBessel_I (n - 1) z"
    by (subst "3.IH") auto
  also have "Bessel_I (of_int (n - 2) + 1 / 2) z = C * SBessel_I (n - 2) z"
    by (subst "3.IH") auto
  also have "(-2 * of_int n + 1) / z * (C * SBessel_I (n - 1) z) + C * SBessel_I (n - 2) z = 
               C * SBessel_I n z"
    using "3.hyps" z by (subst (3) SBessel_I.simps) (auto simp: field_simps)
  finally show ?case .
next
  case (4 n)
  have "Bessel_I (of_int n + 1 / 2) z =
           2 * (of_int n + 3 / 2) / z * Bessel_I (of_int (n + 1) + 1 / 2) z +
           Bessel_I (of_int (n + 2) + 1 / 2) z"
    using Bessel_I_contiguous_complex[of z "of_int n + 1 / 2"] using z
    by (simp add: field_simps)
  also have "2 * (of_int n + 3 / 2) = 2 * complex_of_int n + 3"
    by (simp add: field_simps)
  also have "Bessel_I (of_int (n + 1) + 1 / 2) z = C * SBessel_I (n + 1) z"
    by (subst "4.IH") auto
  also have "Bessel_I (of_int (n + 2) + 1 / 2) z = C * SBessel_I (n + 2) z"
    by (subst "4.IH") auto
  also have "(2 * of_int n + 3) / z * (C * SBessel_I (n + 1) z) + C * SBessel_I (n + 2) z =
             C * ((2 * of_int n + 3) / z * SBessel_I (n + 1) z + SBessel_I (n + 2) z)"
    using z by (simp add: field_simps)
  also have "(2 * of_int n + 3) / z * SBessel_I (n + 1) z + SBessel_I (n + 2) z = SBessel_I n z"
    by (subst (2) SBessel_I.simps) (use "4.hyps" in \<open>simp_all add: add_ac\<close>)
  finally show ?case .
qed

lemma Bessel_I_conv_SBessel_I_real:
  assumes z: "z > (0 :: real)"
  shows   "Bessel_I (of_int n + 1 / 2) z = sqrt (2 * z / pi) * SBessel_I n z"
proof -
  have "complex_of_real (Bessel_I (of_int n + 1 / 2) z) = Bessel_I (of_int n + 1 / 2) (of_real z)"
    by (subst Bessel_I_complex_of_real [symmetric]) (use z in auto)
  also have "Bessel_I (of_int n + 1 / 2) (complex_of_real z) = 
               of_real (sqrt (2 * z / pi) * SBessel_I n z)"
    by (subst Bessel_I_conv_SBessel_I_complex) 
       (use z in \<open>auto simp: SBessel_I_of_real real_sqrt_divide real_sqrt_mult\<close>)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed

lemma Bessel_I_pos_real:
  assumes "(x :: real) > 0" "a > -1"
  shows   "Bessel_I a x > 0"
proof -
  define f where "f = (\<lambda>n. (x / 2) powr' (a + 2 * real n) / (fact n * Gamma (1 + a + real n)))"
  have *: "f sums Bessel_I a x"
    unfolding f_def by (rule sums_Bessel_I_real) (use assms in auto)
  have "0 < f 0"
    unfolding f_def using assms
    by (auto intro!: divide_pos_pos simp: powr'_real)
  also have "\<dots> = (\<Sum>n\<in>{0}. f n)"
    by simp
  also have "\<dots> \<le> (\<Sum>n. f n)"
  proof (rule sum_le_suminf)
    show "f n \<ge> 0" for n
      unfolding f_def using assms
      by (intro divide_nonneg_pos mult_pos_pos) (auto simp: powr'_real)
  qed (use * in \<open>auto simp: sums_iff\<close>)
  also have "\<dots> = Bessel_I a x"
    using * by (simp add: sums_iff)
  finally show ?thesis .
qed

lemma Bessel_I_strict_mono_real:
  assumes "0 \<le> x" "x < (y :: real)" "a > 0"
  shows   "Bessel_I a x < Bessel_I a y"
proof (cases "x = 0")
  case True
  thus ?thesis using assms
    by (auto simp: Bessel_I_0_right intro!: Bessel_I_pos_real)
next
  case False
  hence "x > 0"
    using assms by auto
  show ?thesis
  proof (rule DERIV_pos_imp_increasing[where f = "Bessel_I a"])
    fix t assume t: "x \<le> t" "t \<le> y"
    define D where "D = (Bessel_I (a - 1) t + Bessel_I (a + 1) t) / 2"
    have "(Bessel_I a has_real_derivative D) (at t)"
      using t \<open>x > 0\<close> by (auto intro!: derivative_eq_intros simp: D_def)
    moreover have "D > 0" unfolding D_def 
      by (intro divide_pos_pos Bessel_I_pos_real add_pos_pos)
         (use assms t \<open>x > 0\<close> in auto)
    ultimately show "\<exists>D. (Bessel_I a has_real_derivative D) (at t) \<and> D > 0"
      by blast
  qed fact
qed

lemma Bessel_I_mono_real:
  assumes "0 \<le> x" "x \<le> (y :: real)" "a > 0"
  shows   "Bessel_I a x \<le> Bessel_I a y"
  using Bessel_I_strict_mono_real[of x y a] assms by (cases "x = y") auto

(* TODO: add to or replace version in library *)
lemma convex_on_realI_strong:
  assumes "connected A"
    and "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x within A)"
    and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f' x \<le> f' y"
  shows "convex_on A f"
proof (rule convex_on_linorderI)
  show "convex A"
    using \<open>connected A\<close> convex_real_interval interval_cases
    by (smt (verit, ccfv_SIG) connectedD_interval convex_UNIV convex_empty)
      \<comment> \<open>the equivalence of "connected" and "convex" for real intervals is proved later\<close>
next
  fix t x y :: real
  assume t: "t > 0" "t < 1"
  assume xy: "x \<in> A" "y \<in> A" "x < y"
  define z where "z = (1 - t) * x + t * y"
  with \<open>connected A\<close> and xy have ivl: "{x..y} \<subseteq> A"
    using connected_contains_Icc by blast

  from xy t have xz: "z > x"
    by (simp add: z_def algebra_simps)
  have "y - z = (1 - t) * (y - x)"
    by (simp add: z_def algebra_simps)
  also from xy t have "\<dots> > 0"
    by (intro mult_pos_pos) simp_all
  finally have yz: "z < y"
    by simp

  have cont: "continuous_on A f"
    using assms(2) by (intro DERIV_continuous_on)
  have deriv: "(f has_real_derivative f' \<xi>) (at \<xi>)" if \<xi>: "\<xi> \<in> {x<..<y}" for \<xi>
  proof -
    have "(f has_real_derivative f' \<xi>) (at \<xi> within A)"
      by (rule assms) (use \<xi> ivl xz yz in auto)
    moreover have "{x<..<y} \<subseteq> A"
      using ivl by auto
    ultimately have "(f has_real_derivative f' \<xi>) (at \<xi> within {x<..<y})"
      using DERIV_subset by blast
    also have "at \<xi> within {x<..<y} = at \<xi>"
      using \<xi> by (intro at_within_open) auto
    finally show ?thesis .
  qed
  have diff: "f differentiable at \<xi>" if "\<xi> \<in> {x<..<y}" for \<xi>
    using deriv[OF that] real_differentiable_def by blast

  have "\<exists>D \<xi>. \<xi> > x \<and> \<xi> < z \<and> (f has_real_derivative D) (at \<xi>) \<and> f z - f x = (z - x) * D"
    by (rule MVT) (use xz yz ivl in \<open>auto intro!: continuous_on_subset[OF cont] diff\<close>)
  then obtain \<xi> D1 where \<xi>: "\<xi> \<in> {x<..<z}" "(f has_field_derivative D1) (at \<xi>)" "D1 = (f z - f x) / (z - x)"
    by auto
  have "(f has_field_derivative f' \<xi>) (at \<xi>)"
    by (rule deriv) (use \<xi> xy xz yz in auto)
  from DERIV_unique[OF \<xi>(2) this] have [simp]: "D1 = f' \<xi>" .
  
  have "\<exists>D \<eta>. \<eta> > z \<and> \<eta> < y \<and> (f has_real_derivative D) (at \<eta>) \<and> f y - f z = (y - z) * D"
    by (rule MVT) (use xz yz ivl in \<open>auto intro!: continuous_on_subset[OF cont] diff\<close>)
  then obtain D2 \<eta> where \<eta>: "\<eta> \<in> {z<..<y}" "(f has_field_derivative D2) (at \<eta>)" "D2 = (f y - f z) / (y - z)"
    by auto
  have "(f has_field_derivative f' \<eta>) (at \<eta>)"
    by (rule deriv) (use \<eta> xy xz yz in auto)
  from DERIV_unique[OF \<eta>(2) this] have [simp]: "D2 = f' \<eta>" .

  from \<eta> have "(f y - f z) / (y - z) = f' \<eta>"
    by simp
  also from \<xi> \<eta> ivl have "\<xi> \<in> A" "\<eta> \<in> A"
    by auto
  with \<xi> \<eta> have "f' \<eta> \<ge> f' \<xi>"
    by (intro assms(3)) auto
  also from \<xi>(3) have "f' \<xi> = (f z - f x) / (z - x)"
    by simp
  finally have "(f y - f z) * (z - x) \<ge> (f z - f x) * (y - z)"
    using xz yz by (simp add: field_simps)
  also have "z - x = t * (y - x)"
    by (simp add: z_def algebra_simps)
  also have "y - z = (1 - t) * (y - x)"
    by (simp add: z_def algebra_simps)
  finally have "(f y - f z) * t \<ge> (f z - f x) * (1 - t)"
    using xy by simp
  then show "(1 - t) * f x + t * f y \<ge> f ((1 - t) *\<^sub>R x + t *\<^sub>R y)"
    by (simp add: z_def algebra_simps)
qed

(* TODO: could be strengthened to also allow 0 *)
lemma Bessel_I_convex_real:
  assumes "a > 1"
  shows   "convex_on {0<..} (Bessel_I a)"
proof (rule convex_on_realI)
  define f where "f = (\<lambda>x. (Bessel_I (a - 1) x + Bessel_I (a + 1) x) / 2)"
  show "(Bessel_I a has_real_derivative f x) (at x)" if "x \<in> {0<..}" for x
    using that by (auto simp: f_def intro!: derivative_eq_intros)
  show "f x \<le> f y" if "x \<le> y" "x \<in> {0<..}" for x y
    using that unfolding f_def
    by (intro divide_right_mono add_mono Bessel_I_mono_real) (use assms in auto)
qed auto

text \<open>
  The Bessel function of the second kind $Y_a$ and its modified version $K_a$ are easy to derive
  from $J_a$ and $I_a$ whenever $a\notin\mathbb{Z}$, but the case where $a\in\mathbb{Z}$ is more
  tedious to do, so we leave that as future work.
\<close>

end
