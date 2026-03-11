(*
  File:    Prime_Distribution_Elementary_Library.thy
  Author:  Manuel Eberl, TU München

  Various auxiliary material, much of which should probably be moved somewhere else
  eventually.
*)
section \<open>Auxiliary material\<close>
theory Prime_Distribution_Elementary_Library
imports
  Zeta_Function.Zeta_Function
  Prime_Number_Theorem.Prime_Counting_Functions
  Stirling_Formula.Stirling_Formula
begin

lemma pbernpoly_bigo: "pbernpoly n \<in> O(\<lambda>_. 1)"
proof -
  from bounded_pbernpoly[of n] obtain c where "\<And>x. norm (pbernpoly n x) \<le> c"
    by auto
  thus ?thesis by (intro bigoI[of _ c]) auto
qed

(* TODO: move to HOL-Analysis.Harmonic_Numbers *)
lemma harm_le: "n \<ge> 1 \<Longrightarrow> harm n \<le> ln n + 1"
  using euler_mascheroni_sequence_decreasing[of 1 n]
  by (simp add: harm_expand)

(* TODO: Move to HOL.Filter *)
lemma frequently_mono_filter: "frequently P F \<Longrightarrow> F \<le> F' \<Longrightarrow> frequently P F'"
  using filter_leD[of F F' "\<lambda>x. \<not>P x"] by (auto simp: frequently_def)

lemma sum_upto_ln_stirling_weak_bigo: "(\<lambda>x. sum_upto ln x - x * ln x + x) \<in> O(ln)"
proof -
  let ?f = "\<lambda>x. x * ln x - x + ln (2 * pi * x) / 2"
  have "ln (fact n) - (n * ln n - n + ln (2 * pi * n) / 2) \<in> {0..1/(12*n)}" if "n > 0" for n :: nat
    using ln_fact_bounds[OF that] by (auto simp: algebra_simps)
  hence "(\<lambda>n. ln (fact n) - ?f n) \<in> O(\<lambda>n. 1 / real n)"
    by (intro bigoI[of _ "1/12"] eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x. 1 / real (nat \<lfloor>x\<rfloor>))"
    by (rule landau_o.big.compose)
       (intro filterlim_compose[OF filterlim_nat_sequentially] filterlim_floor_sequentially)
  also have "(\<lambda>x. 1 / real (nat \<lfloor>x\<rfloor>)) \<in> O(\<lambda>x::real. ln x)" by real_asymp
  finally have "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f (nat \<lfloor>x\<rfloor>) + (?f (nat \<lfloor>x\<rfloor>) - ?f x)) \<in> O(\<lambda>x. ln x)"
    by (rule sum_in_bigo) real_asymp
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f x) \<in> O(\<lambda>x. ln x)"
    by (simp add: algebra_simps)
  hence "(\<lambda>x. ln (fact (nat \<lfloor>x\<rfloor>)) - ?f x + ln (2 * pi * x) / 2) \<in> O(\<lambda>x. ln x)"
    by (rule sum_in_bigo) real_asymp
  thus ?thesis by (simp add: sum_upto_ln_conv_ln_fact algebra_simps)
qed


subsection \<open>Strengthening `Big-O' bounds\<close>

text \<open>
  The following two statements are crucial: They allow us to strengthen a `Big-O' statement
  for $n\to\infty$ or $x\to\infty$ to a bound for \<^emph>\<open>all\<close> $n\geq n_0$ or all $x\geq x_0$ under
  some mild conditions.

  This allows us to use all the machinery of asymptotics in Isabelle and still get a bound
  that is applicable over the full domain of the function in the end. This is important because
  Newman often shows that $f(x) \in O(g(x))$ and then writes
  \[\sum_{n\leq x} f(\frac{x}{n}) = \sum_{n\leq x} O(g(\frac{x}{n}))\]
  which is not easy to justify otherwise.
\<close>
lemma natfun_bigoE:
  fixes f :: "nat \<Rightarrow> _"
  assumes bigo: "f \<in> O(g)" and nz: "\<And>n. n \<ge> n0 \<Longrightarrow> g n \<noteq> 0"
  obtains c where "c > 0" "\<And>n. n \<ge> n0 \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
proof -
  from bigo obtain c where c: "c > 0" "eventually (\<lambda>n. norm (f n) \<le> c * norm (g n)) at_top"
    by (auto elim: landau_o.bigE)
  then obtain n0' where n0': "\<And>n. n \<ge> n0' \<Longrightarrow> norm (f n) \<le> c * norm (g n)"
    by (auto simp: eventually_at_top_linorder)
  define c' where "c' = Max ((\<lambda>n. norm (f n) / norm (g n)) ` (insert n0 {n0..<n0'}))"
  have "norm (f n) \<le> max 1 (max c c') * norm (g n)" if "n \<ge> n0" for n
  proof (cases "n \<ge> n0'")
    case False
    with that have "norm (f n) / norm (g n) \<le> c'"
      unfolding c'_def by (intro Max.coboundedI) auto
    also have "\<dots> \<le> max 1 (max c c')" by simp
    finally show ?thesis using nz[of n] that by (simp add: field_simps)
  next
    case True
    hence "norm (f n) \<le> c * norm (g n)" by (rule n0')
    also have "\<dots> \<le> max 1 (max c c') * norm (g n)"
      by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  with that[of "max 1 (max c c')"] show ?thesis by auto
qed

lemma bigoE_bounded_real_fun:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<in> O(g)"
  assumes "\<And>x. x \<ge> x0 \<Longrightarrow> \<bar>g x\<bar> \<ge> cg" "cg > 0"
  assumes "\<And>b. b \<ge> x0 \<Longrightarrow> bounded (f ` {x0..b})"
  shows   "\<exists>c>0. \<forall>x\<ge>x0. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
proof -
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top"
    by (elim landau_o.bigE) auto
  then obtain b where b: "\<And>x. x \<ge> b \<Longrightarrow> \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
    by (auto simp: eventually_at_top_linorder)
  have "bounded (f ` {x0..max x0 b})" by (intro assms) auto
  then obtain C where C: "\<And>x. x \<in> {x0..max x0 b} \<Longrightarrow> \<bar>f x\<bar> \<le> C"
    unfolding bounded_iff by fastforce

  define c' where "c' = max c (C / cg)"
  have "\<bar>f x\<bar> \<le> c' * \<bar>g x\<bar>" if "x \<ge> x0" for x
  proof (cases "x \<ge> b")
    case False
    then have "\<bar>f x\<bar> \<le> C"
      using C that by auto
    with False have "\<bar>f x\<bar> / \<bar>g x\<bar> \<le> C / cg"
      by (meson abs_ge_zero assms frac_le landau_omega.R_trans that)
    also have "\<dots> \<le> c'" by (simp add: c'_def)
    finally show "\<bar>f x\<bar> \<le> c' * \<bar>g x\<bar>"
      using that False assms(2)[of x] assms(3) by (auto simp add: divide_simps split: if_splits)
  next
    case True
    hence "\<bar>f x\<bar> \<le> c * \<bar>g x\<bar>" by (intro b) auto
    also have "\<dots> \<le> c' * \<bar>g x\<bar>" by (intro mult_right_mono) (auto simp: c'_def)
    finally show ?thesis .
  qed
  moreover from c(1) have "c' > 0" by (auto simp: c'_def)
  ultimately show ?thesis by blast
qed

lemma sum_upto_asymptotics_lift_nat_real_aux:
  fixes f :: "nat \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes bigo: "(\<lambda>n. (\<Sum>k=1..n. f k) - g (real n)) \<in> O(\<lambda>n. h (real n))"
  assumes g_bigo_self: "(\<lambda>n. g (real n) - g (real (Suc n))) \<in> O(\<lambda>n. h (real n))"
  assumes h_bigo_self: "(\<lambda>n. h (real n)) \<in> O(\<lambda>n. h (real (Suc n)))"
  assumes h_pos: "\<And>x. x \<ge> 1 \<Longrightarrow> h x > 0"
  assumes mono_g: "mono_on {1..} g \<or> mono_on {1..} (\<lambda>x. - g x)"
  assumes mono_h: "mono_on {1..} h \<or> mono_on {1..} (\<lambda>x. - h x)"
  shows   "\<exists>c>0. \<forall>x\<ge>1. sum_upto f x - g x \<le> c * h x"
proof -
  have h_nz: "h (real n) \<noteq> 0" if "n \<ge> 1" for n
    using h_pos[of n] that by simp

  from natfun_bigoE[OF bigo h_nz] obtain c1 where
    c1: "c1 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm ((\<Sum>k=1..n. f k) - g (real n)) \<le> c1 * norm (h (real n))"
    by auto
  from natfun_bigoE[OF g_bigo_self h_nz] obtain c2 where
    c2: "c2 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm (g (real n) - g (real (Suc n))) \<le> c2 * norm (h (real n))"
    by auto
  from natfun_bigoE[OF h_bigo_self h_nz] obtain c3 where
    c3: "c3 > 0" "\<And>n. n \<ge> 1 \<Longrightarrow> norm (h (real n)) \<le> c3 * norm (h (real (Suc n)))"
    by auto

  {
    fix x :: real assume x: "x \<ge> 1"
    define n where "n = nat \<lfloor>x\<rfloor>"
    from x have n: "n \<ge> 1" unfolding n_def by linarith

    have "(\<Sum>k = 1..n. f k) - g x \<le> (c1 + c2) * h (real n)" using mono_g
    proof
      assume mono: "mono_on {1..} (\<lambda>x. -g x)"
      from x have "x \<le> real (Suc n)"
        unfolding n_def by linarith
      hence "(\<Sum>k=1..n. f k) - g x \<le> (\<Sum>k=1..n. f k) - g n + (g n - g (Suc n))"
        using mono_onD[OF mono, of x "real (Suc n)"] x by auto
      also have "\<dots> \<le> norm ((\<Sum>k=1..n. f k) - g n) + norm (g n - g (Suc n))"
        by simp
      also have "\<dots> \<le> c1 * norm (h n) + c2 * norm (h n)"
        using n by (intro add_mono c1 c2) auto
      also have "\<dots> = (c1 + c2) * h n"
        using h_pos[of "real n"] n by (simp add: algebra_simps)
      finally show ?thesis .
    next
      assume mono: "mono_on {1..} g"
      have "(\<Sum>k=1..n. f k) - g x \<le> (\<Sum>k=1..n. f k) - g n"
        using x by (intro diff_mono mono_onD[OF mono]) (auto simp: n_def)
      also have "\<dots> \<le> c1 * h (real n)"
        using c1(2)[of n] n h_pos[of n] by simp
      also have "\<dots> \<le> (c1 + c2) * h (real n)"
        using c2 h_pos[of n] n by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    also have "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x"
      using mono_h
    proof
      assume mono: "mono_on {1..} (\<lambda>x. -h x)"
      have "(c1 + c2) * h (real n) \<le> (c1 + c2) * (c3 * h (real (Suc n)))"
        using c3(2)[of n] n h_pos[of n] h_pos[of "Suc n"] c1(1) c2(1)
        by (intro mult_left_mono) (auto)
      also have "\<dots> = (c1 + c2) * c3 * h (real (Suc n))"
        by (simp add: mult_ac)
      also have "\<dots> \<le> (c1 + c2) * (1 + c3) * h (real (Suc n))"
        using c1(1) c2(1) c3(1) h_pos[of "Suc n"] by (intro mult_left_mono mult_right_mono) auto
      also from x have "x \<le> real (Suc n)"
        unfolding n_def by linarith
      hence "(c1 + c2) * (1 + c3) * h (real (Suc n)) \<le> (c1 + c2) * (1 + c3) * h x"
        using c1(1) c2(1) c3(1) mono_onD[OF mono, of x "real (Suc n)"] x
        by (intro mult_left_mono) (auto simp: n_def)
      finally show "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x" .
    next
      assume mono: "mono_on {1..} h"
      have "(c1 + c2) * h (real n) = 1 * ((c1 + c2) * h (real n))" by simp
      also have "\<dots> \<le> (1 + c3) * ((c1 + c2) * h (real n))"
        using c1(1) c2(1) c3(1) h_pos[of n] x n by (intro mult_right_mono) auto
      also have "\<dots> = (1 + c3) * (c1 + c2) * h (real n)"
        by (simp add: mult_ac)
      also have "\<dots> \<le> (1 + c3) * (c1 + c2) * h x"
        using x c1(1) c2(1) c3(1) h_pos[of n] n
        by (intro mult_left_mono mono_onD[OF mono]) (auto simp: n_def)
      finally show "(c1 + c2) * h (real n) \<le> (c1 + c2) * (1 + c3) * h x"
        by (simp add: mult_ac)
    qed
    also have "(\<Sum>k = 1..n. f k) = sum_upto f x"
      unfolding sum_upto_altdef n_def by (intro sum.cong) auto
    finally have "sum_upto f x - g x \<le> (c1 + c2) * (1 + c3) * h x" .
  }
  moreover have "(c1 + c2) * (1 + c3) > 0"
    using c1(1) c2(1) c3(1) by (intro mult_pos_pos add_pos_pos) auto
  ultimately show ?thesis by blast
qed

lemma sum_upto_asymptotics_lift_nat_real:
  fixes f :: "nat \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes bigo: "(\<lambda>n. (\<Sum>k=1..n. f k) - g (real n)) \<in> O(\<lambda>n. h (real n))"
  assumes g_bigo_self: "(\<lambda>n. g (real n) - g (real (Suc n))) \<in> O(\<lambda>n. h (real n))"
  assumes h_bigo_self: "(\<lambda>n. h (real n)) \<in> O(\<lambda>n. h (real (Suc n)))"
  assumes h_pos: "\<And>x. x \<ge> 1 \<Longrightarrow> h x > 0"
  assumes mono_g: "mono_on {1..} g \<or> mono_on {1..} (\<lambda>x. - g x)"
  assumes mono_h: "mono_on {1..} h \<or> mono_on {1..} (\<lambda>x. - h x)"
  shows   "\<exists>c>0. \<forall>x\<ge>1. \<bar>sum_upto f x - g x\<bar> \<le> c * h x"
proof -
  have "\<exists>c>0. \<forall>x\<ge>1. sum_upto f x - g x \<le> c * h x"
    by (intro sum_upto_asymptotics_lift_nat_real_aux assms)
  then obtain c1 where c1: "c1 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> sum_upto f x - g x \<le> c1 * h x"
    by auto

  have "(\<lambda>n. -(g (real n) - g (real (Suc n)))) \<in> O(\<lambda>n. h (real n))"
    by (subst landau_o.big.uminus_in_iff) fact
  also have "(\<lambda>n. -(g (real n) - g (real (Suc n)))) = (\<lambda>n. g (real (Suc n)) - g (real n))"
    by simp
  finally have "(\<lambda>n. g (real (Suc n)) - g (real n)) \<in> O(\<lambda>n. h (real n))" .
  moreover {
    have "(\<lambda>n. -((\<Sum>k=1..n. f k) - g (real n))) \<in> O(\<lambda>n. h (real n))"
      by (subst landau_o.big.uminus_in_iff) fact
    also have "(\<lambda>n. -((\<Sum>k=1..n. f k) - g (real n))) =
                 (\<lambda>n. (\<Sum>k=1..n. -f k) + g (real n))" by (simp add: sum_negf)
    finally have "(\<lambda>n. (\<Sum>k=1..n. - f k) + g (real n)) \<in> O(\<lambda>n. h (real n))" .
  }
  ultimately have "\<exists>c>0. \<forall>x\<ge>1. sum_upto (\<lambda>n. -f n) x - (-g x) \<le> c * h x" using mono_g
    by (intro sum_upto_asymptotics_lift_nat_real_aux assms) (simp_all add: disj_commute)
  then obtain c2 where c2: "c2 > 0" "\<And>x. x \<ge> 1 \<Longrightarrow> sum_upto (\<lambda>n. - f n) x + g x \<le> c2 * h x"
    by auto

  {
    fix x :: real assume x: "x \<ge> 1"
    have "sum_upto f x - g x \<le> max c1 c2 * h x"
      using h_pos[of x] x by (intro order.trans[OF c1(2)] mult_right_mono) auto
    moreover have "sum_upto (\<lambda>n. -f n) x + g x \<le> max c1 c2 * h x"
      using h_pos[of x] x by (intro order.trans[OF c2(2)] mult_right_mono) auto
    hence "-(sum_upto f x - g x) \<le> max c1 c2 * h x"
      by (simp add: sum_upto_def sum_negf)
    ultimately have "\<bar>sum_upto f x - g x\<bar> \<le> max c1 c2 * h x" by linarith
  }
  moreover from c1(1) c2(1) have "max c1 c2 > 0" by simp
  ultimately show ?thesis by blast
qed

(* TODO: Move to HOL_Computational_Algebra.Factorial_Ring *)
lemma (in factorial_semiring) primepow_divisors_induct [case_names zero unit factor]:
  assumes "P 0" "\<And>x. is_unit x \<Longrightarrow> P x"
          "\<And>p k x. prime p \<Longrightarrow> k > 0 \<Longrightarrow> \<not>p dvd x \<Longrightarrow> P x \<Longrightarrow> P (p ^ k * x)"
  shows   "P x"
proof -
  have "finite (prime_factors x)" by simp
  thus ?thesis
  proof (induction "prime_factors x" arbitrary: x rule: finite_induct)
    case empty
    hence "prime_factors x = {}" by metis
    hence "prime_factorization x = {#}" by simp
    thus ?case using assms(1,2) by (auto simp: prime_factorization_empty_iff)
  next
    case (insert p A x)
    define k where "k = multiplicity p x"
    have "k > 0" using insert.hyps
      by (auto simp: prime_factors_multiplicity k_def)
    have p: "p \<in> prime_factors x" using insert.hyps by auto
    from p have "x \<noteq> 0" "\<not>is_unit p" by (auto simp: in_prime_factors_iff)

    from multiplicity_decompose'[OF this] obtain y where y: "x = p ^ k * y" "\<not>p dvd y"
      by (auto simp: k_def)
    have "prime_factorization x = replicate_mset k p + prime_factorization y"
      using p \<open>k > 0\<close> y unfolding y
      by (subst prime_factorization_mult)
         (auto simp: prime_factorization_prime_power in_prime_factors_iff)
    moreover from y p have "p \<notin> prime_factors y"
      by (auto simp: in_prime_factors_iff)
    ultimately have "prime_factors y = prime_factors x - {p}"
      by auto
    also have "\<dots> = A"
      using insert.hyps by auto
    finally have "P y" using insert by auto
    thus "P x"
      unfolding y using y \<open>k > 0\<close> p by (intro assms(3)) (auto simp: in_prime_factors_iff)
  qed
qed

end