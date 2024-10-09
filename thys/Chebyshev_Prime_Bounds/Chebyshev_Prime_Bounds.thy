theory Chebyshev_Prime_Bounds
imports
  "Prime_Number_Theorem.Prime_Counting_Functions"
  "Prime_Distribution_Elementary.Prime_Distribution_Elementary_Library"
  "Prime_Distribution_Elementary.Primorial"
  "HOL-Decision_Procs.Approximation"
  "HOL-Library.Code_Target_Numeral"
  Chebyshev_Prime_Exhaust
begin

subsection \<open>Auxiliary material\<close>

context comm_monoid_set
begin

lemma union_disjoint':
  assumes "finite C" "A \<union> B = C" "A \<inter> B = {}"
  shows   "f (F g A) (F g B) = F g C"
  using union_disjoint[of A B g] assms by auto

end

lemma sum_mset_nonneg:
  fixes X :: "'a :: ordered_comm_monoid_add multiset"
  shows "(\<And>x. x \<in># X \<Longrightarrow> x \<ge> 0) \<Longrightarrow> sum_mset X \<ge> 0"
  by (induction X) (auto)

lemma of_int_sum_mset: "of_int (sum_mset M) = sum_mset (image_mset of_int M)"
  by (induction M) auto

lemma sum_sum_mset: "(\<Sum>x\<in>A. \<Sum>y\<in>#B. f x y) = (\<Sum>y\<in>#B. \<Sum>x\<in>A. f x y)"
  by (induction B) (auto simp: algebra_simps sum.distrib)

lemma sum_mset_diff_distrib:
  fixes f g :: "'a \<Rightarrow> 'b :: ab_group_add"
  shows   "(\<Sum>x\<in>#A. f x - g x) = (\<Sum>x\<in>#A. f x) - (\<Sum>x\<in>#A. g x)"
  by (induction A) (auto simp: algebra_simps)

lemma sum_mset_neg_distrib:
  fixes f :: "'a \<Rightarrow> 'b :: ab_group_add"
  shows   "(\<Sum>x\<in>#A. -f x) = -(\<Sum>x\<in>#A. f x)"
  by (induction A) (auto simp: algebra_simps)


subsection \<open>Bounds for the remainder in Stirling's approximation\<close>

definition ln_fact_remainder :: "real \<Rightarrow> real" where
  "ln_fact_remainder x = ln (fact (nat \<lfloor>x\<rfloor>)) - (x * ln x - x)"

lemma ln_fact_remainder_bounds:
  assumes x: "x \<ge> 3"
  shows "ln_fact_remainder x \<le>  ln x / 2 + ln (2 * pi) / 2 + 1 / (12 * \<lfloor>x\<rfloor>)"
    and "ln_fact_remainder x \<ge> -ln x / 2 + ln (2 * pi) / 2 - 1 / (2 * x)"
proof -
  define n where "n = nat \<lfloor>x\<rfloor>"
  define f where "f = (\<lambda>t. t * (ln t - 1) + ln t / 2 :: real)"

  have "ln \<lfloor>x\<rfloor> \<ge> 1"
  proof -
    have "1 \<le> ln (3 :: real)"
      by (approximation 10)
    also have "ln 3 \<le> ln \<lfloor>x\<rfloor>"
      using assms by simp
    finally show ?thesis .
  qed 

  have n: "n \<ge> 1"
    using x by (auto simp: n_def le_nat_iff)
  have "ln_fact_remainder x = ln (fact n) + ln x / 2 - f x"
    by (simp add: ln_fact_remainder_def n_def f_def algebra_simps)
  also have "ln (fact n) \<le> ln (2 * pi) / 2 + f n + 1 / (12 * n)"
    using ln_fact_bounds(2)[of n] n by (auto simp: f_def ln_mult add_divide_distrib algebra_simps)
  also have "\<dots> + ln x / 2 - f x = ln x / 2 + (f n - f x) + ln (2 * pi) / 2 + 1 / (12 * n)"
    using n by (simp add: algebra_simps ln_mult)
  also have "f n \<le> f x"
    unfolding f_def using assms \<open>ln \<lfloor>x\<rfloor> \<ge> 1\<close>
    by (intro add_mono mult_mono) (auto simp: n_def)
  finally show "ln_fact_remainder x \<le> ln x / 2 + ln (2 * pi) / 2 + 1 / (12 * \<lfloor>x\<rfloor>)"
    using assms by (simp add: n_def)

  define f' :: "real \<Rightarrow> real" where "f' = (\<lambda>x. ln x + 1 / (2 * x))"
  have f'_mono: "f' x \<le> f' y" if "x \<le> y" "x \<ge> 1 / 2" for x y :: real
    using that(1)
  proof (rule DERIV_nonneg_imp_nondecreasing)
    fix t assume t: "t \<ge> x" "t \<le> y"
    hence "t > 0"
      using \<open>x \<ge> 1 / 2\<close> by auto
    have "(t - 1 / 2) / t ^ 2 \<ge> 0"
      using t that by auto
    have "(f' has_field_derivative (1 / t - 1 / (2 * t ^ 2))) (at t)"
      using \<open>t > 0\<close> by (auto simp: f'_def power2_eq_square intro!: derivative_eq_intros)
    also have "1 / t - 1 / (2 * t ^ 2) = (t - 1 / 2) / t ^ 2"
      using \<open>t > 0\<close> by (simp add: field_simps eval_nat_numeral del: div_diff)
    finally show "\<exists>y. (f' has_real_derivative y) (at t) \<and> 0 \<le> y"
      using \<open>(t - 1 / 2) / t ^ 2 \<ge> 0\<close> by blast
  qed

  have f'_nonneg: "f' t \<ge> 0" if "t \<ge> 3" for t
  proof -
    have "0 \<le> f' 3"
      unfolding f'_def by (approximation 10)
    also have "f' 3 \<le> f' t"
      by (rule f'_mono) (use that in auto)
    finally show ?thesis .
  qed

  have "f x - f n \<le> f' x * frac x"
  proof (cases "n < x")
    case False
    hence "x = n"
      using assms unfolding n_def by linarith
    thus ?thesis using f'_nonneg[of x] assms
      by (simp add: n_def)
  next
    case True
    have "\<exists>z::real. z > n \<and> z < x \<and> f x - f n = (x - n) * f' z"
      using True assms n
      by (intro MVT2) (auto intro!: derivative_eq_intros simp: f_def f'_def)
    then obtain z :: real where z: "z > n" "z < x" "f x - f n = (x - n) * f' z"
      by blast
    have "f' z \<le> f' x"
      by (rule f'_mono) (use z assms n in auto)

    have "f x - f n = (x - n) * f' z"
      by fact
    also have "\<dots> \<le> (x - n) * f' x"
      using \<open>f' z \<le> f' x\<close> True by (intro mult_left_mono ) auto
    also have "x - n = frac x"
      using assms by (simp add: n_def frac_def)
    finally show ?thesis
      by (simp add: mult_ac)
  qed

  also have "\<dots> \<le> f' x * 1"
    using frac_lt_1[of x] f'_nonneg[of x] assms
    by (intro mult_left_mono) auto
  finally have "f n - f x \<ge> -1 / (2 * x) - ln x"
    by (simp add: f'_def)

  have "-ln x / 2 - 1 / (2 * x) + ln (2 * pi) / 2 = 
        ln x / 2 + (-1 / (2 * x) - ln x) + ln (2 * pi) / 2"
    by (simp add: algebra_simps)
  also have "-1 / (2 * x) - ln x \<le> f n - f x"
    by fact
  also have "ln x / 2 + (f n - f x) + ln (2 * pi) / 2 =
          ln (2 * pi) / 2 + f n + ln x / 2 - f x"
    by (simp add: algebra_simps)
  also have "ln (2 * pi) / 2 + f n \<le> ln (fact n)"
    using ln_fact_bounds(1)[of n] n by (auto simp: f_def ln_mult add_divide_distrib algebra_simps)
  also have "ln (fact n) + ln x / 2 - f x = ln_fact_remainder x"
    by (simp add: ln_fact_remainder_def f_def n_def algebra_simps)
  finally show "ln_fact_remainder x \<ge> -ln x / 2 + ln (2 * pi) / 2 - 1 / (2 * x)"
    by simp
qed

lemma abs_ln_fact_remainder_bounds:
  assumes x: "x \<ge> 3"
  shows "\<bar>ln_fact_remainder x\<bar> < ln x / 2 + 1"
proof -
  have "ln_fact_remainder x \<le> ln x / 2 + (ln (2 * pi) / 2 + 1 / (12 * \<lfloor>x\<rfloor>))"
    using ln_fact_remainder_bounds(1)[of x] assms by (simp add: algebra_simps)
  also have "1 / (12 * \<lfloor>x\<rfloor>) \<le> 1 / 36"
    using assms by auto
  also have "ln (2 * pi) / 2 + 1 / 36 < 1"
    by (approximation 10)
  finally have less: "ln_fact_remainder x < ln x / 2 + 1"
    by simp

  have "-(ln x / 2 + 1) = -ln x / 2 + (-1)"
    by simp
  also have "-1 < 0 - 1 / (2 * x)"
    using assms by simp
  also have "0 \<le> ln (2 * pi) / 2"
    using pi_gt3 by simp
  also have "-ln x / 2 + (ln (2 * pi) / 2 - 1 / (2 * x)) \<le> ln_fact_remainder x"
    using ln_fact_remainder_bounds(2)[of x] assms by (simp add: algebra_simps)
  finally have "- (ln x / 2 + 1) < ln_fact_remainder x" by - simp_all
  with less show ?thesis
    by linarith
qed


subsection \<open>Approximating \<open>\<psi>\<close>\<close>

unbundle prime_counting_syntax

lemma primes_psi_lower_rec:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<And>x. x \<ge> x0 \<Longrightarrow> f x \<le> f (x / c) + h x"
  assumes  "x0 > 0" "x * c \<ge> x0 * c ^ n" "c \<ge> 1"
  shows   "f x \<le> f (x / c ^ n) + (\<Sum>k<n. h (x / c ^ k))"
  using assms(2-)
proof (induction n arbitrary: x)
  case 0
  thus ?case by auto
next
  case (Suc n)
  have "0 < x0 * c ^ n"
    using Suc.prems by auto
  also have "\<dots> \<le> x"
    using Suc.prems by auto
  finally have "x > 0" .

  have "x0 * c ^ n \<le> 1 * x"
    using Suc.prems by simp
  also have "1 * x \<le> c * x"
    by (rule mult_right_mono) (use Suc.prems \<open>x > 0\<close> in auto)
  finally have "f x \<le> f (x / c ^ n) + (\<Sum>k<n. h (x / c ^ k))"
    by (intro Suc.IH) (use Suc.prems in \<open>auto simp: mult_ac\<close>)
  also have "f (x / c ^ n) \<le> f (x / c ^ n / c) + h (x / c ^ n)"
    by (rule assms(1)) (use Suc.prems \<open>x > 0\<close> in \<open>auto simp: field_simps less_imp_le\<close>)
  finally show ?case
    by (simp add: mult_ac add_ac)
qed


locale chebyshev_multiset =
  fixes L :: "int multiset"
  assumes L_nonzero: "0 \<notin># L"
begin

definition chi_L :: "real \<Rightarrow> int" ("\<chi>\<^sub>L")
  where "chi_L t = (\<Sum>l\<in>#L. sgn l * \<lfloor>t / \<bar>l\<bar>\<rfloor>)"

definition psi_L :: "real \<Rightarrow> real" ("\<psi>\<^sub>L")
  where "psi_L x = sum_upto (\<lambda>d. mangoldt d * chi_L (x / d)) x"

definition alpha_L :: real ("\<alpha>\<^sub>L")
  where "alpha_L = -(\<Sum>l\<in>#L. ln \<bar>l\<bar> / l)"

definition period :: nat
  where "period = nat (Lcm (set_mset L))"

lemma period_pos: "period > 0"
proof -
  have "Lcm (set_mset L) \<noteq> 0"
    using L_nonzero unfolding period_def by (subst Lcm_0_iff) auto
  moreover have "Lcm (set_mset L) \<ge> 0"
    by auto
  ultimately have "Lcm (set_mset L) > 0"
    by linarith
  thus ?thesis
    by (simp add: period_def)
qed

lemma dvd_period: "l \<in># L \<Longrightarrow> l dvd period"
  unfolding period_def by auto

lemma chi_L_decompose:
  "\<chi>\<^sub>L (x + of_int (m * int period)) = \<chi>\<^sub>L x + m * int period * (\<Sum>l\<in>#L. 1 / l)"
proof -
  have "real_of_int (\<chi>\<^sub>L (x + of_int (m * int period))) = 
          (\<Sum>l\<in>#L. of_int (sgn l * \<lfloor>(x + of_int m * real period) / real_of_int \<bar>l\<bar>\<rfloor>))"
    by (simp add: chi_L_def of_int_sum_mset multiset.map_comp o_def)
  also have "\<dots> = (\<Sum>l\<in>#L. real_of_int (sgn l * (\<lfloor>x / of_int \<bar>l\<bar>\<rfloor>)) + m * period / l)"
  proof (intro arg_cong[of _ _ sum_mset] image_mset_cong, goal_cases)
    case (1 l)
    with L_nonzero have [simp]: "l \<noteq> 0"
      by auto
    have "(x + of_int m * real period) / real_of_int \<bar>l\<bar> =
           x / of_int \<bar>l\<bar> + of_int (m * period div \<bar>l\<bar>)"
      using dvd_period[of l] 1 by (subst real_of_int_div) (auto simp: field_simps)
    also have "floor \<dots> = \<lfloor>x / of_int \<bar>l\<bar> :: real\<rfloor> + m * period div \<bar>l\<bar>"
      by (subst floor_add_int) auto
    also have "real_of_int \<dots> = \<lfloor>x / of_int \<bar>l\<bar>\<rfloor> + m * period / \<bar>l\<bar>"
      using dvd_period[of l] 1 by (simp add: real_of_int_div)
    also have "sgn l * \<dots> = sgn l * \<lfloor>x / of_int \<bar>l\<bar>\<rfloor> + m * period / l"
      by (simp add: sgn_if)
    finally show ?case
      by simp
  qed
  also have "\<dots> = of_int (\<chi>\<^sub>L x) + (\<Sum>l\<in>#L. m * period / l)"
    by (subst sum_mset.distrib)
       (auto simp: chi_L_def of_int_sum_mset multiset.map_comp o_def)
  also have "(\<Sum>l\<in>#L. m * period / l) = m * period * (\<Sum>l\<in>#L. 1 / l)"
    by (simp add: sum_mset_distrib_left)
  finally show ?thesis
    by simp
qed

lemma chi_L_floor: "chi_L (floor x) = chi_L x"
  unfolding chi_L_def
proof (intro arg_cong[of _ _ sum_mset] image_mset_cong, goal_cases)
  case (1 l)
  thus ?case
    using floor_divide_real_eq_div[of "\<bar>l\<bar>" x] floor_divide_of_int_eq[of "\<lfloor>x\<rfloor>" "\<bar>l\<bar>"]
    by auto
qed  
    
end


locale balanced_chebyshev_multiset = chebyshev_multiset +
  assumes balanced: "(\<Sum>l\<in>#L. 1 / l) = 0"
begin

lemma chi_L_mod: "\<chi>\<^sub>L (of_int (a mod int period)) = \<chi>\<^sub>L (of_int a)"
proof -
  have a: "a = a mod period + period * (a div period)"
    by simp
  have "of_int a = real_of_int (a mod int period) +
                   real_of_int (a div int period * int period)"
    by (subst a, unfold of_int_add) auto
  also have "real_of_int (\<chi>\<^sub>L \<dots>) = real_of_int (\<chi>\<^sub>L (real_of_int (a mod int period)))"
    using balanced by (subst chi_L_decompose) auto
  finally show ?thesis
    by linarith
qed

sublocale chi: periodic_fun_simple chi_L "of_int period"
proof
  fix x :: real
  have "\<chi>\<^sub>L (x + real_of_int (int period)) = \<chi>\<^sub>L (of_int (\<lfloor>x + real_of_int (int period)\<rfloor> mod int period))"
    unfolding chi_L_mod chi_L_floor ..
  also have "\<lfloor>x + real_of_int (int period)\<rfloor> mod int period = \<lfloor>x\<rfloor> mod int period"
    by simp
  also have "\<chi>\<^sub>L \<dots> = \<chi>\<^sub>L x"
    by (simp add: chi_L_mod chi_L_floor)
  finally show "\<chi>\<^sub>L (x + real_of_int (int period)) = \<chi>\<^sub>L x" .
qed


definition psi_L_remainder where
  "psi_L_remainder x = (\<Sum>l\<in>#L. sgn l * ln_fact_remainder (x / \<bar>l\<bar>))"

lemma abs_sum_mset_le:
  fixes f :: "'a \<Rightarrow> 'b :: ordered_ab_group_add_abs"
  shows "\<bar>\<Sum>x\<in>#A. f x\<bar> \<le> (\<Sum>x\<in>#A. \<bar>f x\<bar>)"
  by (induction A) (auto intro: order.trans[OF abs_triangle_ineq])

lemma psi_L_remainder_bounds:
  fixes x :: real
  assumes x: "x \<ge> 3" "\<And>l. l \<in># L \<Longrightarrow> x \<ge> 3 * \<bar>l\<bar>"
  shows "\<bar>psi_L_remainder x\<bar> \<le>
           ln x * size L / 2 - 1/2 * (\<Sum>l\<in>#L. ln \<bar>l\<bar>) + size L"
proof -
  have nonzero: "l \<noteq> 0" if "l \<in># L" for l
    using L_nonzero that by auto
  have "psi_L_remainder x = (\<Sum>l\<in>#L. sgn l * ln_fact_remainder (x / \<bar>l\<bar>))"
    by (simp add: psi_L_remainder_def)
  also have "\<bar>\<dots>\<bar> \<le> (\<Sum>l\<in>#L. \<bar>sgn l * ln_fact_remainder (x / \<bar>l\<bar>)\<bar>)"
    by (rule abs_sum_mset_le)
  also have "\<dots> = (\<Sum>l\<in>#L. \<bar>ln_fact_remainder (x / \<bar>l\<bar>)\<bar>)"
    by (intro arg_cong[of _ _ sum_mset] image_mset_cong)
       (auto simp: nonzero abs_mult simp flip: of_int_abs)
  also have "\<dots> \<le> (\<Sum>l\<in>#L. ln (x / \<bar>l\<bar>) / 2 + 1)"
    using x
    by (intro sum_mset_mono less_imp_le[OF abs_ln_fact_remainder_bounds])
       (auto simp: nonzero field_simps)
  also have "\<dots> = (\<Sum>l\<in>#L. 1 / 2 * (ln x - ln \<bar>l\<bar>) + 1)"
    using assms
    by (intro arg_cong[of _ _ sum_mset] image_mset_cong) (auto simp: algebra_simps ln_div nonzero)
  also have "\<dots> = ln x / 2 * size L + (-1/2) * (\<Sum>l\<in>#L. ln \<bar>l\<bar>) + size L"
    unfolding sum_mset_distrib_left of_int_sum_mset
    by (simp add: sum_mset.distrib sum_mset_diff_distrib diff_divide_distrib sum_mset_neg_distrib)
  finally show ?thesis
    using assms by (simp add: mult_left_mono divide_right_mono add_mono)
qed  

lemma psi_L_eq:
  assumes "x > 0"
  shows   "psi_L x = \<alpha>\<^sub>L * x + psi_L_remainder x"
proof -
  have "psi_L x = (\<Sum>l\<in>#L. sgn l *
          sum_upto (\<lambda>d. mangoldt d * \<lfloor>x / (d * \<bar>l\<bar>)\<rfloor>) x)"
    by (simp add: psi_L_def chi_L_def sum_upto_def sum_mset_distrib_left of_int_sum_mset
          multiset.map_comp o_def sum_sum_mset algebra_simps sum_distrib_left sum_distrib_right)
  also have "\<dots> = (\<Sum>l\<in>#L. sgn l *
          sum_upto (\<lambda>d. mangoldt d * \<lfloor>x / (d * \<bar>l\<bar>)\<rfloor>) (x / \<bar>l\<bar>))"
  proof (intro arg_cong[of _ _ sum_mset] image_mset_cong, goal_cases)
    case (1 l)
    have "l \<noteq> 0"
      using 1 L_nonzero by auto

    have "sum_upto (\<lambda>d. mangoldt d * real_of_int \<lfloor>x / real_of_int (int d * \<bar>l\<bar>)\<rfloor>) (x / real_of_int \<bar>l\<bar>) =
          sum_upto (\<lambda>d. mangoldt d * real_of_int \<lfloor>x / real_of_int (int d * \<bar>l\<bar>)\<rfloor>) x"
      unfolding sum_upto_def
    proof (intro sum.mono_neutral_left subsetI ballI, goal_cases)
      case (2 d)
      hence "real d \<le> x / \<bar>real_of_int l\<bar>"
        by auto
      also have "\<dots> \<le> x / 1"
        using \<open>l \<noteq> 0\<close> and assms by (intro divide_left_mono) auto
      finally show ?case
        using 2 by auto
    next
      case (3 d)
      hence "x < d * \<bar>l\<bar>" and "d > 0"
        using \<open>l \<noteq> 0\<close> and assms by (auto simp: field_simps)
      hence "x / real_of_int (int d * \<bar>l\<bar>) \<ge> 0" and "x / real_of_int (int d * \<bar>l\<bar>) < 1"
        using assms by auto
      hence "\<lfloor>x / real_of_int (int d * \<bar>l\<bar>)\<rfloor> = 0"
        by linarith
      thus ?case
        by simp
    qed auto
    thus ?case
      by simp
  qed

  also have "\<dots> = (\<Sum>l\<in>#L. sgn l * ln (fact (nat \<lfloor>x/\<bar>l\<bar>\<rfloor>)))"
    by (subst ln_fact_conv_sum_mangoldt [symmetric]) (auto simp: mult_ac)

  also have "\<dots> = (\<Sum>l\<in>#L. x / l * ln x - x * ln \<bar>l\<bar> / l - x / l + sgn l * ln_fact_remainder (x / \<bar>l\<bar>))"
  proof (intro arg_cong[of _ _ sum_mset] image_mset_cong, goal_cases)
    case (1 l)
    hence [simp]: "l \<noteq> 0"
      using L_nonzero by auto
    have "ln (fact (nat \<lfloor>x/\<bar>l\<bar>\<rfloor>)) = x / \<bar>l\<bar> * ln (x / \<bar>l\<bar>) - x / \<bar>l\<bar> + ln_fact_remainder (x / \<bar>l\<bar>)"
      by (simp add: ln_fact_remainder_def)
    also have "real_of_int (sgn l) * \<dots> = x / l * ln x - x * ln \<bar>l\<bar> / l - x / l + sgn l * ln_fact_remainder (x / \<bar>l\<bar>)"
      using assms by (auto simp: sgn_if ln_div diff_divide_distrib algebra_simps)
    finally show ?case .
  qed
  also have "\<dots> = (x * ln x - x) * (\<Sum>l\<in>#L. 1 / l) - x * (\<Sum>l\<in>#L. ln \<bar>l\<bar> / l) + (\<Sum>l\<in>#L. sgn l * ln_fact_remainder (x / \<bar>l\<bar>))"
    by (simp add: sum_mset.distrib sum_mset_diff_distrib sum_mset_distrib_left diff_divide_distrib)
  also have "\<dots> = \<alpha>\<^sub>L * x + psi_L_remainder x"
    by (subst balanced) (auto simp: alpha_L_def psi_L_remainder_def)
  finally show ?thesis .
qed

lemma primes_psi_lower_bound:
  fixes x C :: real
  defines "x0 \<equiv> Max (insert 3 ((\<lambda>l. 3 * \<bar>l\<bar>) ` set_mset L))"
  assumes x: "x \<ge> x0"
  assumes chi_le1: "\<And>n. n \<in> {0..<period} \<Longrightarrow> \<chi>\<^sub>L (real n) \<le> 1"
  defines "C \<equiv> 1 / 2 * (\<Sum>l\<in>#L. ln \<bar>l\<bar>) - size L"
  shows   "\<psi> x \<ge> \<alpha>\<^sub>L * x - ln x * size L / 2 + C"
proof -
  have chi_le1': "\<chi>\<^sub>L x \<le> 1" for x
    proof -
    have "\<chi>\<^sub>L x = \<chi>\<^sub>L (floor x mod period)"
      by (simp add: chi_L_mod chi_L_floor)
    also have "floor x mod period = real (nat (floor x mod period))"
      using period_pos by auto
    also have "\<chi>\<^sub>L \<dots> \<le> 1"
      by (rule chi_le1) (use period_pos in \<open>auto simp: nat_less_iff\<close>)
    finally show ?thesis .
  qed

  have x0: "x0 \<ge> 3" "\<And>l. l \<in># L \<Longrightarrow> x0 \<ge> 3 * \<bar>l\<bar>"
    unfolding x0_def by auto

  have *: "x * y \<le> x" if "y \<le> 1" "x \<ge> 0" for x y :: real
    using mult_left_mono[OF that] by auto

  have "\<bar>psi_L_remainder x\<bar> \<le> ln x * real (size L) / 2 -
          1 / 2 * (\<Sum>l\<in>#L. ln (real_of_int \<bar>l\<bar>)) + real (size L)"
    by (rule psi_L_remainder_bounds)
       (use x x0 in \<open>force simp flip: of_int_abs\<close>)+
  hence "\<bar>psi_L_remainder x\<bar> \<le> ln x * size L / 2 - C"
    by (simp add: C_def algebra_simps)
  hence "\<alpha>\<^sub>L * x - ln x * size L / 2 + C \<le> \<alpha>\<^sub>L * x + psi_L_remainder x"
    by linarith
  also have "\<alpha>\<^sub>L * x + psi_L_remainder x = \<psi>\<^sub>L x"
    using x x0(1) by (subst psi_L_eq) auto
  also have "\<psi>\<^sub>L x \<le> \<psi> x"
    unfolding psi_L_def primes_psi_def sum_upto_def
    by (intro sum_mono *) (auto simp: mangoldt_nonneg chi_le1')
  finally show ?thesis
    by (simp add: C_def)
qed

end

lemma psi_lower_bound_precise:
  assumes x: "x \<ge> 90"
  shows   "\<psi> x \<ge> 0.92128 * x - 2.5 * ln x - 1.6"
proof -
  interpret balanced_chebyshev_multiset "{#1, -2, -3, -5, 30#}"
    by unfold_locales auto

  define C :: real where "C = ((ln 2 + (ln 3 + (ln 5 + ln 30))) / 2 - 5)"
  have "alpha_L = ln 2 / 2 - (ln 30 / 30 - ln 5 / 5 - ln 3 / 3)"
    by (simp add: alpha_L_def)
  also have "\<dots> \<ge> 0.92128"
    by (approximation 30)
  finally have "alpha_L \<ge> 0.92128" .
  have "C \<ge> -1.6"
    unfolding C_def by (approximation 20)

  have "0.92128 * x - ln x * 5 / 2 + (-1.6) \<le> alpha_L * x - ln x * 5 / 2 + C"
    using \<open>alpha_L \<ge> _\<close> \<open>C \<ge> _\<close> x by (intro diff_mono add_mono mult_right_mono) auto
  also have "chi_L k \<le> 1" if "k \<in> {..<30}" for k :: nat
    using that unfolding lessThan_nat_numeral pred_numeral_simps arith_simps
    by (elim insertE) (auto simp: chi_L_def)
  hence "alpha_L * x - ln x * 5 / 2 + C \<le> \<psi> x"
    using primes_psi_lower_bound[of x] x by (simp add: C_def period_def)
  finally show ?thesis
    by (simp add: mult_ac)
qed

context balanced_chebyshev_multiset
begin

lemma psi_upper_bound:
  fixes x c C :: real
  defines "x0 \<equiv> Max ({3, 55 * c} \<union> {3 * \<bar>l\<bar> |l. l \<in># L})"
  assumes x: "x \<ge> x0"
  assumes chi_nonneg: "\<And>n. n \<in> {0..<period} \<Longrightarrow> \<chi>\<^sub>L (real n) \<ge> 0"
  assumes chi_ge1: "\<And>n. real n \<in> {1..<c} \<Longrightarrow> \<chi>\<^sub>L (real n) \<ge> 1"
  assumes c: "c > 1" "c \<le> period"
  assumes "\<alpha>\<^sub>L \<ge> 0"
  shows "\<psi> x \<le> c / (c - 1) * \<alpha>\<^sub>L * x + (3 * size L) / (4 * ln c) * ln x ^ 2 + \<psi> x0"
proof -
  have L_nonzero': "l \<noteq> 0" if "l \<in># L" for l
    using that L_nonzero by auto

  have chi_nonneg: "\<chi>\<^sub>L x \<ge> 0" for x
    proof -
    have "\<chi>\<^sub>L x = \<chi>\<^sub>L (floor x mod period)"
      by (simp add: chi_L_mod chi_L_floor)
    also have "floor x mod period = real (nat (floor x mod period))"
      using period_pos by auto
    also have "\<chi>\<^sub>L \<dots> \<ge> 0"
      by (rule chi_nonneg) (use period_pos in \<open>auto simp: nat_less_iff\<close>)
    finally show ?thesis .
  qed

  have chi_ge1: "\<chi>\<^sub>L x \<ge> 1" if "x \<ge> 1" "x < c" for x
    proof -
    have "\<chi>\<^sub>L x = \<chi>\<^sub>L (floor x mod period)"
      by (simp add: chi_L_mod chi_L_floor)
    also have "floor x mod period = real (nat (floor x mod period))"
      using period_pos by auto
    also have "\<chi>\<^sub>L \<dots> \<ge> 1"
    proof (rule chi_ge1)
      have "real_of_int \<lfloor>x\<rfloor> < c"
        using that by linarith
      hence "real_of_int (\<lfloor>x\<rfloor> mod int period) < c"
        using that period_pos c by simp
      moreover have "1 \<le> \<lfloor>x\<rfloor> mod int period"
        by (use period_pos c that in \<open>auto simp: floor_less_iff\<close>)
      ultimately show "real (nat (\<lfloor>x\<rfloor> mod int period)) \<in> {1..<c}"
        by auto
    qed
    finally show ?thesis .
  qed

  have "finite {3 * l |l. l \<in># L}"
    by auto
  have x1: "x0 \<ge> 3" "x0 \<ge> 55 * c"
    unfolding x0_def by (rule Max_ge; simp)+
  have x2: "3 * \<bar>l\<bar> \<le> x0" if "l \<in># L" for l
    unfolding x0_def by (rule Max_ge) (use that in auto)

  define C where "C = 1/2 * (\<Sum>l\<in>#L. ln  \<bar>l\<bar>) - size L"
  have *: "x \<le> x * y" if "y \<ge> 1" "x \<ge> 0" for x y :: real
    using mult_left_mono[of 1 y x] that by simp

  have rec: "\<psi> x \<le> \<psi> (x / c) + \<alpha>\<^sub>L * x + ln x * size L / 2 - C" if x: "x \<ge> x0" for x :: real
  proof -
    have "x / c \<le> x"
      using c using divide_left_mono[of 1 c x] \<open>x0 \<ge> 3\<close> x by auto
    have "\<psi> x = \<psi> (x / c) + (\<Sum>d | d > 0 \<and> real d \<in> {x/c<..x}. mangoldt d)"
      unfolding \<psi>_def sum_upto_def
      by (rule sum.union_disjoint' [symmetric])
         (use c \<open>x / c \<le> x\<close> in auto)
    also have "(\<Sum>d | d > 0 \<and> real d \<in> {x/c<..x}. mangoldt d) \<le>
               (\<Sum>d | d > 0 \<and> real d \<in> {x/c<..x}. mangoldt d * \<chi>\<^sub>L (x / d))"
      using c by (intro sum_mono * mangoldt_nonneg) (auto intro!: chi_ge1 simp: field_simps)
    also have "\<dots> \<le> (\<Sum>d | d > 0 \<and> real d \<le> x. mangoldt d * \<chi>\<^sub>L (x / d))"
      by (intro sum_mono2) (auto intro!: mult_nonneg_nonneg mangoldt_nonneg chi_nonneg)
    also have "\<dots> = \<psi>\<^sub>L x"
      by (simp add: psi_L_def sum_upto_def)
    finally have "\<psi> x \<le> \<psi> (x / c) + \<psi>\<^sub>L x"
      by - simp_all

    have L: "3 * \<bar>real_of_int l\<bar> \<le> x" if "l \<in># L" for l
      using x2[OF that] x by linarith
  
    have "\<psi> x \<le> \<psi> (x / c) + \<psi>\<^sub>L x"
      by fact
    also have "\<psi>\<^sub>L x = \<alpha>\<^sub>L * x + psi_L_remainder x"
      using \<open>x0 \<ge> 3\<close> x by (subst psi_L_eq) auto
    also have "\<bar>psi_L_remainder x\<bar> \<le> ln x * size L / 2 - C"
      using psi_L_remainder_bounds[of x] \<open>x0 \<ge> 3\<close> x L by (simp add: C_def)
    hence "psi_L_remainder x \<le> ln x * size L / 2 - C"
      by linarith
    finally show "\<psi> x \<le> \<psi> (x / c) + \<alpha>\<^sub>L * x + ln x * size L / 2 - C"
      by (simp add: algebra_simps)
  qed

  define m where "m = nat \<lceil>log c (x / x0)\<rceil>"
  have "x > 0"
    using x x1 by simp

  have "\<psi> x \<le> \<psi> x0 + (\<Sum>k<m. \<alpha>\<^sub>L * x / c ^ k + ln (x / c ^ k) * size L / 2 - C)"
  proof -
    have "\<psi> x \<le> \<psi> (x / c ^ m) + (\<Sum>k<m. \<alpha>\<^sub>L * (x / c ^ k) + ln (x / c ^ k) * size L / 2 - C)"
    proof (rule primes_psi_lower_rec)
      fix x :: real assume "x \<ge> x0"
      thus "\<psi> x \<le> \<psi> (x / c) + (\<alpha>\<^sub>L * x + ln x * size L / 2 - C)"
        using rec[of x] by (simp add: algebra_simps)
    next
      have "c ^ m = c powr real m"
        using c by (simp add: powr_realpow)
      also have "\<dots> \<le> c powr (log c (x / x0) + 1)"
        using c x \<open>x0 \<ge> 3\<close> by (intro powr_mono) (auto simp: m_def)
      also have "\<dots> = c * x / x0"
        using c x \<open>x0 \<ge> 3\<close> by (auto simp: powr_add)
      finally show "x0 * c ^ m \<le> x * c"
        using \<open>x0 \<ge> 3\<close> by (simp add: field_simps)
    qed (use x1 c in auto)
    also have "\<psi> (x / c ^ m) \<le> \<psi> x0"
    proof (rule \<psi>_mono)
      have "x / x0 = c powr log c (x / x0)"
        using c x \<open>x0 \<ge> 3\<close> by simp
      also have "\<dots> \<le> c powr m"
        unfolding m_def using c \<open>x0 \<ge> 3\<close> x by (intro powr_mono) auto
      also have "\<dots> = c ^ m"
        using c by (simp add: powr_realpow)
      finally show "x / c ^ m \<le> x0"
        using \<open>x0 \<ge> 3\<close> c by (simp add: field_simps)
    qed
    finally show ?thesis
      by simp
  qed
  also have "\<dots> = \<psi> x0 + (\<Sum>k<m. \<alpha>\<^sub>L * x / c ^ k + (ln x - k * ln c) * size L / 2 - C)"
    using x(1) \<open>x0 \<ge> 3\<close> c by (simp add: ln_div ln_realpow)
  also have "\<dots> = \<psi> x0 + \<alpha>\<^sub>L * x * (\<Sum>k<m. 1 / c ^ k) + ln x * m * size L / 2 - real (\<Sum>k<m. k) * ln c * size L / 2 - C * m"
    by (simp add: sum_diff_distrib sum_subtractf sum.distrib sum_distrib_left sum_distrib_right algebra_simps diff_divide_distrib sum_divide_distrib)
  also have "(\<Sum>k<m. 1 / c ^ k) = (1 - (1 / c) ^ m) / (1 - 1 / c)"
    using sum_gp_strict[of "1/c" m] c by (simp add: field_simps)
  also have "\<dots> \<le> 1 / (1 - 1 / c)"
    using c by (intro divide_right_mono) auto
  also have "1 / (1 - 1/c) = c / (c - 1)"
    using c by (simp add: field_simps)
  also have "(\<Sum>k<m. k) = real m * (real m - 1) / 2"
    by (induction m) (auto simp: field_simps)
  finally have "\<psi> x \<le> \<psi> x0 + c / (c - 1) * \<alpha>\<^sub>L * x +
                  ln x * m * size L / 2 -
                  real m * (real m - 1) / 2 * ln c * size L / 2 - C * m"
    using \<open>\<alpha>\<^sub>L \<ge> 0\<close> \<open>x > 0\<close> x1 by (simp add: mult_left_mono mult_right_mono mult_ac)
  also have "\<dots> = \<psi> x0 + c / (c - 1) * \<alpha>\<^sub>L * x + m/2 * (size L * (ln x - (real m - 1)/2 * ln c + 2) - (\<Sum>l\<in>#L. ln \<bar>l\<bar>))"
    by (simp add: algebra_simps C_def)
  also have "m/2 * (size L * (ln x - (real m - 1)/2 * ln c + 2) - (\<Sum>l\<in>#L. ln \<bar>l\<bar>)) \<le>
             m/2 * (size L * (3/2 * ln x) - 0)"
  proof (intro mult_left_mono diff_mono)
    have "real m \<ge> log c (x / x0)"
      using c \<open>x0 \<ge> 3\<close> x unfolding m_def by auto
    hence "ln x - (real m - 1)/2 * ln c + 2 \<le>
           ln x - (log c (x / x0) - 1)/2 * ln c + 2"
      using c by (intro diff_mono add_mono mult_right_mono divide_right_mono) auto
    also have "\<dots> = (ln x + ln x0 + (ln c + 4)) / 2"
      using c x \<open>x0 \<ge> 3\<close> by (simp add: log_def ln_div field_simps)
    also have "ln x0 \<le> ln x"
      using x x1 by simp
    also have "ln c + 4 \<le> ln x"
    proof -
      have "exp (4 :: real) \<le> 55"
        by (approximation 10)
      hence "exp 4 * c \<le> 55 * c"
        using c by (intro mult_right_mono) auto
      also have "55 * c \<le> x0"
        by fact
      also have "\<dots> \<le> x"
        by fact
      finally have "exp (ln c + 4) \<le> exp (ln x)"
        unfolding exp_add using c x1 x by (simp add: mult_ac)
      thus ?thesis
        by (simp only: exp_le_cancel_iff)
    qed
    also have "(ln x + ln x + ln x) / 2 = 3 / 2 * ln x"
      by simp
    finally show "ln x - (real m - 1) / 2 * ln c + 2 \<le> 3 / 2 * ln x"
      by - simp
  qed (auto intro!: sum_mset_nonneg simp: L_nonzero' Ints_nonzero_abs_ge1)
  also have "m / 2 * (size L * (3/2 * ln x) - 0) = 3 / 4 * m * size L * ln x"
    by simp
  also have "\<dots> \<le> 3 / 4 * (ln x / ln c) * size L * ln x"
  proof (intro mult_left_mono mult_right_mono)
    have "real m \<le> log c (x / x0) + 1"
      unfolding m_def using c x \<open>x0 \<ge> 3\<close> by auto
    also have "\<dots> / 2 = (ln x / ln c + (1 - log c x0)) / 2"
      using \<open>x0 \<ge> 3\<close> \<open>x \<ge> x0\<close> c 
      by (simp add: log_def ln_div field_simps)
    also have "1 - log c x0 \<le> 0"
      using x1 c by simp
    finally show "real m \<le> ln x / ln c" by - simp_all
  qed (use x x1 in auto)
  also have "\<dots> = (3 * size L) / (4 * ln c) * ln x ^ 2"
    by (simp add: power2_eq_square)
  finally show "\<psi> x \<le> c / (c - 1) * \<alpha>\<^sub>L * x + (3 * size L) / (4 * ln c) * ln x ^ 2 + \<psi> x0"
    by (simp add: algebra_simps)
qed

end


subsection \<open>Final results\<close>

theorem psi_lower_ge_9:
  assumes x: "x \<ge> 41"
  shows   "\<psi> x \<ge> 0.9 * x"
proof (cases "x \<ge> 900")
  case False
  have "\<forall>x\<in>{real 41..real 900}. primes_psi x \<ge> 0.9 * x"
    by (rule check_psi_lower_correct[where prec = 16]) eval
  from bspec[OF this, of x] show ?thesis
    using assms False by simp
next
  case x: True
  define f :: "real \<Rightarrow> real"
    where "f = (\<lambda>x. 0.02128 * x - 2.5 * ln x - 1.6)"
  have "0 \<le> f 900"
    unfolding f_def by (approximation 10)
  also have "f 900 \<le> f x"
    using x
  proof (rule DERIV_nonneg_imp_nondecreasing, goal_cases)
    case (1 t)
    have "(f has_real_derivative (0.02128 - 2.5 / t)) (at t)"
      unfolding f_def using 1 by (auto intro!: derivative_eq_intros)
    moreover have "0.02128 - 2.5 / t \<ge> 0"
      using 1 by (auto simp: field_simps)
    ultimately show ?case
      by blast
  qed
  finally have "0.9 * x \<le> 0.9 * x + f x"
    by linarith
  also have "\<dots> = 0.92128 * x - 2.5 * ln x - 1.6"
    by (simp add: f_def)
  also have "\<dots> \<le> \<psi> x"
    by (rule psi_lower_bound_precise) (use x in auto)
  finally show ?thesis .
qed

theorem primes_theta_ge_82:
  assumes "x \<ge> 97"
  shows   "\<theta> x \<ge> 0.82 * x"
proof (cases "x \<ge> 46000")
  case False
  have "\<forall>x\<in>{real 97..real 46000}. \<theta> x \<ge> 0.82 * x"
    by (rule check_theta_lower_correct[where prec = 20]) eval
  from bspec[OF this, of x] show ?thesis
    using False assms by simp
next
  case True
  with assms have x: "x \<ge> 46000"
    by auto
  define f :: "real \<Rightarrow> real"
    where "f = (\<lambda>x. 0.10128 * x - 2.5 * ln x - 2 * ln x * sqrt x - 1.6)"
  have "0 \<le> f 46000"
    unfolding f_def by (approximation 30)
  also have "f 46000 \<le> f x"
    using x
  proof (rule DERIV_nonneg_imp_nondecreasing, goal_cases)
    case (1 t)
    define D where "D = 0.10128 - 2.5 / t - 2 * sqrt t / t - ln t / sqrt t"
    have deriv: "(f has_real_derivative D) (at t)"
      unfolding f_def
      by (rule derivative_eq_intros refl | use 1 in force)+
         (simp add: field_simps D_def)
    have "0.10128 - D = 2.5 / t + 2 / sqrt t + ln t / sqrt t"
      using 1 by (simp add: D_def field_simps del: div_add div_diff  div_mult_self1 div_mult_self2  div_mult_self3  div_mult_self4)
    also have "\<dots> \<le> 2.5 / 46000 + 2 / 214 + ln t / sqrt t"
      using 1 by (intro add_mono) (auto simp: real_le_rsqrt)

    also have "ln t / sqrt t \<le> ln 46000 / sqrt 46000"
      using 1(1)
    proof (rule DERIV_nonpos_imp_nonincreasing, goal_cases)
      case (1 u)
      have "((\<lambda>t. ln t / sqrt t) has_real_derivative ((2 - ln u) / (2 * u * sqrt u))) (at u)"
        by (rule derivative_eq_intros refl | use 1 in force)+
           (use 1 in \<open>simp add: field_simps\<close>)
      moreover {
        have "2 \<le> ln (10::real)"
          by (approximation 30)
        also have "\<dots> \<le> ln u"
          using 1 by simp
        finally have "ln u \<ge> 2" .
      }      
      hence "((2 - ln u) / (2 * u * sqrt u)) \<le> 0"
        using 1 by (intro divide_nonpos_nonneg) auto
      ultimately show ?case
        by blast
    qed
    also have "\<dots> \<le> 0.0501"
      by (approximation 30)
    also have "2.5 / 46000 + 2 / 214 + 0.0501 \<le> (0.10128 :: real)"
      by simp
    finally have "D \<ge> 0"
      by simp
    with deriv show ?case by blast
  qed

  finally have "0.82 * x \<le> 0.82 * x + f x"
    by linarith
  also have "\<dots> = 0.92128 * x - 2.5 * ln x - 2 * ln x * sqrt x - 1.6"
    by (simp add: f_def)
  also have "\<dots> \<le> 0.92128 * x - 2.5 * ln x - 1.6 + \<theta> x - \<psi> x"
    using \<psi>_minus_\<theta>_bound[of x] x by simp
  also have "0.92128 * x - 2.5 * ln x - 1.6 \<le> \<psi> x"
    by (rule psi_lower_bound_precise) (use x in auto)
  finally show ?thesis by simp
qed

corollary primorial_ge_exp_82:
  assumes "x \<ge> 97"
  shows   "primorial x \<ge> exp (0.82 * x)"
proof -
  have "primorial x = exp (\<theta> x)"
    using ln_primorial[of x] primorial_pos[of x]
    by (metis exp_ln of_nat_0_less_iff)
  also have "\<dots> \<ge> exp (0.82 * x)"
    using primes_theta_ge_82[OF assms] by simp
  finally show ?thesis .
qed


theorem primes_psi_le_111:
  assumes "x \<ge> 0"
  shows   "\<psi> x \<le> 1.11 * x"
proof -
  have "\<forall>x\<in>{real 0..real 146000}. primes_psi x \<le> 1.04 * x"
  proof (rule check_psi_upper_correct[where prec = 16])
    show "check_psi_upper (104 / 10\<^sup>2) 16 0 146000"
      by eval
  qed auto
  hence initial: "primes_psi x \<le> 1.04 * x" if "x \<in> {0..146000}" for x
    using that by auto

  show ?thesis
  proof (cases "x \<ge> 146000")
    case False
    thus ?thesis
      using initial[of x] assms by simp
  next
    case x: True
    define L :: "int multiset" where "L = {#1, -2, -3, -5, 30#}"
    have [simp]: "set_mset L = {1, -2, -3, -5, 30}" "size L = 5"
      by (simp_all add: L_def)
    interpret balanced_chebyshev_multiset L
      by unfold_locales (auto simp: L_def)
    define x0 :: real where "x0 = Max ({3, 55 * 6} \<union> {3 * \<bar>real_of_int l\<bar> |l. l \<in># L})"
  
    have x0: "x0 = 330"
    proof -
      have "x0 = Max ({3, 55 * 6} \<union> {3 * \<bar>real_of_int l\<bar> |l. l \<in># L})"
        unfolding x0_def ..
      also have "{3 * \<bar>real_of_int l\<bar> |l. l \<in># L} = (\<lambda>l. 3 * \<bar>of_int l\<bar>) ` set_mset L"
        by blast
      finally show ?thesis
        by simp
    qed

    define f :: "real \<Rightarrow> real"
      where "f = (\<lambda>t. 2.093 * ln t ^ 2 + 343.2 - 0.0044 * t)"
  
    have alpha_L: "alpha_L = ln 2 / 2 - (ln 30 / 30 - ln 5 / 5 - ln 3 / 3)"
      unfolding alpha_L_def by (simp add: L_def)
    have "alpha_L \<ge> 0"
      unfolding alpha_L by (approximation 10)
    have period: "period = 30"
      by (simp add: period_def)
  
    have "\<psi> x \<le> 6 / (6 - 1) * alpha_L * x + (3 * size L) / (4 * ln 6) * ln x ^ 2 + \<psi> x0"
      unfolding x0_def
    proof (rule psi_upper_bound; (unfold period)?)
      show "chi_L (real n) \<ge> 0" if "n \<in> {0..<30}" for n
        unfolding chi_L_def
        using that unfolding atLeastLessThan_nat_numeral pred_numeral_simps arith_simps
        by (auto simp: L_def)
    next
      show "chi_L (real n) \<ge> 1" if "real n \<in> {1..<6}" for n
      proof -
        have "n \<in> {1..<6}"
          using that by auto
        also have "{1..<6} = {1,2,3,4,5::nat}"
          by auto
        finally show ?thesis
          unfolding chi_L_def by (elim insertE) (auto simp: L_def)
      qed
    qed (use \<open>alpha_L \<ge> 0\<close> x in auto)
  
    also have "\<dots> = 6/5 * alpha_L * x + 15 / (4 * ln 6) * (ln x)\<^sup>2 + \<psi> x0"
      by simp
    also have "\<psi> x0 \<le> 343.2"
      using initial[of x0] by (simp add: x0)
    also have "6/5 * alpha_L \<le> 1.1056"
      unfolding alpha_L by (approximation 30)
    also have "15 / (4 * ln 6 :: real) \<le> 2.093"
      by (approximation 20)
    finally have "\<psi> x \<le> 1.1056 * x + 2.093 * ln x ^ 2 + 343.2"
      using x by - simp_all
    also have "\<dots> = 1.11 * x + f x"
      by (simp add: algebra_simps f_def)
    also have "f x \<le> f 146000"
      using x
    proof (rule DERIV_nonpos_imp_nonincreasing, goal_cases)
      case (1 t)
      define f' :: "real \<Rightarrow> real"
        where "f' = (\<lambda>t. 4.186 * ln t / t - 0.0044)"
      have "(f has_field_derivative f' t) (at t)"
        using 1 unfolding f_def f'_def
        by (auto intro!: derivative_eq_intros)
      moreover {
        have "f' t \<le> f' 146000"
          using 1(1)
        proof (rule DERIV_nonpos_imp_nonincreasing, goal_cases)
          case (1 u)
          have "(f' has_field_derivative (4.186 * (1 - ln u) / u ^ 2)) (at u)"
            using 1 unfolding f'_def
            by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
          moreover have "4.186 * (1 - ln u) / u ^ 2 \<le> 0"
            using 1 exp_le by (auto intro!: divide_nonpos_nonneg simp: ln_ge_iff)
          ultimately show ?case
            by blast
        qed
        also have "\<dots> \<le> 0"
          unfolding f'_def by (approximation 10)
        finally have "f' t \<le> 0" .
      }
      ultimately show ?case
        by blast
    qed
    also have "f 146000 \<le> 0"
      unfolding f_def by (approximation 10)
    finally show ?thesis
      by - simp_all
  qed
qed

corollary primes_theta_le_111:
  assumes "x \<ge> 0"
  shows   "\<theta> x \<le> 1.11 * x"
  using primes_psi_le_111[OF assms] \<theta>_le_\<psi>[of x]
  by linarith

text \<open>
  As an easy corollary, we obtain Bertrand's postulate:
  For any real number $x > 1$, the interval $(x, 2x)$ contains
  at least one prime.
\<close>
corollary bertrands_postulate:
  assumes "x > 1"
  shows   "\<exists>p. prime p \<and> real p \<in> {x<..<2*x}"
proof (cases "x \<ge> 7")
  case False
  consider "x \<in> {1<..<2}" | "x \<in> {2..<3}" | "x \<in> {3..<5}" | "x \<in> {5..<7}"
    using False assms by force
  thus ?thesis
  proof cases
    case 1
    thus ?thesis by (intro exI[of _ 2]; simp)
  next
    case 2
    thus ?thesis by (intro exI[of _ 3]; simp)
  next
    case 3
    thus ?thesis by (intro exI[of _ 5]; simp)
  next
    case 4
    thus ?thesis by (intro exI[of _ 7]; simp)
  qed
next
  case x: True
  have fin: "finite {p. prime p \<and> real p \<le> 1.999 * x}"
    by (rule finite_subset[of _ "{..nat \<lfloor>2*x\<rfloor>}"])
       (use x in \<open>auto simp: le_nat_iff le_floor_iff\<close>)

  have "\<theta> (1.999 * x) > 1.11 * x"
  proof (cases "x \<ge> 49")
    case False
    have "\<forall>x\<in>{real 11..real 100}. \<theta> x \<ge> 0.556 * x"
      by (rule check_theta_lower_correct[where prec = 10]) eval
    from bspec[OF this, of "1.999*x"] show ?thesis
      using False x by simp
  next
    case True
    thus ?thesis
      using primes_theta_ge_82[of "1.999*x"] True by auto
  qed

  have "\<theta> x \<le> 1.11 * x"
    by (rule primes_theta_le_111) (use x in auto)
  also have "\<dots> < \<theta> (1.999 * x)"
    by fact
  finally have "\<theta> (1.999 * x) > \<theta> x" .

  have "{p. prime p \<and> real p \<in> {x<..1.999*x}} \<noteq> {}"
  proof
    assume eq: "{p. prime p \<and> real p \<in> {x<..1.999*x}} = {}"
    have "\<theta> (1.999 * x) = \<theta> x + (\<Sum>p | prime p \<and> real p \<in> {x<..1.999*x}. ln p)"
      unfolding primes_theta_def prime_sum_upto_def
      by (rule sum.union_disjoint' [symmetric]) (use fin in auto)
    also note eq
    finally show False
      using \<open>\<theta> (1.999 * x) > \<theta> x\<close> by simp
  qed
  thus ?thesis
    by auto
qed

unbundle no prime_counting_syntax

end
