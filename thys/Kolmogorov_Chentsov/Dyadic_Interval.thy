(* Title:      Kolmogorov_Chentsov/Dyadic_Interval.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Intervals of dyadic rationals"

theory Dyadic_Interval
  imports "HOL-Analysis.Analysis"
begin

text \<open> In this file we describe intervals of dyadic numbers ${S..T}$ for reals S T. We use the floor
  and ceiling functions to approximate the numbers with increasing accuracy. \<close>

lemma frac_floor: "\<lfloor>x\<rfloor> = x - frac x"
  by (simp add: frac_def)

lemma frac_ceil: "\<lceil>x\<rceil> = x + frac (- x)"
  apply (cases "x = real_of_int \<lfloor>x\<rfloor>")
  unfolding ceiling_altdef apply simp
   apply (metis Ints_minus Ints_of_int)
  apply (simp add: frac_neg frac_floor)
  done

lemma floor_pow2_lim: "(\<lambda>n. \<lfloor>2^n * T\<rfloor> / 2 ^ n) \<longlonglongrightarrow> T"
proof (intro LIMSEQ_I)
  fix r :: real assume "r > 0"
  obtain k where k: "1 / 2^k < r"
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have "\<forall>n\<ge>k. norm (\<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r"
    apply (simp add: frac_floor field_simps)
    by (smt (verit, ccfv_SIG) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show "\<exists>no. \<forall>n\<ge>no. norm (real_of_int \<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r"
    by blast
qed

lemma floor_pow2_leq: "\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> T"
  by (simp add: frac_floor field_simps)

lemma ceil_pow2_lim: "(\<lambda>n. \<lceil>2^n * T\<rceil> / 2 ^ n) \<longlonglongrightarrow> T"
proof (intro LIMSEQ_I)
  fix r :: real assume "r > 0"
  obtain k where k: "1 / 2^k < r"
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have "\<forall>n\<ge>k. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r"
    apply (simp add: frac_ceil field_simps)
    by (smt (verit) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show "\<exists>no. \<forall>n\<ge>no. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r"
    by blast 
qed

lemma ceil_pow2_geq: "\<lceil>2^n * T\<rceil> / 2 ^ n \<ge> T"
  by (simp add: frac_ceil field_simps)

text \<open> \texttt{dyadic\_interval\_step} $n$ $S$ $T$ is the collection of dyadic numbers in $\{S..T\}$ with denominator $2^n$. As
 $n \to \infty$ this collection approximates $\{S..T\}$. Compare with @{thm dyadics_def}\<close>

definition dyadic_interval_step :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set"
  where "dyadic_interval_step n S T \<equiv> (\<lambda>k. k / (2 ^ n)) ` {\<lceil>2^n * S\<rceil>..\<lfloor>2^n * T\<rfloor>}"

definition dyadic_interval :: "real \<Rightarrow> real \<Rightarrow> real set"
  where "dyadic_interval S T \<equiv> (\<Union>n. dyadic_interval_step n S T)"

lemma dyadic_interval_step_empty[simp]: "T < S \<Longrightarrow> dyadic_interval_step n S T = {}"
  unfolding dyadic_interval_step_def apply simp
  by (smt (verit) ceil_pow2_geq floor_le_ceiling floor_mono floor_pow2_leq
      linordered_comm_semiring_strict_class.comm_mult_strict_left_mono zero_less_power)

lemma dyadic_interval_step_singleton[simp]: "X \<in> \<int> \<Longrightarrow> dyadic_interval_step n X X = {X}"
proof -
  assume "X \<in> \<int>"
  then have *: "\<lfloor>2 ^ k * X\<rfloor> = 2 ^ k * X" for k :: nat
    by simp
  then show ?thesis
    unfolding dyadic_interval_step_def apply (simp add: ceiling_altdef)
    using * by presburger
qed

lemma dyadic_interval_step_zero [simp]: "dyadic_interval_step 0 S T = real_of_int ` {\<lceil>S\<rceil> .. \<lfloor>T\<rfloor>}"
  unfolding dyadic_interval_step_def by simp

lemma dyadic_interval_step_mem [intro]:
  assumes"x \<ge> 0" "T \<ge> 0" "x \<le> T" 
  shows "\<lfloor>2^n * x\<rfloor> / 2 ^ n \<in> dyadic_interval_step n 0 T"
  unfolding dyadic_interval_step_def by (simp add: assms image_iff floor_mono)

lemma dyadic_interval_step_iff: 
  "x \<in> dyadic_interval_step n S T \<longleftrightarrow>
   (\<exists>k. k \<ge> \<lceil>2^n * S\<rceil> \<and> k \<le> \<lfloor>2^n * T\<rfloor> \<and> x = k/2^n)"
  unfolding dyadic_interval_step_def by (auto simp add: image_iff)

lemma dyadic_interval_step_memI [intro]:
  assumes "\<exists>k::int. x = k/2^n" "x \<ge> S" "x \<le> T"
  shows "x \<in> dyadic_interval_step n S T"
proof -
  obtain k :: int where "x = k/2^n"
    using assms(1) by blast
  then have k: "k = 2^n * x"
    by simp
  then have "k \<ge> \<lceil>2^n * S\<rceil>"
    by (simp add: assms(2) ceiling_le)
  moreover from k have "k \<le> \<lfloor>2^n * T\<rfloor>"
    by (simp add: assms(3) le_floor_iff)
  ultimately show ?thesis
    using dyadic_interval_step_iff \<open>x = k / 2 ^ n\<close> by blast
qed

lemma mem_dyadic_interval: "x \<in> dyadic_interval S T \<longleftrightarrow> (\<exists>n. x \<in> dyadic_interval_step n S T)"
  unfolding dyadic_interval_def by blast

lemma mem_dyadic_intervalI: "\<exists>n. x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<in> dyadic_interval S T"
  using mem_dyadic_interval by fast

lemma dyadic_step_leq: "x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<le> T"
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: divide_le_eq le_floor_iff mult.commute)

lemma dyadics_leq: "x \<in> dyadic_interval S T \<Longrightarrow> x \<le> T"
  using dyadic_step_leq mem_dyadic_interval by blast

lemma dyadic_step_geq: "x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<ge> S"
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: ceiling_le_iff mult.commute pos_le_divide_eq)

lemma dyadics_geq: "x \<in> dyadic_interval S T \<Longrightarrow> x \<ge> S"
  using dyadic_step_geq mem_dyadic_interval by blast

corollary dyadic_interval_subset_interval [simp]: "(dyadic_interval 0 T) \<subseteq> {0..T}"
  using dyadics_geq dyadics_leq by force

lemma zero_in_dyadics: "T \<ge> 0 \<Longrightarrow> 0 \<in> dyadic_interval_step n 0 T"
  using dyadic_interval_step_def by force

text \<open> The following theorem is useful for reasoning with at\_within \<close>
lemma dyadic_interval_converging_sequence:
  assumes "t \<in> {0..T}" "T \<noteq> 0"
  shows "\<exists>s. \<forall>n. s n \<in> dyadic_interval 0 T - {t} \<and> s \<longlonglongrightarrow> t"
proof -
  from assms have "T > 0"
    by auto
  consider (eq_0) "t = 0" | (dyadic) "t \<in> dyadic_interval 0 T - {0}" | (real) "t \<notin> dyadic_interval 0 T"
    by blast
  then show ?thesis
  proof cases
    case eq_0
    obtain n where "1 \<le> 2 ^ n * T"
    proof -
      assume *: "\<And>n. 1 \<le> 2 ^ n * T \<Longrightarrow> thesis"
      obtain n where "2 ^ n > 1/T"
        using real_arch_pow by fastforce
      then have "2 ^ n * T \<ge> 1"
        using \<open>T > 0\<close> by (simp add: field_simps)
      then show ?thesis
        using * by blast
    qed
    define s :: "nat \<Rightarrow> real" where "s = (\<lambda>m. 1/2^(m + n))"
    have "\<forall>m. s m \<in> dyadic_interval_step (m + n) 0 T - {0}"
      unfolding s_def apply (simp add: dyadic_interval_step_iff)
      using  \<open>1 \<le> 2 ^ n * T\<close>
      by (smt (verit, best) \<open>0 < T\<close> le_add2 mult_right_mono power_increasing_iff)
    then have "\<forall>m. s m \<in> dyadic_interval 0 T - {0}"
      using mem_dyadic_interval by auto
    moreover {
      have "(\<lambda>m. (1::real)/2^m) \<longlonglongrightarrow> 0"
        by (simp add: divide_real_def LIMSEQ_inverse_realpow_zero)
      then have "s \<longlonglongrightarrow> 0"
        unfolding s_def using LIMSEQ_ignore_initial_segment by auto
    }
    ultimately show ?thesis
      using eq_0 by blast
  next
    case dyadic
    then have "t \<noteq> 0"
      by blast
    from dyadic obtain n where n: "t \<in> dyadic_interval_step n 0 T"
      by (auto simp: mem_dyadic_interval)
    then obtain k :: int where k: "t = k / 2^n" "k \<le> \<lfloor>2 ^ n * T\<rfloor>"
      using dyadic_interval_step_iff by blast
    then have "k > 0"
      using \<open>t \<noteq> 0\<close> dyadic_interval_step_iff n by force
    define s :: "nat \<Rightarrow> real" where "s \<equiv> \<lambda>m. (k * 2^(m+1) - 1) / 2 ^ (m + n + 1)"
    have "s m \<in> dyadic_interval_step (m + n + 1) 0 T" for m
    proof -
      have "k * (2 ^ (m+1)) - 1 \<le> \<lfloor>2 ^ n * T\<rfloor> * (2 ^ (m+1)) - 1"
        by (smt (verit) k(2) mult_right_mono zero_le_power)
      also have "... \<le> \<lfloor>2 ^ n * T\<rfloor> * \<lfloor>(2 ^ (m+1))\<rfloor>"
        by (metis add.commute add_le_cancel_left diff_add_cancel diff_self floor_numeral_power
            zero_less_one_class.zero_le_one)
      also have "\<lfloor>2 ^ n * T\<rfloor> * \<lfloor>(2 ^ (m+1))\<rfloor> \<le> \<lfloor>2 ^ n * T * (2 ^ (m+1))\<rfloor>"
        by (smt (z3) \<open>0 < T\<close> floor_one floor_power le_mult_floor mult_nonneg_nonneg of_int_1
            of_int_add one_add_floor one_add_one zero_le_power)
      also have "... = \<lfloor>(2 ^ (m+n+1)) * T\<rfloor>"
        apply (rule arg_cong[where f=floor])
        by (simp add: power_add)
      finally show ?thesis
        unfolding s_def apply (simp only: dyadic_interval_step_iff)
        apply (rule exI[where x="k * (2 ^ (m+1)) - 1"])
        by (simp add: \<open>0 < k\<close>)
    qed
    then have "s m \<in> dyadic_interval 0 T" for m
      using mem_dyadic_interval by blast
    moreover have "s m \<noteq> t" for m
      unfolding s_def k(1) by (simp add: power_add field_simps)
    moreover have "s \<longlonglongrightarrow> t"
    proof
      fix e :: real assume "0 < e"
      then obtain m where "1 / 2 ^ m < e"
        by (metis one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
      { fix m' assume "m' \<ge> m"
        then have "1 / 2 ^ m' < e"
          using \<open>1/2^m < e\<close>
          by (smt (verit) frac_less2 le_eq_less_or_eq power_strict_increasing zero_less_power)
        then have "1/ 2^(m'+n+1) < e"
          by (smt (verit, ccfv_SIG) divide_less_eq_1_pos half_gt_zero_iff power_less_imp_less_exp 
              power_one_over power_strict_decreasing trans_less_add1)
        have "s m' - t = (k * 2^(m'+1) - 1) / 2 ^ (m' + n + 1) - k / 2 ^ n"
          by (simp add: s_def k(1))
        also have "... = ((k * 2 ^ (m' + 1) - 1) - (k * 2 ^(m'+1))) / 2 ^ (m' + n + 1)"
          by (simp add: field_simps power_add)
        also have "... = -1/ 2^(m'+n+1)"
          by (simp add: field_simps)
        finally have "dist (s m') t < e"
          unfolding s_def k(1)
          apply (simp add: dist_real_def)
          using \<open>1 / 2 ^ (m' + n + 1) < e\<close> by auto
      }
      then show "\<forall>\<^sub>F x in sequentially. dist (s x) t < e"
        apply (simp add: eventually_sequentially)
        apply (intro exI[where x=m])
        by simp
    qed
    ultimately show ?thesis
      by blast
  next
    case real
    then obtain n where "dyadic_interval_step n 0 T \<noteq> {}"
      by (metis \<open>0 < T\<close> empty_iff less_eq_real_def zero_in_dyadics)
    define s :: "nat \<Rightarrow> real" where "s \<equiv> \<lambda>m. \<lfloor>2^(m+n) * t\<rfloor> / 2 ^ (m+n)"
    have "s m \<in> dyadic_interval_step (m+n) 0 T" for m
      unfolding s_def
      by (metis assms(1) atLeastAtMost_iff ceiling_zero dyadic_interval_step_iff floor_mono 
          mult.commute mult_eq_0_iff mult_right_mono zero_le_floor zero_le_numeral zero_le_power)
    then have "s m \<in> dyadic_interval 0 T" for m
      using mem_dyadic_interval by blast
    moreover have "s \<longlonglongrightarrow> t"
      unfolding s_def using LIMSEQ_ignore_initial_segment floor_pow2_lim by blast
    ultimately show ?thesis
      using real by blast
  qed
qed

lemma dyadic_interval_dense: "closure (dyadic_interval 0 T) = {0..T}"
proof (rule subset_antisym)
  have "(dyadic_interval 0 T) \<subseteq> {0..T}"
    by (fact dyadic_interval_subset_interval)
  then show "closure (dyadic_interval 0 T) \<subseteq> {0..T}"
    by (auto simp: closure_minimal)
  have "{0..T} \<subseteq> closure (dyadic_interval 0 T)" if "T \<ge> 0"
    unfolding closure_def
  proof -
    {
      fix x assume x: "0 \<le> x" "x \<le> T" "x \<notin> dyadic_interval 0 T"
      then have "x > 0"
        unfolding dyadic_interval_def
        using zero_in_dyadics[OF that] order_le_less by blast
      have "x islimpt (dyadic_interval 0 T)"
        apply (simp add: islimpt_sequential)
        apply (rule exI [where x="\<lambda>n. \<lfloor>2^n * x\<rfloor> / 2^n"])
        apply safe
        using dyadic_interval_step_mem mem_dyadic_interval x(1,2) apply auto[1]
         apply (smt (verit, ccfv_threshold) dyadic_interval_step_mem mem_dyadic_interval x)
        using floor_pow2_lim apply blast
        done
    }
    thus "{0..T} \<subseteq> dyadic_interval 0 T \<union> {x. x islimpt dyadic_interval 0 T}"
      by force
  qed
  then show "{0..T} \<subseteq> closure (dyadic_interval 0 T)"
    by (cases "T \<ge> 0"; simp)
qed

corollary dyadic_interval_islimpt:
  assumes "T > 0" "t \<in> {0..T}"
  shows "t islimpt dyadic_interval 0 T"
  using assms by (subst limpt_of_closure[symmetric], simp add: dyadic_interval_dense)

corollary at_within_dyadic_interval_nontrivial[simp]:
  assumes "T > 0" "t \<in> {0..T}"
  shows "(at t within dyadic_interval 0 T) \<noteq> bot"
  using assms dyadic_interval_islimpt trivial_limit_within by blast

lemma dyadic_interval_step_finite[simp]: "finite (dyadic_interval_step n S T)"
  unfolding dyadic_interval_step_def by simp

lemma dyadic_interval_countable[simp]: "countable (dyadic_interval S T)"
  by (simp add: dyadic_interval_def dyadic_interval_step_def)

lemma floor_pow2_add_leq:
  fixes T :: real
  shows "\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> \<lfloor>2 ^ (n+k) * T\<rfloor> / 2 ^ (n+k)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?f = "frac (2 ^ (n + k) * T)"
    and ?f' = "frac (2 ^ (n + (Suc k)) * T)"
  show ?case
  proof (cases "?f < 1/2")
    case True
    then have "?f + ?f < 1"
      by auto
    then have "frac ((2 ^ (n + k) * T) + (2 ^ (n + k) * T)) = ?f + ?f"
      using frac_add by meson
    then have "?f' = ?f + ?f"
      by (simp add: field_simps)
    then have "\<lfloor>2 ^ (n + Suc k) * T\<rfloor> / 2 ^ (n + Suc k) = \<lfloor>2^(n + k) * T\<rfloor> / 2 ^ (n + k)"
      by (simp add: frac_def)
    then show ?thesis
      using Suc by presburger
  next
    case False
    have "?f' = frac (2 ^ (n + k) * T + 2 ^ (n + k) * T)"
      by (simp add: field_simps)
    then have "?f' = 2 * ?f - 1"
      by (smt (verit, del_insts) frac_add False field_sum_of_halves)
    then have "?f' < ?f"
      using frac_lt_1 by auto
    then have "(2 ^ (n + k) * T - ?f) / 2 ^ (n + k) < (2 ^ (n + (Suc k)) * T - ?f') / 2 ^ (n + Suc k)"
      apply (simp add: field_simps)
      by (smt (verit, ccfv_threshold) frac_ge_0)
    then show ?thesis
      by (smt (verit, ccfv_SIG) Suc frac_def)
  qed
qed

corollary floor_pow2_mono: "mono (\<lambda>n. \<lfloor>2^n * (T :: real)\<rfloor> / 2 ^ n)"
  apply (intro monoI)
  subgoal for x y
    using floor_pow2_add_leq[of x T "y - x"] by force
  done

lemma dyadic_interval_step_Max: "T \<ge> 0 \<Longrightarrow> Max (dyadic_interval_step n 0 T) = \<lfloor>2^n * T\<rfloor> / 2^n"
  apply (simp add: dyadic_interval_step_def)
  apply (subst mono_Max_commute[of "\<lambda>x. real_of_int x / 2^n", symmetric])
  by (auto simp: mono_def field_simps Max_eq_iff)

lemma dyadic_interval_step_subset:
  "n \<le> m \<Longrightarrow> dyadic_interval_step n 0 T \<subseteq> dyadic_interval_step m 0 T"
proof (rule subsetI)
  fix x assume "n \<le> m" "x \<in> dyadic_interval_step n 0 T"
  then obtain k where k:  "k \<ge> 0" "k \<le> \<lfloor>2^n * T\<rfloor>" "x = k / 2^n"
    unfolding dyadic_interval_step_def by fastforce
  then have "k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}"
  proof -
    have "k / 2 ^ n \<le> \<lfloor>2^m * T\<rfloor> / 2 ^ m"
      by (smt floor_pow2_mono[THEN monoD, OF \<open>n \<le> m\<close>] k(2) divide_right_mono of_int_le_iff zero_le_power)
    then have "k / 2 ^ n * 2 ^ m \<le> \<lfloor>2^m * T\<rfloor>"
      by (simp add: field_simps)
    moreover have "k / 2 ^ n * 2 ^ m = k * 2 ^ (m - n)"
      apply (simp add: field_simps)
      apply (metis \<open>n \<le> m\<close> add_diff_inverse_nat not_less power_add)
      done
    ultimately have "k * 2 ^ (m - n) \<le> \<lfloor>2^m * T\<rfloor>"
      by linarith
    then show "k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}"
      using k(1) by simp
  qed
  then show "x \<in> dyadic_interval_step m 0 T"
    apply (subst dyadic_interval_step_iff)
    apply (rule exI[where x="k * 2 ^ (m - n)"])
    apply simp
    apply (simp add: \<open>n \<le> m\<close> k(3) power_diff)
    done
qed

corollary dyadic_interval_step_mono: 
  assumes "x \<in> dyadic_interval_step n 0 T" "n \<le> m"
  shows "x \<in> dyadic_interval_step m 0 T"
  using assms dyadic_interval_step_subset by blast

lemma dyadic_as_natural:
  assumes "x \<in> dyadic_interval_step n 0 T"
  shows "\<exists>!k. x = real k / 2 ^ n"
  using assms
proof (induct n)
  case 0
  then show ?case
    apply simp
    by (metis 0 ceiling_zero div_by_1 dyadic_interval_step_iff mult_not_zero of_nat_eq_iff of_nat_nat power.simps(1))
next
  case (Suc n)
  then show ?case
    by (auto simp: dyadic_interval_step_iff, metis of_nat_nat)
qed

lemma dyadic_of_natural:
  assumes "real k / 2 ^ n \<le> T"
  shows "real k / 2 ^ n  \<in> dyadic_interval_step n 0 T"
  using assms apply (induct n)
   apply simp
   apply (metis atLeastAtMost_iff imageI le_floor_iff of_int_of_nat_eq of_nat_0_le_iff)
  apply (simp add: dyadic_interval_step_iff)
  by (smt (verit, ccfv_SIG) divide_le_eq le_floor_iff mult.commute of_int_of_nat_eq of_nat_0_le_iff zero_less_power)

lemma dyadic_interval_minus:
  assumes "x \<in> dyadic_interval_step n 0 T" "y \<in> dyadic_interval_step n 0 T" "x \<le> y"
  shows "y - x \<in> dyadic_interval_step n 0 T"
proof -
  obtain kx :: nat where "x = real kx / 2 ^ n"
    using dyadic_as_natural assms(1) by blast
  obtain ky :: nat where "y = real ky / 2 ^ n"
    using dyadic_as_natural assms(2) by blast
  then have "y - x = (ky - kx) / 2^n"
    by (smt (verit, ccfv_SIG) \<open>x = real kx / 2 ^ n\<close> add_diff_inverse_nat add_divide_distrib 
        assms(3) divide_strict_right_mono of_nat_add of_nat_less_iff zero_less_power)
  then show ?thesis
    using dyadic_of_natural
    by (smt (verit, best) assms(1,2) dyadic_step_geq dyadic_step_leq)
qed

lemma dyadic_times_nat: "x \<in> dyadic_interval_step n 0 T \<Longrightarrow> (x * 2 ^ n) \<in> \<nat>"
  using dyadic_as_natural by fastforce

definition "dyadic_expansion x n b k \<equiv> set b \<subseteq> {0,1}
  \<and> length b = n \<and> x = real_of_int k + (\<Sum>m\<in>{1..n}. real (b ! (m-1)) / 2 ^ m)"

lemma dyadic_expansionI:
  assumes "set b \<subseteq> {0,1}" "length b = n" "x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)"
  shows "dyadic_expansion x n b k"
  unfolding dyadic_expansion_def using assms by blast

lemma dyadic_expansionD:
  assumes "dyadic_expansion x n b k"
  shows "set b \<subseteq> {0,1}"
    and "length b = n"
    and "x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)"
  using assms unfolding dyadic_expansion_def by simp_all

lemma dyadic_expansion_ex:
  assumes "x \<in> dyadic_interval_step n 0 T" 
  shows "\<exists>b k. dyadic_expansion x n b k"
  using assms
proof (induction n arbitrary: x)
  case 0
  then show ?case
    unfolding dyadic_expansion_def by force
next
  case (Suc n)
  then obtain k where k: "k \<in> {0..\<lfloor>2 ^ (Suc n) * T\<rfloor>}" "x = k / 2 ^ (Suc n)"
    unfolding dyadic_interval_step_def by fastforce
  then have div2: "k div 2 \<in> {0..\<lfloor>2 ^ n * T\<rfloor>}"
    using k(1) apply simp
    by (metis divide_le_eq_numeral1(1) floor_divide_of_int_eq floor_mono le_floor_iff mult.assoc mult.commute of_int_numeral)
  then show ?case
  proof (cases "even k")
    case True
    then have "x = k div 2 / 2 ^ n"
      by (simp add: k(2) real_of_int_div)
    then have "x \<in> dyadic_interval_step n 0 T"
      using dyadic_interval_step_def div2 by force
    then obtain k' b where kb: "dyadic_expansion x n b k'"
      using Suc(1) by blast
    show ?thesis
      apply (rule exI[where x="b @ [0]"])
      apply (rule exI[where x="k'"])
      unfolding dyadic_expansion_def apply safe
      using kb unfolding dyadic_expansion_def apply simp_all
       apply (auto intro!: sum.cong simp: nth_append)
      done
  next
    case False
    then have "k = 2 * (k div 2) + 1"
      by force
    then have "x = k div 2 / 2 ^ n + 1 / 2 ^ (Suc n)"
      by (simp add: k(2) field_simps)
    then have "x - 1 / 2 ^ (Suc n) \<in> dyadic_interval_step n 0 T"
      using div2 by (simp add: dyadic_interval_step_def)
    then obtain k' b where kb: "dyadic_expansion (x-1/2^Suc n) n b k'"
      using Suc(1)[of "x - 1 / 2 ^ (Suc n)"] by blast
    have x: "x = real_of_int k' + (\<Sum>m = 1..n. b ! (m-1) / 2 ^ m) + 1/2^Suc n"
      using dyadic_expansionD(3)[OF kb] by (simp add: field_simps)
    show ?thesis
      apply (rule exI[where x="b @ [1]"])
      apply (rule exI[where x="k'"])
      unfolding dyadic_expansion_def apply safe
      using kb x unfolding dyadic_expansion_def apply simp_all
       apply (auto intro!: sum.cong simp: nth_append)
      done
  qed
qed

lemma dyadic_expansion_frac_le_1: 
  assumes "dyadic_expansion x n b k"
  shows "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) < 1"
proof -
  have "b ! (m - 1) \<in> {0,1}" if "m \<in> {1..n}" for m
  proof -
    from assms have "set b \<subseteq> {0,1}" "length b = n"
      unfolding dyadic_expansion_def by blast+
    then have "a < n \<Longrightarrow> b ! a \<in> {0,1}" for a
      using nth_mem by blast
    moreover have "m - 1 < n"
      using that by force
    ultimately show ?thesis
      by blast
  qed
  then have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<le> (\<Sum>m\<in>{1..n}. 1 / 2 ^ m)"
    apply (intro sum_mono)
    using assms by fastforce
  also have "... = 1 - 1/2^n"
    by (induct n, auto)
  finally show ?thesis
    by (smt (verit, ccfv_SIG) add_divide_distrib divide_strict_right_mono zero_less_power)
qed

lemma dyadic_expansion_frac_range:
  assumes "dyadic_expansion x n b k" "m \<in> {1..n}"
  shows "b ! (m-1) \<in> {0,1}"
proof -
  have "m - 1 < length b"
    using dyadic_expansionD(2)[OF assms(1)] assms(2) by fastforce
  then show ?thesis
    using nth_mem dyadic_expansionD(1)[OF assms(1)] by blast
qed

lemma dyadic_expansion_interval:
  assumes "dyadic_expansion x n b k" "x \<in> {S..T}"
  shows "x \<in> dyadic_interval_step n S T"
proof (subst dyadic_interval_step_iff, intro exI, safe)
  define k' where "k' \<equiv> k * 2^n + (\<Sum>i = 1..n. b!(i-1) * 2^(n-i))"
  show "x = k' / 2^n"
    apply (simp add: dyadic_expansionD(3)[OF assms(1)] k'_def add_divide_distrib sum_divide_distrib)
    apply (intro sum.cong, simp)
    apply (simp add: field_simps)
    by (metis add_diff_inverse_nat linorder_not_le power_add)
  then have "k' = \<lfloor>2^n * x\<rfloor>"
    by simp
  then show "k' \<le> \<lfloor>2 ^ n * T\<rfloor>"
    using assms(2) by (auto intro!: floor_mono mult_left_mono)
  from \<open>x = k'/2^n\<close> have "k' = \<lceil>2^n * x\<rceil>"
    by force
  then show "\<lceil>2 ^ n * S\<rceil> \<le> k'"
    using assms(2) by (auto intro!: ceiling_mono mult_left_mono)
qed

lemma dyadic_expansion_nth_geq:
  assumes "dyadic_expansion x n b k" "m \<in> {1..n}" "b ! (m-1) = 1"
  shows "x \<ge> k + 1/2^m"
proof -
  have "(\<Sum> i = 1..n. f i) = f m + (\<Sum> i \<in> ({1..n} - {m}). f i)" for f :: "nat \<Rightarrow> real"
    by (meson assms(2) finite_atLeastAtMost sum.remove)
  with dyadic_expansionD(3)[OF assms(1)] assms(2,3)
  have "x = k + b!(m-1)/2^m + (\<Sum> i \<in> ({1..n} - {m}). b ! (i-1) / 2^i)"
    by simp
  moreover have "(\<Sum> i \<in> ({1..n} - {m}). b ! (i-1) / 2^i) \<ge> 0"
    by (simp add: sum_nonneg)
  ultimately show ?thesis
    using assms(3) by fastforce
qed

lemma dyadic_expansion_frac_geq_0:
  assumes "dyadic_expansion x n b k"
  shows "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> 0"
proof -
  have "b ! (m - 1) \<in> {0,1}" if "m \<in> {1..n}" for m
    using dyadic_expansion_frac_range[OF assms] that by blast
  then have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> (\<Sum>m\<in>{1..n}. 0)"
    by (intro sum_mono, fastforce)
  then show ?thesis
    by auto
qed

lemma dyadic_expansion_frac:
  assumes "dyadic_expansion x n b k"
  shows "frac x = (\<Sum>m\<in>{1..n}. (b ! (m-1))/ 2 ^ m)"
  apply (simp add: frac_unique_iff)
  apply safe
  using dyadic_expansionD(3)[OF assms] apply simp
  using dyadic_expansion_frac_geq_0[OF assms] apply simp
  using dyadic_expansion_frac_le_1[OF assms] apply simp
  done

lemma dyadic_expansion_floor:
  assumes "dyadic_expansion x n b k"
  shows "k = \<lfloor>x\<rfloor>"
proof -
  have "x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1))/ 2 ^ m)"
    using assms by (rule dyadic_expansionD(3))
  then have "x = k + frac x"
    using dyadic_expansion_frac[OF assms] by linarith
  then have "k = x - frac x"
    by simp
  then show "k = \<lfloor>x\<rfloor>"
    by (metis floor_of_int frac_floor)
qed

lemma sum_interval_pow2_inv: "(\<Sum>m\<in>{Suc l..n}. (1 :: real) / 2 ^ m) = 1 / 2^l - 1/2^n" if "l < n"
  using that proof (induct l)
  case 0
  then show ?case
    by (induct n; fastforce)
next
  case (Suc l)
  have "(\<Sum>m\<in>{Suc l..n} - {Suc l}. (1::real) / 2 ^ m) = (\<Sum>m = Suc l..n. 1 / 2 ^ m) - 1 / 2 ^ Suc l"
    using Suc by (auto simp add: Suc sum_diff1, linarith)
  moreover have "{Suc l..n} - {Suc l} = {Suc (Suc l)..n}" 
    by fastforce
  ultimately have "(\<Sum>m = Suc (Suc l)..n. (1::real) / 2 ^ m) = (\<Sum>m = (Suc l)..n. 1 / 2 ^ m) - 1 / 2^(Suc l)"
    by force
  also have "... = 1 / 2 ^ l - 1 / 2 ^ n - 1 / 2^(Suc l)"
    using Suc by linarith
  also have "... = 1 / 2 ^ Suc l - 1 / 2 ^ n"
    by (simp add: field_simps)
  finally show ?case
    by blast
qed

lemma dyadic_expansion_unique:
  assumes "dyadic_expansion x n b k"
    and "dyadic_expansion x n c j"
  shows "b = c \<and> j = k"
proof (safe, rule ccontr)
  show "j = k"
    using assms dyadic_expansion_floor by blast
  assume "b \<noteq> c"
  have eq: "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
  proof -
    have "k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = j + (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
      using assms dyadic_expansionD(3) by blast
    then show ?thesis
      using \<open>j = k\<close> by linarith
  qed
  have ex: "\<exists>l < n. b ! l \<noteq> c ! l"
    by (metis list_eq_iff_nth_eq assms \<open>b \<noteq> c\<close> dyadic_expansionD(2))
  define l where "l \<equiv> LEAST l. l < n \<and> b ! l \<noteq> c ! l"
  then have l: "l < n" "b ! l \<noteq> c ! l"
    unfolding l_def using LeastI_ex[OF ex] by blast+
  have less_l: "b ! k = c ! k" if \<open>k < l\<close> for k
  proof -
    have "k < n"
      using that l by linarith
    then show "b ! k = c ! k"
      using that unfolding l_def using not_less_Least by blast
  qed
  then have "l \<in> {0..n-1}"
    using l by simp
  then have "l < n"
    apply (simp add: algebra_simps)
    using ex by fastforce
  then have "b ! l \<in> {0,1}" "c ! l \<in> {0,1}"
    by (metis assms insert_absorb insert_subset dyadic_expansionD(1,2) nth_mem)+
  then consider "b ! l = 0 \<and> c ! l = 1" | "b ! l = 1 \<and> c ! l = 0"
    by (smt (verit) LeastI_ex emptyE insertE l_def ex)
  then have sum_ge_l_noteq:"(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m)"
  proof cases
    case 1
    have *: ?thesis if "l + 1 = n"
      using that 1 by auto
    {
      assume \<open>l + 1 < n\<close>
      have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) = 
           (c ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
        by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close>
            atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
      also have "... \<ge> 1 / 2 ^ (l+1)"
        apply (simp add: 1)
        apply (rule sum_nonneg)
        using dyadic_expansion_frac_range[OF assms(2)] by simp
      finally have c_ge: "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) \<ge> 1/2^(l+1)" .
      have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) =
            (b ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
        by (meson \<open>l + 1 < n\<close> nat_less_le sum.atLeast_Suc_atMost)
      also have "... = (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
        using 1 by auto
      also have "... \<le> (\<Sum>m\<in>{Suc (l+1)..n}. 1 / 2 ^ m)"
        apply (rule sum_mono)
        using dyadic_expansion_frac_range[OF assms(1)] apply (simp add: field_simps)
        by (metis (no_types, lifting) One_nat_def add_leE nle_le plus_1_eq_Suc)
      also have "... < 1 / 2 ^ (l+1)"
        using sum_interval_pow2_inv[OF \<open>l + 1 < n\<close>] by fastforce
      finally have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) < 1 / 2 ^ (l+1)" .
      with c_ge have ?thesis
        by argo
    }
    then show ?thesis
      using * \<open>l < n\<close> by linarith
  next
    case 2 (* Copied and pasted from above - WLOG argument *)
    have *: ?thesis if "l + 1 = n"
      using that 2 by auto
    {
      assume \<open>l + 1 < n\<close>
      have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) =
           (b ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
        by (meson \<open>l + 1 < n\<close> nat_less_le sum.atLeast_Suc_atMost)
      also have "... \<ge> 1 / 2 ^ (l+1)"
        apply (simp add: 2)
        apply (rule sum_nonneg)
        using dyadic_expansion_frac_range[OF assms(1)] by simp
      finally have b_ge: "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) \<ge> 1/2^(l+1)" .
      have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) =
            (c ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
        by (meson \<open>l + 1 < n\<close> nat_less_le sum.atLeast_Suc_atMost)
      also have "... = (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
        using 2 by auto
      also have "... \<le> (\<Sum>m\<in>{Suc (l+1)..n}. 1 / 2 ^ m)"
        apply (intro sum_mono divide_right_mono)
        using dyadic_expansion_frac_range[OF assms(2)]
         apply (metis (no_types, opaque_lifting) One_nat_def Suc_leI Suc_le_mono atLeastAtMost_iff
            atLeastAtMost_singleton_iff bot_nat_0.extremum bot_nat_0.not_eq_extremum 
            insert_iff of_nat_eq_1_iff of_nat_le_iff)
        apply simp
        done
      also have "... < 1 / 2 ^ (l+1)"
        using sum_interval_pow2_inv[OF \<open>l + 1 < n\<close>] by fastforce
      finally have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) < 1 / 2 ^ (l+1)" .
      with b_ge have ?thesis
        by argo
    }
    then show ?thesis
      using * \<open>l < n\<close> by linarith
  qed
  moreover have sum_upto_l_eq: "(\<Sum>m\<in>{1..l}. (b ! (m-1)) / 2 ^ m) =
                                (\<Sum>m\<in>{1..l}. (c ! (m-1)) / 2 ^ m)"
    apply (safe intro!: sum.cong)
    apply simp
    by (smt (verit, best) Suc_le_eq Suc_pred \<open>l < n\<close> l_def not_less_Least order_less_trans)
  ultimately have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
  proof -
    have "{1..n} = {1..l} \<union> {l<..n}"
      using \<open>l < n\<close> by auto
    moreover have "{1..l} \<inter> {l<..n} = {}"
      using ivl_disj_int_two(8) by blast
    ultimately have split_sum: "(\<Sum>m \<in>{1..n}. (c ! (m-1)) / 2 ^ m) =
                 (\<Sum>m =1..l. (c ! (m-1)) / 2 ^ m) + (\<Sum>m \<in> {l<..n}. (c ! (m-1)) / 2 ^ m)"
      for c :: "nat list"
      by (simp add: sum_Un)
    then show ?thesis
      using sum_upto_l_eq sum_ge_l_noteq split_sum[of b] split_sum[of c]
      by (smt (verit, del_insts) Suc_eq_plus1 atLeastSucAtMost_greaterThanAtMost)
  qed
  then show False
    using eq by blast
qed

end
