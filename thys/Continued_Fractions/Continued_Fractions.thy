(*
  File:     Continued_Fractions/Continued_Fractions.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Continued Fractions\<close>
theory Continued_Fractions
imports
  Complex_Main
  "Coinductive.Lazy_LList"
  "Coinductive.Coinductive_Nat"
  "HOL-Number_Theory.Fib"
  "HOL-Library.BNF_Corec"
  "Coinductive.Coinductive_Stream"
begin

subsection \<open>Auxiliary results\<close>

(* TODO: Move? *)
coinductive linfinite :: "'a llist \<Rightarrow> bool" where
  "linfinite xs \<Longrightarrow> linfinite (LCons x xs)"

lemma llength_llist_of_stream [simp]: "llength (llist_of_stream xs) = \<infinity>"
  by (simp add: not_lfinite_llength)

lemma linfinite_conv_llength: "linfinite xs \<longleftrightarrow> llength xs = \<infinity>"
proof
  assume "linfinite xs"
  thus "llength xs = \<infinity>"                          
  proof (coinduction arbitrary: xs rule: enat_coinduct2)
    fix xs :: "'a llist"
    assume "llength xs \<noteq> 0" "linfinite xs"
    thus "(\<exists>xs'::'a llist. epred (llength xs) = llength xs' \<and> epred \<infinity> = \<infinity> \<and> linfinite xs') \<or>
             epred (llength xs) = epred \<infinity>"
      by (intro disjI1 exI[of _ "ltl xs"]) (auto simp: linfinite.simps[of xs])
  next
    fix xs :: "'a llist" assume "linfinite xs"thus "(llength xs = 0) \<longleftrightarrow> (\<infinity> = (0::enat))"
      by (subst (asm) linfinite.simps) auto
  qed
next
  assume "llength xs = \<infinity>"
  thus "linfinite xs"
  proof (coinduction arbitrary: xs)
    case linfinite
    thus "\<exists>xsa x.
             xs = LCons x xsa \<and>
             ((\<exists>xs. xsa = xs \<and> llength xs = \<infinity>) \<or>
              linfinite xsa)"
      by (cases xs) (auto simp: eSuc_eq_infinity_iff)
  qed
qed

definition lnth_default :: "'a \<Rightarrow> 'a llist \<Rightarrow> nat \<Rightarrow> 'a" where
  "lnth_default dflt xs n = (if n < llength xs then lnth xs n else dflt)"

lemma lnth_default_code [code]:
  "lnth_default dflt xs n =
     (if lnull xs then dflt else if n = 0 then lhd xs else lnth_default dflt (ltl xs) (n - 1))"
proof (induction n arbitrary: xs)
  case 0
  thus ?case
    by (cases xs) (auto simp: lnth_default_def simp flip: zero_enat_def)
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case LNil
    thus ?thesis
      by (auto simp: lnth_default_def)
  next
    case (LCons x xs')
    thus ?thesis
      by (auto simp: lnth_default_def Suc_ile_eq)
  qed
qed

lemma enat_le_iff:
  "enat n \<le> m \<longleftrightarrow> m = \<infinity> \<or> (\<exists>m'. m = enat m' \<and> n \<le> m')"
  by (cases m) auto

lemma enat_less_iff:
  "enat n < m \<longleftrightarrow> m = \<infinity> \<or> (\<exists>m'. m = enat m' \<and> n < m')"
  by (cases m) auto

lemma real_of_int_divide_in_Ints_iff:
  "real_of_int a / real_of_int b \<in> \<int> \<longleftrightarrow> b dvd a \<or> b = 0"
proof safe
  assume "real_of_int a / real_of_int b \<in> \<int>" "b \<noteq> 0"
  then obtain n where "real_of_int a / real_of_int b = real_of_int n"
    by (auto simp: Ints_def)
  hence "real_of_int b * real_of_int n = real_of_int a"
    using \<open>b \<noteq> 0\<close> by (auto simp: field_simps)
  also have "real_of_int b * real_of_int n = real_of_int (b * n)"
    by simp
  finally have "b * n = a"
    by linarith
  thus "b dvd a"
    by auto
qed auto

lemma frac_add_of_nat: "frac (of_nat y + x) = frac x"
  unfolding frac_def by simp

lemma frac_add_of_int: "frac (of_int y + x) = frac x"
  unfolding frac_def by simp

lemma frac_fraction: "frac (real_of_int a / real_of_int b) = (a mod b) / b"
proof -
  have "frac (a / b) = frac ((a mod b + b * (a div b)) / b)"
    by (subst mod_mult_div_eq) auto
  also have "(a mod b + b * (a div b)) / b = of_int (a div b) + a mod b / b"
    unfolding of_int_add by (subst add_divide_distrib) auto
  also have "frac \<dots> = frac (a mod b / b)"
    by (rule frac_add_of_int)
  also have "\<dots> = a mod b / b"
    by (simp add: floor_divide_of_int_eq frac_def)
  finally show ?thesis .
qed

lemma Suc_fib_ge: "Suc (fib n) \<ge> n"
proof (induction n rule: fib.induct)
  case (3 n)
  show ?case
  proof (cases "n < 2")
    case True
    thus ?thesis by (cases n) auto
  next
    case False
    hence "Suc (Suc (Suc n)) \<le> Suc n + n" by simp
    also have "\<dots> \<le> Suc (fib (Suc n)) + Suc (fib n)"
      by (intro add_mono 3)
    also have "\<dots> = Suc (Suc (fib (Suc (Suc n))))"
      by simp
    finally show ?thesis by (simp only: Suc_le_eq)
  qed
qed auto

lemma fib_ge: "fib n \<ge> n - 1"
  using Suc_fib_ge[of n] by simp

lemma frac_diff_of_nat_right [simp]: "frac (x - of_nat y) = frac x"
  using floor_diff_of_int[of x "int y"] by (simp add: frac_def)

lemma funpow_cycle:
  assumes "m > 0"
  assumes "(f ^^ m) x = x"
  shows   "(f ^^ k) x = (f ^^ (k mod m)) x"
proof (induction k rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k < m")
    case True
    thus ?thesis using \<open>m > 0\<close> by simp
  next
    case False
    hence "k = (k - m) + m" by simp
    also have "(f ^^ \<dots>) x = (f ^^ (k - m)) ((f ^^ m) x)"
      by (simp add: funpow_add)
    also have "(f ^^ m) x = x" by fact
    also have "(f ^^ (k - m)) x = (f ^^ (k mod m)) x"
      using assms False by (subst less.IH) (auto simp: mod_geq)
    finally show ?thesis .
  qed
qed

lemma of_nat_ge_1_iff: "of_nat n \<ge> (1 :: 'a :: linordered_semidom) \<longleftrightarrow> n > 0"
  using of_nat_le_iff[of 1 n] unfolding of_nat_1 by auto

lemma not_frac_less_0: "\<not>frac x < 0"
  by (simp add: frac_def not_less)

lemma frac_le_1: "frac x \<le> 1"
  unfolding frac_def by linarith

lemma divide_in_Rats_iff1:
  "(x::real) \<in> \<rat> \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> x / y \<in> \<rat> \<longleftrightarrow> y \<in> \<rat>"
proof safe
  assume *: "x \<in> \<rat>" "x \<noteq> 0" "x / y \<in> \<rat>"
  from *(1,3) have "x / (x / y) \<in> \<rat>"
    by (rule Rats_divide)
  also from * have "x / (x / y) = y" by simp
  finally show "y \<in> \<rat>" .
qed (auto intro: Rats_divide)

lemma divide_in_Rats_iff2:
  "(y::real) \<in> \<rat> \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x / y \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
proof safe
  assume *: "y \<in> \<rat>" "y \<noteq> 0" "x / y \<in> \<rat>"
  from *(3,1) have "x / y * y \<in> \<rat>"
    by (rule Rats_mult)
  also from * have "x / y * y = x" by simp
  finally show "x \<in> \<rat>" .
qed (auto intro: Rats_divide)

lemma add_in_Rats_iff1: "x \<in> \<rat> \<Longrightarrow> x + y \<in> \<rat> \<longleftrightarrow> y \<in> \<rat>"
  using Rats_diff[of "x + y" x] by auto

lemma add_in_Rats_iff2: "y \<in> \<rat> \<Longrightarrow> x + y \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
  using Rats_diff[of "x + y" y] by auto

lemma diff_in_Rats_iff1: "x \<in> \<rat> \<Longrightarrow> x - y \<in> \<rat> \<longleftrightarrow> y \<in> \<rat>"
  using Rats_diff[of x "x - y"] by auto

lemma diff_in_Rats_iff2: "y \<in> \<rat> \<Longrightarrow> x - y \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
  using Rats_add[of "x - y" y] by auto

lemma frac_in_Rats_iff [simp]: "frac x \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
  by (simp add: frac_def diff_in_Rats_iff2)

lemma filterlim_sequentially_shift:
  "filterlim (\<lambda>n. f (n + m)) F sequentially \<longleftrightarrow> filterlim f F sequentially"
proof (induction m)
  case (Suc m)
  have "filterlim (\<lambda>n. f (n + Suc m)) F at_top \<longleftrightarrow>
          filterlim (\<lambda>n. f (Suc n + m)) F at_top" by simp
  also have "\<dots> \<longleftrightarrow> filterlim (\<lambda>n. f (n + m)) F at_top"
    by (rule filterlim_sequentially_Suc)
  also have "\<dots> \<longleftrightarrow> filterlim f F at_top"
    by (rule Suc.IH)
  finally show ?case .
qed simp_all


subsection \<open>Bounds on alternating decreasing sums\<close>

lemma alternating_decreasing_sum_bounds:
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m \<le> n" "\<And>k. k \<in> {m..n} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n} \<Longrightarrow> f (Suc k) \<le> f k"
  defines "S \<equiv> (\<lambda>m. (\<Sum>k=m..n. (-1) ^ k * f k))"
  shows   "if even m then S m \<in> {0..f m} else S m \<in> {-f m..0}"
  using assms(1)
proof (induction rule: inc_induct)
  case (step m')
  have [simp]: "-a \<le> b \<longleftrightarrow> a + b \<ge> (0 :: 'a)" for a b
    by (metis le_add_same_cancel1 minus_add_cancel)
  have [simp]: "S m' = (-1) ^ m' * f m' + S (Suc m')"
    using step.hyps unfolding S_def
    by (subst sum.atLeast_Suc_atMost) simp_all
  from step.hyps have nonneg: "f m' \<ge> 0"
    by (intro assms) auto
  from step.hyps have mono: "f (Suc m') \<le> f m'"
    by (intro assms) auto
  show ?case
  proof (cases "even m'")
    case True
    hence "0 \<le> f (Suc m') + S (Suc m')"
      using step.IH by simp
    also note mono
    finally show ?thesis using True step.IH by auto
  next
    case False
    with step.IH have "S (Suc m') \<le> f (Suc m')"
      by simp
    also note mono
    finally show ?thesis using step.IH False by auto
  qed
qed (insert assms, auto)

lemma alternating_decreasing_sum_bounds':
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m < n" "\<And>k. k \<in> {m..n-1} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n-1} \<Longrightarrow> f (Suc k) \<le> f k"
  defines "S \<equiv> (\<lambda>m. (\<Sum>k=m..<n. (-1) ^ k * f k))"
  shows   "if even m then S m \<in> {0..f m} else S m \<in> {-f m..0}"
proof (cases n)
  case 0
  thus ?thesis using assms by auto
next
  case (Suc n')
  hence "if even m then (\<Sum>k=m..n-1. (-1) ^ k * f k) \<in> {0..f m}
           else (\<Sum>k=m..n-1. (-1) ^ k * f k) \<in> {-f m..0}"
    using assms by (intro alternating_decreasing_sum_bounds) auto
  also have "(\<Sum>k=m..n-1. (-1) ^ k * f k) = S m"
    unfolding S_def by (intro sum.cong) (auto simp: Suc)
  finally show ?thesis .
qed

lemma alternating_decreasing_sum_upper_bound:
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m \<le> n" "\<And>k. k \<in> {m..n} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "(\<Sum>k=m..n. (-1) ^ k * f k) \<le> f m"
  using alternating_decreasing_sum_bounds[of m n f, OF assms] assms(1)
  by (auto split: if_splits intro: order.trans[OF _ assms(2)])

lemma alternating_decreasing_sum_upper_bound':
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m < n" "\<And>k. k \<in> {m..n-1} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n-1} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "(\<Sum>k=m..<n. (-1) ^ k * f k) \<le> f m"
  using alternating_decreasing_sum_bounds'[of m n f, OF assms] assms(1)
  by (auto split: if_splits intro: order.trans[OF _ assms(2)])

lemma abs_alternating_decreasing_sum_upper_bound:
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m \<le> n" "\<And>k. k \<in> {m..n} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "\<bar>(\<Sum>k=m..n. (-1) ^ k * f k)\<bar> \<le> f m" (is "abs ?S \<le> _")
  using alternating_decreasing_sum_bounds[of m n f, OF assms]
  by (auto split: if_splits simp: minus_le_iff)

lemma abs_alternating_decreasing_sum_upper_bound':
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m < n" "\<And>k. k \<in> {m..n-1} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n-1} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "\<bar>(\<Sum>k=m..<n. (-1) ^ k * f k)\<bar> \<le> f m"
  using alternating_decreasing_sum_bounds'[of m n f, OF assms]
  by (auto split: if_splits simp: minus_le_iff)

lemma abs_alternating_decreasing_sum_lower_bound:
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m < n" "\<And>k. k \<in> {m..n} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "\<bar>(\<Sum>k=m..n. (-1) ^ k * f k)\<bar> \<ge> f m - f (Suc m)"
proof -
  have "(\<Sum>k=m..n. (-1) ^ k * f k) = (\<Sum>k\<in>insert m {m<..n}. (-1) ^ k * f k)"
    using assms by (intro sum.cong) auto
  also have "\<dots> = (-1) ^ m * f m + (\<Sum>k\<in>{m<..n}. (-1) ^ k * f k)"
    by auto
  also have "(\<Sum>k\<in>{m<..n}. (-1) ^ k * f k) = (\<Sum>k\<in>{m..<n}. (-1) ^ Suc k * f (Suc k))"
    by (intro sum.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1"]) auto
  also have "(-1)^m * f m + \<dots> = (-1)^m * f m - (\<Sum>k\<in>{m..<n}. (-1) ^ k * f (Suc k))"
    by (simp add: sum_negf)
  also have "\<bar>\<dots>\<bar> \<ge> \<bar>(-1)^m * f m\<bar> - \<bar>(\<Sum>k\<in>{m..<n}. (-1) ^ k * f (Suc k))\<bar>"
    by (rule abs_triangle_ineq2)
  also have "\<bar>(-1)^m * f m\<bar> = f m"
    using assms by (cases "even m") auto
  finally have "f m - \<bar>\<Sum>k = m..<n. (- 1) ^ k * f (Suc k)\<bar>
                  \<le> \<bar>\<Sum>k = m..n. (- 1) ^ k * f k\<bar>" .
  moreover have "f m - \<bar>(\<Sum>k\<in>{m..<n}. (-1) ^ k * f (Suc k))\<bar> \<ge> f m - f (Suc m)"
    using assms by (intro diff_mono abs_alternating_decreasing_sum_upper_bound') auto
  ultimately show ?thesis by (rule order.trans[rotated])
qed

lemma abs_alternating_decreasing_sum_lower_bound':
  fixes f :: "nat \<Rightarrow> 'a :: {linordered_ring, ring_1}"
  assumes "m+1 < n" "\<And>k. k \<in> {m..n} \<Longrightarrow> f k \<ge> 0"
          "\<And>k. k \<in> {m..<n} \<Longrightarrow> f (Suc k) \<le> f k"
  shows   "\<bar>(\<Sum>k=m..<n. (-1) ^ k * f k)\<bar> \<ge> f m - f (Suc m)"
proof (cases n)
  case 0
  thus ?thesis using assms by auto
next
  case (Suc n')
  hence "\<bar>(\<Sum>k=m..n-1. (-1) ^ k * f k)\<bar> \<ge> f m - f (Suc m)"
    using assms by (intro abs_alternating_decreasing_sum_lower_bound) auto
  also have "(\<Sum>k=m..n-1. (-1) ^ k * f k) = (\<Sum>k=m..<n. (-1) ^ k * f k)"
    by (intro sum.cong) (auto simp: Suc)
  finally show ?thesis .
qed

lemma alternating_decreasing_suminf_bounds:
  assumes "\<And>k. f k \<ge> (0 :: real)" "\<And>k. f (Suc k) \<le> f k"
          "f \<longlonglongrightarrow> 0"
  shows   "(\<Sum>k. (-1) ^ k * f k) \<in> {f 0 - f 1..f 0}"
proof -
  have "summable (\<lambda>k. (-1) ^ k * f k)"
    by (intro summable_Leibniz' assms)
  hence lim: "(\<lambda>n. \<Sum>k\<le>n. (-1) ^ k * f k) \<longlonglongrightarrow> (\<Sum>k. (-1) ^ k * f k)"
    by (auto dest: summable_LIMSEQ')
  have bounds: "(\<Sum>k=0..n. (- 1) ^ k * f k) \<in> {f 0 - f 1..f 0}"
    if "n > 0" for n
    using alternating_decreasing_sum_bounds[of 1 n f] assms that
    by (subst sum.atLeast_Suc_atMost) auto
  note [simp] = atLeast0AtMost
  note [intro!] = eventually_mono[OF eventually_gt_at_top[of 0]]
 
  from lim have "(\<Sum>k. (-1) ^ k * f k) \<ge> f 0 - f 1"
    by (rule tendsto_lowerbound) (insert bounds, auto)
  moreover from lim have "(\<Sum>k. (-1) ^ k * f k) \<le> f 0"
    by (rule tendsto_upperbound) (use bounds in auto)
  ultimately show ?thesis by simp
qed

lemma
  assumes "\<And>k. k \<ge> m \<Longrightarrow> f k \<ge> (0 :: real)"
          "\<And>k. k \<ge> m \<Longrightarrow> f (Suc k) \<le> f k" "f \<longlonglongrightarrow> 0"
  defines "S \<equiv> (\<Sum>k. (-1) ^ (k + m) * f (k + m))"
  shows   summable_alternating_decreasing: "summable (\<lambda>k. (-1) ^ (k + m) * f (k + m))"
    and   alternating_decreasing_suminf_bounds':
            "if even m then S \<in> {f m - f (Suc m) .. f m}
               else S \<in> {-f m..f (Suc m) - f m}" (is ?th1)
    and   abs_alternating_decreasing_suminf:
            "abs S \<in> {f m - f (Suc m)..f m}" (is ?th2)
proof -
  have summable: "summable (\<lambda>k. (-1) ^ k * f (k + m))"
    using assms by (intro summable_Leibniz') (auto simp: filterlim_sequentially_shift)
  thus "summable (\<lambda>k. (-1) ^ (k + m) * f (k + m))"
    by (subst add.commute) (auto simp: power_add mult.assoc intro: summable_mult)
  have "S = (\<Sum>k. (-1) ^ m * ((-1) ^ k * f (k + m)))"
    by (simp add: S_def power_add mult_ac)
  also have "\<dots> = (-1) ^ m * (\<Sum>k. (-1) ^ k * f (k + m))"
    using summable by (rule suminf_mult)
  finally have "S = (- 1) ^ m * (\<Sum>k. (- 1) ^ k * f (k + m))" .
  moreover have "(\<Sum>k. (-1) ^ k * f (k + m)) \<in>
     {f (0 + m) - f (1 + m) .. f (0 + m)}"
    using assms
    by (intro alternating_decreasing_suminf_bounds)
       (auto simp: filterlim_sequentially_shift)
  ultimately show ?th1 by (auto split: if_splits)
  thus ?th2 using assms(2)[of m] by (auto split: if_splits)
qed

lemma
  assumes "\<And>k. k \<ge> m \<Longrightarrow> f k \<ge> (0 :: real)"
          "\<And>k. k \<ge> m \<Longrightarrow> f (Suc k) < f k" "f \<longlonglongrightarrow> 0"
  defines "S \<equiv> (\<Sum>k. (-1) ^ (k + m) * f (k + m))"
  shows   alternating_decreasing_suminf_bounds_strict':
            "if even m then S \<in> {f m - f (Suc m)<..<f m}
               else S \<in> {-f m<..<f (Suc m) - f m}" (is ?th1)
    and   abs_alternating_decreasing_suminf_strict:
            "abs S \<in> {f m - f (Suc m)<..<f m}" (is ?th2)
proof -
  define S' where "S' = (\<Sum>k. (-1) ^ (k + Suc (Suc m)) * f (k + Suc (Suc m)))"
  have "(\<lambda>k. (-1) ^ (k + m) * f (k + m)) sums S" using assms unfolding S_def
    by (intro summable_sums summable_Leibniz' summable_alternating_decreasing)
       (auto simp: less_eq_real_def)
  from sums_split_initial_segment[OF this, of 2]
    have S': "S' = S - (-1) ^ m * (f m - f (Suc m))"
    by (simp_all add: sums_iff S'_def algebra_simps lessThan_nat_numeral)
  have "if even (Suc (Suc m)) then S' \<in> {f (Suc (Suc m)) - f (Suc (Suc (Suc m)))..f (Suc (Suc m))}
        else S' \<in> {- f (Suc (Suc m))..f (Suc (Suc (Suc m))) - f (Suc (Suc m))}" unfolding S'_def
    using assms by (intro alternating_decreasing_suminf_bounds') (auto simp: less_eq_real_def)
  thus ?th1 using assms(2)[of "Suc m"] assms(2)[of "Suc (Suc m)"]
    unfolding S' by (auto simp: algebra_simps)
  thus ?th2 using assms(2)[of m] by (auto split: if_splits)
qed


datatype cfrac = CFrac int "nat llist"

quickcheck_generator cfrac constructors: CFrac

lemma type_definition_cfrac':
  "type_definition (\<lambda>x. case x of CFrac a b \<Rightarrow> (a, b)) (\<lambda>(x,y). CFrac x y) UNIV"
  by (auto simp: type_definition_def split: cfrac.splits)

setup_lifting type_definition_cfrac'

lift_definition cfrac_of_int :: "int \<Rightarrow> cfrac" is
  "\<lambda>n. (n, LNil)" .

lemma cfrac_of_int_code [code]: "cfrac_of_int n = CFrac n LNil"
  by (auto simp: cfrac_of_int_def)

lift_definition cfrac_of_stream :: "int stream \<Rightarrow> cfrac" is
  "\<lambda>xs. (shd xs, llist_of_stream (smap (\<lambda>x. nat (x - 1)) (stl xs)))" .

instantiation cfrac :: zero
begin
definition zero_cfrac where "0 = cfrac_of_int 0"
instance ..
end

instantiation cfrac :: one
begin
definition one_cfrac where "1 = cfrac_of_int 1"
instance ..
end

lift_definition cfrac_tl :: "cfrac \<Rightarrow> cfrac" is
  "\<lambda>(_, bs) \<Rightarrow> case bs of LNil \<Rightarrow> (1, LNil) | LCons b bs' \<Rightarrow> (int b + 1, bs')" .

lemma cfrac_tl_code [code]:
  "cfrac_tl (CFrac a bs) =
     (case bs of LNil \<Rightarrow> CFrac 1 LNil | LCons b bs' \<Rightarrow> CFrac (int b + 1) bs')"
  by (auto simp: cfrac_tl_def split: llist.splits)

definition cfrac_drop :: "nat \<Rightarrow> cfrac \<Rightarrow> cfrac" where
  "cfrac_drop n c = (cfrac_tl ^^ n) c"

lemma cfrac_drop_Suc_right: "cfrac_drop (Suc n) c = cfrac_drop n (cfrac_tl c)"
  by (simp add: cfrac_drop_def funpow_Suc_right del: funpow.simps)

lemma cfrac_drop_Suc_left: "cfrac_drop (Suc n) c = cfrac_tl (cfrac_drop n c)"
  by (simp add: cfrac_drop_def)

lemma cfrac_drop_add: "cfrac_drop (m + n) c = cfrac_drop m (cfrac_drop n c)"
  by (simp add: cfrac_drop_def funpow_add)

lemma cfrac_drop_0 [simp]: "cfrac_drop 0 = (\<lambda>x. x)"
  by (simp add: fun_eq_iff cfrac_drop_def)

lemma cfrac_drop_1 [simp]: "cfrac_drop 1 = cfrac_tl"
  by (simp add: fun_eq_iff cfrac_drop_def)

lift_definition cfrac_length :: "cfrac \<Rightarrow> enat" is
  "\<lambda>(_, bs) \<Rightarrow> llength bs" .

lemma cfrac_length_code [code]: "cfrac_length (CFrac a bs) = llength bs"
  by (simp add: cfrac_length_def)

lemma cfrac_length_tl [simp]: "cfrac_length (cfrac_tl c) = cfrac_length c - 1"
  by transfer (auto split: llist.splits)

lemma enat_diff_Suc_right [simp]: "m - enat (Suc n) = m - n - 1"
  by (auto simp: diff_enat_def enat_1_iff split: enat.splits)

lemma cfrac_length_drop [simp]: "cfrac_length (cfrac_drop n c) = cfrac_length c - n"
  by (induction n) (auto simp: cfrac_drop_def)

lemma cfrac_length_of_stream [simp]: "cfrac_length (cfrac_of_stream xs) = \<infinity>"
  by transfer auto

lift_definition cfrac_nth :: "cfrac \<Rightarrow> nat \<Rightarrow> int" is
  "\<lambda>(a :: int, bs :: nat llist). \<lambda>(n :: nat).
      if n = 0 then a
      else if n \<le> llength bs then int (lnth bs (n - 1)) + 1 else 1" .

lemma cfrac_nth_code [code]:
  "cfrac_nth (CFrac a bs) n = (if n = 0 then a else lnth_default 0 bs (n - 1) + 1)"
proof -
  have "n > 0 \<longrightarrow> enat (n - Suc 0) < llength bs \<longleftrightarrow> enat n \<le> llength bs"
    by (metis Suc_ile_eq Suc_pred)
  thus ?thesis by (auto simp: cfrac_nth_def lnth_default_def)
qed

lemma cfrac_nth_nonneg [simp, intro]: "n > 0 \<Longrightarrow> cfrac_nth c n \<ge> 0"
  by transfer auto

lemma cfrac_nth_nonzero [simp]: "n > 0 \<Longrightarrow> cfrac_nth c n \<noteq> 0"
  by transfer (auto split: if_splits)

lemma cfrac_nth_pos[simp, intro]: "n > 0 \<Longrightarrow> cfrac_nth c n > 0"
  by transfer auto

lemma cfrac_nth_ge_1[simp, intro]: "n > 0 \<Longrightarrow> cfrac_nth c n \<ge> 1"
  by transfer auto

lemma cfrac_nth_not_less_1[simp, intro]: "n > 0 \<Longrightarrow> \<not>cfrac_nth c n < 1"
  by transfer (auto split: if_splits)

lemma cfrac_nth_tl [simp]: "cfrac_nth (cfrac_tl c) n = cfrac_nth c (Suc n)"
  apply transfer
  apply (auto split: llist.splits nat.splits simp: Suc_ile_eq lnth_LCons enat_0_iff
              simp flip: zero_enat_def)
  done

lemma cfrac_nth_drop [simp]: "cfrac_nth (cfrac_drop n c) m = cfrac_nth c (m + n)"
  by (induction n arbitrary: m) (auto simp: cfrac_drop_def)

lemma cfrac_nth_0_of_int [simp]: "cfrac_nth (cfrac_of_int n) 0 = n"
  by transfer auto

lemma cfrac_nth_gt0_of_int [simp]: "m > 0 \<Longrightarrow> cfrac_nth (cfrac_of_int n) m = 1"
  by transfer (auto simp: enat_0_iff)

lemma cfrac_nth_of_stream:
  assumes "sset (stl xs) \<subseteq> {0<..}"
  shows   "cfrac_nth (cfrac_of_stream xs) n = snth xs n"
  using assms
proof (transfer', goal_cases)
  case (1 xs n)
  thus ?case
    by (cases xs; cases n) (auto simp: subset_iff)
qed


lift_definition cfrac :: "(nat \<Rightarrow> int) \<Rightarrow> cfrac" is
  "\<lambda>f. (f 0, inf_llist (\<lambda>n. nat (f (Suc n) - 1)))" .

definition is_cfrac :: "(nat \<Rightarrow> int) \<Rightarrow> bool" where "is_cfrac f \<longleftrightarrow> (\<forall>n>0. f n > 0)"

lemma cfrac_nth_cfrac [simp]:
  assumes "is_cfrac f"
  shows   "cfrac_nth (cfrac f) n = f n"
  using assms unfolding is_cfrac_def by transfer auto

lemma llength_eq_infty_lnth: "llength b = \<infinity> \<Longrightarrow> inf_llist (lnth b) = b"
  by (simp add: llength_eq_infty_conv_lfinite)

lemma cfrac_cfrac_nth [simp]: "cfrac_length c = \<infinity> \<Longrightarrow> cfrac (cfrac_nth c) = c"
  by transfer (auto simp: llength_eq_infty_lnth)

lemma cfrac_length_cfrac [simp]: "cfrac_length (cfrac f) = \<infinity>"
  by transfer auto


lift_definition cfrac_of_list :: "int list \<Rightarrow> cfrac" is
  "\<lambda>xs. if xs = [] then (0, LNil) else (hd xs, llist_of (map (\<lambda>n. nat n - 1) (tl xs)))" .

lemma cfrac_length_of_list [simp]: "cfrac_length (cfrac_of_list xs) = length xs - 1"
  by transfer (auto simp: zero_enat_def)

lemma cfrac_of_list_Nil [simp]: "cfrac_of_list [] = 0"
  unfolding zero_cfrac_def by transfer auto

lemma cfrac_nth_of_list [simp]:
  assumes "n < length xs" and "\<forall>i\<in>{0<..<length xs}. xs ! i > 0"
  shows   "cfrac_nth (cfrac_of_list xs) n = xs ! n"
  using assms
proof (transfer, goal_cases)
  case (1 n xs)
  show ?case
  proof (cases n)
    case (Suc n')
    with 1 have "xs ! n > 0"
      using 1 by auto
    hence "int (nat (tl xs ! n') - Suc 0) + 1 = xs ! Suc n'"
      using 1(1) Suc by (auto simp: nth_tl of_nat_diff)
    thus ?thesis
      using Suc 1(1) by (auto simp: hd_conv_nth zero_enat_def)
  qed (use 1 in \<open>auto simp: hd_conv_nth\<close>)
qed


primcorec cfrac_of_real_aux :: "real \<Rightarrow> nat llist" where
  "cfrac_of_real_aux x =
     (if x \<in> {0<..<1} then LCons (nat \<lfloor>1/x\<rfloor> - 1) (cfrac_of_real_aux (frac (1/x))) else LNil)"

lemma cfrac_of_real_aux_code [code]:
  "cfrac_of_real_aux x =
     (if x > 0 \<and> x < 1 then LCons (nat \<lfloor>1/x\<rfloor> - 1) (cfrac_of_real_aux (frac (1/x))) else LNil)"
  by (subst cfrac_of_real_aux.code) auto
  

lemma cfrac_of_real_aux_LNil [simp]: "x \<notin> {0<..<1} \<Longrightarrow> cfrac_of_real_aux x = LNil"
  by (subst cfrac_of_real_aux.code) auto

lemma cfrac_of_real_aux_0 [simp]: "cfrac_of_real_aux 0 = LNil"
  by (subst cfrac_of_real_aux.code) auto

lemma cfrac_of_real_aux_eq_LNil_iff [simp]: "cfrac_of_real_aux x = LNil \<longleftrightarrow> x \<notin> {0<..<1}"
  by (subst cfrac_of_real_aux.code) auto

lemma lnth_cfrac_of_real_aux:
  assumes "n < llength (cfrac_of_real_aux x)"
  shows   "lnth (cfrac_of_real_aux x) (Suc n) = lnth (cfrac_of_real_aux (frac (1/x))) n"
  using assms
  apply (induction n arbitrary: x)
   apply (subst cfrac_of_real_aux.code)
   apply auto []
  apply (subst cfrac_of_real_aux.code)
  apply (auto)
  done

lift_definition cfrac_of_real :: "real \<Rightarrow> cfrac" is
  "\<lambda>x. (\<lfloor>x\<rfloor>, cfrac_of_real_aux (frac x))" .

lemma cfrac_of_real_code [code]: "cfrac_of_real x = CFrac \<lfloor>x\<rfloor> (cfrac_of_real_aux (frac x))"
  by (simp add: cfrac_of_real_def)

lemma eq_epred_iff: "m = epred n \<longleftrightarrow> m = 0 \<and> n = 0 \<or> n = eSuc m"
  by (cases m; cases n) (auto simp: enat_0_iff enat_eSuc_iff infinity_eq_eSuc_iff)

lemma epred_eq_iff: "epred n = m \<longleftrightarrow> m = 0 \<and> n = 0 \<or> n = eSuc m"
  by (cases m; cases n) (auto simp: enat_0_iff enat_eSuc_iff infinity_eq_eSuc_iff)

lemma epred_less: "n > 0 \<Longrightarrow> n \<noteq> \<infinity> \<Longrightarrow> epred n < n"
  by (cases n) (auto simp: enat_0_iff)

lemma cfrac_nth_of_real_0 [simp]:
  "cfrac_nth (cfrac_of_real x) 0 = \<lfloor>x\<rfloor>"
  by transfer auto

lemma frac_eq_0 [simp]: "x \<in> \<int> \<Longrightarrow> frac x = 0"
  by simp

lemma cfrac_tl_of_real:
  assumes "x \<notin> \<int>"
  shows   "cfrac_tl (cfrac_of_real x) = cfrac_of_real (1 / frac x)"
  using assms
proof (transfer, goal_cases)
  case (1 x)
  hence "int (nat \<lfloor>1 / frac x\<rfloor> - Suc 0) + 1 = \<lfloor>1 / frac x\<rfloor>"
    by (subst of_nat_diff) (auto simp: le_nat_iff frac_le_1)
  with \<open>x \<notin> \<int>\<close> show ?case
  by (subst cfrac_of_real_aux.code) (auto split: llist.splits simp: frac_lt_1)
qed

lemma cfrac_nth_of_real_Suc:
  assumes "x \<notin> \<int>"
  shows   "cfrac_nth (cfrac_of_real x) (Suc n) = cfrac_nth (cfrac_of_real (1 / frac x)) n"
proof -
  have "cfrac_nth (cfrac_of_real x) (Suc n) =
          cfrac_nth (cfrac_tl (cfrac_of_real x)) n"
    by simp
  also have "cfrac_tl (cfrac_of_real x) = cfrac_of_real (1 / frac x)"
    by (simp add: cfrac_tl_of_real assms)
  finally show ?thesis .
qed


fun conv :: "cfrac \<Rightarrow> nat \<Rightarrow> real" where
  "conv c 0 = real_of_int (cfrac_nth c 0)"
| "conv c (Suc n) = real_of_int (cfrac_nth c 0) + 1 / conv (cfrac_tl c) n"


text \<open>
  The numerator and denominator of a convergent:
\<close>
fun conv_num :: "cfrac \<Rightarrow> nat \<Rightarrow> int" where
  "conv_num c 0 = cfrac_nth c 0"
| "conv_num c (Suc 0) = cfrac_nth c 1 * cfrac_nth c 0 + 1"
| "conv_num c (Suc (Suc n)) = cfrac_nth c (Suc (Suc n)) * conv_num c (Suc n) + conv_num c n"

fun conv_denom :: "cfrac \<Rightarrow> nat \<Rightarrow> int" where
  "conv_denom c 0 = 1"
| "conv_denom c (Suc 0) = cfrac_nth c 1"
| "conv_denom c (Suc (Suc n)) = cfrac_nth c (Suc (Suc n)) * conv_denom c (Suc n) + conv_denom c n"

lemma conv_num_rec:
  "n \<ge> 2 \<Longrightarrow> conv_num c n = cfrac_nth c n * conv_num c (n - 1) + conv_num c (n - 2)"
  by (cases n; cases "n - 1") auto

lemma conv_denom_rec:
  "n \<ge> 2 \<Longrightarrow> conv_denom c n = cfrac_nth c n * conv_denom c (n - 1) + conv_denom c (n - 2)"
  by (cases n; cases "n - 1") auto


fun conv' :: "cfrac \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "conv' c 0 z = z"
| "conv' c (Suc n) z = conv' c n (real_of_int (cfrac_nth c n) + 1 / z)"

text \<open>
  Occasionally, it can be useful to extend the domain of @{const conv_num} and @{const conv_denom}
  to \<open>-1\<close> and \<open>-2\<close>.
\<close>
definition conv_num_int :: "cfrac \<Rightarrow> int \<Rightarrow> int" where
  "conv_num_int c n = (if n = -1 then 1 else if n < 0 then 0 else conv_num c (nat n))"

definition conv_denom_int :: "cfrac \<Rightarrow> int \<Rightarrow> int" where
  "conv_denom_int c n = (if n = -2 then 1 else if n < 0 then 0 else conv_denom c (nat n))"

lemma conv_num_int_rec:
  assumes "n \<ge> 0"
  shows   "conv_num_int c n = cfrac_nth c (nat n) * conv_num_int c (n - 1) + conv_num_int c (n - 2)"
proof (cases "n \<ge> 2")
  case True
  define n' where "n' = nat (n - 2)"
  have n: "n = int (Suc (Suc n'))"
    using True by (simp add: n'_def)
  show ?thesis
    by (simp add: n conv_num_int_def nat_add_distrib)
qed (use assms in \<open>auto simp: conv_num_int_def\<close>)

lemma conv_denom_int_rec:
  assumes "n \<ge> 0"
  shows   "conv_denom_int c n = cfrac_nth c (nat n) * conv_denom_int c (n - 1) + conv_denom_int c (n - 2)"
proof -
  consider "n = 0" | "n = 1" | "n \<ge> 2"
    using assms by force
  thus ?thesis
  proof cases
    assume "n \<ge> 2"
    define n' where "n' = nat (n - 2)"
    have n: "n = int (Suc (Suc n'))"
      using \<open>n \<ge> 2\<close> by (simp add: n'_def)
    show ?thesis
      by (simp add: n conv_denom_int_def nat_add_distrib)
  qed (use assms in \<open>auto simp: conv_denom_int_def\<close>)
qed

text \<open>
  The number \<open>[a\<^sub>0; a\<^sub>1, a\<^sub>2, \<dots>]\<close> that the infinite continued fraction converges to:
\<close>
definition cfrac_lim :: "cfrac \<Rightarrow> real" where
  "cfrac_lim c =
     (case cfrac_length c of \<infinity> \<Rightarrow> lim (conv c) | enat l \<Rightarrow> conv c l)"

lemma cfrac_lim_code [code]:
  "cfrac_lim c =
     (case cfrac_length c of enat l \<Rightarrow> conv c l
      | _ \<Rightarrow> Code.abort (STR ''Cannot compute infinite continued fraction'') (\<lambda>_. cfrac_lim c))"
  by (simp add: cfrac_lim_def split: enat.splits)

definition cfrac_remainder where "cfrac_remainder c n = cfrac_lim (cfrac_drop n c)"

lemmas conv'_Suc_right = conv'.simps(2)

lemma conv'_Suc_left:
  assumes "z > 0"
  shows "conv' c (Suc n) z =
           real_of_int (cfrac_nth c 0) + 1 / conv' (cfrac_tl c) n z"
  using assms
proof (induction n arbitrary: z)
  case (Suc n z)
  have "conv' c (Suc (Suc n)) z = 
          conv' c (Suc n) (real_of_int (cfrac_nth c (Suc n)) + 1 / z)"
    by simp
  also have "\<dots> = cfrac_nth c 0 + 1 / conv' (cfrac_tl c) (Suc n) z"
    using Suc.prems by (subst Suc.IH) (auto intro!: add_nonneg_pos cfrac_nth_nonneg)
  finally show ?case .
qed simp_all

lemmas [simp del] = conv'.simps(2)

lemma conv'_left_induct:
  assumes "\<And>c. P c 0 z" "\<And>c n. P (cfrac_tl c) n z \<Longrightarrow> P c (Suc n) z"
  shows   "P c n z"
  using assms by (rule conv.induct)

lemma enat_less_diff_conv [simp]:
  assumes "a = \<infinity> \<or> b < \<infinity> \<or> c < \<infinity>"
  shows   "a < c - (b :: enat) \<longleftrightarrow> a + b < c"
  using assms by (cases a; cases b; cases c) auto

lemma conv_eq_conv': "conv c n = conv' c n (cfrac_nth c n)"
proof (cases "n = 0")
  case False
  hence "cfrac_nth c n > 0" by (auto intro!: cfrac_nth_pos)
  thus ?thesis
    by (induction c n rule: conv.induct) (simp_all add: conv'_Suc_left)
qed simp_all

lemma conv_num_pos':
  assumes "cfrac_nth c 0 > 0"
  shows   "conv_num c n > 0"
  using assms by (induction n rule: fib.induct) (auto simp: intro!: add_pos_nonneg)

lemma conv_num_nonneg: "cfrac_nth c 0 \<ge> 0 \<Longrightarrow> conv_num c n \<ge> 0"
  by (induction c n rule: conv_num.induct)
     (auto simp: intro!: mult_nonneg_nonneg add_nonneg_nonneg
           intro: cfrac_nth_nonneg)

lemma conv_num_pos:
  "cfrac_nth c 0 \<ge> 0 \<Longrightarrow> n > 0 \<Longrightarrow> conv_num c n > 0"
  by (induction c n rule: conv_num.induct)
     (auto intro!: mult_pos_pos mult_nonneg_nonneg add_pos_nonneg conv_num_nonneg cfrac_nth_pos
           intro: cfrac_nth_nonneg simp:  enat_le_iff)

lemma conv_denom_pos [simp, intro]: "conv_denom c n > 0"
  by (induction c n rule: conv_num.induct)
     (auto intro!: add_nonneg_pos mult_nonneg_nonneg cfrac_nth_nonneg
           simp: enat_le_iff)

lemma conv_denom_not_nonpos [simp]: "\<not>conv_denom c n \<le> 0"
  using conv_denom_pos[of c n] by linarith

lemma conv_denom_not_neg [simp]: "\<not>conv_denom c n < 0"
  using conv_denom_pos[of c n] by linarith

lemma conv_denom_nonzero [simp]: "conv_denom c n \<noteq> 0"
  using conv_denom_pos[of c n] by linarith

lemma conv_denom_nonneg [simp, intro]: "conv_denom c n \<ge> 0"
  using conv_denom_pos[of c n] by linarith

lemma conv_num_int_neg1 [simp]: "conv_num_int c (-1) = 1"
  by (simp add: conv_num_int_def)

lemma conv_num_int_neg [simp]: "n < 0 \<Longrightarrow> n \<noteq> -1 \<Longrightarrow> conv_num_int c n = 0"
  by (simp add: conv_num_int_def)

lemma conv_num_int_of_nat [simp]: "conv_num_int c (int n) = conv_num c n"
  by (simp add: conv_num_int_def)

lemma conv_num_int_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> conv_num_int c n = conv_num c (nat n)"
  by (simp add: conv_num_int_def)

lemma conv_denom_int_neg2 [simp]: "conv_denom_int c (-2) = 1"
  by (simp add: conv_denom_int_def)

lemma conv_denom_int_neg [simp]: "n < 0 \<Longrightarrow> n \<noteq> -2 \<Longrightarrow> conv_denom_int c n = 0"
  by (simp add: conv_denom_int_def)

lemma conv_denom_int_of_nat [simp]: "conv_denom_int c (int n) = conv_denom c n"
  by (simp add: conv_denom_int_def)

lemma conv_denom_int_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> conv_denom_int c n = conv_denom c (nat n)"
  by (simp add: conv_denom_int_def)

lemmas conv_Suc [simp del] = conv.simps(2)


lemma conv'_gt_1:
  assumes "cfrac_nth c 0 > 0" "x > 1"
  shows   "conv' c n x > 1"
  using assms
proof (induction n arbitrary: c x)
  case (Suc n c x)
  from Suc.prems have pos: "cfrac_nth c n > 0" using cfrac_nth_pos[of n c]
    by (cases "n = 0") (auto simp: enat_le_iff)
  have "1 < 1 + 1 / x"
    using Suc.prems by simp
  also have "\<dots> \<le> cfrac_nth c n + 1 / x" using pos
    by (intro add_right_mono) (auto simp: of_nat_ge_1_iff)
  finally show ?case
    by (subst conv'_Suc_right, intro Suc.IH)
       (use Suc.prems in \<open>auto simp: enat_le_iff\<close>)
qed auto

lemma enat_eq_iff: "a = enat b \<longleftrightarrow> (\<exists>a'. a = enat a' \<and> a' = b)"
  by (cases a) auto

lemma eq_enat_iff: "enat a = b \<longleftrightarrow> (\<exists>b'. b = enat b' \<and> a = b')"
  by (cases b) auto

lemma enat_diff_one [simp]: "enat a - 1 = enat (a - 1)"
  by (cases "enat (a - 1)") (auto simp flip: idiff_enat_enat)

lemma conv'_eqD:
  assumes "conv' c n x = conv' c' n x" "x > 1" "m < n"
  shows   "cfrac_nth c m = cfrac_nth c' m"
  using assms
proof (induction n arbitrary: m c c')
  case (Suc n m c c')
  have gt: "conv' (cfrac_tl c) n x > 1" "conv' (cfrac_tl c') n x > 1"
    by (rule conv'_gt_1;
        use Suc.prems in \<open>force intro: cfrac_nth_pos simp: enat_le_iff\<close>)+
  have eq: "cfrac_nth c 0 + 1 / conv' (cfrac_tl c) n x =
            cfrac_nth c' 0 + 1 / conv' (cfrac_tl c') n x"
    using Suc.prems by (subst (asm) (1 2) conv'_Suc_left) auto
  hence "\<lfloor>cfrac_nth c 0 + 1 / conv' (cfrac_tl c) n x\<rfloor> =
         \<lfloor>cfrac_nth c' 0 + 1 / conv' (cfrac_tl c') n x\<rfloor>"
    by (simp only: )
  also from gt have "floor (cfrac_nth c 0 + 1 / conv' (cfrac_tl c) n x) = cfrac_nth c 0"
    by (intro floor_unique) auto
  also from gt have "floor (cfrac_nth c' 0 + 1 / conv' (cfrac_tl c') n x) = cfrac_nth c' 0"
    by (intro floor_unique) auto
  finally have [simp]: "cfrac_nth c 0 = cfrac_nth c' 0" by simp

  show ?case
  proof (cases m)
    case (Suc m')
    from eq and gt have "conv' (cfrac_tl c) n x = conv' (cfrac_tl c') n x"
      by simp
    hence "cfrac_nth (cfrac_tl c) m' = cfrac_nth (cfrac_tl c') m'"
      using Suc.prems
      by (intro Suc.IH[of "cfrac_tl c" "cfrac_tl c'"]) (auto simp: o_def Suc enat_le_iff)
    with Suc show ?thesis by simp
  qed simp_all
qed simp_all

context
  fixes c :: cfrac and h k
  defines "h \<equiv> conv_num c" and "k \<equiv> conv_denom c"
begin

lemma conv'_num_denom_aux:
  assumes z: "z > 0"
  shows   "conv' c (Suc (Suc n)) z * (z * k (Suc n) + k n) = 
             (z * h (Suc n) + h n)"
  using z
proof (induction n arbitrary: z)
  case 0
  hence "1 + z * cfrac_nth c 1 > 0"
    by (intro add_pos_nonneg) (auto simp: cfrac_nth_nonneg)
  with 0 show ?case
    by (auto simp add: h_def k_def field_simps conv'_Suc_right max_def not_le)
next
  case (Suc n)
  have [simp]: "h (Suc (Suc n)) = cfrac_nth c (n+2) * h (n+1) + h n"
    by (simp add: h_def)
  have [simp]: "k (Suc (Suc n)) = cfrac_nth c (n+2) * k (n+1) + k n"
    by (simp add: k_def)
  define z' where "z' = cfrac_nth c (n+2) + 1 / z"
  from \<open>z > 0\<close> have "z' > 0"
    by (auto simp: z'_def intro!: add_nonneg_pos cfrac_nth_nonneg)

  have "z * real_of_int (h (Suc (Suc n))) + real_of_int (h (Suc n)) =
          z * (z' * h (Suc n) + h n)"
    using \<open>z > 0\<close> by (simp add: algebra_simps z'_def)
  also have "\<dots> = z * (conv' c (Suc (Suc n)) z' * (z' * k (Suc n) + k n))"
    using \<open>z' > 0\<close> by (subst Suc.IH [symmetric]) auto
  also have "\<dots> = conv' c (Suc (Suc (Suc n))) z *
            (z * k (Suc (Suc n)) + k (Suc n))"
    unfolding z'_def using \<open>z > 0\<close>
    by (subst (2) conv'_Suc_right) (simp add: algebra_simps)
  finally show ?case ..
qed

lemma conv'_num_denom:
  assumes "z > 0"
  shows   "conv' c (Suc (Suc n)) z =
             (z * h (Suc n) + h n) / (z * k (Suc n) + k n)"
proof -
  have "z * real_of_int (k (Suc n)) + real_of_int (k n) > 0"
    using assms by (intro add_pos_nonneg mult_pos_pos) (auto simp: k_def)
  with conv'_num_denom_aux[of z n] assms show ?thesis
    by (simp add: divide_simps)
qed

lemma conv_num_denom: "conv c n = h n / k n"
proof -
  consider "n = 0" | "n = Suc 0" | m where "n = Suc (Suc m)"
    using not0_implies_Suc by blast
  thus ?thesis
  proof cases
    assume "n = Suc 0"
    thus ?thesis
      by (auto simp: h_def k_def field_simps max_def conv_Suc)
  next
    fix m assume [simp]: "n = Suc (Suc m)"
    have "conv c n = conv' c (Suc (Suc m)) (cfrac_nth c (Suc (Suc m)))"
      by (subst conv_eq_conv') simp_all
    also have "\<dots> = h n / k n"
      by (subst conv'_num_denom) (simp_all add: h_def k_def)
    finally show ?thesis .
  qed (auto simp: h_def k_def)
qed

lemma conv'_num_denom':
  assumes "z > 0" and "n \<ge> 2"
  shows   "conv' c n z = (z * h (n - 1) + h (n - 2)) / (z * k (n - 1) + k (n - 2))"
  using assms conv'_num_denom[of z "n - 2"]
  by (auto simp: eval_nat_numeral Suc_diff_Suc)

lemma conv'_num_denom_int:
  assumes "z > 0"
  shows   "conv' c n z =
             (z * conv_num_int c (int n - 1) + conv_num_int c (int n - 2)) /
             (z * conv_denom_int c (int n - 1) + conv_denom_int c (int n - 2))"
proof -
  consider "n = 0" | "n = 1" | "n \<ge> 2" by force
  thus ?thesis
  proof cases
    case 1
    thus ?thesis using conv_num_int_neg1 by auto
  next
    case 2
    thus ?thesis using assms by (auto simp: conv'_Suc_right field_simps)
  next
    case 3
    thus ?thesis using conv'_num_denom'[OF assms(1), of "nat n"]
      by (auto simp: nat_diff_distrib h_def k_def)
  qed
qed

lemma conv_nonneg: "cfrac_nth c 0 \<ge> 0 \<Longrightarrow> conv c n \<ge> 0"
  by (subst conv_num_denom)
    (auto intro!: divide_nonneg_nonneg conv_num_nonneg simp: h_def k_def)

lemma conv_pos:
  assumes "cfrac_nth c 0 > 0"
  shows   "conv c n > 0"
proof -
  have "conv c n = h n / k n"
    using assms by (intro conv_num_denom)
  also from assms have "\<dots> > 0" unfolding h_def k_def
    by (intro divide_pos_pos) (auto intro!: conv_num_pos')
  finally show ?thesis .
qed

lemma conv_num_denom_prod_diff:
  "k n * h (Suc n) - k (Suc n) * h n = (-1) ^ n"
  by (induction c n rule: conv_num.induct)
     (auto simp: k_def h_def algebra_simps)

lemma conv_num_denom_prod_diff':
  "k (Suc n) * h n - k n * h (Suc n) = (-1) ^ Suc n"
  by (induction c n rule: conv_num.induct)
     (auto simp: k_def h_def algebra_simps)

lemma
  fixes n :: int
  assumes "n \<ge> -2"
  shows   conv_num_denom_int_prod_diff:
            "conv_denom_int c n * conv_num_int c (n + 1) - 
               conv_denom_int c (n + 1) * conv_num_int c n = (-1) ^ (nat (n + 2))" (is ?th1)
  and     conv_num_denom_int_prod_diff':
            "conv_denom_int c (n + 1) * conv_num_int c n - 
               conv_denom_int c n * conv_num_int c (n + 1) = (-1) ^ (nat (n + 3))" (is ?th2)
proof -
  from assms consider "n = -2" | "n = -1" | "n \<ge> 0" by force
  thus ?th1 using conv_num_denom_prod_diff[of "nat n"]
    by cases (auto simp: h_def k_def nat_add_distrib)
  moreover from assms have "nat (n + 3) = Suc (nat (n + 2))" by (simp add: nat_add_distrib)
  ultimately show ?th2 by simp
qed

lemma coprime_conv_num_denom: "coprime (h n) (k n)"
proof (cases n)
  case [simp]: (Suc m)
  {
    fix d :: int
    assume "d dvd h n" and "d dvd k n"
    hence "abs d dvd abs (k n * h (Suc n) - k (Suc n) * h n)"
      by simp
    also have "\<dots> = 1"
      by (subst conv_num_denom_prod_diff) auto
    finally have "is_unit d" by simp
  }
  thus ?thesis by (rule coprimeI)
qed (auto simp: h_def k_def)

lemma coprime_conv_num_denom_int:
  assumes "n \<ge> -2"
  shows   "coprime (conv_num_int c n) (conv_denom_int c n)"
proof -
  from assms consider "n = -2" | "n = -1" | "n \<ge> 0" by force
  thus ?thesis by cases (insert coprime_conv_num_denom[of "nat n"], auto simp: h_def k_def)
qed

lemma mono_conv_num:
  assumes "cfrac_nth c 0 \<ge> 0"
  shows   "mono h"
proof (rule incseq_SucI)
  show "h n \<le> h (Suc n)" for n
  proof (cases n)
    case 0
    have "1 * cfrac_nth c 0 + 1 \<le> cfrac_nth c (Suc 0) * cfrac_nth c 0 + 1"
      using assms by (intro add_mono mult_right_mono) auto
    thus ?thesis using assms by (simp add: le_Suc_eq Suc_le_eq h_def 0)
  next
    case (Suc m)
    have "1 * h (Suc m) + 0 \<le> cfrac_nth c (Suc (Suc m)) * h (Suc m) + h m"
      using assms
      by (intro add_mono mult_right_mono)
         (auto simp: Suc_le_eq h_def intro!: conv_num_nonneg)
    with Suc show ?thesis by (simp add: h_def)
  qed
qed

lemma mono_conv_denom: "mono k"
proof (rule incseq_SucI)
  show "k n \<le> k (Suc n)" for n
  proof (cases n)
    case 0
    thus ?thesis by (simp add: le_Suc_eq Suc_le_eq k_def)
  next
    case (Suc m)
    have "1 * k (Suc m) + 0 \<le> cfrac_nth c (Suc (Suc m)) * k (Suc m) + k m"
      by (intro add_mono mult_right_mono) (auto simp: Suc_le_eq k_def)
    with Suc show ?thesis by (simp add: k_def)
  qed
qed

lemma conv_num_leI: "cfrac_nth c 0 \<ge> 0 \<Longrightarrow> m \<le> n \<Longrightarrow> h m \<le> h n"
  using mono_conv_num by (auto simp: mono_def)

lemma conv_denom_leI: "m \<le> n \<Longrightarrow> k m \<le> k n"
  using mono_conv_denom by (auto simp: mono_def)

lemma conv_denom_lessI:
  assumes "m < n" "1 < n"
  shows   "k m < k n"
proof (cases n)
  case [simp]: (Suc n')
  show ?thesis
  proof (cases n')
    case [simp]: (Suc n'')
    from assms have "k m \<le> 1 * k n' + 0"
      by (auto intro: conv_denom_leI simp: less_Suc_eq)
    also have "\<dots> \<le> cfrac_nth c n * k n' + 0"
      using assms by (intro add_mono mult_mono) (auto simp: Suc_le_eq k_def)
    also have "\<dots> < cfrac_nth c n * k n' + k n''" unfolding k_def
      by (intro add_strict_left_mono conv_denom_pos assms)
    also have "\<dots> = k n" by (simp add: k_def)
    finally show ?thesis .
  qed (insert assms, auto simp: k_def)
qed (insert assms, auto)

lemma conv_num_lower_bound:
  assumes "cfrac_nth c 0 \<ge> 0"
  shows   "h n \<ge> fib n" unfolding h_def
  using assms
proof (induction c n rule: conv_denom.induct)
  case (3 c n)
  hence "conv_num c (Suc (Suc n)) \<ge> 1 * int (fib (Suc n)) + int (fib n)"
    using "3.prems" unfolding conv_num.simps
    by (intro add_mono mult_mono "3.IH") auto
  thus ?case by simp
qed auto

lemma conv_denom_lower_bound: "k n \<ge> fib (Suc n)"
  unfolding k_def
proof (induction c n rule: conv_denom.induct)
  case (3 c n)
  hence "conv_denom c (Suc (Suc n)) \<ge> 1 * int (fib (Suc (Suc n))) + int (fib (Suc n))"
    using "3.prems" unfolding conv_denom.simps
    by (intro add_mono mult_mono "3.IH") auto
  thus ?case by simp
qed (auto simp: Suc_le_eq)

lemma conv_diff_eq: "conv c (Suc n) - conv c n = (-1) ^ n / (k n * k (Suc n))"
proof -
  have pos: "k n > 0" "k (Suc n) > 0" unfolding k_def
    by (intro conv_denom_pos)+
  have "conv c (Suc n) - conv c n =
          (k n * h (Suc n) - k (Suc n) * h n) / (k n * k (Suc n))"
    using pos by (subst (1 2) conv_num_denom) (simp add: conv_num_denom field_simps)
  also have "k n * h (Suc n) - k (Suc n) * h n = (-1) ^ n"
    by (rule conv_num_denom_prod_diff)
  finally show ?thesis by simp
qed

lemma conv_telescope:
  assumes "m \<le> n"
  shows   "conv c m + (\<Sum>i=m..<n. (-1) ^ i / (k i * k (Suc i))) = conv c n"
proof -
  have "(\<Sum>i=m..<n. (-1) ^ i / (k i * k (Suc i))) =
          (\<Sum>i=m..<n. conv c (Suc i) - conv c i)"
    by (simp add: conv_diff_eq assms del: conv.simps)
  also have "conv c m + \<dots> = conv c n"
    using assms by (induction rule: dec_induct) simp_all
  finally show ?thesis .
qed

lemma fib_at_top: "filterlim fib at_top at_top"
proof (rule filterlim_at_top_mono)
  show "eventually (\<lambda>n. fib n \<ge> n - 1) at_top"
    by (intro always_eventually fib_ge allI)
  show "filterlim (\<lambda>n::nat. n - 1) at_top at_top"
    by (subst filterlim_sequentially_Suc [symmetric])
       (simp_all add: filterlim_ident)
qed

lemma conv_denom_at_top: "filterlim k at_top at_top"
proof (rule filterlim_at_top_mono)
  show "filterlim (\<lambda>n. int (fib (Suc n))) at_top at_top"
    by (rule filterlim_compose[OF filterlim_int_sequentially])
       (simp add: fib_at_top filterlim_sequentially_Suc)
  show "eventually (\<lambda>n. fib (Suc n) \<le> k n) at_top"
    by (intro always_eventually conv_denom_lower_bound allI)
qed

lemma
  shows   summable_conv_telescope:
            "summable (\<lambda>i. (-1) ^ i / (k i * k (Suc i)))" (is ?th1)
    and   cfrac_remainder_bounds:
            "\<bar>(\<Sum>i. (-1) ^ (i + m) / (k (i + m) * k (Suc i + m)))\<bar> \<in>
                {1/(k m * (k m + k (Suc m))) <..< 1 / (k m * k (Suc m))}" (is ?th2)
proof -
  have [simp]: "k n > 0" "k n \<ge> 0" "\<not>k n = 0" for n
    by (auto simp: k_def)
  have k_rec: "k (Suc (Suc n)) = cfrac_nth c (Suc (Suc n)) * k (Suc n) + k n" for n
    by (simp add: k_def)
  have [simp]: "a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0" if "a \<ge> 0" "b \<ge> 0" for a b :: real
    using that by linarith

  define g where "g = (\<lambda>i. inverse (real_of_int (k i * k (Suc i))))"

  {
    fix m :: nat
    have "filterlim (\<lambda>n. k n) at_top at_top" and "filterlim (\<lambda>n. k (Suc n)) at_top at_top"
      by (force simp: filterlim_sequentially_Suc intro: conv_denom_at_top)+
    hence lim: "g \<longlonglongrightarrow> 0"
      unfolding g_def of_int_mult
      by (intro tendsto_inverse_0_at_top filterlim_at_top_mult_at_top
                filterlim_compose[OF filterlim_real_of_int_at_top])
    from lim have A: "summable (\<lambda>n. (-1) ^ (n + m) * g (n + m))" unfolding g_def
      by (intro summable_alternating_decreasing)
         (auto intro!: conv_denom_leI mult_nonneg_nonneg)

    have "1 / (k m * (real_of_int (k (Suc m)) + k m / 1)) \<le>
            1 / (k m * (k (Suc m) + k m / cfrac_nth c (m+2)))"
      by (intro divide_left_mono mult_left_mono add_left_mono mult_pos_pos add_pos_pos divide_pos_pos)
         (auto simp: of_nat_ge_1_iff)
    also have "\<dots> = g m - g (Suc m)"
      by (simp add: g_def k_rec field_simps add_pos_pos)
    finally have le: "1 / (k m * (real_of_int (k (Suc m)) + k m / 1)) \<le> g m - g (Suc m)" by simp
    have *: "\<bar>(\<Sum>i. (-1) ^ (i + m) * g (i + m))\<bar> \<in> {g m - g (Suc m) <..< g m}"
      using lim unfolding g_def
      by (intro abs_alternating_decreasing_suminf_strict) (auto intro!: conv_denom_lessI)
    also from le have "\<dots> \<subseteq> {1 / (k m * (k (Suc m) + k m)) <..< g m}"
      by (subst greaterThanLessThan_subseteq_greaterThanLessThan) auto
    finally have B: "\<bar>\<Sum>i. (- 1) ^ (i + m) * g (i + m)\<bar> \<in> \<dots>" .
    note A B
  } note AB = this

  from AB(1)[of 0] show ?th1 by (simp add: field_simps g_def)
  from AB(2)[of m] show ?th2 by (simp add: g_def divide_inverse add_ac)
qed
 
lemma convergent_conv: "convergent (conv c)"
proof -
  have "convergent (\<lambda>n. conv c 0 + (\<Sum>i<n. (-1) ^ i / (k i * k (Suc i))))"
    using summable_conv_telescope
    by (intro convergent_add convergent_const)
       (simp_all add: summable_iff_convergent)
  also have "\<dots> = conv c"
    by (rule ext, subst (2) conv_telescope [of 0, symmetric]) (simp_all add: atLeast0LessThan)
  finally show ?thesis .
qed

lemma LIMSEQ_cfrac_lim: "cfrac_length c = \<infinity> \<Longrightarrow> conv c \<longlonglongrightarrow> cfrac_lim c"
  using convergent_conv by (auto simp: convergent_LIMSEQ_iff cfrac_lim_def)

lemma cfrac_lim_nonneg:
  assumes "cfrac_nth c 0 \<ge> 0"
  shows   "cfrac_lim c \<ge> 0"
proof (cases "cfrac_length c")
  case infinity
  have "conv c \<longlonglongrightarrow> cfrac_lim c"
    by (rule LIMSEQ_cfrac_lim) fact
  thus ?thesis
    by (rule tendsto_lowerbound)
       (auto intro!: conv_nonneg always_eventually assms)
next
  case (enat l)
  thus ?thesis using assms
    by (auto simp: cfrac_lim_def conv_nonneg)
qed

lemma sums_cfrac_lim_minus_conv:
  assumes "cfrac_length c = \<infinity>"
  shows "(\<lambda>i. (-1) ^ (i + m) / (k (i + m) * k (Suc i + m))) sums (cfrac_lim c - conv c m)"
proof -
  have "(\<lambda>n. conv c (n + m) - conv c m) \<longlonglongrightarrow> cfrac_lim c - conv c m"
    by (auto intro!: tendsto_diff LIMSEQ_cfrac_lim simp: filterlim_sequentially_shift assms)
  also have "(\<lambda>n. conv c (n + m) - conv c m) =
          (\<lambda>n. (\<Sum>i=0 + m..<n + m. (-1) ^ i / (k i * k (Suc i))))"
    by (subst conv_telescope [of m, symmetric]) simp_all
  also have "\<dots> = (\<lambda>n. (\<Sum>i<n. (-1) ^ (i + m) / (k (i + m) * k (Suc i + m))))"
    by (subst sum.shift_bounds_nat_ivl) (simp_all add: atLeast0LessThan)
  finally show ?thesis unfolding sums_def .
qed

lemma cfrac_lim_minus_conv_upper_bound:
  assumes "m \<le> cfrac_length c"
  shows   "\<bar>cfrac_lim c - conv c m\<bar> \<le> 1 / (k m * k (Suc m))"
proof (cases "cfrac_length c")
  case infinity
  have "cfrac_lim c - conv c m = (\<Sum>i. (-1) ^ (i + m) / (k (i + m) * k (Suc i + m)))"
    using sums_cfrac_lim_minus_conv infinity by (simp add: sums_iff)
  also note cfrac_remainder_bounds[of m]
  finally show ?thesis by simp
next
  case [simp]: (enat l)
  show ?thesis
  proof (cases "l = m")
    case True
    thus ?thesis by (auto simp: cfrac_lim_def k_def)
  next
    case False
    let ?S = "(\<Sum>i=m..<l. (-1) ^ i * (1 / real_of_int (k i * k (Suc i))))"
    have [simp]: "k n \<ge> 0" "k n > 0" for n
      by (simp_all add: k_def)
    hence "cfrac_lim c - conv c m = conv c l - conv c m"
      by (simp add: cfrac_lim_def)
    also have "\<dots> = ?S"
      using assms by (subst conv_telescope [symmetric, of m]) auto
    finally have "cfrac_lim c - conv c m = ?S" .
    moreover have "\<bar>?S\<bar> \<le> 1 / real_of_int (k m * k (Suc m))"
      unfolding of_int_mult using assms False
      by (intro abs_alternating_decreasing_sum_upper_bound' divide_nonneg_nonneg frac_le mult_mono)
         (simp_all add: conv_denom_leI del: conv_denom.simps)
    ultimately show ?thesis by simp
  qed
qed

lemma cfrac_lim_minus_conv_lower_bound:
  assumes "m < cfrac_length c"
  shows   "\<bar>cfrac_lim c - conv c m\<bar> \<ge> 1 / (k m * (k m + k (Suc m)))"
proof (cases "cfrac_length c")
  case infinity
  have "cfrac_lim c - conv c m = (\<Sum>i. (-1) ^ (i + m) / (k (i + m) * k (Suc i + m)))"
    using sums_cfrac_lim_minus_conv infinity by (simp add: sums_iff)
  also note cfrac_remainder_bounds[of m]
  finally show ?thesis by simp
next
  case [simp]: (enat l)
  let ?S = "(\<Sum>i=m..<l. (-1) ^ i * (1 / real_of_int (k i * k (Suc i))))"
  have [simp]: "k n \<ge> 0" "k n > 0" for n
    by (simp_all add: k_def)
  hence "cfrac_lim c - conv c m = conv c l - conv c m"
    by (simp add: cfrac_lim_def)
  also have "\<dots> = ?S"
    using assms by (subst conv_telescope [symmetric, of m]) (auto simp: split: enat.splits)
  finally have "cfrac_lim c - conv c m = ?S" .

  moreover have "\<bar>?S\<bar> \<ge> 1 / (k m * (k m + k (Suc m)))"
  proof (cases "m < cfrac_length c - 1")
    case False
    hence [simp]: "m = l - 1" and "l > 0" using assms
      by (auto simp: not_less)
    have "1 / (k m * (k m + k (Suc m))) \<le> 1 / (k m * k (Suc m))"
      unfolding of_int_mult
      by (intro divide_left_mono mult_mono mult_pos_pos) (auto intro!: add_pos_pos)
    also from \<open>l > 0\<close> have "{m..<l} = {m}" by auto
    hence "1 / (k m * k (Suc m)) = \<bar>?S\<bar>"
      by simp
    finally show ?thesis .
  next
    case True
    with assms have less: "m < l - 1"
      by auto
    have "k m + k (Suc m) > 0"
      by (intro add_pos_pos) (auto simp: k_def)
    hence "1 / (k m * (k m + k (Suc m))) \<le> 1 / (k m * k (Suc m)) - 1 / (k (Suc m) * k (Suc (Suc m)))"
      by (simp add: divide_simps) (auto simp: k_def algebra_simps)
    also have "\<dots> \<le> \<bar>?S\<bar>"
      unfolding of_int_mult using less
      by (intro abs_alternating_decreasing_sum_lower_bound' divide_nonneg_nonneg frac_le mult_mono)
         (simp_all add: conv_denom_leI del: conv_denom.simps)
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

lemma cfrac_lim_minus_conv_bounds:
  assumes "m < cfrac_length c"
  shows   "\<bar>cfrac_lim c - conv c m\<bar> \<in> {1 / (k m * (k m + k (Suc m)))..1 / (k m * k (Suc m))}"
  using cfrac_lim_minus_conv_lower_bound[of m] cfrac_lim_minus_conv_upper_bound[of m] assms
  by auto

end


lemma conv_pos':
  assumes "n > 0" "cfrac_nth c 0 \<ge> 0"
  shows   "conv c n > 0"
  using assms by (cases n) (auto simp: conv_Suc intro!: add_nonneg_pos conv_pos)

lemma conv_in_Rats [intro]: "conv c n \<in> \<rat>"
  by (induction c n rule: conv.induct) (auto simp: conv_Suc o_def)

lemma
  assumes "0 < z1" "z1 \<le> z2"
  shows   conv'_even_mono: "even n \<Longrightarrow> conv' c n z1 \<le> conv' c n z2"
    and   conv'_odd_mono:  "odd n \<Longrightarrow> conv' c n z1 \<ge> conv' c n z2"
proof -
  let ?P = "(\<lambda>n (f::nat\<Rightarrow>real\<Rightarrow>real). 
               if even n then f n z1 \<le> f n z2 else f n z1 \<ge> f n z2)"
  have "?P n (conv' c)" using assms
  proof (induction n arbitrary: z1 z2)
    case (Suc n)
    note z12 = Suc.prems
    consider "n = 0" | "even n" "n > 0" | "odd n" by force
    thus ?case
    proof cases
      assume "n = 0"
      thus ?thesis using Suc by (simp add: conv'_Suc_right field_simps)
    next
      assume n: "even n" "n > 0"
      with Suc.IH have IH: "conv' c n z1 \<le> conv' c n z2"
        if "0 < z1" "z1 \<le> z2" for z1 z2 using that by auto
      show ?thesis using Suc.prems n z12
        by (auto simp: conv'_Suc_right field_simps intro!: IH add_pos_nonneg mult_nonneg_nonneg)
    next
      assume n: "odd n"
      hence [simp]: "n > 0" by (auto intro!: Nat.gr0I)
      from n and Suc.IH have IH: "conv' c n z1 \<ge> conv' c n z2"
        if "0 < z1" "z1 \<le> z2" for z1 z2 using that by auto
      show ?thesis using Suc.prems n
        by (auto simp: conv'_Suc_right field_simps
                 intro!: IH add_pos_nonneg mult_nonneg_nonneg)
    qed
  qed auto
  thus "even n \<Longrightarrow> conv' c n z1 \<le> conv' c n z2"
       "odd n \<Longrightarrow> conv' c n z1 \<ge> conv' c n z2" by auto
qed

lemma
  shows   conv_even_mono: "even n \<Longrightarrow> n \<le> m \<Longrightarrow> conv c n \<le> conv c m"
    and   conv_odd_mono:  "odd n  \<Longrightarrow> n \<le> m \<Longrightarrow> conv c n \<ge> conv c m"
proof -
  assume "even n"
  have A: "conv c n \<le> conv c (Suc (Suc n))" if "even n" for n
  proof (cases "n = 0")
    case False
    with \<open>even n\<close> show ?thesis
      by (auto simp add: conv_eq_conv' conv'_Suc_right intro: conv'_even_mono)
  qed (auto simp:  conv_Suc)

  have B: "conv c n \<le> conv c (Suc n)" if "even n" for n
  proof (cases "n = 0")
    case False
    with \<open>even n\<close> show ?thesis
      by (auto simp add: conv_eq_conv' conv'_Suc_right intro: conv'_even_mono)
  qed (auto simp:  conv_Suc)

  show "conv c n \<le> conv c m" if "n \<le> m" for m
    using that
  proof (induction m rule: less_induct)
    case (less m)
    from \<open>n \<le> m\<close> consider "m = n" | "even m" "m > n" | "odd m" "m > n"
      by force
    thus ?case
    proof cases
      assume m: "even m" "m > n"
      with \<open>even n\<close> have m': "m - 2 \<ge> n" by presburger
      with m have "conv c n \<le> conv c (m - 2)"
        by (intro less.IH) auto
      also have "\<dots> \<le> conv c (Suc (Suc (m - 2)))"
        using m m' by (intro A) auto
      also have "Suc (Suc (m - 2)) = m"
        using m by presburger
      finally show ?thesis .
    next
      assume m: "odd m" "m > n"
      hence "conv c n \<le> conv c (m - 1)"
        by (intro less.IH) auto
      also have "\<dots> \<le> conv c (Suc (m - 1))"
        using m by (intro B) auto
      also have "Suc (m - 1) = m"
        using m by simp
      finally show ?thesis .
    qed simp_all
  qed
next
  assume "odd n"
  have A: "conv c n \<ge> conv c (Suc (Suc n))" if "odd n" for n
    using that
    by (auto simp add: conv_eq_conv' conv'_Suc_right odd_pos intro!: conv'_odd_mono)
  have B: "conv c n \<ge> conv c (Suc n)" if "odd n" for n using that
    by (auto simp add: conv_eq_conv' conv'_Suc_right odd_pos intro!: conv'_odd_mono)

  show "conv c n \<ge> conv c m" if "n \<le> m" for m
    using that
  proof (induction m rule: less_induct)
    case (less m)
    from \<open>n \<le> m\<close> consider "m = n" | "even m" "m > n" | "odd m" "m > n"
      by force
    thus ?case
    proof cases
      assume m: "odd m" "m > n"
      with \<open>odd n\<close> have m': "m - 2 \<ge> n" "m \<ge> 2" by presburger+
      from m and \<open>odd n\<close> have "m = Suc (Suc (m - 2))" by presburger
      also have "conv c \<dots> \<le> conv c (m - 2)"
        using m m' by (intro A) auto
      also have "\<dots> \<le> conv c n"
        using m m' by (intro less.IH) auto
      finally show ?thesis .
    next
      assume m: "even m" "m > n"
      from m have "m = Suc (m - 1)" by presburger
      also have "conv c \<dots> \<le> conv c (m - 1)"
        using m by (intro B) auto
      also have "\<dots> \<le> conv c n"
        using m by (intro less.IH) auto
      finally show ?thesis .
    qed simp_all
  qed
qed

lemma
  assumes "m \<le> cfrac_length c"
  shows   conv_le_cfrac_lim: "even m \<Longrightarrow> conv c m \<le> cfrac_lim c"
    and   conv_ge_cfrac_lim: "odd m \<Longrightarrow> conv c m \<ge> cfrac_lim c"
proof -
  have "if even m then conv c m \<le> cfrac_lim c else conv c m \<ge> cfrac_lim c"
  proof (cases "cfrac_length c")
    case [simp]: infinity
    show ?thesis
    proof (cases "even m")
      case True
      have "eventually (\<lambda>i. conv c m \<le> conv c i) at_top"
        using eventually_ge_at_top[of m] by eventually_elim (rule conv_even_mono[OF True])
      hence "conv c m \<le> cfrac_lim c"
        by (intro tendsto_lowerbound[OF LIMSEQ_cfrac_lim]) auto
      thus ?thesis using True by simp
    next
      case False
      have "eventually (\<lambda>i. conv c m \<ge> conv c i) at_top"
        using eventually_ge_at_top[of m] by eventually_elim (rule conv_odd_mono[OF False])
      hence "conv c m \<ge> cfrac_lim c"
        by (intro tendsto_upperbound[OF LIMSEQ_cfrac_lim]) auto
      thus ?thesis using False by simp
    qed
  next
    case [simp]: (enat l)
    show ?thesis
      using conv_even_mono[of m l c] conv_odd_mono[of m l c] assms
      by (auto simp: cfrac_lim_def)
  qed
  thus "even m \<Longrightarrow> conv c m \<le> cfrac_lim c" and "odd m \<Longrightarrow> conv c m \<ge> cfrac_lim c"
    by auto
qed

lemma cfrac_lim_ge_first: "cfrac_lim c \<ge> cfrac_nth c 0"
  using conv_le_cfrac_lim[of 0 c] by (auto simp: less_eq_enat_def split: enat.splits)

lemma cfrac_lim_pos: "cfrac_nth c 0 > 0 \<Longrightarrow> cfrac_lim c > 0"
  by (rule less_le_trans[OF _ cfrac_lim_ge_first]) auto

lemma conv'_eq_iff:
  assumes "0 \<le> z1 \<or> 0 \<le> z2"
  shows   "conv' c n z1 = conv' c n z2 \<longleftrightarrow> z1 = z2"
proof
  assume "conv' c n z1 = conv' c n z2"
  thus "z1 = z2" using assms
  proof (induction n arbitrary: z1 z2)
    case (Suc n)
    show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis using Suc by (auto simp: conv'_Suc_right)
    next
      case False
      have "conv' c n (real_of_int (cfrac_nth c n) + 1 / z1) =
               conv' c n (real_of_int (cfrac_nth c n) + 1 / z2)" using Suc.prems
        by (simp add: conv'_Suc_right)
      hence "real_of_int (cfrac_nth c n) + 1 / z1 = real_of_int (cfrac_nth c n) + 1 / z2"
        by (rule Suc.IH)
           (insert Suc.prems False, auto intro!: add_nonneg_pos add_nonneg_nonneg)
      with Suc.prems show "z1 = z2" by simp
    qed
  qed auto
qed auto

lemma conv_even_mono_strict:
  assumes "even n" "n < m"
  shows   "conv c n < conv c m"
proof (cases "m = n + 1")
  case [simp]: True
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis using assms by (auto simp: conv_Suc)
  next
    case False
    hence "conv' c n (real_of_int (cfrac_nth c n)) \<noteq>
           conv' c n (real_of_int (cfrac_nth c n) + 1 / real_of_int (cfrac_nth c (Suc n)))"
      by (subst conv'_eq_iff) auto
    with assms have "conv c n \<noteq> conv c m"
      by (auto simp: conv_eq_conv' conv'_eq_iff conv'_Suc_right field_simps)
    moreover from assms have "conv c n \<le> conv c m"
      by (intro conv_even_mono) auto
   
    ultimately show ?thesis by simp
  qed
next
  case False
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis using assms
      by (cases m) (auto simp: conv_Suc conv_pos)
  next
    case False
    have "1 + real_of_int (cfrac_nth c (n+1)) * cfrac_nth c (n+2) > 0"
      by (intro add_pos_nonneg) auto
    with assms have "conv c n \<noteq> conv c (Suc (Suc n))"
      unfolding conv_eq_conv' conv'_Suc_right using False
      by (subst conv'_eq_iff) (auto simp: field_simps)
    moreover from assms have "conv c n \<le> conv c (Suc (Suc n))"
      by (intro conv_even_mono) auto
    ultimately have "conv c n < conv c (Suc (Suc n))" by simp
    also have "\<dots> \<le> conv c m" using assms \<open>m \<noteq> n + 1\<close>
      by (intro conv_even_mono) auto
    finally show ?thesis .
  qed
qed

lemma conv_odd_mono_strict:
  assumes "odd n" "n < m"
  shows   "conv c n > conv c m"
proof (cases "m = n + 1")
  case [simp]: True
  from assms have "n > 0" by (intro Nat.gr0I) auto
  hence "conv' c n (real_of_int (cfrac_nth c n)) \<noteq>
         conv' c n (real_of_int (cfrac_nth c n) + 1 / real_of_int (cfrac_nth c (Suc n)))"
    by (subst conv'_eq_iff) auto
  hence "conv c n \<noteq> conv c m"
    by (simp add: conv_eq_conv' conv'_Suc_right)
  moreover from assms have "conv c n \<ge> conv c m"
    by (intro conv_odd_mono) auto
  ultimately show ?thesis by simp
next
  case False
  from assms have "n > 0" by (intro Nat.gr0I) auto
  have "1 + real_of_int (cfrac_nth c (n+1)) * cfrac_nth c (n+2) > 0"
    by (intro add_pos_nonneg) auto
  with assms \<open>n > 0\<close> have "conv c n \<noteq> conv c (Suc (Suc n))"
    unfolding conv_eq_conv' conv'_Suc_right
    by (subst conv'_eq_iff) (auto simp: field_simps)
  moreover from assms have "conv c n \<ge> conv c (Suc (Suc n))"
    by (intro conv_odd_mono) auto
  ultimately have "conv c n > conv c (Suc (Suc n))" by simp
  moreover have "conv c (Suc (Suc n)) \<ge> conv c m" using assms False
    by (intro conv_odd_mono) auto
  ultimately show ?thesis by linarith
qed

lemma conv_less_cfrac_lim:
  assumes "even n" "n < cfrac_length c"
  shows   "conv c n < cfrac_lim c"
proof (cases "cfrac_length c")
  case (enat l)
  with assms show ?thesis by (auto simp: cfrac_lim_def conv_even_mono_strict)
next
  case [simp]: infinity
  from assms have "conv c n < conv c (n + 2)"
    by (intro conv_even_mono_strict) auto
  also from assms have "\<dots> \<le> cfrac_lim c"
    by (intro conv_le_cfrac_lim) auto
  finally show ?thesis .
qed

lemma conv_gt_cfrac_lim:
  assumes "odd n" "n < cfrac_length c"
  shows   "conv c n > cfrac_lim c"
proof (cases "cfrac_length c")
  case (enat l)
  with assms show ?thesis by (auto simp: cfrac_lim_def conv_odd_mono_strict)
next
  case [simp]: infinity
  from assms have "cfrac_lim c \<le> conv c (n + 2)"
    by (intro conv_ge_cfrac_lim) auto
  also from assms have "\<dots> < conv c n"
    by (intro conv_odd_mono_strict) auto
  finally show ?thesis .
qed

lemma conv_neq_cfrac_lim:
  assumes "n < cfrac_length c"
  shows   "conv c n \<noteq> cfrac_lim c"
  using conv_gt_cfrac_lim[OF _ assms] conv_less_cfrac_lim[OF _ assms]
  by (cases "even n") auto

lemma conv_ge_first: "conv c n \<ge> cfrac_nth c 0"
  using conv_even_mono[of 0 n c] by simp


definition cfrac_is_zero :: "cfrac \<Rightarrow> bool" where "cfrac_is_zero c \<longleftrightarrow> c = 0"

lemma cfrac_is_zero_code [code]: "cfrac_is_zero (CFrac n xs) \<longleftrightarrow> lnull xs \<and> n = 0"
  unfolding cfrac_is_zero_def lnull_def zero_cfrac_def cfrac_of_int_def
  by (auto simp: cfrac_length_def)


definition cfrac_is_int where "cfrac_is_int c \<longleftrightarrow> cfrac_length c = 0"

lemma cfrac_is_int_code [code]: "cfrac_is_int (CFrac n xs) \<longleftrightarrow> lnull xs"
  unfolding cfrac_is_int_def lnull_def by (auto simp: cfrac_length_def)

lemma cfrac_length_of_int [simp]: "cfrac_length (cfrac_of_int n) = 0"
  by transfer auto

lemma cfrac_is_int_of_int [simp, intro]: "cfrac_is_int (cfrac_of_int n)"
  unfolding cfrac_is_int_def by simp

lemma cfrac_is_int_iff: "cfrac_is_int c \<longleftrightarrow> (\<exists>n. c = cfrac_of_int n)"
proof -
  have "c = cfrac_of_int (cfrac_nth c 0)" if "cfrac_is_int c"
    using that unfolding cfrac_is_int_def by transfer auto
  thus ?thesis
    by auto
qed  

lemma cfrac_lim_reduce:
  assumes "\<not>cfrac_is_int c"
  shows   "cfrac_lim c = cfrac_nth c 0 + 1 / cfrac_lim (cfrac_tl c)"
proof (cases "cfrac_length c")
  case [simp]: infinity
  have "0 < cfrac_nth (cfrac_tl c) 0"
    by simp
  also have "\<dots> \<le> cfrac_lim (cfrac_tl c)"
    by (rule cfrac_lim_ge_first)
  finally have "(\<lambda>n. real_of_int (cfrac_nth c 0) + 1 / conv (cfrac_tl c) n) \<longlonglongrightarrow>
           real_of_int (cfrac_nth c 0) + 1 / cfrac_lim (cfrac_tl c)"
    by (intro tendsto_intros LIMSEQ_cfrac_lim) auto
  also have "(\<lambda>n. real_of_int (cfrac_nth c 0) + 1 / conv (cfrac_tl c) n) = conv c \<circ> Suc"
    by (simp add: o_def conv_Suc)
  finally have *: "conv c \<longlonglongrightarrow> real_of_int (cfrac_nth c 0) + 1 / cfrac_lim (cfrac_tl c)"
    by (simp add: o_def filterlim_sequentially_Suc)
  show ?thesis
    by (rule tendsto_unique[OF _ LIMSEQ_cfrac_lim *]) auto
next
  case [simp]: (enat l)
  from assms obtain l' where [simp]: "l = Suc l'"
    by (cases l) (auto simp: cfrac_is_int_def zero_enat_def)
  thus ?thesis
    by (auto simp: cfrac_lim_def conv_Suc)
qed

lemma cfrac_lim_tl:
  assumes "\<not>cfrac_is_int c"
  shows   "cfrac_lim (cfrac_tl c) = 1 / (cfrac_lim c - cfrac_nth c 0)"
  using cfrac_lim_reduce[OF assms] by simp



lemma cfrac_remainder_Suc':
  assumes "n < cfrac_length c"
  shows "cfrac_remainder c (Suc n) * (cfrac_remainder c n - cfrac_nth c n) = 1"
proof -
  have "0 < real_of_int (cfrac_nth c (Suc n))" by simp
  also have "cfrac_nth c (Suc n) \<le> cfrac_remainder c (Suc n)"
    using cfrac_lim_ge_first[of "cfrac_drop (Suc n) c"]
    by (simp add: cfrac_remainder_def)
  finally have "\<dots> > 0" .

  have "cfrac_remainder c (Suc n) = cfrac_lim (cfrac_tl (cfrac_drop n c))"
    by (simp add: o_def cfrac_remainder_def cfrac_drop_Suc_left)                   
  also have "\<dots> = 1 / (cfrac_remainder c n - cfrac_nth c n)" using assms
    by (subst cfrac_lim_tl) (auto simp: cfrac_remainder_def cfrac_is_int_def enat_less_iff enat_0_iff)
  finally show ?thesis
    using \<open>cfrac_remainder c (Suc n) > 0\<close>
    by (auto simp add: cfrac_remainder_def field_simps)
qed

lemma cfrac_remainder_Suc:
  assumes "n < cfrac_length c"
  shows   "cfrac_remainder c (Suc n) = 1 / (cfrac_remainder c n - cfrac_nth c n)"
proof -
  have "cfrac_remainder c (Suc n) = cfrac_lim (cfrac_tl (cfrac_drop n c))"
    by (simp add: o_def cfrac_remainder_def cfrac_drop_Suc_left)
  also have "\<dots> = 1 / (cfrac_remainder c n - cfrac_nth c n)" using assms
    by (subst cfrac_lim_tl) (auto simp: cfrac_remainder_def cfrac_is_int_def enat_less_iff enat_0_iff)
  finally show ?thesis .
qed

lemma cfrac_remainder_0 [simp]: "cfrac_remainder c 0 = cfrac_lim c"
  by (simp add: cfrac_remainder_def)

context
  fixes c h k x
  defines "h \<equiv> conv_num c" and "k \<equiv> conv_denom c" and "x \<equiv> cfrac_remainder c"
begin

lemma cfrac_lim_eq_num_denom_remainder_aux:  
  assumes "Suc (Suc n) \<le> cfrac_length c"
  shows   "cfrac_lim c * (k (Suc n) * x (Suc (Suc n)) + k n) = h (Suc n) * x (Suc (Suc n)) + h n"
  using assms
proof (induction n)
  case 0
  have "cfrac_lim c \<noteq> cfrac_nth c 0"
    using conv_neq_cfrac_lim[of 0 c] 0 by (auto simp: enat_le_iff)
  moreover have "cfrac_nth c 1 * (cfrac_lim c - cfrac_nth c 0) \<noteq> 1"
    using conv_neq_cfrac_lim[of 1 c] 0
    by (auto simp: enat_le_iff conv_Suc field_simps)
  ultimately show ?case using assms
    by (auto simp: cfrac_remainder_Suc divide_simps x_def h_def k_def enat_le_iff)
       (auto simp: field_simps)
next
  case (Suc n)
  have less: "enat (Suc (Suc n)) < cfrac_length c"
    using Suc.prems by (cases "cfrac_length c") auto
  have *: "x (Suc (Suc n)) \<noteq> real_of_int (cfrac_nth c (Suc (Suc n)))"
    using conv_neq_cfrac_lim[of 0 "cfrac_drop (n+2) c"] Suc.prems
    by (cases "cfrac_length c") (auto simp: x_def cfrac_remainder_def)
  hence "cfrac_lim c * (k (Suc (Suc n)) * x (Suc (Suc (Suc n))) + k (Suc n)) =
           (cfrac_lim c * (k (Suc n) * x (Suc (Suc n)) + k n)) / (x (Suc (Suc n)) - cfrac_nth c (Suc (Suc n)))"
    unfolding x_def k_def h_def using less
    by (subst cfrac_remainder_Suc) (auto simp: field_simps)
  also have "cfrac_lim c * (k (Suc n) * x (Suc (Suc n)) + k n) =
               h (Suc n) * x (Suc (Suc n)) + h n" using less
    by (intro Suc.IH) auto
  also have "(h (Suc n) * x (Suc (Suc n)) + h n) / (x (Suc (Suc n)) - cfrac_nth c (Suc (Suc n))) = 
               h (Suc (Suc n)) * x (Suc (Suc (Suc n))) + h (Suc n)" using *
    unfolding x_def k_def h_def using less
    by (subst (3) cfrac_remainder_Suc) (auto simp: field_simps)
  finally show ?case .
qed

lemma cfrac_remainder_nonneg: "cfrac_nth c n \<ge> 0 \<Longrightarrow> cfrac_remainder c n \<ge> 0"
  unfolding cfrac_remainder_def by (rule cfrac_lim_nonneg) auto

lemma cfrac_remainder_pos: "cfrac_nth c n > 0 \<Longrightarrow> cfrac_remainder c n > 0"
  unfolding cfrac_remainder_def by (rule cfrac_lim_pos) auto

lemma cfrac_lim_eq_num_denom_remainder:
  assumes "Suc (Suc n) < cfrac_length c"
  shows   "cfrac_lim c = (h (Suc n) * x (Suc (Suc n)) + h n) / (k (Suc n) * x (Suc (Suc n)) + k n)"
proof -
  have "k (Suc n) * x (Suc (Suc n)) + k n > 0"
    by (intro add_nonneg_pos mult_nonneg_nonneg)
       (auto simp: k_def x_def intro!: conv_denom_pos cfrac_remainder_nonneg)
  with cfrac_lim_eq_num_denom_remainder_aux[of n] assms show ?thesis
    by (auto simp add: field_simps h_def k_def x_def)
qed

lemma abs_diff_successive_convs:
  shows   "\<bar>conv c (Suc n) - conv c n\<bar> = 1 / (k n * k (Suc n))"
proof -
  have [simp]: "k n \<noteq> 0" for n :: nat
    unfolding k_def using conv_denom_pos[of c n] by auto
  have "conv c (Suc n) - conv c n = h (Suc n) / k (Suc n) - h n / k n"
    by (simp add: conv_num_denom k_def h_def)
  also have "\<dots> = (k n * h (Suc n) - k (Suc n) * h n) / (k n * k (Suc n))"
    by (simp add: field_simps)
  also have "k n * h (Suc n) - k (Suc n) * h n = (-1) ^ n"
    unfolding h_def k_def by (intro conv_num_denom_prod_diff)
  finally show ?thesis by (simp add: k_def)
qed

lemma conv_denom_plus2_ratio_ge: "k (Suc (Suc n)) \<ge> 2 * k n"
proof -
  have "1 * k n + k n \<le> cfrac_nth c (Suc (Suc n)) * k (Suc n) + k n"
    by (intro add_mono mult_mono)
       (auto simp: k_def Suc_le_eq intro!: conv_denom_leI)
  thus ?thesis by (simp add: k_def)
qed

end

lemma conv'_cfrac_remainder:
  assumes "n < cfrac_length c"
  shows   "conv' c n (cfrac_remainder c n) = cfrac_lim c"
  using assms
proof (induction n arbitrary: c)
  case (Suc n c)
  have "conv' c (Suc n) (cfrac_remainder c (Suc n)) =
          cfrac_nth c 0 + 1 / conv' (cfrac_tl c) n (cfrac_remainder c (Suc n))"
    using Suc.prems
    by (subst conv'_Suc_left) (auto intro!: cfrac_remainder_pos)
  also have "cfrac_remainder c (Suc n) = cfrac_remainder (cfrac_tl c) n"
    by (simp add: cfrac_remainder_def cfrac_drop_Suc_right)
  also have "conv' (cfrac_tl c) n \<dots> = cfrac_lim (cfrac_tl c)"
    using Suc.prems by (subst Suc.IH) (auto simp: cfrac_remainder_def enat_less_iff)
  also have "cfrac_nth c 0 + 1 / \<dots> = cfrac_lim c"
    using Suc.prems by (intro cfrac_lim_reduce [symmetric]) (auto simp: cfrac_is_int_def)
  finally show ?case by (simp add: cfrac_remainder_def cfrac_drop_Suc_right)
qed auto

lemma cfrac_lim_rational [intro]:
  assumes "cfrac_length c < \<infinity>"
  shows   "cfrac_lim c \<in> \<rat>"
  using assms by (cases "cfrac_length c") (auto simp: cfrac_lim_def)

lemma linfinite_cfrac_of_real_aux:
  "x \<notin> \<rat> \<Longrightarrow> x \<in> {0<..<1} \<Longrightarrow> linfinite (cfrac_of_real_aux x)"
proof (coinduction arbitrary: x)
  case (linfinite x)
  hence "1 / x \<notin> \<rat>" using Rats_divide[of 1 "1 / x"] by auto
  thus ?case using linfinite Ints_subset_Rats
    by (intro disjI1 exI[of _ "nat \<lfloor>1/x\<rfloor> - 1"] exI[of _ "cfrac_of_real_aux (frac (1/x))"] 
              exI[of _ "frac (1/x)"] conjI)
       (auto simp: cfrac_of_real_aux.code[of x] frac_lt_1)
qed

lemma cfrac_length_of_real_irrational:
  assumes "x \<notin> \<rat>"
  shows   "cfrac_length (cfrac_of_real x) = \<infinity>"
proof (insert assms, transfer, clarify)
  fix x :: real assume "x \<notin> \<rat>"
  thus "llength (cfrac_of_real_aux (frac x)) = \<infinity>"
    using linfinite_cfrac_of_real_aux[of "frac x"] Ints_subset_Rats
    by (auto simp: linfinite_conv_llength frac_lt_1)
qed

lemma cfrac_length_of_real_reduce:
  assumes "x \<notin> \<int>"
  shows   "cfrac_length (cfrac_of_real x) = eSuc (cfrac_length (cfrac_of_real (1 / frac x)))"
  using assms
  by (transfer, subst cfrac_of_real_aux.code) (auto simp: frac_lt_1)

lemma cfrac_length_of_real_int [simp]: "x \<in> \<int> \<Longrightarrow> cfrac_length (cfrac_of_real x) = 0"
  by transfer auto

lemma conv_cfrac_of_real_le_ge:
  assumes "n \<le> cfrac_length (cfrac_of_real x)"
  shows   "if even n then conv (cfrac_of_real x) n \<le> x else conv (cfrac_of_real x) n \<ge> x"
  using assms
proof (induction n arbitrary: x)
  case (Suc n x)
  hence [simp]: "x \<notin> \<int>"
    using Suc by (auto simp: enat_0_iff)
  let ?x' = "1 / frac x"
  have "enat n \<le> cfrac_length (cfrac_of_real (1 / frac x))"
    using Suc.prems by (auto simp: cfrac_length_of_real_reduce simp flip: eSuc_enat)
  hence IH: "if even n then conv (cfrac_of_real ?x') n \<le> ?x' else ?x' \<le> conv (cfrac_of_real ?x') n"
    using Suc.prems by (intro Suc.IH) auto
  have remainder_pos: "conv (cfrac_of_real ?x') n > 0"
    by (rule conv_pos) (auto simp: frac_le_1)
  show ?case
  proof (cases "even n")
    case True
    have "x \<le> real_of_int \<lfloor>x\<rfloor> + frac x"
      by (simp add: frac_def)
    also have "frac x \<le> 1 / conv (cfrac_of_real ?x') n"
      using IH True remainder_pos frac_gt_0_iff[of x] by (simp add: field_simps)
    finally show ?thesis using True
      by (auto simp: conv_Suc cfrac_tl_of_real)
  next
    case False
    have "real_of_int \<lfloor>x\<rfloor> + 1 / conv (cfrac_of_real ?x') n \<le> real_of_int \<lfloor>x\<rfloor> + frac x"
      using IH False remainder_pos frac_gt_0_iff[of x] by (simp add: field_simps)
    also have "\<dots> = x"
      by (simp add: frac_def)
    finally show ?thesis using False
      by (auto simp: conv_Suc cfrac_tl_of_real)
  qed
qed auto

lemma cfrac_lim_of_real [simp]: "cfrac_lim (cfrac_of_real x) = x"
proof (cases "cfrac_length (cfrac_of_real x)")
  case (enat l)
  hence "conv (cfrac_of_real x) l = x"
  proof (induction l arbitrary: x)
    case 0
    hence "x \<in> \<int>"
      using cfrac_length_of_real_reduce zero_enat_def by fastforce
    thus ?case by (auto elim: Ints_cases)
  next
    case (Suc l x)
    hence [simp]: "x \<notin> \<int>" 
      by (auto simp: enat_0_iff)
    have "eSuc (cfrac_length (cfrac_of_real (1 / frac x))) = enat (Suc l)"
      using Suc.prems by (auto simp: cfrac_length_of_real_reduce)
    hence "conv (cfrac_of_real (1 / frac x)) l = 1 / frac x"
      by (intro Suc.IH) (auto simp flip: eSuc_enat)
    thus ?case
      by (simp add: conv_Suc cfrac_tl_of_real frac_def)
  qed
  thus ?thesis by (simp add: enat cfrac_lim_def)
next
  case [simp]: infinity
  have lim: "conv (cfrac_of_real x) \<longlonglongrightarrow> cfrac_lim (cfrac_of_real x)"
    by (simp add: LIMSEQ_cfrac_lim)
  have "cfrac_lim (cfrac_of_real x) \<le> x"
  proof (rule tendsto_upperbound)
    show "(\<lambda>n. conv (cfrac_of_real x) (n * 2)) \<longlonglongrightarrow> cfrac_lim (cfrac_of_real x)"
      by (intro filterlim_compose[OF lim] mult_nat_right_at_top) auto
    show "eventually (\<lambda>n. conv (cfrac_of_real x) (n * 2) \<le> x) at_top"
      using conv_cfrac_of_real_le_ge[of "n * 2" x for n] by (intro always_eventually) auto
  qed auto
  moreover have "cfrac_lim (cfrac_of_real x) \<ge> x"
  proof (rule tendsto_lowerbound)
    show "(\<lambda>n. conv (cfrac_of_real x) (Suc (n * 2))) \<longlonglongrightarrow> cfrac_lim (cfrac_of_real x)"
      by (intro filterlim_compose[OF lim] filterlim_compose[OF filterlim_Suc]
                mult_nat_right_at_top) auto
    show "eventually (\<lambda>n. conv (cfrac_of_real x) (Suc (n * 2)) \<ge> x) at_top"
      using conv_cfrac_of_real_le_ge[of "Suc (n * 2)" x for n] by (intro always_eventually) auto
  qed auto
  ultimately show ?thesis by (rule antisym)
qed

lemma Ints_add_left_cancel: "x \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  using Ints_diff[of "x + y" x] by auto

lemma Ints_add_right_cancel: "y \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  using Ints_diff[of "x + y" y] by auto

lemma cfrac_of_real_conv':
  fixes m n :: nat
  assumes "x > 1" "m < n"
  shows   "cfrac_nth (cfrac_of_real (conv' c n x)) m = cfrac_nth c m"
  using assms
proof (induction n arbitrary: c m)
  case (Suc n c m)
  from Suc.prems have gt_1: "1 < conv' (cfrac_tl c) n x"
    by (intro conv'_gt_1) (auto simp: enat_le_iff intro: cfrac_nth_pos)
  show ?case
  proof (cases m)
    case 0
    thus ?thesis using gt_1 Suc.prems
      by (simp add: conv'_Suc_left nat_add_distrib floor_eq_iff)
  next
    case (Suc m')
    from gt_1 have "1 / conv' (cfrac_tl c) n x \<in> {0<..<1}"
      by auto
    have "1 / conv' (cfrac_tl c) n x \<notin> \<int>"
    proof
      assume "1 / conv' (cfrac_tl c) n x \<in> \<int>"
      then obtain k :: int where k: "1 / conv' (cfrac_tl c) n x = of_int k"
        by (elim Ints_cases)
      have "real_of_int k \<in> {0<..<1}"
        using gt_1 by (subst k [symmetric]) auto
      thus False by auto
    qed
    hence not_int: "real_of_int (cfrac_nth c 0) + 1 / conv' (cfrac_tl c) n x \<notin> \<int>"
      by (subst Ints_add_left_cancel) (auto simp: field_simps elim!: Ints_cases)
    have "cfrac_nth (cfrac_of_real (conv' c (Suc n) x)) m =
          cfrac_nth (cfrac_of_real (of_int (cfrac_nth c 0) + 1 / conv' (cfrac_tl c) n x)) (Suc m')"
      using \<open>x > 1\<close> by (subst conv'_Suc_left) (auto simp: Suc)
    also have "\<dots> = cfrac_nth (cfrac_of_real (1 / frac (1 / conv' (cfrac_tl c) n x))) m'" 
      using \<open>x > 1\<close> Suc not_int by (subst cfrac_nth_of_real_Suc) (auto simp: frac_add_of_int)
    also have "1 / conv' (cfrac_tl c) n x \<in> {0<..<1}" using gt_1
      by (auto simp: field_simps)
    hence "frac (1 / conv' (cfrac_tl c) n x) = 1 / conv' (cfrac_tl c) n x"
      by (subst frac_eq) auto
    hence "1 / frac (1 / conv' (cfrac_tl c) n x) = conv' (cfrac_tl c) n x"
      by simp
    also have "cfrac_nth (cfrac_of_real \<dots>) m' = cfrac_nth c m"
      using Suc.prems by (subst Suc.IH) (auto simp: Suc enat_le_iff)
    finally show ?thesis .
  qed
qed simp_all

lemma cfrac_lim_irrational:
  assumes [simp]: "cfrac_length c = \<infinity>"
  shows   "cfrac_lim c \<notin> \<rat>"
proof
  assume "cfrac_lim c \<in> \<rat>"
  then obtain a :: int and b :: nat where ab: "b > 0" "cfrac_lim c = a / b"
    by (auto simp: Rats_eq_int_div_nat)
  define h and k where "h = conv_num c" and "k = conv_denom c"

  have "filterlim (\<lambda>m. conv_denom c (Suc m)) at_top at_top"
    using conv_denom_at_top filterlim_Suc by (rule filterlim_compose)
  then obtain m where m: "conv_denom c (Suc m) \<ge> b + 1"
    by (auto simp: filterlim_at_top eventually_at_top_linorder)

  have *: "(a * k m - b * h m) / (k m * b) = a / b - h m / k m"
    using \<open>b > 0\<close> by (simp add: field_simps k_def)
  have "\<bar>cfrac_lim c - conv c m\<bar> = \<bar>(a * k m - b * h m) / (k m * b)\<bar>"
    by (subst *) (auto simp: ab h_def k_def conv_num_denom)
  also have "\<dots> = \<bar>a * k m - b * h m\<bar> / (k m * b)"
    by (simp add: k_def)
  finally have eq: "\<bar>cfrac_lim c - conv c m\<bar> = of_int \<bar>a * k m - b * h m\<bar> / of_int (k m * b)" .

  have "\<bar>cfrac_lim c - conv c m\<bar> * (k m * b) \<noteq> 0"
    using conv_neq_cfrac_lim[of m c] \<open>b > 0\<close> by (auto simp: k_def)
  also have "\<bar>cfrac_lim c - conv c m\<bar> * (k m * b) = of_int \<bar>a * k m - b * h m\<bar>"
    using \<open>b > 0\<close> by (subst eq) (auto simp: k_def)
  finally have "\<bar>a * k m - b * h m\<bar> \<ge> 1" by linarith
  hence "real_of_int \<bar>a * k m - b * h m\<bar> \<ge> 1" by linarith
  hence "1 / of_int (k m * b) \<le> of_int \<bar>a * k m - b * h m\<bar> / real_of_int (k m * b)"
    using \<open>b > 0\<close> by (intro divide_right_mono) (auto simp: k_def)
  also have "\<dots> = \<bar>cfrac_lim c - conv c m\<bar>"
    by (rule eq [symmetric])
  also have "\<dots> \<le> 1 / real_of_int (conv_denom c m * conv_denom c (Suc m))"
    by (intro cfrac_lim_minus_conv_upper_bound) auto
  also have "\<dots> = 1 / (real_of_int (k m) * real_of_int (k (Suc m)))"
    by (simp add: k_def)
  also have "\<dots> < 1 / (real_of_int (k m) * real b)"
    using m \<open>b > 0\<close>
    by (intro divide_strict_left_mono mult_strict_left_mono) (auto simp: k_def)
  finally show False by simp
qed

lemma cfrac_infinite_iff: "cfrac_length c = \<infinity> \<longleftrightarrow> cfrac_lim c \<notin> \<rat>"
  using cfrac_lim_irrational[of c] cfrac_lim_rational[of c] by auto

lemma cfrac_lim_rational_iff: "cfrac_lim c \<in> \<rat> \<longleftrightarrow> cfrac_length c \<noteq> \<infinity>"
  using cfrac_lim_irrational[of c] cfrac_lim_rational[of c] by auto

lemma cfrac_of_real_infinite_iff [simp]: "cfrac_length (cfrac_of_real x) = \<infinity> \<longleftrightarrow> x \<notin> \<rat>"
  by (simp add: cfrac_infinite_iff)

lemma cfrac_remainder_rational_iff [simp]:
  "cfrac_remainder c n \<in> \<rat> \<longleftrightarrow> cfrac_length c < \<infinity>"
proof -
  have "cfrac_remainder c n \<in> \<rat> \<longleftrightarrow> cfrac_lim (cfrac_drop n c) \<in> \<rat>"
    by (simp add: cfrac_remainder_def)
  also have "\<dots> \<longleftrightarrow> cfrac_length c \<noteq> \<infinity>"
    by (cases "cfrac_length c") (auto simp add: cfrac_lim_rational_iff)
  finally show ?thesis by simp
qed

lift_definition cfrac_cons :: "int \<Rightarrow> cfrac \<Rightarrow> cfrac" is
  "\<lambda>a bs. case bs of (b, bs) \<Rightarrow> if b \<le> 0 then (1, LNil) else (a, LCons (nat (b - 1)) bs)" .

lemma cfrac_nth_cons:
  assumes "cfrac_nth x 0 \<ge> 1"
  shows   "cfrac_nth (cfrac_cons a x) n = (if n = 0 then a else cfrac_nth x (n - 1))"
  using assms
proof (transfer, goal_cases)
  case (1 x a n)
  obtain b bs where [simp]: "x = (b, bs)"
    by (cases x)
  show ?case using 1
    by (cases "llength bs") (auto simp: lnth_LCons eSuc_enat le_imp_diff_is_add split: nat.splits)
qed

lemma cfrac_length_cons [simp]:
  assumes "cfrac_nth x 0 \<ge> 1"
  shows   "cfrac_length (cfrac_cons a x) = eSuc (cfrac_length x)"
  using assms by transfer auto

lemma cfrac_tl_cons [simp]:
  assumes "cfrac_nth x 0 \<ge> 1"
  shows   "cfrac_tl (cfrac_cons a x) = x"
  using assms by transfer auto

lemma cfrac_cons_tl:
  assumes "\<not>cfrac_is_int x"
  shows   "cfrac_cons (cfrac_nth x 0) (cfrac_tl x) = x"
  using assms unfolding cfrac_is_int_def
  by transfer (auto split: llist.splits)


subsection \<open>Non-canonical continued fractions\<close>

text \<open>
  As we will show later, every irrational number has a unique continued fraction
  expansion. Every rational number \<open>x\<close>, however, has two different expansions:
  The canonical one ends with some number \<open>n\<close> (which is not equal to 1 unless \<open>x = 1\<close>)
  and a non-canonical one which ends with $n-1, 1$.

  We now define this non-canonical expansion analogously to the canonical one before
  and show its characteristic properties:

    \<^item> The length of the non-canonical expansion is one greater than that of the
      canonical one.

    \<^item> If the expansion is infinite, the non-canonical and the canonical one coincide.

    \<^item> The coefficients of the expansions are all equal except for the last two.
      The last coefficient of the non-canonical expansion is always 1, and the
      second to last one is the last of the canonical one minus 1.
\<close>

lift_definition cfrac_canonical :: "cfrac \<Rightarrow> bool" is
  "\<lambda>(x, xs). \<not>lfinite xs \<or> lnull xs \<or> llast xs \<noteq> 0" .

lemma cfrac_canonical [code]:
  "cfrac_canonical (CFrac x xs) \<longleftrightarrow> lnull xs \<or> llast xs \<noteq> 0 \<or> \<not>lfinite xs"
  by (auto simp add: cfrac_canonical_def)

lemma cfrac_canonical_iff:
  "cfrac_canonical c \<longleftrightarrow>
     cfrac_length c \<in> {0, \<infinity>} \<or> cfrac_nth c (the_enat (cfrac_length c)) \<noteq> 1"
proof (transfer, clarify, goal_cases)
  case (1 x xs)
  show ?case
    by (cases "llength xs")
       (auto simp: llast_def enat_0 lfinite_conv_llength_enat split: nat.splits)
qed

lemma llast_cfrac_of_real_aux_nonzero:
  assumes "lfinite (cfrac_of_real_aux x)" "\<not>lnull (cfrac_of_real_aux x)" 
  shows   "llast (cfrac_of_real_aux x) \<noteq> 0"
  using assms
proof (induction "cfrac_of_real_aux x" arbitrary: x rule: lfinite_induct)
  case (LCons x)
  from LCons.prems have "x \<in> {0<..<1}"
    by (subst (asm) cfrac_of_real_aux.code) (auto split: if_splits)
  show ?case
  proof (cases "1 / x \<in> \<int>")
    case False
    thus ?thesis using LCons
      by (auto simp: llast_LCons frac_lt_1 cfrac_of_real_aux.code[of x])
  next
    case True
    then obtain n where n: "1 / x = of_int n"
      by (elim Ints_cases)
    have "1 / x > 1" using \<open>x \<in> _\<close> by auto
    with n have "n > 1" by simp
    from n have "x = 1 / of_int n"
      using \<open>n > 1\<close> \<open>x \<in> _\<close> by (simp add: field_simps)
    with \<open>n > 1\<close> show ?thesis
      using LCons cfrac_of_real_aux.code[of x] by (auto simp: llast_LCons frac_lt_1)
  qed
qed auto

lemma cfrac_canonical_of_real [intro]: "cfrac_canonical (cfrac_of_real x)"
  by (transfer fixing: x) (use llast_cfrac_of_real_aux_nonzero[of "frac x"] in force)

primcorec cfrac_of_real_alt_aux :: "real \<Rightarrow> nat llist" where
  "cfrac_of_real_alt_aux x =
     (if x \<in> {0<..<1} then
        if 1 / x \<in> \<int> then
          LCons (nat \<lfloor>1/x\<rfloor> - 2) (LCons 0 LNil)
        else LCons (nat \<lfloor>1/x\<rfloor> - 1) (cfrac_of_real_alt_aux (frac (1/x)))
      else LNil)"

lemma cfrac_of_real_aux_alt_LNil [simp]: "x \<notin> {0<..<1} \<Longrightarrow> cfrac_of_real_alt_aux x = LNil"
  by (subst cfrac_of_real_alt_aux.code) auto

lemma cfrac_of_real_aux_alt_0 [simp]: "cfrac_of_real_alt_aux 0 = LNil"
  by (subst cfrac_of_real_alt_aux.code) auto

lemma cfrac_of_real_aux_alt_eq_LNil_iff [simp]: "cfrac_of_real_alt_aux x = LNil \<longleftrightarrow> x \<notin> {0<..<1}"
  by (subst cfrac_of_real_alt_aux.code) auto

lift_definition cfrac_of_real_alt :: "real \<Rightarrow> cfrac" is
  "\<lambda>x. if x \<in> \<int> then (\<lfloor>x\<rfloor> - 1, LCons 0 LNil) else (\<lfloor>x\<rfloor>, cfrac_of_real_alt_aux (frac x))" .

lemma cfrac_tl_of_real_alt:
  assumes "x \<notin> \<int>"
  shows   "cfrac_tl (cfrac_of_real_alt x) = cfrac_of_real_alt (1 / frac x)"
  using assms
proof (transfer, goal_cases)
  case (1 x)
  show ?case
  proof (cases "1 / frac x \<in> \<int>")
    case False
    from 1 have "int (nat \<lfloor>1 / frac x\<rfloor> - Suc 0) + 1 = \<lfloor>1 / frac x\<rfloor>"
      by (subst of_nat_diff) (auto simp: le_nat_iff frac_le_1)
    with False show ?thesis
      using \<open>x \<notin> \<int>\<close>
      by (subst cfrac_of_real_alt_aux.code) (auto split: llist.splits simp: frac_lt_1)
  next
    case True
    then obtain n where "1 / frac x = of_int n"
      by (auto simp: Ints_def)
    moreover have "1 / frac x > 1"
      using 1 by (auto simp: divide_simps frac_lt_1)
    ultimately have "1 / frac x \<ge> 2"
      by simp
    hence "int (nat \<lfloor>1 / frac x\<rfloor> - 2) + 2 = \<lfloor>1 / frac x\<rfloor>"
      by (subst of_nat_diff) (auto simp: le_nat_iff frac_le_1)
    thus ?thesis
      using \<open>x \<notin> \<int>\<close>
      by (subst cfrac_of_real_alt_aux.code) (auto split: llist.splits simp: frac_lt_1)
  qed
qed

lemma cfrac_nth_of_real_alt_Suc:
  assumes "x \<notin> \<int>"
  shows   "cfrac_nth (cfrac_of_real_alt x) (Suc n) = cfrac_nth (cfrac_of_real_alt (1 / frac x)) n"
proof -
  have "cfrac_nth (cfrac_of_real_alt x) (Suc n) =
          cfrac_nth (cfrac_tl (cfrac_of_real_alt x)) n"
    by simp
  also have "cfrac_tl (cfrac_of_real_alt x) = cfrac_of_real_alt (1 / frac x)"
    by (simp add: cfrac_tl_of_real_alt assms)
  finally show ?thesis .
qed

lemma cfrac_nth_gt0_of_real_int [simp]:
  "m > 0 \<Longrightarrow> cfrac_nth (cfrac_of_real (of_int n)) m = 1"
  by transfer (auto simp: lnth_LCons eSuc_def enat_0_iff split: nat.splits)

lemma cfrac_nth_0_of_real_alt_int [simp]:
  "cfrac_nth (cfrac_of_real_alt (of_int n)) 0 = n - 1"
  by transfer auto

lemma cfrac_nth_gt0_of_real_alt_int [simp]:
  "m > 0 \<Longrightarrow> cfrac_nth (cfrac_of_real_alt (of_int n)) m = 1"
  by transfer (auto simp: lnth_LCons eSuc_def split: nat.splits)

lemma llength_cfrac_of_real_alt_aux:
  assumes "x \<in> {0<..<1}"
  shows   "llength (cfrac_of_real_alt_aux x) = eSuc (llength (cfrac_of_real_aux x))"
  using assms
proof (coinduction arbitrary: x rule: enat_coinduct)
  case (Eq_enat x)
  show ?case
  proof (cases "1 / x \<in> \<int>")
    case False
    with Eq_enat have "frac (1 / x) \<in> {0<..<1}"
      by (auto intro: frac_lt_1)
    hence "\<exists>x'. llength (cfrac_of_real_alt_aux (frac (1 / x))) =
              llength (cfrac_of_real_alt_aux x') \<and> 
              llength (cfrac_of_real_aux (frac (1 / x))) = llength (cfrac_of_real_aux x') \<and> 
              0 < x' \<and> x' < 1"
      by (intro exI[of _ "frac (1 / x)"]) auto
    thus ?thesis using False Eq_enat
      by (auto simp: cfrac_of_real_alt_aux.code[of x] cfrac_of_real_aux.code[of x])
  qed (use Eq_enat in \<open>auto simp: cfrac_of_real_alt_aux.code[of x] cfrac_of_real_aux.code[of x]\<close>)
qed

lemma cfrac_length_of_real_alt:
  "cfrac_length (cfrac_of_real_alt x) = eSuc (cfrac_length (cfrac_of_real x))"
  by transfer (auto simp: llength_cfrac_of_real_alt_aux frac_lt_1)

lemma cfrac_of_real_alt_aux_eq_regular:
  assumes "x \<in> {0<..<1}" "llength (cfrac_of_real_aux x) = \<infinity>"
  shows   "cfrac_of_real_alt_aux x = cfrac_of_real_aux x"
  using assms
proof (coinduction arbitrary: x)
  case (Eq_llist x)
  hence "\<exists>x'. cfrac_of_real_aux (frac (1 / x)) =
        cfrac_of_real_aux x' \<and>
        cfrac_of_real_alt_aux (frac (1 / x)) =
        cfrac_of_real_alt_aux x' \<and> 0 < x' \<and> x' < 1 \<and> llength (cfrac_of_real_aux x') = \<infinity>"
    by (intro exI[of _ "frac (1 / x)"])
       (auto simp: cfrac_of_real_aux.code[of x] cfrac_of_real_alt_aux.code[of x]
                   eSuc_eq_infinity_iff frac_lt_1)
  with Eq_llist show ?case
    by (auto simp: eSuc_eq_infinity_iff)
qed

lemma cfrac_of_real_alt_irrational [simp]:
  assumes "x \<notin> \<rat>"
  shows   "cfrac_of_real_alt x = cfrac_of_real x"
proof -
  from assms have "cfrac_length (cfrac_of_real x) = \<infinity>"
    using cfrac_length_of_real_irrational by blast
  with assms show ?thesis
    by transfer
       (use Ints_subset_Rats in 
        \<open>auto intro!: cfrac_of_real_alt_aux_eq_regular simp: frac_lt_1 llength_cfrac_of_real_alt_aux\<close>)
qed

lemma cfrac_nth_of_real_alt_0:
  "cfrac_nth (cfrac_of_real_alt x) 0 = (if x \<in> \<int> then \<lfloor>x\<rfloor> - 1 else \<lfloor>x\<rfloor>)"
  by transfer auto

lemma cfrac_nth_of_real_alt:
  fixes n :: nat and x :: real
  defines "c \<equiv> cfrac_of_real x"
  defines "c' \<equiv> cfrac_of_real_alt x"
  defines "l \<equiv> cfrac_length c"
  shows   "cfrac_nth c' n =
           (if enat n = l then
              cfrac_nth c n - 1
            else if enat n = l + 1 then
              1
            else
              cfrac_nth c n)"
  unfolding c_def c'_def l_def
proof (induction n arbitrary: x rule: less_induct)
  case (less n)
  consider "x \<notin> \<rat>" | "x \<in> \<int>" | "n = 0" "x \<in> \<rat> - \<int>" | n' where "n = Suc n'" "x \<in> \<rat> - \<int>"
    by (cases n) auto
  thus ?case
  proof cases
    assume "x \<notin> \<rat>"
    thus ?thesis
      by (auto simp: cfrac_length_of_real_irrational)
  next
    assume "x \<in> \<int>"
    thus ?thesis
      by (auto simp: Ints_def one_enat_def zero_enat_def)
  next
    assume *: "n = 0" "x \<in> \<rat> - \<int>"
    have "enat 0 \<noteq> cfrac_length (cfrac_of_real x) + 1"
      using zero_enat_def by auto
    moreover have "enat 0 \<noteq> cfrac_length (cfrac_of_real x)"
      using * cfrac_length_of_real_reduce zero_enat_def by auto
    ultimately show ?thesis using *
      by (auto simp: cfrac_nth_of_real_alt_0)
  next
    fix n' assume *: "n = Suc n'" "x \<in> \<rat> - \<int>"
    from less.IH [of n' "1 / frac x"] and * show ?thesis
      by (auto simp: cfrac_nth_of_real_Suc cfrac_nth_of_real_alt_Suc cfrac_length_of_real_reduce 
                     eSuc_def one_enat_def enat_0_iff split: enat.splits)
  qed
qed

lemma cfrac_of_real_length_eq_0_iff: "cfrac_length (cfrac_of_real x) = 0 \<longleftrightarrow> x \<in> \<int>"
  by transfer (auto simp: frac_lt_1)

lemma conv'_cong:
  assumes "(\<And>k. k < n \<Longrightarrow> cfrac_nth c k = cfrac_nth c' k)" "n = n'" "x = y"
  shows   "conv' c n x = conv' c' n' y"
  using assms(1) unfolding assms(2,3) [symmetric]
  by (induction n arbitrary: x) (auto simp: conv'_Suc_right)

lemma conv_cong:
  assumes "(\<And>k. k \<le> n \<Longrightarrow> cfrac_nth c k = cfrac_nth c' k)" "n = n'"
  shows   "conv c n = conv c' n'"
  using assms(1) unfolding assms(2) [symmetric]
  by (induction n arbitrary: c c') (auto simp: conv_Suc)

lemma conv'_cfrac_of_real_alt:
  assumes "enat n \<le> cfrac_length (cfrac_of_real x)"
  shows   "conv' (cfrac_of_real_alt x) n y = conv' (cfrac_of_real x) n y"
proof (cases "cfrac_length (cfrac_of_real x)")
  case infinity
  thus ?thesis by auto
next
  case [simp]: (enat l')
  with assms show ?thesis
    by (intro conv'_cong refl; subst cfrac_nth_of_real_alt) (auto simp: one_enat_def)
qed

lemma cfrac_lim_of_real_alt [simp]: "cfrac_lim (cfrac_of_real_alt x) = x"
proof (cases "cfrac_length (cfrac_of_real x)")
  case infinity
  thus ?thesis by auto
next
  case (enat l)
  thus ?thesis
  proof (induction l arbitrary: x)
    case 0
    hence "x \<in> \<int>"
      using cfrac_of_real_length_eq_0_iff zero_enat_def by auto
    thus ?case
      by (auto simp: Ints_def cfrac_lim_def cfrac_length_of_real_alt eSuc_def conv_Suc)
  next
    case (Suc l x)
    hence *: "\<not>cfrac_is_int (cfrac_of_real_alt x)" "x \<notin> \<int>"
      by (auto simp: cfrac_is_int_def cfrac_length_of_real_alt Ints_def zero_enat_def eSuc_def)
    hence "cfrac_lim (cfrac_of_real_alt x) =
             of_int \<lfloor>x\<rfloor> + 1 / cfrac_lim (cfrac_tl (cfrac_of_real_alt x))"
      by (subst cfrac_lim_reduce) (auto simp: cfrac_nth_of_real_alt_0)
    also have "cfrac_length (cfrac_of_real (1 / frac x)) = l"
      using Suc.prems * by (metis cfrac_length_of_real_reduce eSuc_enat eSuc_inject)
    hence "1 / cfrac_lim (cfrac_tl (cfrac_of_real_alt x)) = frac x"
      by (subst cfrac_tl_of_real_alt[OF *(2)], subst Suc) (use Suc.prems * in auto)
    also have "real_of_int \<lfloor>x\<rfloor> + frac x = x"
      by (simp add: frac_def)
    finally show ?case .
  qed
qed

lemma cfrac_eqI:
  assumes "cfrac_length c = cfrac_length c'" and "\<And>n. cfrac_nth c n = cfrac_nth c' n"
  shows   "c = c'"
proof (use assms in transfer, safe, goal_cases)
  case (1 a xs b ys)
  from 1(2)[of 0] show ?case
    by auto
next
  case (2 a xs b ys)
  define f where "f = (\<lambda>xs n. if enat (Suc n) \<le> llength xs then int (lnth xs n) + 1 else 1)"
  have "\<forall>n. f xs n = f ys n"
    using 2(2)[of "Suc n" for n] by (auto simp: f_def cong: if_cong)
  with 2(1) show "xs = ys"
  proof (coinduction arbitrary: xs ys)
    case (Eq_llist xs ys)
    show ?case
    proof (cases "lnull xs \<or> lnull ys")
      case False
      from False have *: "enat (Suc 0) \<le> llength ys"
        using Suc_ile_eq zero_enat_def by auto
      have "llength (ltl xs) = llength (ltl ys)"
        using Eq_llist by (cases xs; cases ys) auto
      moreover have "lhd xs = lhd ys"
        using False * Eq_llist(1) spec[OF Eq_llist(2), of 0] 
        by (auto simp: f_def lnth_0_conv_lhd)
      moreover have "f (ltl xs) n = f (ltl ys) n" for n
        using Eq_llist(1) * spec[OF Eq_llist(2), of "Suc n"]
        by (cases xs; cases ys) (auto simp: f_def Suc_ile_eq split: if_splits)
      ultimately show ?thesis
        using False by auto
    next
      case True
      thus ?thesis
        using Eq_llist(1) by auto
    qed
  qed
qed

lemma cfrac_eq_0I:
  assumes "cfrac_lim c = 0" "cfrac_nth c 0 \<ge> 0"
  shows   "c = 0"
proof -
  have *: "cfrac_is_int c"
  proof (rule ccontr)
    assume *: "\<not>cfrac_is_int c"
    from * have "conv c 0 < cfrac_lim c"
      by (intro conv_less_cfrac_lim) (auto simp: cfrac_is_int_def simp flip: zero_enat_def)
    hence "cfrac_nth c 0 < 0"
      using assms by simp
    thus False
      using assms by simp
  qed
  from * assms have "cfrac_nth c 0 = 0"
    by (auto simp: cfrac_lim_def cfrac_is_int_def)
  from * and this show  "c = 0"
    unfolding zero_cfrac_def cfrac_is_int_def by transfer auto
qed

lemma cfrac_eq_1I:
  assumes "cfrac_lim c = 1" "cfrac_nth c 0 \<noteq> 0"
  shows   "c = 1"
proof -
  have *: "cfrac_is_int c"
  proof (rule ccontr)
    assume *: "\<not>cfrac_is_int c"
    from * have "conv c 0 < cfrac_lim c"
      by (intro conv_less_cfrac_lim) (auto simp: cfrac_is_int_def simp flip: zero_enat_def)
    hence "cfrac_nth c 0 < 0"
      using assms by simp

    have "cfrac_lim c = real_of_int (cfrac_nth c 0) + 1 / cfrac_lim (cfrac_tl c)"
      using * by (subst cfrac_lim_reduce) auto
    also have "real_of_int (cfrac_nth c 0) < 0"
      using \<open>cfrac_nth c 0 < 0\<close> by simp
    also have "1 / cfrac_lim (cfrac_tl c) \<le> 1"
    proof -
      have "1 \<le> cfrac_nth (cfrac_tl c) 0"
        by auto
      also have "\<dots> \<le> cfrac_lim (cfrac_tl c)"
        by (rule cfrac_lim_ge_first)
      finally show ?thesis by simp
    qed
    finally show False
      using assms by simp
  qed

  from * assms have "cfrac_nth c 0 = 1"
    by (auto simp: cfrac_lim_def cfrac_is_int_def)
  from * and this show  "c = 1"
    unfolding one_cfrac_def cfrac_is_int_def by transfer auto
qed

lemma cfrac_coinduct [coinduct type: cfrac]:
  assumes "R c1 c2"
  assumes IH: "\<And>c1 c2. R c1 c2 \<Longrightarrow>
                cfrac_is_int c1 = cfrac_is_int c2 \<and>
                cfrac_nth c1 0 = cfrac_nth c2 0 \<and>
                (\<not>cfrac_is_int c1 \<longrightarrow> \<not>cfrac_is_int c2 \<longrightarrow> R (cfrac_tl c1) (cfrac_tl c2))"
  shows   "c1 = c2"
proof (rule cfrac_eqI)
  show "cfrac_nth c1 n = cfrac_nth c2 n" for n
    using assms(1)
  proof (induction n arbitrary: c1 c2)
    case 0
    from IH[OF this] show ?case
      by auto
  next
    case (Suc n)
    thus ?case
      using IH by (metis cfrac_is_int_iff cfrac_nth_0_of_int cfrac_nth_tl)
  qed
next
  show "cfrac_length c1 = cfrac_length c2"
    using assms(1)
  proof (coinduction arbitrary: c1 c2 rule: enat_coinduct)
    case (Eq_enat c1 c2)
    show ?case
    proof (cases "cfrac_is_int c1")
      case True
      thus ?thesis
        using IH[OF Eq_enat(1)] by (auto simp: cfrac_is_int_def)
    next
      case False
      with IH[OF Eq_enat(1)] have **: "\<not>cfrac_is_int c1" "R (cfrac_tl c1) (cfrac_tl c2)"
        by auto
      have *: "(cfrac_length c1 = 0) = (cfrac_length c2 = 0)"
        using IH[OF Eq_enat(1)] by (auto simp: cfrac_is_int_def)
      show ?thesis
        by (intro conjI impI disjI1 *, rule exI[of _ "cfrac_tl c1"], rule exI[of _ "cfrac_tl c2"])
           (use ** in \<open>auto simp: epred_conv_minus\<close>)
    qed
  qed
qed

lemma cfrac_nth_0_cases:
  "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>  \<or>  cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor> - 1 \<and> cfrac_tl c = 1"
proof (cases "cfrac_is_int c")
  case True
  hence "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
    by (auto simp: cfrac_lim_def cfrac_is_int_def)
  thus ?thesis by blast
next
  case False
  note not_int = this
  have bounds: "1 / cfrac_lim (cfrac_tl c) \<ge> 0 \<and> 1 / cfrac_lim (cfrac_tl c) \<le> 1"
  proof -
    have "1 \<le> cfrac_nth (cfrac_tl c) 0"
      by simp
    also have "\<dots> \<le> cfrac_lim (cfrac_tl c)"
      by (rule cfrac_lim_ge_first)
    finally show ?thesis
      using False by (auto simp: cfrac_lim_nonneg)
  qed

  thus ?thesis
  proof (cases "cfrac_lim (cfrac_tl c) = 1")
    case False
    have "\<lfloor>cfrac_lim c\<rfloor> = cfrac_nth c 0 + \<lfloor>1 / cfrac_lim (cfrac_tl c)\<rfloor>"
      using not_int by (subst cfrac_lim_reduce) auto
    also have "1 / cfrac_lim (cfrac_tl c) \<ge> 0 \<and> 1 / cfrac_lim (cfrac_tl c) < 1"
      using bounds False by (auto simp: divide_simps)
    hence "\<lfloor>1 / cfrac_lim (cfrac_tl c)\<rfloor> = 0"
      by linarith
    finally show ?thesis by simp
  next
    case True
    have "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor> - 1"
      using not_int True by (subst cfrac_lim_reduce) auto
    moreover have "cfrac_tl c = 1"
      using True by (intro cfrac_eq_1I) auto
    ultimately show ?thesis by blast
  qed
qed

lemma cfrac_length_1 [simp]: "cfrac_length 1 = 0"
  unfolding one_cfrac_def by simp

lemma cfrac_nth_1 [simp]: "cfrac_nth 1 m = 1"
  unfolding one_cfrac_def by transfer (auto simp: enat_0_iff)

lemma cfrac_lim_1 [simp]: "cfrac_lim 1 = 1"
  by (auto simp: cfrac_lim_def)


lemma cfrac_nth_0_not_int:
  assumes "cfrac_lim c \<notin> \<int>"
  shows   "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
proof -
  have "cfrac_tl c \<noteq> 1"
  proof
    assume eq: "cfrac_tl c = 1"
    have "\<not>cfrac_is_int c"
      using assms by (auto simp: cfrac_lim_def cfrac_is_int_def)
    hence "cfrac_lim c = of_int \<lfloor>cfrac_nth c 0\<rfloor> + 1"
      using eq by (subst cfrac_lim_reduce) auto
    hence "cfrac_lim c \<in> \<int>"
      by auto
    with assms show False by auto
  qed
  with cfrac_nth_0_cases[of c] show ?thesis by auto
qed

lemma cfrac_of_real_cfrac_lim_irrational:
  assumes "cfrac_lim c \<notin> \<rat>"
  shows   "cfrac_of_real (cfrac_lim c) = c"
proof (rule cfrac_eqI)
  from assms show "cfrac_length (cfrac_of_real (cfrac_lim c)) = cfrac_length c"
    using cfrac_lim_rational_iff by auto
next
  fix n
  show "cfrac_nth (cfrac_of_real (cfrac_lim c)) n = cfrac_nth c n"
    using assms
  proof (induction n arbitrary: c)
    case (0 c)
    thus ?case
      using Ints_subset_Rats by (subst cfrac_nth_0_not_int) auto
  next
    case (Suc n c)
    from Suc.prems have [simp]: "cfrac_lim c \<notin> \<int>"
      using Ints_subset_Rats by blast
    have "cfrac_nth (cfrac_of_real (cfrac_lim c)) (Suc n) =
          cfrac_nth (cfrac_tl (cfrac_of_real (cfrac_lim c))) n"
      by (simp flip: cfrac_nth_tl)
    also have "cfrac_tl (cfrac_of_real (cfrac_lim c)) = cfrac_of_real (1 / frac (cfrac_lim c))"
      using Suc.prems Ints_subset_Rats by (subst cfrac_tl_of_real) auto
    also have "1 / frac (cfrac_lim c) = cfrac_lim (cfrac_tl c)"
      using Suc.prems by (subst cfrac_lim_tl) (auto simp: frac_def cfrac_is_int_def cfrac_nth_0_not_int)
    also have "cfrac_nth (cfrac_of_real (cfrac_lim (cfrac_tl c))) n = cfrac_nth c (Suc n)"
      using Suc.prems by (subst Suc.IH) (auto simp: cfrac_lim_rational_iff)
    finally show ?case .
  qed
qed

lemma cfrac_eqI_first:
  assumes "\<not>cfrac_is_int c" "\<not>cfrac_is_int c'"
  assumes "cfrac_nth c 0 = cfrac_nth c' 0" and "cfrac_tl c = cfrac_tl c'"
  shows   "c = c'"
  using assms unfolding cfrac_is_int_def
  by transfer (auto split: llist.splits)

lemma cfrac_is_int_of_real_iff: "cfrac_is_int (cfrac_of_real x) \<longleftrightarrow> x \<in> \<int>"
  unfolding cfrac_is_int_def by transfer (use frac_lt_1 in auto)

lemma cfrac_not_is_int_of_real_alt: "\<not>cfrac_is_int (cfrac_of_real_alt x)"
  unfolding cfrac_is_int_def by transfer (auto simp: frac_lt_1)

lemma cfrac_tl_of_real_alt_of_int [simp]: "cfrac_tl (cfrac_of_real_alt (of_int n)) = 1"
  unfolding one_cfrac_def by transfer auto

lemma cfrac_is_intI:
  assumes "cfrac_nth c 0 \<ge> \<lfloor>cfrac_lim c\<rfloor>" and "cfrac_lim c \<in> \<int>"
  shows   "cfrac_is_int c"
proof (rule ccontr)
  assume *: "\<not>cfrac_is_int c"
  from * have "conv c 0 < cfrac_lim c"
    by (intro conv_less_cfrac_lim) (auto simp: cfrac_is_int_def simp flip: zero_enat_def)
  with assms show False
    by (auto simp: Ints_def)
qed

lemma cfrac_eq_of_intI:
  assumes "cfrac_nth c 0 \<ge> \<lfloor>cfrac_lim c\<rfloor>" and "cfrac_lim c \<in> \<int>"
  shows   "c = cfrac_of_int \<lfloor>cfrac_lim c\<rfloor>"
proof -
  from assms have int: "cfrac_is_int c"
    by (intro cfrac_is_intI) auto
  have [simp]: "cfrac_lim c = cfrac_nth c 0"
    using int by (simp add: cfrac_lim_def cfrac_is_int_def)
  from int have "c = cfrac_of_int (cfrac_nth c 0)"
    unfolding cfrac_is_int_def by transfer auto
  also from assms have "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
    using int by auto
  finally show ?thesis .
qed

lemma cfrac_lim_of_int [simp]: "cfrac_lim (cfrac_of_int n) = of_int n"
  by (simp add: cfrac_lim_def)

lemma cfrac_of_real_of_int [simp]: "cfrac_of_real (of_int n) = cfrac_of_int n"
  by transfer auto

lemma cfrac_of_real_of_nat [simp]: "cfrac_of_real (of_nat n) = cfrac_of_int (int n)"
  by transfer auto

lemma cfrac_int_cases:
  assumes "cfrac_lim c = of_int n"
  shows   "c = cfrac_of_int n \<or> c = cfrac_of_real_alt (of_int n)"
proof -
  from cfrac_nth_0_cases[of c] show ?thesis
  proof (rule disj_forward)
    assume eq: "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
    have "c = cfrac_of_int \<lfloor>cfrac_lim c\<rfloor>"
      using assms eq by (intro cfrac_eq_of_intI) auto
    with assms eq show "c = cfrac_of_int n"
      by simp
  next
    assume *: "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor> - 1 \<and> cfrac_tl c = 1"
    have "\<not>cfrac_is_int c"
      using * by (auto simp: cfrac_is_int_def cfrac_lim_def)
    hence "cfrac_length c = eSuc (cfrac_length (cfrac_tl c))"
      by (subst cfrac_length_tl; cases "cfrac_length c")
         (auto simp: cfrac_is_int_def eSuc_def enat_0_iff split: enat.splits)
    also have "cfrac_tl c = 1"
      using * by auto
    finally have "cfrac_length c = 1"
      by (simp add: eSuc_def one_enat_def)
    show "c = cfrac_of_real_alt (of_int n)"
      by (rule cfrac_eqI_first)
         (use \<open>\<not>cfrac_is_int c\<close> * assms in \<open>auto simp: cfrac_not_is_int_of_real_alt\<close>)
  qed
qed

lemma cfrac_cases:
  "c \<in> {cfrac_of_real (cfrac_lim c), cfrac_of_real_alt (cfrac_lim c)}"
proof (cases "cfrac_length c")
  case infinity
  hence "cfrac_lim c \<notin> \<rat>"
    by (simp add: cfrac_lim_irrational)
  thus ?thesis
    using cfrac_of_real_cfrac_lim_irrational by simp
next
  case (enat l)
  thus ?thesis
  proof (induction l arbitrary: c)
    case (0 c)
    hence "c = cfrac_of_real (cfrac_nth c 0)"
      by transfer (auto simp flip: zero_enat_def)
    with 0 show ?case by (auto simp: cfrac_lim_def)
  next
    case (Suc l c)
    show ?case
    proof (cases "cfrac_lim c \<in> \<int>")
      case True
      thus ?thesis
        using cfrac_int_cases[of c] by (force simp: Ints_def)
    next
      case [simp]: False
      have "\<not>cfrac_is_int c"
        using Suc.prems by (auto simp: cfrac_is_int_def enat_0_iff)
      show ?thesis
        using cfrac_nth_0_cases[of c]
      proof (elim disjE conjE)
        assume *: "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor> - 1" "cfrac_tl c = 1"
        hence "cfrac_lim c \<in> \<int>"
          using \<open>\<not>cfrac_is_int c\<close> by (subst cfrac_lim_reduce) auto
        thus ?thesis
          by (auto simp: cfrac_int_cases)
      next
        assume eq: "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
        have "cfrac_tl c = cfrac_of_real (cfrac_lim (cfrac_tl c)) \<or>
              cfrac_tl c = cfrac_of_real_alt (cfrac_lim (cfrac_tl c))"
          using Suc.IH[of "cfrac_tl c"] Suc.prems by auto
        hence "c = cfrac_of_real (cfrac_lim c) \<or>
               c = cfrac_of_real_alt (cfrac_lim c)"
        proof (rule disj_forward)
          assume eq': "cfrac_tl c = cfrac_of_real (cfrac_lim (cfrac_tl c))"
          show "c = cfrac_of_real (cfrac_lim c)"
            by (rule cfrac_eqI_first)
               (use \<open>\<not>cfrac_is_int c\<close> eq eq' in
                \<open>auto simp: cfrac_is_int_of_real_iff cfrac_tl_of_real cfrac_lim_tl frac_def\<close>)
        next
          assume eq': "cfrac_tl c = cfrac_of_real_alt (cfrac_lim (cfrac_tl c))"
          have eq'': "cfrac_nth (cfrac_of_real_alt (cfrac_lim c)) 0 = \<lfloor>cfrac_lim c\<rfloor>"
            using Suc.prems by (subst cfrac_nth_of_real_alt_0) auto
          show "c = cfrac_of_real_alt (cfrac_lim c)"
            by (rule cfrac_eqI_first)
               (use \<open>\<not>cfrac_is_int c\<close> eq eq' eq'' in
                \<open>auto simp: cfrac_not_is_int_of_real_alt cfrac_tl_of_real_alt cfrac_lim_tl frac_def\<close>)
        qed
        thus ?thesis by simp
      qed
    qed
  qed
qed

lemma cfrac_lim_eq_iff:
  assumes "cfrac_length c = \<infinity> \<or> cfrac_length c' = \<infinity>"
  shows   "cfrac_lim c = cfrac_lim c' \<longleftrightarrow> c = c'"
proof
  assume *: "cfrac_lim c = cfrac_lim c'"
  hence "cfrac_of_real (cfrac_lim c) = cfrac_of_real (cfrac_lim c')"
    by (simp only:)
  thus "c = c'"
    using assms *
    by (subst (asm) (1 2) cfrac_of_real_cfrac_lim_irrational)
       (auto simp: cfrac_infinite_iff)
qed auto

lemma floor_cfrac_remainder:
  assumes "cfrac_length c = \<infinity>"
  shows   "\<lfloor>cfrac_remainder c n\<rfloor> = cfrac_nth c n"
  by (metis add.left_neutral assms cfrac_length_drop cfrac_lim_eq_iff idiff_infinity
            cfrac_lim_of_real cfrac_nth_drop cfrac_nth_of_real_0 cfrac_remainder_def)
      

subsection \<open>Approximation properties\<close>

text \<open>
  In this section, we will show that convergents of the continued fraction expansion of a 
  number \<open>x\<close> are good approximations of \<open>x\<close>, and in a certain sense, the reverse holds as well.
\<close>

lemma sgn_of_int:
  "sgn (of_int x :: 'a :: {linordered_idom}) = of_int (sgn x)"
  by (auto simp: sgn_if)

lemma conv_ge_one: "cfrac_nth c 0 > 0 \<Longrightarrow> conv c n \<ge> 1"
  by (rule order.trans[OF _ conv_ge_first]) auto

context
  fixes c h k
  defines "h \<equiv> conv_num c" and "k \<equiv> conv_denom c"
begin

lemma abs_diff_le_abs_add:
  fixes x y :: real
  assumes "x \<ge> 0 \<and> y \<ge> 0 \<or> x \<le> 0 \<and> y \<le> 0"
  shows   "\<bar>x - y\<bar> \<le> \<bar>x + y\<bar>"
  using assms by linarith

lemma abs_diff_less_abs_add:
  fixes x y :: real
  assumes "x > 0 \<and> y > 0 \<or> x < 0 \<and> y < 0"
  shows   "\<bar>x - y\<bar> < \<bar>x + y\<bar>"
  using assms by linarith

lemma abs_diff_le_imp_same_sign:
  assumes "\<bar>x - y\<bar> \<le> d" "d < \<bar>y\<bar>"
  shows   "sgn x = sgn (y::real)"
  using assms by (auto simp: sgn_if)

lemma conv_nonpos:
  assumes "cfrac_nth c 0 < 0"
  shows   "conv c n \<le> 0"
proof (cases n)
  case 0
  thus ?thesis using assms by auto
next
  case [simp]: (Suc n')
  have "conv c n = real_of_int (cfrac_nth c 0) + 1 / conv (cfrac_tl c) n'"
    by (simp add: conv_Suc)
  also have "\<dots> \<le> -1 + 1 / 1"
    using assms by (intro add_mono divide_left_mono) (auto intro!: conv_pos conv_ge_one)
  finally show ?thesis by simp
qed

lemma cfrac_lim_nonpos:
  assumes "cfrac_nth c 0 < 0"
  shows   "cfrac_lim c \<le> 0"
proof (cases "cfrac_length c")
  case infinity
  show ?thesis using LIMSEQ_cfrac_lim[OF infinity]
    by (rule tendsto_upperbound) (use assms in \<open>auto simp: conv_nonpos\<close>)
next
  case (enat l)
  thus ?thesis by (auto simp: cfrac_lim_def conv_nonpos assms)
qed

lemma conv_num_nonpos:
  assumes "cfrac_nth c 0 < 0"
  shows   "h n \<le> 0"
proof (induction n rule: fib.induct)
  case 2
  have "cfrac_nth c (Suc 0) * cfrac_nth c 0 \<le> 1 * cfrac_nth c 0"
    using assms by (intro mult_right_mono_neg) auto
  also have "\<dots> + 1 \<le> 0" using assms by auto
  finally show ?case by (auto simp: h_def)
next
  case (3 n)
  have "cfrac_nth c (Suc (Suc n)) * h (Suc n) \<le> 0"
    using 3 by (simp add: mult_nonneg_nonpos)
  also have "\<dots> + h n \<le> 0"
    using 3 by simp
  finally show ?case
    by (auto simp: h_def)
qed (use assms in \<open>auto simp: h_def\<close>)

lemma conv_best_approximation_aux:
  "cfrac_lim c \<ge> 0 \<and> h n \<ge> 0 \<or> cfrac_lim c \<le> 0 \<and> h n \<le> 0"
proof (cases "cfrac_nth c 0 \<ge> 0")
  case True
  from True have "0 \<le> conv c 0"
    by simp
  also have "\<dots> \<le> cfrac_lim c"
    by (rule conv_le_cfrac_lim) (auto simp: enat_0)
  finally have "cfrac_lim c \<ge> 0" .
  moreover from True have "h n \<ge> 0"
    unfolding h_def by (intro conv_num_nonneg)
  ultimately show ?thesis by (simp add: sgn_if)
next
  case False
  thus ?thesis
    using cfrac_lim_nonpos conv_num_nonpos[of n] by (auto simp: h_def)
qed

lemma conv_best_approximation_ex:
  fixes a b :: int and x :: real
  assumes "n \<le> cfrac_length c"
  assumes "0 < b" and "b \<le> k n" and "coprime a b" and "n > 0"
  assumes "(a, b) \<noteq> (h n, k n)"
  assumes "\<not>(cfrac_length c = 1 \<and> n = 0)"
  assumes "Suc n \<noteq> cfrac_length c \<or> cfrac_canonical c"
  defines "x \<equiv> cfrac_lim c"
  shows   "\<bar>k n * x - h n\<bar> < \<bar>b * x - a\<bar>"
proof (cases "\<bar>a\<bar> = \<bar>h n\<bar> \<and> b = k n")
  case True
  with assms have [simp]: "a = -h n"
    by (auto simp: abs_if split: if_splits)
  have "k n > 0"
    by (auto simp: k_def)
  show ?thesis
  proof (cases "x = 0")
    case True
    hence "c = cfrac_of_real 0 \<or> c = cfrac_of_real_alt 0"
      unfolding x_def by (metis cfrac_cases empty_iff insert_iff)
    hence False
    proof
      assume "c = cfrac_of_real 0"
      thus False
        using assms by (auto simp: enat_0_iff h_def k_def)
    next
      assume [simp]: "c = cfrac_of_real_alt 0"
      hence "n = 0 \<or> n = 1"
        using assms by (auto simp: cfrac_length_of_real_alt enat_0_iff k_def h_def eSuc_def)
      thus False
        using assms True
        by (elim disjE) (auto simp: cfrac_length_of_real_alt enat_0_iff k_def h_def eSuc_def
                                    cfrac_nth_of_real_alt one_enat_def split: if_splits)
    qed
    thus ?thesis ..
  next
    case False
    have "h n \<noteq> 0"
      using True assms(6) h_def by auto
    hence "x > 0 \<and> h n > 0 \<or> x < 0 \<and> h n < 0"
      using \<open>x \<noteq> 0\<close> conv_best_approximation_aux[of n] unfolding x_def by auto
    hence "\<bar>real_of_int (k n) * x - real_of_int (h n)\<bar> < \<bar>real_of_int (k n) * x + real_of_int (h n)\<bar>"   
      using \<open>k n > 0\<close>
      by (intro abs_diff_less_abs_add) (auto simp: not_le zero_less_mult_iff mult_less_0_iff)
    thus ?thesis using True by auto
  qed
next
  case False
  note * = this
  show ?thesis
  proof (cases "n = cfrac_length c")
    case True
    hence "x = conv c n"
      by (auto simp: cfrac_lim_def x_def split: enat.splits)
    also have "\<dots> = h n / k n"
      by (auto simp: h_def k_def conv_num_denom)
    finally have x: "x = h n / k n" .
    hence "\<bar>k n * x - h n\<bar> = 0"
      by (simp add: k_def)
    also have "b * x \<noteq> a"
    proof
      assume "b * x = a"
      hence "of_int (h n) * of_int b = of_int (k n) * (of_int a :: real)"
        using assms True by (auto simp: field_simps k_def x)
      hence "of_int (h n * b) = (of_int (k n * a) :: real)"
        by (simp only: of_int_mult)
      hence "h n * b = k n * a"
        by linarith
      hence "h n = a \<and> k n = b"
        using assms by (subst (asm) coprime_crossproduct')
                       (auto simp: h_def k_def coprime_conv_num_denom)
      thus False using True False by simp
    qed
    hence "0 < \<bar>b * x - a\<bar>"
      by simp
    finally show ?thesis .
  next
    case False

    define s where "s = (-1) ^ n * (a * k n - b * h n)"
    define r where "r = (-1) ^ n * (b * h (Suc n) - a * k (Suc n))"
    have "k n \<le> k (Suc n)"
      unfolding k_def by (intro conv_denom_leI) auto

    have "r * h n + s * h (Suc n) = 
            (-1) ^ Suc n * a * (k (Suc n) * h n - k n * h (Suc n))"
      by (simp add: s_def r_def algebra_simps h_def k_def)
    also have "\<dots> = a" using assms unfolding h_def k_def
      by (subst conv_num_denom_prod_diff') (auto simp: algebra_simps)
    finally have eq1: "r * h n + s * h (Suc n) = a" .
  
    have "r * k n + s * k (Suc n) = 
            (-1) ^ Suc n * b * (k (Suc n) * h n - k n * h (Suc n))"
      by (simp add: s_def r_def algebra_simps h_def k_def)
    also have "\<dots> = b" using assms unfolding h_def k_def
      by (subst conv_num_denom_prod_diff') (auto simp: algebra_simps)
    finally have eq2: "r * k n + s * k (Suc n) = b" .

    have "k n < k (Suc n)"
      using \<open>n > 0\<close> by (auto simp: k_def intro: conv_denom_lessI)
  
    have "r \<noteq> 0"
    proof
      assume "r = 0"
      hence "a * k (Suc n) = b * h (Suc n)" by (simp add: r_def)
      hence "abs (a * k (Suc n)) = abs (h (Suc n) * b)" by (simp only: mult_ac)
      hence *: "abs (h (Suc n)) = abs a \<and> k (Suc n) = b"
        unfolding abs_mult h_def k_def using coprime_conv_num_denom assms
        by (subst (asm) coprime_crossproduct_int) auto
      with \<open>k n < k (Suc n)\<close> and \<open>b \<le> k n\<close> show False by auto
    qed

    have "s \<noteq> 0"
    proof
      assume "s = 0"
      hence "a * k n = b * h n" by (simp add: s_def)
      hence "abs (a * k n) = abs (h n * b)" by (simp only: mult_ac)
      hence "b = k n \<and> \<bar>a\<bar> = \<bar>h n\<bar>" unfolding abs_mult h_def k_def using coprime_conv_num_denom assms
        by (subst (asm) coprime_crossproduct_int) auto
      with * show False by simp
    qed

    have "r * k n + s * k (Suc n) = b" by fact
    also have "\<dots> \<in> {0<..<k (Suc n)}" using assms \<open>k n < k (Suc n)\<close> by auto
    finally have *: "r * k n + s * k (Suc n) \<in> \<dots>" .

    have opposite_signs1: "r > 0 \<and> s < 0 \<or> r < 0 \<and> s > 0"
    proof (cases "r \<ge> 0"; cases "s \<ge> 0")
      assume "r \<ge> 0" "s \<ge> 0"
      hence "0 * (k n) + 1 * (k (Suc n)) \<le> r * k n + s * k (Suc n)"
        using \<open>s \<noteq> 0\<close> by (intro add_mono mult_mono) (auto simp: k_def)
      with * show ?thesis by auto
    next
      assume "\<not>(r \<ge> 0)" "\<not>(s \<ge> 0)"
      hence "r * k n + s * k (Suc n) \<le> 0"
        by (intro add_nonpos_nonpos mult_nonpos_nonneg) (auto simp: k_def)
      with * show ?thesis by auto
    qed (insert \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close>, auto)

    have "r \<noteq> 1"
    proof
      assume [simp]: "r = 1"
      have "b = r * k n + s * k (Suc n)"
        using \<open>r * k n + s * k (Suc n) = b\<close> ..
      also have "s * k (Suc n) \<le> (-1) * k (Suc n)"
        using opposite_signs1 by (intro mult_right_mono) (auto simp: k_def)
      also have "r * k n + (-1) * k (Suc n) = k n - k (Suc n)"
        by simp
      also have "\<dots> \<le> 0"
        unfolding k_def by (auto intro!: conv_denom_leI)
      finally show False using \<open>b > 0\<close> by simp
    qed

    have "enat n \<le> cfrac_length c" "enat (Suc n) \<le> cfrac_length c"
      using assms False by (cases "cfrac_length c"; simp)+
    hence "conv c n \<ge> x \<and> conv c (Suc n) \<le> x \<or> conv c n \<le> x \<and> conv c (Suc n) \<ge> x"
      using conv_ge_cfrac_lim[of n c] conv_ge_cfrac_lim[of "Suc n" c]
            conv_le_cfrac_lim[of n c] conv_le_cfrac_lim[of "Suc n" c] assms
      by (cases "even n") auto
    hence opposite_signs2: "k n * x - h n \<ge> 0 \<and> k (Suc n) * x - h (Suc n) \<le> 0 \<or>
                           k n * x - h n \<le> 0 \<and> k (Suc n) * x - h (Suc n) \<ge> 0"
      using assms conv_denom_pos[of c n] conv_denom_pos[of c "Suc n"]
      by (auto simp: k_def h_def conv_num_denom field_simps)
  
    from opposite_signs1 opposite_signs2 have same_signs:
      "r * (k n * x - h n) \<ge> 0 \<and> s * (k (Suc n) * x - h (Suc n)) \<ge> 0 \<or>
       r * (k n * x - h n) \<le> 0 \<and> s * (k (Suc n) * x - h (Suc n)) \<le> 0"
      by (auto intro: mult_nonpos_nonneg mult_nonneg_nonpos mult_nonneg_nonneg mult_nonpos_nonpos)

    show ?thesis
    proof (cases "Suc n = cfrac_length c")
      case True
      have x: "x = h (Suc n) / k (Suc n)"
        using True[symmetric] by (auto simp: cfrac_lim_def h_def k_def conv_num_denom x_def)
      have "r \<noteq> -1"
      proof
        assume [simp]: "r = -1"
        have "r * k n + s * k (Suc n) = b"
          by fact
        also have "b < k (Suc n)"
          using \<open>b \<le> k n\<close> and \<open>k n < k (Suc n)\<close> by simp
        finally have "(s - 1) * k (Suc n) < k n"
          by (simp add: algebra_simps)
        also have "k n \<le> 1 * k (Suc n)"
          by (simp add: k_def conv_denom_leI)
        finally have "s < 2"
          by (subst (asm) mult_less_cancel_right) (auto simp: k_def)
        moreover from opposite_signs1 have "s > 0" by auto
        ultimately have [simp]: "s = 1" by simp

        have "b = (cfrac_nth c (Suc n) - 1) * k n + k (n - 1)"
          using eq2 \<open>n > 0\<close> by (cases n) (auto simp: k_def algebra_simps)
        also have "cfrac_nth c (Suc n) > 1"
        proof -
          have "cfrac_canonical c"
            using assms True by auto
          hence "cfrac_nth c (Suc n) \<noteq> 1"
            using True[symmetric] by (auto simp: cfrac_canonical_iff enat_0_iff)
          moreover have "cfrac_nth c (Suc n) > 0"
            by auto
          ultimately show "cfrac_nth c (Suc n) > 1"
            by linarith
        qed
        hence "(cfrac_nth c (Suc n) - 1) * k n + k (n - 1) \<ge> 1 * k n + k (n - 1)"
          by (intro add_mono mult_right_mono) (auto simp: k_def)
        finally have "b > k n"
          using conv_denom_pos[of c "n - 1"] unfolding k_def by linarith
        with assms show False by simp
      qed
      with \<open>r \<noteq> 1\<close> \<open>r \<noteq> 0\<close> have "\<bar>r\<bar> > 1"
        by auto

      from \<open>s \<noteq> 0\<close> have "k n * x \<noteq> h n"
        using conv_num_denom_prod_diff[of c n]
        by (auto simp: x field_simps k_def h_def simp flip: of_int_mult)
      hence "1 * \<bar>k n * x - h n\<bar> < \<bar>r\<bar> * \<bar>k n * x - h n\<bar>"
        using \<open>\<bar>r\<bar> > 1\<close> by (intro mult_strict_right_mono) auto
      also have "\<dots> = \<bar>r\<bar> * \<bar>k n * x - h n\<bar> + 0" by simp
      also have "\<dots> \<le> \<bar>r * (k n * x - h n)\<bar> + \<bar>s * (k (Suc n) * x - h (Suc n))\<bar>"
        unfolding abs_mult of_int_abs using conv_denom_pos[of c "Suc n"] \<open>s \<noteq> 0\<close>
        by (intro add_left_mono mult_nonneg_nonneg) (auto simp: field_simps k_def)
      also have "\<dots> = \<bar>r * (k n * x - h n) + s * (k (Suc n) * x - h (Suc n))\<bar>"
        using same_signs by auto
      also have "\<dots> = \<bar>(r * k n + s * k (Suc n)) * x - (r * h n + s * h (Suc n))\<bar>"
        by (simp add: algebra_simps)
      also have "\<dots> = \<bar>b * x - a\<bar>"
        unfolding eq1 eq2 by simp
      finally show ?thesis by simp
    next
      case False
      from assms have "Suc n < cfrac_length c"
        using False \<open>Suc n \<le> cfrac_length c\<close> by force
      have "1 * \<bar>k n * x - h n\<bar> \<le> \<bar>r\<bar> * \<bar>k n * x - h n\<bar>"
        using \<open>r \<noteq> 0\<close> by (intro mult_right_mono) auto
      also have "\<dots> = \<bar>r\<bar> * \<bar>k n * x - h n\<bar> + 0" by simp
      also have "x \<noteq> h (Suc n) / k (Suc n)"
        using conv_neq_cfrac_lim[of "Suc n" c] \<open>Suc n < cfrac_length c\<close>
        by (auto simp: conv_num_denom h_def k_def x_def)
      hence  "\<bar>s * (k (Suc n) * x - h (Suc n))\<bar> > 0"
        using \<open>s \<noteq> 0\<close> by (auto simp: field_simps k_def)
      also have "\<bar>r\<bar> * \<bar>k n * x - h n\<bar> + \<dots> \<le> 
                 \<bar>r * (k n * x - h n)\<bar> + \<bar>s * (k (Suc n) * x - h (Suc n))\<bar>"
        unfolding abs_mult of_int_abs by (intro add_left_mono mult_nonneg_nonneg) auto
      also have "\<dots> = \<bar>r * (k n * x - h n) + s * (k (Suc n) * x - h (Suc n))\<bar>"
        using same_signs by auto
      also have "\<dots> = \<bar>(r * k n + s * k (Suc n)) * x - (r * h n + s * h (Suc n))\<bar>"
        by (simp add: algebra_simps)
      also have "\<dots> = \<bar>b * x - a\<bar>"
        unfolding eq1 eq2 by simp
      finally show ?thesis by simp
    qed
  qed
qed

lemma conv_best_approximation_ex_weak:
  fixes a b :: int and x :: real
  assumes "n \<le> cfrac_length c"
  assumes "0 < b" and "b < k (Suc n)" and "coprime a b"
  defines "x \<equiv> cfrac_lim c"
  shows   "\<bar>k n * x - h n\<bar> \<le> \<bar>b * x - a\<bar>"
proof (cases "\<bar>a\<bar> = \<bar>h n\<bar> \<and> b = k n")
  case True
  note * = this
  show ?thesis
  proof (cases "sgn a = sgn (h n)")
    case True
    with * have [simp]: "a = h n"
      by (auto simp: abs_if split: if_splits)
    thus ?thesis using * by auto
  next
    case False
    with True have [simp]: "a = -h n"
      by (auto simp: abs_if split: if_splits)
    have "\<bar>real_of_int (k n) * x - real_of_int (h n)\<bar> \<le> \<bar>real_of_int (k n) * x + real_of_int (h n)\<bar>"
      unfolding x_def using conv_best_approximation_aux[of n]
      by (intro abs_diff_le_abs_add) (auto simp: k_def not_le zero_less_mult_iff)
    thus ?thesis using True by auto
  qed
next
  case False
  note * = this
  show ?thesis
  proof (cases "n = cfrac_length c")
    case True
    hence "x = conv c n"
      by (auto simp: cfrac_lim_def x_def split: enat.splits)
    also have "\<dots> = h n / k n"
      by (auto simp: h_def k_def conv_num_denom)
    finally show ?thesis by (auto simp: k_def)
  next
    case False

    define s where "s = (-1) ^ n * (a * k n - b * h n)"
    define r where "r = (-1) ^ n * (b * h (Suc n) - a * k (Suc n))"
  
    have "r * h n + s * h (Suc n) = 
            (-1) ^ Suc n * a * (k (Suc n) * h n - k n * h (Suc n))"
      by (simp add: s_def r_def algebra_simps h_def k_def)
    also have "\<dots> = a" using assms unfolding h_def k_def
      by (subst conv_num_denom_prod_diff') (auto simp: algebra_simps)
    finally have eq1: "r * h n + s * h (Suc n) = a" .
  
    have "r * k n + s * k (Suc n) = 
            (-1) ^ Suc n * b * (k (Suc n) * h n - k n * h (Suc n))"
      by (simp add: s_def r_def algebra_simps h_def k_def)
    also have "\<dots> = b" using assms unfolding h_def k_def
      by (subst conv_num_denom_prod_diff') (auto simp: algebra_simps)
    finally have eq2: "r * k n + s * k (Suc n) = b" .
  
    have "r \<noteq> 0"
    proof
      assume "r = 0"
      hence "a * k (Suc n) = b * h (Suc n)" by (simp add: r_def)
      hence "abs (a * k (Suc n)) = abs (h (Suc n) * b)" by (simp only: mult_ac)
      hence "b = k (Suc n)" unfolding abs_mult h_def k_def using coprime_conv_num_denom assms
        by (subst (asm) coprime_crossproduct_int) auto
      with assms show False by simp
    qed
  
    have "s \<noteq> 0"
    proof
      assume "s = 0"
      hence "a * k n = b * h n" by (simp add: s_def)
      hence "abs (a * k n) = abs (h n * b)" by (simp only: mult_ac)
      hence "b = k n \<and> \<bar>a\<bar> = \<bar>h n\<bar>" unfolding abs_mult h_def k_def using coprime_conv_num_denom assms
        by (subst (asm) coprime_crossproduct_int) auto
      with * show False by simp
    qed

    have "r * k n + s * k (Suc n) = b" by fact
    also have "\<dots> \<in> {0<..<k (Suc n)}" using assms by auto
    finally have *: "r * k n + s * k (Suc n) \<in> \<dots>" .
    
    have opposite_signs1: "r > 0 \<and> s < 0 \<or> r < 0 \<and> s > 0"
    proof (cases "r \<ge> 0"; cases "s \<ge> 0")
      assume "r \<ge> 0" "s \<ge> 0"
      hence "0 * (k n) + 1 * (k (Suc n)) \<le> r * k n + s * k (Suc n)"
        using \<open>s \<noteq> 0\<close> by (intro add_mono mult_mono) (auto simp: k_def)
      with * show ?thesis by auto
    next
      assume "\<not>(r \<ge> 0)" "\<not>(s \<ge> 0)"
      hence "r * k n + s * k (Suc n) \<le> 0"
        by (intro add_nonpos_nonpos mult_nonpos_nonneg) (auto simp: k_def)
      with * show ?thesis by auto
    qed (insert \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close>, auto)

    have "enat n \<le> cfrac_length c" "enat (Suc n) \<le> cfrac_length c"
      using assms False by (cases "cfrac_length c"; simp)+
    hence "conv c n \<ge> x \<and> conv c (Suc n) \<le> x \<or> conv c n \<le> x \<and> conv c (Suc n) \<ge> x"
      using conv_ge_cfrac_lim[of n c] conv_ge_cfrac_lim[of "Suc n" c]
            conv_le_cfrac_lim[of n c] conv_le_cfrac_lim[of "Suc n" c] assms
      by (cases "even n") auto
    hence opposite_signs2: "k n * x - h n \<ge> 0 \<and> k (Suc n) * x - h (Suc n) \<le> 0 \<or>
                           k n * x - h n \<le> 0 \<and> k (Suc n) * x - h (Suc n) \<ge> 0"
      using assms conv_denom_pos[of c n] conv_denom_pos[of c "Suc n"]
      by (auto simp: k_def h_def conv_num_denom field_simps)
  
    from opposite_signs1 opposite_signs2 have same_signs:
      "r * (k n * x - h n) \<ge> 0 \<and> s * (k (Suc n) * x - h (Suc n)) \<ge> 0 \<or>
       r * (k n * x - h n) \<le> 0 \<and> s * (k (Suc n) * x - h (Suc n)) \<le> 0"
      by (auto intro: mult_nonpos_nonneg mult_nonneg_nonpos mult_nonneg_nonneg mult_nonpos_nonpos)

    have "1 * \<bar>k n * x - h n\<bar> \<le> \<bar>r\<bar> * \<bar>k n * x - h n\<bar>"
      using \<open>r \<noteq> 0\<close> by (intro mult_right_mono) auto
    also have "\<dots> = \<bar>r\<bar> * \<bar>k n * x - h n\<bar> + 0" by simp
    also have "\<dots> \<le> \<bar>r * (k n * x - h n)\<bar> + \<bar>s * (k (Suc n) * x - h (Suc n))\<bar>"
      unfolding abs_mult of_int_abs using conv_denom_pos[of c "Suc n"] \<open>s \<noteq> 0\<close>
      by (intro add_left_mono mult_nonneg_nonneg) (auto simp: field_simps k_def)
    also have "\<dots> = \<bar>r * (k n * x - h n) + s * (k (Suc n) * x - h (Suc n))\<bar>"
      using same_signs by auto
    also have "\<dots> = \<bar>(r * k n + s * k (Suc n)) * x - (r * h n + s * h (Suc n))\<bar>"
      by (simp add: algebra_simps)
    also have "\<dots> = \<bar>b * x - a\<bar>"
      unfolding eq1 eq2 by simp
    finally show ?thesis by simp
  qed
qed

lemma cfrac_canonical_reduce:
  "cfrac_canonical c \<longleftrightarrow>
     cfrac_is_int c \<or> \<not>cfrac_is_int c \<and> cfrac_tl c \<noteq> 1 \<and> cfrac_canonical (cfrac_tl c)"
  unfolding cfrac_is_int_def one_cfrac_def
  by transfer (auto simp: cfrac_canonical_def llast_LCons split: if_splits split: llist.splits)
             
lemma cfrac_nth_0_conv_floor:
  assumes "cfrac_canonical c \<or> cfrac_length c \<noteq> 1"
  shows   "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
proof (cases "cfrac_is_int c")
  case True
  thus ?thesis
    by (auto simp: cfrac_lim_def cfrac_is_int_def)
next
  case False
  show ?thesis
  proof (cases "cfrac_length c = 1")
    case True
    hence "cfrac_canonical c" using assms by auto
    hence "cfrac_tl c \<noteq> 1" using False
      by (subst (asm) cfrac_canonical_reduce) auto
    thus ?thesis
      using cfrac_nth_0_cases[of c] by auto
  next
    case False
    hence "cfrac_length c > 1"
      using \<open>\<not>cfrac_is_int c\<close>
      by (cases "cfrac_length c") (auto simp: cfrac_is_int_def one_enat_def zero_enat_def)
    have "cfrac_tl c \<noteq> 1"
    proof
      assume "cfrac_tl c = 1"
      have "0 < cfrac_length c - 1"
      proof (cases "cfrac_length c")
        case [simp]: (enat l)
        have "cfrac_length c - 1 = enat (l - 1)"
          by auto
        also have "\<dots> > enat 0"
          using \<open>cfrac_length c > 1\<close> by (simp add: one_enat_def)
        finally show ?thesis by (simp add: zero_enat_def)
      qed auto
      also have "\<dots> = cfrac_length (cfrac_tl c)"
        by simp
      also have "cfrac_tl c = 1"
        by fact
      finally show False by simp
    qed
    thus ?thesis using cfrac_nth_0_cases[of c] by auto
  qed
qed

lemma conv_best_approximation_ex_nat:
  fixes a b :: nat and x :: real
  assumes "n \<le> cfrac_length c" "0 < b" "b < k (Suc n)" "coprime a b"
  shows   "\<bar>k n * cfrac_lim c - h n\<bar> \<le> \<bar>b * cfrac_lim c - a\<bar>"
  using conv_best_approximation_ex_weak[OF assms(1), of b a] assms by auto

lemma abs_mult_nonneg_left:
  assumes "x \<ge> (0 :: 'a :: {ordered_ab_group_add_abs, idom_abs_sgn})"
  shows   "x * \<bar>y\<bar> = \<bar>x * y\<bar>"
proof -
  from assms have "x = \<bar>x\<bar>" by simp
  also have "\<dots> * \<bar>y\<bar> = \<bar>x * y\<bar>" by (simp add: abs_mult)
  finally show ?thesis .
qed

text \<open>
  Any convergent of the continued fraction expansion of \<open>x\<close> is a best approximation of \<open>x\<close>,
  i.e. there is no other number with a smaller denominator that approximates it better.
\<close>
lemma conv_best_approximation:
  fixes a b :: int and x :: real
  assumes "n \<le> cfrac_length c"
  assumes "0 < b" and "b < k n" and "coprime a b"
  defines "x \<equiv> cfrac_lim c"
  shows   "\<bar>x - conv c n\<bar> \<le> \<bar>x - a / b\<bar>"
proof -
  have "b < k n" by fact
  also have "k n \<le> k (Suc n)"
    unfolding k_def by (intro conv_denom_leI) auto
  finally have *: "b < k (Suc n)" by simp
  have "\<bar>x - conv c n\<bar> = \<bar>k n * x - h n\<bar> / k n"
    using conv_denom_pos[of c n] assms(1)
    by (auto simp: conv_num_denom field_simps k_def h_def)
  also have "\<dots> \<le> \<bar>b * x - a\<bar> / k n" unfolding x_def using assms *
    by (intro divide_right_mono conv_best_approximation_ex_weak) auto
  also from assms have "\<dots> \<le> \<bar>b * x - a\<bar> / b"
    by (intro divide_left_mono) auto
  also have "\<dots> = \<bar>x - a / b\<bar>" using assms by (simp add: field_simps)
  finally show ?thesis .
qed

lemma conv_denom_partition:
  assumes "y > 0"
  shows   "\<exists>!n. y \<in> {k n..<k (Suc n)}"
proof (rule ex_ex1I)
  from conv_denom_at_top[of c] assms have *: "\<exists>n. k n \<ge> y + 1"
    by (auto simp: k_def filterlim_at_top eventually_at_top_linorder)
  define n where "n = (LEAST n. k n \<ge> y + 1)"
  from LeastI_ex[OF *] have n: "k n > y" by (simp add: Suc_le_eq n_def)
  from n and assms have "n > 0" by (intro Nat.gr0I) (auto simp: k_def)

  have "k (n - 1) \<le> y"
  proof (rule ccontr)
    assume "\<not>k (n - 1) \<le> y"
    hence "k (n - 1) \<ge> y + 1" by auto
    hence "n - 1 \<ge> n" unfolding n_def by (rule Least_le)
    with \<open>n > 0\<close> show False by simp
  qed
  with n and \<open>n > 0\<close> have "y \<in> {k (n - 1)..<k (Suc (n - 1))}" by auto
  thus "\<exists>n. y \<in> {k n..<k (Suc n)}" by blast
next
  fix m n
  assume "y \<in> {k m..<k (Suc m)}" "y \<in> {k n..<k (Suc n)}"
  thus "m = n"
  proof (induction m n rule: linorder_wlog)
    case (le m n)
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      with le have "k (Suc m) \<le> k n"
        unfolding k_def by (intro conv_denom_leI assms) auto
      with le show False by auto
    qed
  qed auto
qed

text \<open>
  A fraction that approximates a real number \<open>x\<close> sufficiently well (in a certain sense)
  is a convergent of its continued fraction expansion.
\<close>
lemma frac_is_convergentI:
  fixes a b :: int and x :: real
  defines "x \<equiv> cfrac_lim c"
  assumes "b > 0" and "coprime a b" and "\<bar>x - a / b\<bar> < 1 / (2 * b\<^sup>2)"
  shows   "\<exists>n. enat n \<le> cfrac_length c \<and> (a, b) = (h n, k n)"
proof (cases "a = 0")
  case True
  with assms have [simp]: "a = 0" "b = 1"
    by auto

  show ?thesis
  proof (cases x "0 :: real" rule: linorder_cases)
    case greater
    hence "0 < x" "x < 1/2"
      using assms by auto
    hence "x \<notin> \<int>"
      by (auto simp: Ints_def)
    hence "cfrac_nth c 0 = \<lfloor>x\<rfloor>"
      using assms by (subst cfrac_nth_0_not_int) (auto simp: x_def)
    also from \<open>x > 0\<close> \<open>x < 1/2\<close> have "\<dots> = 0"
      by linarith
    finally have "(a, b) = (h 0, k 0)"
      by (auto simp: h_def k_def)
    thus ?thesis by (intro exI[of _ 0]) (auto simp flip: zero_enat_def)
  next
    case less
    hence "x < 0" "x > -1/2"
      using assms by auto
    hence "x \<notin> \<int>"
      by (auto simp: Ints_def)
    hence not_int: "\<not>cfrac_is_int c"
      by (auto simp: cfrac_is_int_def x_def cfrac_lim_def)
    have "cfrac_nth c 0 = \<lfloor>x\<rfloor>"
      using \<open>x \<notin> \<int>\<close> assms by (subst cfrac_nth_0_not_int) (auto simp: x_def)
    also from \<open>x < 0\<close> \<open>x > -1/2\<close> have "\<dots> = -1"
      by linarith
    finally have [simp]: "cfrac_nth c 0 = -1" .
    have "cfrac_nth c (Suc 0) = cfrac_nth (cfrac_tl c) 0"
      by simp
    have "cfrac_lim (cfrac_tl c) = 1 / (x + 1)"
      using not_int by (subst cfrac_lim_tl) (auto simp: x_def)
    also from \<open>x < 0\<close> \<open>x > -1/2\<close> have "\<dots> \<in> {1<..<2}"
      by (auto simp: divide_simps)
    finally have *: "cfrac_lim (cfrac_tl c) \<in> {1<..<2}" .
    have "cfrac_nth (cfrac_tl c) 0 = \<lfloor>cfrac_lim (cfrac_tl c)\<rfloor>"
      using * by (subst cfrac_nth_0_not_int) (auto simp: Ints_def)
    also have "\<dots> = 1"
      using * by (simp, linarith?)
    finally have "(a, b) = (h 1, k 1)"
      by (auto simp: h_def k_def)
    moreover have "cfrac_length c \<ge> 1"
      using not_int
      by (cases "cfrac_length c") (auto simp: cfrac_is_int_def one_enat_def zero_enat_def)
    ultimately show ?thesis by (intro exI[of _ 1]) (auto simp: one_enat_def)   
  next
    case equal
    show ?thesis
      using cfrac_nth_0_cases[of c]
    proof
      assume "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor>"
      with equal have "(a, b) = (h 0, k 0)"
        by (simp add: x_def h_def k_def)
      thus ?thesis by (intro exI[of _ 0]) (auto simp flip: zero_enat_def)
    next
      assume *: "cfrac_nth c 0 = \<lfloor>cfrac_lim c\<rfloor> - 1 \<and> cfrac_tl c = 1"
      have [simp]: "cfrac_nth c 0 = -1"
        using * equal by (auto simp: x_def)
      from * have "\<not>cfrac_is_int c"
        by (auto simp: cfrac_is_int_def cfrac_lim_def floor_minus)
      have "cfrac_nth c 1 = cfrac_nth (cfrac_tl c) 0"
        by auto
      also have "cfrac_tl c = 1"
        using * by auto
      finally have "cfrac_nth c 1 = 1"
        by simp
      hence "(a, b) = (h 1, k 1)"
        by (auto simp: h_def k_def)
      moreover from \<open>\<not>cfrac_is_int c\<close> have "cfrac_length c \<ge> 1"
        by (cases "cfrac_length c") (auto simp: one_enat_def zero_enat_def cfrac_is_int_def)
      ultimately show ?thesis
        by (intro exI[of _ 1]) (auto simp: one_enat_def)
    qed
  qed
next
  case False
  hence a_nz: "a \<noteq> 0" by auto

  have "x \<noteq> 0"
  proof
    assume [simp]: "x = 0"
    hence "\<bar>a\<bar> / b < 1 / (2 * b ^ 2)"
      using assms by simp
    hence "\<bar>a\<bar> < 1 / (2 * b)"
      using assms by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<le> 1 / 2"
      using assms by (intro divide_left_mono) auto
    finally have "a = 0" by auto
    with \<open>a \<noteq> 0\<close> show False by simp
  qed

  show ?thesis
  proof (rule ccontr)
    assume no_convergent: "\<nexists>n. enat n \<le> cfrac_length c \<and> (a, b) = (h n, k n)"
    from assms have "\<exists>!r. b \<in> {k r..<k (Suc r)}"
      by (intro conv_denom_partition) auto
    then obtain r where r: "b \<in> {k r..<k (Suc r)}" by auto
    have "k r > 0"
      using conv_denom_pos[of c r] assms by (auto simp: k_def)

    show False
    proof (cases "enat r \<le> cfrac_length c")
      case False
      then obtain l where l: "cfrac_length c = enat l"
        by (cases "cfrac_length c") auto
      have "k l \<le> k r"
        using False l unfolding k_def by (intro conv_denom_leI) auto
      also have "\<dots> \<le> b"
        using r by simp
      finally have "b \<ge> k l" .

      have "x = conv c l"
        by (auto simp: x_def cfrac_lim_def l)
      hence x_eq: "x = h l / k l"
        by (auto simp: conv_num_denom h_def k_def)
      have "k l > 0"
        by (simp add: k_def)

      have "b * k l * \<bar>h l / k l - a / b\<bar> < k l / (2*b)"
        using assms x_eq \<open>k l > 0\<close> by (auto simp: field_simps power2_eq_square)
      also have "b * k l * \<bar>h l / k l - a / b\<bar> = \<bar>b * k l * (h l / k l - a / b)\<bar>"
        using \<open>b > 0\<close> \<open>k l > 0\<close> by (subst abs_mult) auto
      also have "\<dots> = of_int \<bar>b * h l - a * k l\<bar>"
        using \<open>b > 0\<close> \<open>k l > 0\<close> by (simp add: algebra_simps)
      also have "k l / (2 * b) < 1"
        using \<open>b \<ge> k l\<close> \<open>b > 0\<close> by auto
      finally have "a * k l = b * h l"
        by linarith
      moreover have "coprime (h l) (k l)"
        unfolding h_def k_def by (simp add: coprime_conv_num_denom)
      ultimately have "(a, b) = (h l, k l)"
        using \<open>coprime a b\<close> using a_nz \<open>b > 0\<close> \<open>k l > 0\<close>
        by (subst (asm) coprime_crossproduct') (auto simp: coprime_commute)
      with no_convergent and l show False
        by auto

    next

      case True
      have "k r * \<bar>x - h r / k r\<bar> = \<bar>k r * x - h r\<bar>"
        using \<open>k r > 0\<close> by (simp add: field_simps)
      also have "\<bar>k r * x - h r\<bar> \<le> \<bar>b * x - a\<bar>"
        using assms r True unfolding x_def by (intro conv_best_approximation_ex_weak) auto
      also have "\<dots> = b * \<bar>x - a / b\<bar>"
        using \<open>b > 0\<close> by (simp add: field_simps)
      also have "\<dots> < b * (1 / (2 * b\<^sup>2))"
        using \<open>b > 0\<close> by (intro mult_strict_left_mono assms) auto
      finally have less: "\<bar>x - conv c r\<bar> < 1 / (2 * b * k r)"
        using \<open>k r > 0\<close> and \<open>b > 0\<close> and assms
        by (simp add: field_simps power2_eq_square conv_num_denom h_def k_def)
    
      have "\<bar>x - a / b\<bar> < 1 / (2 * b\<^sup>2)" by fact
      also have "\<dots> = 1 / (2 * b) * (1 / b)"
        by (simp add: power2_eq_square)
      also have "\<dots> \<le> 1 / (2 * b) * (\<bar>a\<bar> / b)"
        using a_nz assms by (intro mult_left_mono divide_right_mono) auto
      also have "\<dots> < 1 / 1 * (\<bar>a\<bar> / b)"
        using a_nz assms
        by (intro mult_strict_right_mono divide_left_mono divide_strict_left_mono) auto
      also have "\<dots> = \<bar>a / b\<bar>" using assms by simp
      finally have "sgn x = sgn (a / b)"
        by (auto simp: sgn_if split: if_splits)
      hence "sgn x = sgn a" using assms by (auto simp: sgn_of_int)
      hence "a \<ge> 0 \<and> x \<ge> 0 \<or> a \<le> 0 \<and> x \<le> 0"
        by (auto simp: sgn_if split: if_splits)
      moreover have "h r \<ge> 0 \<and> x \<ge> 0 \<or> h r \<le> 0 \<and> x \<le> 0"
        using conv_best_approximation_aux[of r] by (auto simp: h_def x_def)
      ultimately have signs: "h r \<ge> 0 \<and> a \<ge> 0 \<or> h r \<le> 0 \<and> a \<le> 0"
        using \<open>x \<noteq> 0\<close> by auto
  
      with no_convergent assms assms True have "\<bar>h r\<bar> \<noteq> \<bar>a\<bar> \<or> b \<noteq> k r"
        by (auto simp: h_def k_def)
      
      hence "\<bar>h r\<bar> * \<bar>b\<bar> \<noteq> \<bar>a\<bar> * \<bar>k r\<bar>" unfolding h_def k_def
        using assms coprime_conv_num_denom[of c r]
        by (subst coprime_crossproduct_int) auto
      hence "\<bar>h r\<bar> * b \<noteq> \<bar>a\<bar> * k r" using assms by (simp add: k_def)
      hence "k r * a - h r * b \<noteq> 0"
        using signs by (auto simp: algebra_simps)
      hence "\<bar>k r * a - h r * b\<bar> \<ge> 1" by presburger
      hence "real_of_int 1 / (k r * b) \<le> \<bar>k r * a - h r * b\<bar> / (k r * b)"
        using assms
        by (intro divide_right_mono, subst of_int_le_iff) (auto simp: k_def)
      also have "\<dots> = \<bar>(real_of_int (k r) * a - h r * b) / (k r * b)\<bar>"
        using assms by (simp add: k_def)
      also have "(real_of_int (k r) * a - h r * b) / (k r * b) = a / b - conv c r"
        using assms \<open>k r > 0\<close> by (simp add: h_def k_def conv_num_denom field_simps)
      also have "\<bar>a / b - conv c r\<bar> = \<bar>(x - conv c r) - (x - a / b)\<bar>"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> \<bar>x - conv c r\<bar> + \<bar>x - a / b\<bar>"
        by (rule abs_triangle_ineq4)
      also have "\<dots> < 1 / (2 * b * k r) + 1 / (2 * b\<^sup>2)"
        by (intro add_strict_mono assms less)
      finally have "k r > b"
        using \<open>b > 0\<close> and \<open>k r > 0\<close> by (simp add: power2_eq_square field_simps)
      with r show False by auto
    qed
  qed
qed

end


subsection \<open>Efficient code for convergents\<close>


function conv_gen :: "(nat \<Rightarrow> int) \<Rightarrow> int \<times> int \<times> nat \<Rightarrow> nat \<Rightarrow> int" where
  "conv_gen c (a, b, n) N =
     (if n > N then b else conv_gen c (b, b * c n + a, Suc n) N)"
  by auto
termination by (relation "measure (\<lambda>(_, (_, _, n), N). Suc N - n)") auto

lemmas [simp del] = conv_gen.simps

lemma conv_gen_aux_simps [simp]:
  "n > N \<Longrightarrow> conv_gen c (a, b, n) N = b"
  "n \<le> N \<Longrightarrow> conv_gen c (a, b, n) N = conv_gen c (b, b * c n + a, Suc n) N"
  by (subst conv_gen.simps, simp)+

lemma conv_num_eq_conv_gen_aux:
  "Suc n \<le> N \<Longrightarrow> conv_num c n = b * cfrac_nth c n + a \<Longrightarrow> 
     conv_num c (Suc n) = conv_num c n * cfrac_nth c (Suc n) + b \<Longrightarrow>
     conv_num c N = conv_gen (cfrac_nth c) (a, b, n) N"
proof (induction "cfrac_nth c" "(a, b, n)" N arbitrary: c a b n rule: conv_gen.induct)
  case (1 a b n N c)
  show ?case
  proof (cases "Suc (Suc n) \<le> N")
    case True
    thus ?thesis
      by (subst 1) (insert "1.prems", auto)
  next
    case False
    thus ?thesis using 1
      by (auto simp: not_le less_Suc_eq)
  qed
qed

lemma conv_denom_eq_conv_gen_aux:
  "Suc n \<le> N \<Longrightarrow> conv_denom c n = b * cfrac_nth c n + a \<Longrightarrow> 
     conv_denom c (Suc n) = conv_denom c n * cfrac_nth c (Suc n) + b \<Longrightarrow>
     conv_denom c N = conv_gen (cfrac_nth c) (a, b, n) N"
proof (induction "cfrac_nth c" "(a, b, n)" N arbitrary: c a b n rule: conv_gen.induct)
  case (1 a b n N c)
  show ?case
  proof (cases "Suc (Suc n) \<le> N")
    case True
    thus ?thesis
      by (subst 1) (insert "1.prems", auto)
  next
    case False
    thus ?thesis using 1
      by (auto simp: not_le less_Suc_eq)
  qed
qed

lemma conv_num_code [code]: "conv_num c n = conv_gen (cfrac_nth c) (0, 1, 0) n"
  using conv_num_eq_conv_gen_aux[of 0 n c 1 0] by (cases n) simp_all

lemma conv_denom_code [code]: "conv_denom c n = conv_gen (cfrac_nth c) (1, 0, 0) n"
  using conv_denom_eq_conv_gen_aux[of 0 n c 0 1] by (cases n) simp_all

definition conv_num_fun where "conv_num_fun c = conv_gen c (0, 1, 0)"
definition conv_denom_fun where "conv_denom_fun c = conv_gen c (1, 0, 0)"

lemma
  assumes "is_cfrac c"
  shows   conv_num_fun_eq: "conv_num_fun c n = conv_num (cfrac c) n"
    and   conv_denom_fun_eq: "conv_denom_fun c n = conv_denom (cfrac c) n"
proof -
  from assms have "cfrac_nth (cfrac c) = c"
    by (intro ext) simp_all
  thus "conv_num_fun c n = conv_num (cfrac c) n" and "conv_denom_fun c n = conv_denom (cfrac c) n"
    by (simp_all add: conv_num_fun_def conv_num_code conv_denom_fun_def conv_denom_code)
qed


subsection \<open>Computing the continued fraction expansion of a rational number\<close>


function cfrac_list_of_rat :: "int \<times> int \<Rightarrow> int list" where
  "cfrac_list_of_rat (a, b) =
     (if b = 0 then [0]
      else a div b # (if a mod b = 0 then [] else cfrac_list_of_rat (b, a mod b)))"
  by auto
termination
  by (relation "measure (\<lambda>(a,b). nat (abs b))") (auto simp: abs_mod_less)

lemmas [simp del] = cfrac_list_of_rat.simps

lemma cfrac_list_of_rat_correct:
  "(let xs = cfrac_list_of_rat (a, b); c = cfrac_of_real (a / b)
    in  length xs = cfrac_length c + 1 \<and> (\<forall>i<length xs. xs ! i = cfrac_nth c i))"
proof (induction "(a, b)" arbitrary: a b rule: cfrac_list_of_rat.induct)
  case (1 a b)
  show ?case
  proof (cases "b = 0")
    case True
    thus ?thesis
      by (subst cfrac_list_of_rat.simps) (auto simp: one_enat_def)
  next
    case False
    define c where "c = cfrac_of_real (a / b)"
    define c' where "c' = cfrac_of_real (b / (a mod b))"
    define xs' where "xs' = (if a mod b = 0 then [] else cfrac_list_of_rat (b, a mod b))"
    define xs where "xs = a div b # xs'"

    have [simp]: "cfrac_nth c 0 = a div b"
      by (auto simp: c_def floor_divide_of_int_eq)

    obtain l where l: "cfrac_length c = enat l"
      by (cases "cfrac_length c") (auto simp: c_def)

    have "length xs = l + 1 \<and> (\<forall>i<length xs. xs ! i = cfrac_nth c i)"
    proof (cases "b dvd a")
      case True
      thus ?thesis using l
        by (auto simp: Let_def xs_def xs'_def c_def of_int_divide_in_Ints one_enat_def enat_0_iff)
    next
      case False
      have "l \<noteq> 0"
        using l False cfrac_of_real_length_eq_0_iff[of "a / b"] \<open>b \<noteq> 0\<close>
        by (auto simp: c_def zero_enat_def real_of_int_divide_in_Ints_iff intro!: Nat.gr0I)
      have c': "c' = cfrac_tl c"
        using False \<open>b \<noteq> 0\<close> unfolding c'_def c_def
        by (subst cfrac_tl_of_real) (auto simp: real_of_int_divide_in_Ints_iff frac_fraction)
      from 1 have "enat (length xs') = cfrac_length c' + 1"
              and xs': "\<forall>i<length xs'. xs' ! i = cfrac_nth c' i"
        using \<open>b \<noteq> 0\<close> \<open>\<not>b dvd a\<close> by (auto simp: Let_def xs'_def c'_def)

      have "enat (length xs') = cfrac_length c' + 1"
        by fact
      also have "\<dots> = enat l - 1 + 1"
        using c' l by simp
      also have "\<dots> = enat (l - 1 + 1)"
        by (metis enat_diff_one one_enat_def plus_enat_simps(1))
      also have "l - 1 + 1 = l"
        using \<open>l \<noteq> 0\<close> by simp
      finally have [simp]: "length xs' = l"
        by simp

      from xs' show ?thesis
        by (auto simp: xs_def nth_Cons c' split: nat.splits)
    qed
    thus ?thesis using l False
      by (subst cfrac_list_of_rat.simps) (simp_all add: xs_def xs'_def c_def one_enat_def)
  qed
qed

lemma conv_num_cong:
  assumes "(\<And>k. k \<le> n \<Longrightarrow> cfrac_nth c k = cfrac_nth c' k)" "n = n'"
  shows   "conv_num c n = conv_num c' n"
proof -
  have "conv_num c n = conv_num c' n"
    using assms(1)
    by (induction n arbitrary: rule: conv_num.induct) simp_all
  thus ?thesis using assms(2)
    by simp
qed

lemma conv_denom_cong:
  assumes "(\<And>k. k \<le> n \<Longrightarrow> cfrac_nth c k = cfrac_nth c' k)" "n = n'"
  shows   "conv_denom c n = conv_denom c' n'"
proof -
  have "conv_denom c n = conv_denom c' n"
    using assms(1)
    by (induction n arbitrary: rule: conv_denom.induct) simp_all
  thus ?thesis using assms(2)
    by simp
qed

lemma cfrac_lim_diff_le:
  assumes "\<forall>k\<le>Suc n. cfrac_nth c1 k = cfrac_nth c2 k"
  assumes "n \<le> cfrac_length c1" "n \<le> cfrac_length c2"
  shows   "\<bar>cfrac_lim c1 - cfrac_lim c2\<bar> \<le> 2 / (conv_denom c1 n * conv_denom c1 (Suc n))"
proof -
  define d where "d = (\<lambda>k. conv_denom c1 k)"
  have "\<bar>cfrac_lim c1 - cfrac_lim c2\<bar> \<le> \<bar>cfrac_lim c1 - conv c1 n\<bar> + \<bar>cfrac_lim c2 - conv c1 n\<bar>"
    by linarith
  also have "\<bar>cfrac_lim c1 - conv c1 n\<bar> \<le> 1 / (d n * d (Suc n))"
    unfolding d_def using assms
    by (intro cfrac_lim_minus_conv_upper_bound) auto
  also have "conv c1 n = conv c2 n"
    using assms by (intro conv_cong) auto
  also have "\<bar>cfrac_lim c2 - conv c2 n\<bar> \<le> 1 / (conv_denom c2 n * conv_denom c2 (Suc n))"
    using assms unfolding d_def by (intro cfrac_lim_minus_conv_upper_bound) auto
  also have "conv_denom c2 n = d n"
    unfolding d_def using assms by (intro conv_denom_cong) auto
  also have "conv_denom c2 (Suc n) = d (Suc n)"
    unfolding d_def using assms by (intro conv_denom_cong) auto
  also have "1 / (d n * d (Suc n)) + 1 / (d n * d (Suc n)) = 2 / (d n * d (Suc n))"
    by simp
  finally show ?thesis
    by (simp add: d_def)
qed

lemma of_int_leI: "n \<le> m \<Longrightarrow> (of_int n :: 'a :: linordered_idom) \<le> of_int m"
  by simp

lemma cfrac_lim_diff_le':
  assumes "\<forall>k\<le>Suc n. cfrac_nth c1 k = cfrac_nth c2 k"
  assumes "n \<le> cfrac_length c1" "n \<le> cfrac_length c2"
  shows   "\<bar>cfrac_lim c1 - cfrac_lim c2\<bar> \<le> 2 / (fib (n+1) * fib (n+2))"
proof -
  have "\<bar>cfrac_lim c1 - cfrac_lim c2\<bar> \<le> 2 / (conv_denom c1 n * conv_denom c1 (Suc n))"
    by (rule cfrac_lim_diff_le) (use assms in auto)
  also have "\<dots> \<le> 2 / (int (fib (Suc n)) * int (fib (Suc (Suc n))))"
    unfolding of_nat_mult of_int_mult
    by (intro divide_left_mono mult_mono mult_pos_pos of_int_leI conv_denom_lower_bound)
       (auto intro!: fib_neq_0_nat simp del: fib.simps)
  also have "\<dots> = 2 / (fib (n+1) * fib (n+2))"
    by simp
  finally show ?thesis .
qed

end