section \<open>Fast algorithms for Computations of Roots\<close>

theory Finite_Fields_Nth_Root_Code
  imports 
    "HOL-Computational_Algebra.Nth_Powers"
    "HOL-Library.Code_Target_Nat"
begin

text \<open>This section adds code equations for @{term "nth_root_nat"} and @{term "is_nth_power"} 
with fast algorithms using binary search. (The existing implementations in 
\verb|HOL-Computational_Algebra| perform linear searches, which are too slow. (An example for 
comparison is the evaluation of the term @{term "nth_root_nat 2 (2^64)"}).\<close>

text \<open>The following is an implementation of binary search, returning the first index in an interval
of the form $[l,u)$ where a predicate becomes true. It returns the upper bound $u$ if the predicate
if @{term "False"} on the entire domain.\<close>

function find_first :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat"
  where 
    "find_first l u f = (
      if (l \<ge> u) then u else 
      (let m = (l + u) div 2 in
        if f m then find_first l m f else find_first (m+1) u f))" 
  by pat_completeness auto

termination by (relation "Wellfounded.measure (\<lambda>(l, u, _). u - l)") auto

lemma Min_subset_eq:
  assumes "A \<subseteq> B" "finite B" "A \<noteq> {}" "\<forall>x \<in> B. \<exists>y \<in> A. y \<le> x"
  shows "Min A = Min B"
proof (rule order_antisym)
  show "Min A \<le> Min B"
    by (metis assms Min.coboundedI basic_trans_rules(23) bot_unique infinite_super obtains_Min)
next
  show "Min B \<le> Min A"
    by (rule Min_antimono[OF assms(1,3,2)])
qed

lemma find_first_eq:
  assumes "mono f"
  shows "find_first l u f = Min ({x. f x} \<inter> {l..<u} \<union> {u})"
  using assms
proof (induction l u f rule:find_first.induct)
  case (1 l u f)
  define x where "x = (l + u) div 2"
  have x_ran: "x \<in> {l..<u}" if "l < u" using that unfolding x_def by auto
  consider (a) "l \<ge> u" | (b) "f x \<and> l < u" | (c) "\<not> f x \<and> l < u" by linarith
  thus ?case
  proof (cases)
    case a thus ?thesis by simp
  next
    case b
    hence "find_first l u f = find_first l x f" by (simp add:x_def Let_def)
    also have "\<dots> = Min ({x. f x} \<inter> {l..<x} \<union> {x})" using 1(1,3) x_def b by simp
    also have "\<dots> = Min ({x. f x} \<inter> {l..<u} \<union> {u})"
      using b x_ran by (intro Min_subset_eq) auto
    finally show ?thesis by simp
  next
    case c
    have "\<not> f y" if "y \<le> x" for y  using mono_onD[OF 1(3) _ _ that] that c by simp
    hence *:"y \<ge> Suc x" if "f y" for y using that 
      by (meson not_less_eq_eq) 
    have "find_first l u f = find_first (x+1) u f" using c by (simp add:x_def Let_def)
    also have "\<dots> = Min ({x. f x} \<inter> {(x+1)..<u} \<union> {u})" using 1(2,3) x_def c by simp
    also have "\<dots> = Min ({x. f x} \<inter> {l..<u} \<union> {u})" 
      using * c x_ran by (intro arg_cong[where f="Min"]) force
    finally show ?thesis by simp
  qed
qed

lemma nth_root_nat_fast[code]: "nth_root_nat e n = (if e = 0 then 0 else find_first 0 (n+1) (\<lambda>x. x^e > n) - 1)" 
proof (cases "e > 0")
  case True

  have mono: "mono (\<lambda>x. x ^ e > n)"
    using power_mono[OF _ zero_le] order_less_le_trans
    by (intro monoI le_boolI) blast

  have "nth_root_nat e n \<le> nth_root_nat e (n^e)" if "n > 0"
    using True that by (intro nth_root_nat_mono self_le_power) auto

  hence 0:"nth_root_nat e n \<le> n"
    using nth_root_nat_nth_power[OF True] by (cases "n = 0") auto

  have "n < n+1" by simp
  also have "\<dots> \<le> (n+1)^e" by (intro self_le_power True) auto
  finally have 1:"n < (n+1)^e" by simp

  have "x^e > n" if "x \<ge> nth_root_nat e n + 1" for x
    using that nth_root_nat_ge[OF True]
    by (metis add_Suc_right nat_arith.rule0 not_less not_less_eq_eq numeral_nat(7))

  hence "nth_root_nat e n+1 \<le> x \<longleftrightarrow> x^e > n" for x
    using nth_root_nat_less[OF True] by fastforce

  hence "{nth_root_nat e n+1..(n+1)} = {x. x^e > n \<and> x \<le> n+1}"
    unfolding atLeastAtMost_def Int_def by simp
  also have "\<dots> = {x. x^e > n \<and> x < n+1} \<union> {n+1}" using True 1 by auto
  finally have 1: "{nth_root_nat e n+1..(n+1)} = {x. x^e > n \<and> x < n+1} \<union> {n+1}" by simp

  have "nth_root_nat e n = Inf {nth_root_nat e n+1..(n+1)} - 1"
    using 0 by (subst cInf_atLeastAtMost) auto
  also have "\<dots> = Inf ({x. x^e > n \<and> x < n+1} \<union> {n+1}) - 1"
    using 1 by simp
  also have "\<dots> = Min ({x. x^e > n \<and> x < n+1} \<union> {n+1}) - 1"
    by (subst cInf_eq_Min) auto
  also have "\<dots> = (if e = 0 then 0 else find_first 0 (n+1) (\<lambda>x. x^e > n) - 1)" 
    using True unfolding find_first_eq[OF mono] Int_def by simp
  finally show ?thesis by simp
next
  case False
  thus ?thesis by simp
qed

lemma is_nth_power_nat_fast[code]: "is_nth_power_nat e n \<longleftrightarrow> ((nth_root_nat e n)^e = n)"
proof -
  have "((nth_root_nat e n)^e = n) \<longrightarrow> is_nth_power e n"
    unfolding is_nth_power_def by metis

  moreover have "((nth_root_nat e n)^e = n)" if "is_nth_power e n" "e > 0"
    using nth_root_nat_nth_power[OF that(2)] that(1)
    unfolding is_nth_power_def by auto

  moreover have "((nth_root_nat 0 n)^0 = n)" if "is_nth_power (0::nat) n" 
    using that unfolding is_zeroth_power by simp

  ultimately show ?thesis unfolding is_nth_power_nat_def by blast
qed

end