(* Author: Alexander Maletzky *)

section \<open>Integer Binomial Coefficients\<close>

theory Binomial_Int
  imports Complex_Main
begin

text \<open>Restore original sort constraints:\<close>
setup \<open>Sign.add_const_constraint (@{const_name gbinomial}, SOME @{typ "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"})\<close>

subsection \<open>Inequalities\<close>

lemma binomial_mono:
  assumes "m \<le> n"
  shows "m choose k \<le> n choose k"
  by (simp add: assms binomial_right_mono)

lemma binomial_plus_le:
  assumes "0 < k"
  shows "(m choose k) + (n choose k) \<le> (m + n) choose k"
proof -
  define k0 where "k0 = k - 1"
  with assms have k: "k = Suc k0" by simp
  show ?thesis unfolding k
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    then show ?case
      by (simp add: add.left_commute add_le_mono binomial_right_mono)
  qed
qed

lemma binomial_ineq_1: "2 * ((n + i) choose k) \<le> (n choose k) + ((n + 2 * i) choose k)"
proof (cases k)
  case 0
  thus ?thesis by simp
next
  case k: (Suc k0)
  show ?thesis unfolding k
  proof (induct i)
    case 0
    thus ?case by simp
  next
    case (Suc i)
    have "2 * (n + Suc i choose Suc k0) = 2 * (n + i choose k0) + 2 * (n + i choose Suc k0)"
      by simp
    also have "\<dots> \<le> ((n + 2 * i choose k0) + (Suc (n + 2 * i) choose k0)) + ((n choose Suc k0) + (n + 2 * i choose Suc k0))"
    proof (rule add_mono)
      have "n + i choose k0 \<le> n + 2 * i choose k0" 
        by (rule binomial_mono) simp
      moreover have "n + 2 * i choose k0 \<le> Suc (n + 2 * i) choose k0" 
        by (rule binomial_mono) simp
      ultimately show "2 * (n + i choose k0) \<le> (n + 2 * i choose k0) + (Suc (n + 2 * i) choose k0)"
        by simp
    qed (fact Suc)
    also have "\<dots> = (n choose Suc k0) + (n + 2 * Suc i choose Suc k0)" by simp
    finally show ?case .
  qed
qed

lemma gbinomial_int_mono:
  assumes "0 \<le> x" and "x \<le> (y::int)"
  shows "x gchoose k \<le> y gchoose k"
proof -
  from assms have "nat x \<le> nat y" by simp
  hence "nat x choose k \<le> nat y choose k" by (rule binomial_mono)
  hence "int (nat x choose k) \<le> int (nat y choose k)" by (simp only: zle_int)
  hence "int (nat x) gchoose k \<le> int (nat y) gchoose k" by (simp only: int_binomial)
  with assms show ?thesis by simp
qed

lemma gbinomial_int_plus_le:
  assumes "0 < k" and "0 \<le> x" and "0 \<le> (y::int)"
  shows "(x gchoose k) + (y gchoose k) \<le> (x + y) gchoose k"
proof -
  from assms(1) have "(nat x choose k) + (nat y choose k) \<le> nat x + nat y choose k"
    by (rule binomial_plus_le)
  hence "int ((nat x choose k) + (nat y choose k)) \<le> int (nat x + nat y choose k)"
    by (simp only: zle_int)
  hence "(int (nat x) gchoose k) + (int (nat y) gchoose k) \<le> int (nat x) + int (nat y) gchoose k"
    by (simp only: int_plus int_binomial)
  with assms(2, 3) show ?thesis by simp
qed

lemma binomial_int_ineq_1:
  assumes "0 \<le> x" and "0 \<le> (y::int)"
  shows "2 * (x + y gchoose k) \<le> (x gchoose k) + ((x + 2 * y) gchoose k)"
proof -
  from binomial_ineq_1[of "nat x" "nat y" k]
  have "int (2 * (nat x + nat y choose k)) \<le> int ((nat x choose k) + (nat x + 2 * nat y choose k))"
    by (simp only: zle_int)
  hence "2 * (int (nat x) + int (nat y) gchoose k) \<le> (int (nat x) gchoose k) + (int (nat x) + 2 * int (nat y) gchoose k)"
    by (simp only: int_binomial int_plus int_ops(7)) simp
  with assms show ?thesis by simp
qed

corollary binomial_int_ineq_2:
  assumes "0 \<le> y" and "y \<le> (x::int)"
  shows "2 * (x gchoose k) \<le> (x - y gchoose k) + (x + y gchoose k)"
proof -
  from assms(2) have "0 \<le> x - y" by simp
  hence "2 * ((x - y) + y gchoose k) \<le> (x - y gchoose k) + ((x - y + 2 * y) gchoose k)"
    using assms(1) by (rule binomial_int_ineq_1)
  thus ?thesis by smt
qed

corollary binomial_int_ineq_3:
  assumes "0 \<le> y" and "y \<le> 2 * (x::int)"
  shows "2 * (x gchoose k) \<le> (y gchoose k) + (2 * x - y gchoose k)"
proof (cases "y \<le> x")
  case True
  hence "0 \<le> x - y" by simp
  moreover from assms(1) have "x - y \<le> x" by simp
  ultimately have "2 * (x gchoose k) \<le> (x - (x - y) gchoose k) + (x + (x - y) gchoose k)"
    by (rule binomial_int_ineq_2)
  thus ?thesis by simp
next
  case False
  hence "0 \<le> y - x" by simp
  moreover from assms(2) have "y - x \<le> x" by simp
  ultimately have "2 * (x gchoose k) \<le> (x - (y - x) gchoose k) + (x + (y - x) gchoose k)"
    by (rule binomial_int_ineq_2)
  thus ?thesis by simp
qed

subsection \<open>Backward Difference Operator\<close>

definition bw_diff :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a::{ab_group_add,one}"
  where "bw_diff f x = f x - f (x - 1)"

lemma bw_diff_const [simp]: "bw_diff (\<lambda>_. c) = (\<lambda>_. 0)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_id [simp]: "bw_diff (\<lambda>x. x) = (\<lambda>_. 1)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_plus [simp]: "bw_diff (\<lambda>x. f x + g x) = (\<lambda>x. bw_diff f x + bw_diff g x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_uminus [simp]: "bw_diff (\<lambda>x. - f x) = (\<lambda>x. - bw_diff f x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_minus [simp]: "bw_diff (\<lambda>x. f x - g x) = (\<lambda>x. bw_diff f x - bw_diff g x)"
  by (rule ext) (simp add: bw_diff_def)

lemma bw_diff_const_pow: "(bw_diff ^^ k) (\<lambda>_. c) = (if k = 0 then \<lambda>_. c else (\<lambda>_. 0))"
  by (induct k, simp_all)

lemma bw_diff_id_pow:
  "(bw_diff ^^ k) (\<lambda>x. x) = (if k = 0 then (\<lambda>x. x) else if k = 1 then (\<lambda>_. 1) else (\<lambda>_. 0))"
  by (induct k, simp_all)

lemma bw_diff_plus_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. f x + g x) = (\<lambda>x. (bw_diff ^^ k) f x + (bw_diff ^^ k) g x)"
  by (induct k, simp_all)

lemma bw_diff_uminus_pow [simp]: "(bw_diff ^^ k) (\<lambda>x. - f x) = (\<lambda>x. - (bw_diff ^^ k) f x)"
  by (induct k, simp_all)

lemma bw_diff_minus_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. f x - g x) = (\<lambda>x. (bw_diff ^^ k) f x - (bw_diff ^^ k) g x)"
  by (induct k, simp_all)

lemma bw_diff_sum_pow [simp]:
  "(bw_diff ^^ k) (\<lambda>x. (\<Sum>i\<in>I. f i x)) = (\<lambda>x. (\<Sum>i\<in>I. (bw_diff ^^ k) (f i) x))"
  by (induct I rule: infinite_finite_induct, simp_all add: bw_diff_const_pow)

lemma bw_diff_gbinomial:
  assumes "0 < k"
  shows "bw_diff (\<lambda>x::int. (x + n) gchoose k) = (\<lambda>x. (x + n - 1) gchoose (k - 1))"
proof (rule ext)
  fix x::int
  from assms have eq: "Suc (k - Suc 0) = k" by simp
  have "x + n gchoose k = (x + n - 1) + 1 gchoose (Suc (k - 1))" by (simp add: eq)
  also have "\<dots> = (x + n - 1 gchoose k - 1) + ((x + n - 1) gchoose (Suc (k - 1)))"
    by (fact gbinomial_int_Suc_Suc)
  finally show "bw_diff (\<lambda>x. x + n gchoose k) x = x + n - 1 gchoose (k - 1)"
    by (simp add: eq bw_diff_def algebra_simps)
qed

lemma bw_diff_gbinomial_pow:
  "(bw_diff ^^ l) (\<lambda>x::int. (x + n) gchoose k) =
      (if l \<le> k then (\<lambda>x. (x + n - int l) gchoose (k - l)) else (\<lambda>_. 0))"
proof -
  have *: "l0 \<le> k \<Longrightarrow> (bw_diff ^^ l0) (\<lambda>x::int. (x + n) gchoose k) = (\<lambda>x. (x + n - int l0) gchoose (k - l0))"
    for l0
  proof (induct l0)
    case 0
    show ?case by simp
  next
    case (Suc l0)
    from Suc.prems have "0 < k - l0" and "l0 \<le> k" by simp_all
    from this(2) have eq: "(bw_diff ^^ l0) (\<lambda>x. x + n gchoose k) = (\<lambda>x. x + n - int l0 gchoose (k - l0))"
      by (rule Suc.hyps)
    have "(bw_diff ^^ Suc l0) (\<lambda>x. x + n gchoose k) = bw_diff (\<lambda>x. x + (n - int l0) gchoose (k - l0))"
      by (simp add: eq algebra_simps)
    also from \<open>0 < k - l0\<close> have "\<dots> = (\<lambda>x. (x + (n - int l0) - 1) gchoose (k - l0 - 1))"
      by (rule bw_diff_gbinomial)
    also have "\<dots> = (\<lambda>x. x + n - int (Suc l0) gchoose (k - Suc l0))" by (simp add: algebra_simps)
    finally show ?case .
  qed
  show ?thesis
  proof (simp add: * split: if_split, intro impI)
    assume "\<not> l \<le> k"
    hence "(l - k) + k = l" and "l - k \<noteq> 0" by simp_all
    hence "(bw_diff ^^ l) (\<lambda>x. x + n gchoose k) = (bw_diff ^^ ((l - k) + k)) (\<lambda>x. x + n gchoose k)"
      by (simp only:)
    also have "\<dots> = (bw_diff ^^ (l - k)) (\<lambda>_. 1)" by (simp add: * funpow_add)
    also from \<open>l - k \<noteq> 0\<close> have "\<dots> = (\<lambda>_. 0)" by (simp add: bw_diff_const_pow)
    finally show "(bw_diff ^^ l) (\<lambda>x. x + n gchoose k) = (\<lambda>_. 0)" .
  qed
qed

end (* theory *)
