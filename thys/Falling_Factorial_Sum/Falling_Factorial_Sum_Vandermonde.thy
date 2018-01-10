(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Proving Falling Factorial of a Sum with Vandermonde Identity\<close>

theory Falling_Factorial_Sum_Vandermonde
imports
  "Discrete_Summation.Factorials"
begin

subsection \<open>Preliminaries: Addition to Factorials Theory\<close>

lemma ffact_fact_div_fact_nat:
  assumes "k \<le> n"
  shows "ffact k n = fact n div fact (n - k)"
using assms by (simp add: fact_div_fact_ffact)

lemma ffact_eq_fact_mult_binomial:
  "ffact k n = fact k * (n choose k)"
proof cases
  assume "k \<le> n"
  have "ffact k n = fact n div fact (n - k)"
    using \<open>k \<le> n\<close> by (simp add: ffact_fact_div_fact_nat)
  also have "\<dots> = fact k * (n choose k)"
    using \<open>k \<le> n\<close> by (simp add: binomial_fact_lemma[symmetric])
  finally show ?thesis .
next
  assume "\<not> k \<le> n"
  from this ffact_nat_triv show ?thesis by force
qed

subsection \<open>Main Proof\<close>

text \<open>Note the potentially special copyright license condition of the following proof.\<close>

lemma ffact_add_nat:
  shows "ffact k (n + m) = (\<Sum>i\<le>k. (k choose i) * ffact i n * ffact (k - i) m)"
proof -
  have "ffact k (n + m) = fact k * ((n + m) choose k)"
    by (simp only: ffact_eq_fact_mult_binomial)
  also have "\<dots> = fact k * (\<Sum>i\<le>k. (n choose i) * (m choose (k - i)))"
    by (simp only: vandermonde)
  also have "\<dots> = (\<Sum>i\<le>k. fact k * (n choose i) * (m choose (k - i)))"
    by (simp add: sum_distrib_left field_simps)
  also have "\<dots> = (\<Sum>i\<le>k. (fact i * fact (k - i) * (k choose i)) * (n choose i) * (m choose (k - i)))"
    by (simp add: binomial_fact_lemma)
  also have "\<dots> = (\<Sum>i\<le>k. (k choose i) * (fact i * (n choose i)) * (fact (k - i) * (m choose (k - i))))"
    by (auto intro: sum.cong)
  also have "\<dots> = (\<Sum>i\<le>k. (k choose i) * ffact i n * ffact (k - i) m)"
    by (simp only: ffact_eq_fact_mult_binomial)
  finally show ?thesis .
qed

end