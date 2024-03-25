(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Roots Bound for Univariate Polynomials\<close>

theory Univariate_Roots_Bound
  imports 
    "HOL-Computational_Algebra.Polynomial"  
begin

text \<open>
\textbf{NOTE:} if considered to be useful enough, the lemmas in this theory could be moved to 
the theory @{theory "HOL-Computational_Algebra.Polynomial"}.
\<close>

subsection \<open>Basic lemmas\<close>

lemma finite_non_zero_coeffs: \<open>finite {n. poly.coeff p n \<noteq> 0}\<close>
  using MOST_coeff_eq_0 eventually_cofinite 
  by fastforce

text \<open>Univariate degree in terms of @{term Max}\<close>

lemma poly_degree_eq_Max_non_zero_coeffs: 
  "degree p = Max (insert 0 {n. poly.coeff p n \<noteq> 0})"
  by (intro le_antisym degree_le) (auto simp add: finite_non_zero_coeffs le_degree)


subsection \<open>Univariate roots bound\<close>

text \<open>The number of roots of a product of polynomials is bounded by 
the sum of the number of roots of each.\<close>

lemma card_poly_mult_roots:
  fixes p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly" 
    and q :: "'a::{comm_ring_1,ring_no_zero_divisors} poly" 
  assumes "p \<noteq> 0" and "q \<noteq> 0" 
  shows "card {x. poly p x * poly q x = 0} \<le> card {x. poly p x = 0} + card {x. poly q x = 0}"
proof -
  have "card {x . poly p x * poly q x = 0} \<le> card ({x . poly p x = 0} \<union> {x . poly q x = 0})"
    by (auto simp add: poly_roots_finite assms intro!: card_mono)
  also have "\<dots> \<le> card {x . poly p x = 0} + card {x . poly q x = 0}" 
    by(auto simp add: Finite_Set.card_Un_le)
  finally show ?thesis .
qed

text \<open>A univariate polynomial p has at most deg p roots.\<close>

lemma univariate_roots_bound:
  fixes p :: \<open>'a::idom poly\<close>
  assumes \<open>p \<noteq> 0\<close> 
  shows \<open>card {x. poly p x = 0} \<le> degree p\<close>
  using assms
proof (induction "degree p" arbitrary: p rule: nat_less_induct)
  case 1
  then show ?case
  proof(cases "\<exists>r. poly p r = 0")
    case True \<comment> \<open>A root exists\<close>

    \<comment> \<open>Get root r of polynomial and write @{text "p = [:- r, 1:] ^ order r p * q"} for some @{text q}.\<close>
    then obtain r where "poly p r = 0" by(auto)
    let ?xr = "[:- r, 1:] ^ order r p"
    obtain q where "p = ?xr * q" using order_decomp \<open>p \<noteq> 0\<close> by(auto)

    \<comment> \<open>Useful facts about q and @{term "[:- r, 1:] ^ order r p"}\<close>
    have "q \<noteq> 0" using \<open>p = ?xr * q\<close> \<open>p \<noteq> 0\<close> by(auto)
    have "?xr \<noteq> 0" by(simp)
    have "degree ?xr > 0" using \<open>?xr \<noteq> 0\<close> \<open>p \<noteq> 0\<close> \<open>poly p r = 0\<close> 
      by (simp add: degree_power_eq order_root) 
    have "degree q < degree p" 
      using \<open>?xr \<noteq> 0\<close> \<open>q \<noteq> 0\<close> \<open>p = ?xr * q\<close> \<open>degree ?xr > 0\<close> 
            degree_mult_eq[where p = "?xr" and q = "q"] 
      by (simp)
    have x_roots: "card {r. poly ?xr r = 0} = 1" using \<open>p \<noteq> 0\<close> \<open>poly p r = 0\<close> 
      by(simp add: order_root)
    have q_roots: "card {r. poly q r = 0} \<le> degree q" using \<open>q \<noteq> 0\<close> \<open>degree q < degree p\<close> 1 
      by (simp)

    \<comment> \<open>Final bound\<close>
    have "card {r . poly p r = 0} \<le> degree p" 
      using \<open>p = ?xr * q\<close> \<open>q \<noteq> 0\<close> \<open>?xr \<noteq> 0\<close> \<open>degree q < degree p\<close>
            poly_mult[where p = "?xr" and q = "q"] 
            card_poly_mult_roots[where p = "?xr" and q = "q"] 
            x_roots q_roots  
      by (simp) 
    then show ?thesis .    
  next
    case False \<comment> \<open>No root exists\<close>
    then show ?thesis by simp
  qed
qed


end