section \<open>Derivative Identities and Smoothness\<close>

theory Derivative_Identities_Smoothness
  imports Sigmoid_Definition
begin

  

text \<open>
  Second derivative:
  The second derivative of the sigmoid function \(\sigma\) can be written as
  \[
    \sigma''(x) = \sigma(x)\,(1 - \sigma(x))\,(1 - 2\,\sigma(x)).
  \]
  This identity is useful when analysing the curvature of \(\sigma\),
  particularly in optimisation problems.
\<close>

lemma sigmoid_second_derivative:
  shows "Nth_derivative 2 sigmoid x = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
proof - 
  have "Nth_derivative 2 sigmoid x =  deriv ((\<lambda>w. deriv sigmoid w)) x"
    by (simp add: second_derivative_alt_def)
  also have "... = deriv ((\<lambda>w. (\<lambda>a. sigmoid a) w * (((\<lambda>u.1) - (\<lambda>v. sigmoid v)) w ))) x"
    by (simp add: sigmoid_derivative)
  also have "... = sigmoid x * (deriv ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (rule deriv_mult,
        simp add: sigmoid_differentiable',
        simp add: Derivative.field_differentiable_diff sigmoid_differentiable')
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (meson minus_apply)
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * (\<lambda>y. 1 - sigmoid y) x"
    by simp
  also have "... = sigmoid x * sigmoid x * (sigmoid x -1) + sigmoid x * (1 - sigmoid x) * (1 - sigmoid x)"
    by (simp add: deriv_one_minus_sigmoid sigmoid_derivative)
  also have "... = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
    by (simp add: right_diff_distrib)
  finally show ?thesis.
qed

(*Reference: https://eecs.ceas.uc.edu/~minaiaa/papers/minai_sigmoids_NN93.pdf 
             https://analyticphysics.com/Mathematical%20Methods/Multiple%20Derivatives%20of%20the%20Sigmoid%20Function.htm *)

text \<open>
  Here we present the proof of the general \(n\)\-th derivative of the sigmoid
  function as given in the paper “On the Derivatives of the Sigmoid” by
  Ali A.~Minai and Ronald D.~Williams~\cite{MINAI1993845}.  Their original
  derivation is natural and intuitive, guiding the reader step by step to
  the closed-form expression if one did not know it in advance.  By contrast,
  our Isabelle formalisation assumes the final formula up front and then
  proves it directly by induction.  Crucially, we make essential use of
  Stirling numbers of the second kind—as formalised in the session
  “Basic combinatorics in Isabelle/HOL (and the Archive of Formal Proofs)” by Amine Chaieb,
  Florian Haftmann,  Lukas Bulwahn, and Manuel Eberl.
\<close>

theorem nth_derivative_sigmoid:
  "\<And>x. Nth_derivative n sigmoid x = 
    (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
proof (induct n)
  case 0
  show ?case
    by simp
next
  fix n x
  assume induction_hypothesis: 
    "\<And>x. Nth_derivative n sigmoid x = 
         (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
  show "Nth_derivative (Suc n) sigmoid x = 
          (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
  proof -
  
    
    (*Auxillary facts: *)

    have sigmoid_pwr_rule: "\<And>k. deriv (\<lambda>v. (sigmoid v)^k) x = k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x"
        by (subst deriv_pow, simp add: sigmoid_differentiable', simp)
    have index_shift: "(\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1)))) = 
                          (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>j. j -1" "\<lambda>j. j + 1"], simp_all, auto)

    have simplified_terms: "(\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                           ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) = 
                            (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k))"
    proof - 
      have equal_terms: "\<forall> (k::nat) \<ge> 1.
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
       ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) = 
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k * (sigmoid x)^k)"

      proof(clarify)
        fix k::nat
        assume "1 \<le> k"

        have "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
              real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
              real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                       (fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1))))) * sigmoid x ^ k"
          by (metis (mono_tags, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) distrib_left mult.commute of_int_add)
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  ((int (k - 1) * fact (k - 2)) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
              by (simp add: ring_class.ring_distribs(1))
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  (fact (k - 1) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
          by (smt (verit, ccfv_threshold) Stirling.simps(3) add.commute diff_diff_left fact_num_eq_if mult_eq_0_iff of_nat_eq_0_iff one_add_one plus_1_eq_Suc)
        also have "... = real_of_int (((- 1) ^ (k + 1) * fact (k - 1)*
                              ( Stirling (n + 1) k *  k +    Stirling (n + 1) (k - 1)  )  )) * sigmoid x ^ k"
          by (simp add: distrib_left)
        also have "... = real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k"
          by (smt (z3) Stirling.simps(4) Suc_eq_plus1 \<open>1 \<le> k\<close> add.commute le_add_diff_inverse mult.commute nat_1_add_1 plus_nat.simps(2))
        finally show "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
         real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
         real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k".
      qed     
      from equal_terms show ?thesis
        by simp
    qed

    (*Main Goal: *)

    have "Nth_derivative (Suc n) sigmoid x = deriv (\<lambda> w. Nth_derivative n sigmoid w) x"
      by simp    
    also have "... = deriv (\<lambda> w.\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x"
      using induction_hypothesis by presburger
    also have "... = (\<Sum>k = 1..n+1. deriv (\<lambda>w. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x)"
      by (rule deriv_sum, metis(mono_tags) DERIV_chain2 DERIV_cmult_Id field_differentiable_def field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * deriv (\<lambda>w. (sigmoid w)^k) x)"
      by(subst deriv_cmult, auto, simp add: field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x))"
      using sigmoid_pwr_rule by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * (sigmoid x * (1 - sigmoid x))))"
      using sigmoid_derivative by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * ((sigmoid x)^(k - 1) * (sigmoid x)^1) * (1 - sigmoid x)))"
      by (simp add: mult.assoc)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k-1+1) * (1 - sigmoid x)))"
      by (metis (no_types, lifting) power_add)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k * (1  -sigmoid x)))"
      by fastforce
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (1 + -sigmoid x))"
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) *1 +
                                    ((    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x)))"
      by (meson vector_space_over_itself.scale_right_distrib)
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                                    (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * ((sigmoid x)^k * (-sigmoid x))))"
      by (simp add: mult.commute mult.left_commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1))))"
      by (simp add: mult.commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      using index_shift by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                      0 +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) of_int_mult of_int_of_nat_eq sum.cong)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                                   ((-1)^(1+1) * fact (1 - 2) * Stirling (n+1) (1 - 1) * (1 - 1) * (sigmoid x)^1 ) +
                     (\<Sum>k = 2..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k - 1) * (k  -1) * (sigmoid x)^k )"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                     (\<Sum>k = 1..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)"
      by (smt (verit) Suc_eq_plus1 Suc_leI add_Suc_shift add_cancel_left_left cancel_comm_monoid_add_class.diff_cancel nat_1_add_1 of_nat_0 sum.atLeast_Suc_atMost zero_less_Suc)
   also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                     (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) +
               ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                    ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) +
                   ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k)) +
                                    ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      using simplified_terms by presburger   
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k *  (sigmoid x)^k)) +
        (\<Sum>k = Suc n + 1..Suc n + 1.((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k)))"
      by(subst atLeastAtMost_singleton,  simp)   
    also have "... = (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
      by (subst sum.cong[where B="{1..n + 1}", where h = "\<lambda>k. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k))"], simp_all)
    finally show ?thesis.
  qed
qed

corollary nth_derivative_sigmoid_differentiable:
  "Nth_derivative n sigmoid differentiable (at x)"
proof -
  have "(\<lambda>x. \<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)
   differentiable (at x)"
  proof - 
    have differentiable_terms: "\<And>k. 1 \<le> k \<and> k \<le> n+1 \<Longrightarrow> 
      (\<lambda>x. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k) differentiable (at x)"
    proof(clarify)
      fix k ::nat
      assume "1 \<le> k"
      assume " k \<le> n+1"
      show "(\<lambda>x. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k) differentiable (at x)"
        by (simp add: field_differentiable_imp_differentiable sigmoid_differentiable')
    qed
    then show ?thesis
      by(subst differentiable_sum,simp+)
  qed
  then show ?thesis
     using nth_derivative_sigmoid by presburger 
qed

corollary next_deriviative_sigmoid: "(Nth_derivative n  sigmoid has_real_derivative Nth_derivative (Suc n)  sigmoid x) (at x)"
  by (simp add: DERIV_deriv_iff_real_differentiable nth_derivative_sigmoid_differentiable)

corollary deriv_sigmoid_has_deriv: "(deriv sigmoid has_real_derivative deriv (deriv sigmoid) x) (at x)"
proof -
  have "\<forall>f. Nth_derivative (Suc 0) f = deriv f"
    using Nth_derivative.simps(1,2) by presburger
  then show ?thesis
    by (metis (no_types) DERIV_deriv_iff_real_differentiable nth_derivative_sigmoid_differentiable)
qed

corollary sigmoid_second_derivative':
  "(deriv sigmoid has_real_derivative (sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x))) (at x)"
  using deriv_sigmoid_has_deriv second_derivative_alt_def sigmoid_second_derivative by force

corollary smooth_sigmoid:
  "smooth_on sigmoid UNIV"
  unfolding smooth_on_def
  by (meson C_k_on_def differentiable_imp_continuous_on differentiable_on_def nth_derivative_sigmoid_differentiable open_UNIV sigmoid_differentiable)


lemma tendsto_exp_neg_at_infinity: "((\<lambda>(x :: real). exp (-x)) \<longlongrightarrow> 0) at_top"
  by real_asymp

end