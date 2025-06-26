theory Sigmoid_Definition
  imports "HOL-Analysis.Analysis" "HOL-Combinatorics.Stirling"  Limits_Higher_Order_Derivatives
begin

section \<open>Definition and Analytical Properties\<close>

definition sigmoid :: "real \<Rightarrow> real" where
  "sigmoid x = exp x / (1 + exp x)"

lemma sigmoid_alt_def: "sigmoid x = inverse (1 + exp(-x))"
proof -
  have "sigmoid x = (exp(x) * exp(-x)) / ((1 + exp(x))* exp(-x))"
    unfolding sigmoid_def by simp
  also have "... = 1 / (1*exp(-x) + exp(x)*exp(-x))"
    by (simp add: distrib_right exp_minus_inverse)
  also have "... = inverse (exp(-x) + 1)"
    by (simp add: divide_inverse_commute exp_minus)
  finally show ?thesis
    by simp
qed

subsection \<open>Range, Monotonicity, and Symmetry\<close>

text \<open>Bounds\<close>
lemma sigmoid_pos: "sigmoid x > 0"
  by (smt (verit) divide_le_0_1_iff exp_gt_zero inverse_eq_divide sigmoid_alt_def)

text \<open>Prove that \(\sigma(x) < 1\) for all \(x\).\<close>
lemma sigmoid_less_1: "sigmoid x < 1"
  by (smt (verit) le_divide_eq_1_pos not_exp_le_zero sigmoid_def)

text \<open>The sigmoid function \(\sigma(x)\) satisfies
  \[
    0 < \sigma(x) < 1
    \quad\text{for all }x \in \mathbb{R}.
  \]
\<close>
corollary sigmoid_range: "0 < sigmoid x \<and> sigmoid x < 1"
  by (simp add: sigmoid_less_1 sigmoid_pos)

text \<open>
  Symmetry around the origin:
  The sigmoid function \(\sigma\) satisfies
  \[
    \sigma(-x) = 1 - \sigma(x)
    \quad\text{for all }x\in\mathbb{R},
  \]
  reflecting that negative inputs shift the output towards \(0\),
  while positive inputs shift it towards \(1\).
\<close>


lemma sigmoid_symmetry: "sigmoid (-x) = 1 - sigmoid x"
  by (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if 
      exp_ge_zero inverse_eq_divide sigmoid_alt_def sigmoid_def)

corollary "sigmoid(x) + sigmoid(-x) = 1"
  by (simp add: sigmoid_symmetry)

text \<open>The sigmoid function is strictly increasing.\<close>
lemma sigmoid_strictly_increasing: "x1 < x2 \<Longrightarrow> sigmoid x1 < sigmoid x2"
  by (unfold sigmoid_alt_def, 
      smt (verit) add_strict_left_mono divide_eq_0_iff exp_gt_zero exp_less_cancel_iff 
      inverse_less_iff_less le_divide_eq_1_pos neg_0_le_iff_le neg_le_iff_le order_less_trans real_add_le_0_iff)

lemma sigmoid_at_zero:
  "sigmoid 0 = 1/2"
  by (simp add: sigmoid_def)

lemma sigmoid_left_dom_range:
  assumes "x < 0"
  shows "sigmoid x < 1/2"
  by (metis assms sigmoid_at_zero sigmoid_strictly_increasing)

lemma sigmoid_right_dom_range:
  assumes "x > 0"
  shows "sigmoid x > 1/2"
  by (metis assms sigmoid_at_zero sigmoid_strictly_increasing)



subsection \<open>Differentiability and Derivative Identities\<close>
text \<open>
  Derivative:
  The derivative of the sigmoid function can be expressed in terms of itself:
  \[
    \sigma'(x) = \sigma(x)\,(1 - \sigma(x)).
  \]
  This identity is central to backpropagation for weight updates in neural
  networks, since it shows the derivative depends only on \(\sigma(x)\),
  simplifying optimisation computations.
\<close>


lemma uminus_derive_minus_one: "(uminus has_derivative (*) (-1 :: real)) (at a within A)"
  by (rule has_derivative_eq_rhs, (rule derivative_intros)+, fastforce)

lemma sigmoid_differentiable: 
  "(\<lambda>x. sigmoid x) differentiable_on UNIV"
proof -
  have "\<forall>x. sigmoid differentiable (at x)"
  proof 
    fix x :: real
    have num_diff: "(\<lambda>x. exp x) differentiable (at x)"
      by (simp add: field_differentiable_imp_differentiable field_differentiable_within_exp)
    have denom_diff: "(\<lambda>x. 1 + exp x) differentiable (at x)"
      by (simp add: num_diff)
    hence "(\<lambda>x. exp x / (1 + exp x)) differentiable (at x)"
      by (metis add_le_same_cancel2 num_diff differentiable_divide exp_ge_zero not_one_le_zero)    
    thus "sigmoid differentiable (at x)"
      unfolding sigmoid_def by simp
  qed
  thus ?thesis
    by (simp add: differentiable_on_def)
qed

lemma sigmoid_differentiable':
 "sigmoid field_differentiable at x"
  by (meson UNIV_I differentiable_on_def field_differentiable_def real_differentiableE sigmoid_differentiable)

lemma sigmoid_derivative:
  shows "deriv sigmoid x = sigmoid x * (1 - sigmoid x)"
  unfolding sigmoid_def
proof -    
  from field_differentiable_within_exp 
  have "deriv (\<lambda>x. exp x /(1 + exp x)) x = (deriv (\<lambda>x. exp x) x * (\<lambda>x. 1 + exp x) x - (\<lambda>x. exp x) x * deriv (\<lambda>x. 1 + exp x) x) / ((\<lambda>x. 1 + exp x) x)\<^sup>2"
    by(rule deriv_divide, 
       simp add: Derivative.field_differentiable_add field_differentiable_within_exp,
       smt (verit, ccfv_threshold) exp_gt_zero)
  also have "... = ((exp x) * (1 + exp x) -(exp x)* (deriv (\<lambda>w. ((\<lambda>v. 1)w + (\<lambda> u. exp u)w)) x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = ((exp x) * (1 + exp x) -(exp x) * (deriv (\<lambda>v. 1) x  + deriv (\<lambda> u. exp u) x)) / (1 + exp x)\<^sup>2"
    by (subst deriv_add, simp, simp add: field_differentiable_within_exp, auto)
  also have "... = ((exp x) * (1 + exp x) -(exp x)  * (exp x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = (exp x + (exp x)\<^sup>2 -(exp x)\<^sup>2) / (1 + exp x)\<^sup>2"
    by (simp add: ring_class.ring_distribs(1))  
  also have "... = (exp x / (1 + exp x))*(1 / (1 + exp x))"
    by (simp add: power2_eq_square)
  also have "... = exp x / (1 + exp x)*(1 - exp x / (1 + exp x))"
    by (metis add.inverse_inverse inverse_eq_divide sigmoid_alt_def sigmoid_def sigmoid_symmetry)
  finally show "deriv (\<lambda>x. exp x / (1 + exp x)) x = exp x / (1 + exp x) * (1 - exp x / (1 + exp x))".  
qed

lemma  sigmoid_derivative': "(sigmoid has_real_derivative (sigmoid x * (1 - sigmoid x))) (at x)"
  by (metis field_differentiable_derivI sigmoid_derivative sigmoid_differentiable')

lemma deriv_one_minus_sigmoid:
  "deriv (\<lambda>y. 1 - sigmoid y) x = sigmoid x * (sigmoid x - 1)"
  apply (subst deriv_diff)
    apply simp
   apply (metis UNIV_I differentiable_on_def real_differentiableE sigmoid_differentiable field_differentiable_def)
  apply (metis deriv_const diff_0 minus_diff_eq mult_minus_right sigmoid_derivative)
  done



subsection \<open>Logit, Softmax, and the Tanh Connection\<close>


text \<open>Logit (Inverse of Sigmoid):
  The inverse of the sigmoid function, often called the logit function,
  is defined by
  \[
    \sigma^{-1}(y) \;=\; \ln\!\bigl(\tfrac{y}{1 - y}\bigr),
    \quad 0 < y < 1.
  \]
  This transformation converts a probability \(y\in(0,1)\) (the output of
  the sigmoid) back into the corresponding log-odds.\<close>

definition logit :: "real \<Rightarrow> real" where
  "logit p = (if 0 < p \<and> p < 1 then ln (p / (1 - p)) else undefined)"


lemma sigmoid_logit_comp:
  "0 < p \<and> p < 1 \<Longrightarrow> sigmoid (logit p) = p"
proof -
  assume "0 < p \<and> p < 1"
  then show "sigmoid (logit p ) = p"
    by (smt (verit, del_insts) divide_pos_pos exp_ln_iff logit_def real_shrink_Galois sigmoid_def)
qed

lemma logit_sigmoid_comp:
  "logit (sigmoid p ) = p"
  by (smt (verit, best) sigmoid_less_1 sigmoid_logit_comp sigmoid_pos sigmoid_strictly_increasing)

definition softmax :: "real^'k \<Rightarrow> real^'k" where 
"softmax z = (\<chi> i. exp (z $ i) / (\<Sum> j\<in>UNIV. exp (z $ j)))"  

lemma tanh_sigmoid_relationship:
  "2 * sigmoid (2 * x) - 1 = tanh x"
proof -
  have "2 * sigmoid (2 * x) - 1 = 2 * (1 / (1 + exp (- (2 * x)))) - 1"
    by (simp add: inverse_eq_divide sigmoid_alt_def)
  also have "... = (2 / (1 + exp (- (2 * x)))) - 1"
    by simp
  also have "... = (2 - (1 + exp (- (2 * x)))) / (1 + exp (- (2 * x)))"
    by (smt (verit, ccfv_SIG) diff_divide_distrib div_self exp_gt_zero)
  also have "... = (exp x * (exp x - exp (-x))) / (exp x * (exp x + exp (-x)))"
    by (smt (z3) exp_not_eq_zero mult_divide_mult_cancel_left_if tanh_altdef tanh_real_altdef)
  also have "... = (exp x - exp (-x)) / (exp x + exp (-x))"
    using exp_gt_zero by simp
  also have "... = tanh x"
    by (simp add: tanh_altdef)
  finally show ?thesis.
qed

end