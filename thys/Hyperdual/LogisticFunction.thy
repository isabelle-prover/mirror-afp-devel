(*  Title:       LogisticFunction.thy
    Author:      Filip Smola, 2019-2021
*)

theory LogisticFunction
  imports HyperdualFunctionExtension
begin

subsection\<open>Logistic Function\<close>

text\<open>Define the standard logistic function and its hyperdual variant:\<close>
definition logistic :: "real \<Rightarrow> real"
  where "logistic x = inverse (1 + exp (-x))"
definition hyp_logistic :: "real hyperdual \<Rightarrow> real hyperdual"
  where "hyp_logistic x = inverse (1 + (*h* exp) (-x))"

text\<open>Hyperdual extension of the logistic function is its hyperdual variant:\<close>
lemma hypext_logistic:
  "(*h* logistic) x = hyp_logistic x"
proof -
  have "(*h* (\<lambda>x. exp (- x) + 1)) x = (*h* exp) (- x) + of_comp 1"
    by (simp add: hypext_compose hypext_uminus hypext_fun_cadd twice_field_differentiable_at_compose)
  then have "(*h* (\<lambda>x. 1 + exp (- x))) x = 1 + (*h* exp) (- x)"
    by (simp add: one_hyperdual_def add.commute)
  moreover have "1 + exp (- Base x) \<noteq> 0"
    by (metis exp_ge_zero add_eq_0_iff neg_0_le_iff_le not_one_le_zero)
  moreover have "(\<lambda>x. 1 + exp (- x)) twice_field_differentiable_at Base x"
  proof -
    have "(\<lambda>x. exp (- x)) twice_field_differentiable_at Base x"
      by (simp add: twice_field_differentiable_at_compose)
    then have "(\<lambda>x. exp (- x) + 1) twice_field_differentiable_at Base x"
      using twice_field_differentiable_at_compose[of "\<lambda>x. exp (- x)" "Base x" "\<lambda>x. x + 1"]
      by simp
    then show ?thesis
      by (simp add: add.commute)
  qed
  ultimately have "(*h* (\<lambda>x. inverse (1 + exp (- x)))) x = inverse (1 + (*h* exp) (- x))"
    by (simp add: hypext_fun_inverse)
  then show ?thesis
    unfolding logistic_def hyp_logistic_def .
qed

text\<open>From properties of autodiff we know it gives us the derivative:\<close>
lemma "Eps1 (hyp_logistic (\<beta> x)) = deriv logistic x"
  by (metis Eps1_hypext hypext_logistic)
text\<open>which is equal to the known derivative of the standard logistic function:\<close>
lemma "First (autodiff logistic x) = exp (- x) / (1 + exp (- x)) ^ 2"
  (* Move to hyperdual variant: *)
  apply (simp only: autodiff.simps hyperdual_to_derivs.simps derivs.sel hypext_logistic)
  (* Unfold extensions of functions that have a hyperdual variant (all except exp): *)
  apply (simp only: hyp_logistic_def inverse_hyperdual.code hyperdual.sel)
  (* Finish by expanding the extension of exp and hyperdual computations: *)
  apply (simp add: hyperdualx_def hypext_exp_Hyperdual hyperdual_bases)
  done

text\<open>Similarly we can get the second derivative:\<close>
lemma "Second (autodiff logistic x) = deriv (deriv logistic) x"
  by (rule autodiff_extract_second)
text\<open>and derive its value:\<close>
lemma "Second (autodiff logistic x) = ((exp (- x) - 1) * exp (- x)) / ((1 + exp (- x)) ^ 3)"
  (* Move to hyperdual variant: *)
  apply (simp only: autodiff.simps hyperdual_to_derivs.simps derivs.sel hypext_logistic)
  (* Unfold extensions of functions that have a hyperdual variant (all except exp): *)
  apply (simp only: hyp_logistic_def inverse_hyperdual.code hyperdual.sel)
  (* Finish by expanding the extension of exp and hyperdual computations: *)
  apply (simp add: hyperdualx_def hypext_exp_Hyperdual hyperdual_bases)
  (* Simplify the resulting expression: *)
proof -
  have
    "2 * (exp (- x) * exp (- x)) / (1 + exp (- x)) ^ 3 - exp (- x) / (1 + exp (- x)) ^ 2 =
     (2 * exp (- x) / (1 + exp (- x)) ^ 3 - 1 / (1 + exp (- x)) ^ 2) * exp (- x)"
    by (simp add: field_simps)
  also have "... = (2 * exp (- x) / (1 + exp (- x)) ^ 3 - (1 + exp (- x)) / (1 + exp (- x)) ^ 3) * exp (- x)"
  proof -
    have "inverse ((1 + exp (- x)) ^ 2) = inverse (1 + exp (- x)) ^ 2"
      by (simp add: power_inverse)
    also have "... = (1 + exp (- x)) * inverse (1 + exp (- x)) * inverse (1 + exp (- x)) ^ 2"
      by (simp add: inverse_eq_divide)
    also have "... = (1 + exp (- x)) * inverse (1 + exp (- x)) ^ 3"
      by (simp add: power2_eq_square power3_eq_cube)
    finally have "inverse ((1 + exp (- x)) ^ 2) = (1 + exp (- x)) * inverse ((1 + exp (- x)) ^ 3)"
      by (simp add: power_inverse)
    then show ?thesis
      by (simp add: inverse_eq_divide)
  qed
  also have "... = (2 * exp (- x) - (1 + exp (- x))) / (1 + exp (- x)) ^ 3 * exp (- x)"
    by (metis diff_divide_distrib)
  finally show
    "2 * (exp (- x) * exp (- x)) / (1 + exp (- x)) ^ 3 - exp (- x) / (1 + exp (- x))\<^sup>2 =
     (exp (- x) - 1) * exp (- x) / (1 + exp (- x)) ^ 3"
    by (simp add: field_simps)
qed

end