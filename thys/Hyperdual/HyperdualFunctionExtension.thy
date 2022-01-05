(*  Title:   HyperdualFunctionExtension.thy
    Authors: Jacques D. Fleuriot and Filip Smola, University of Edinburgh, 2021
*)

section \<open>Hyperdual Extension of Functions\<close>

theory HyperdualFunctionExtension
  imports Hyperdual TwiceFieldDifferentiable
begin

text\<open>The following is an important fact in the derivation of the hyperdual extension.\<close>
lemma
    fixes x :: "('a :: comm_ring_1) hyperdual" and n :: nat
  assumes "Base x = 0"
    shows "x ^ (n + 3) = 0"
proof (induct n)
  case 0
  then show ?case
    using assms hyperdual_power[of x 3] by simp
next
  case (Suc n)
  then show ?case
    using assms power_Suc[of x "n + 3"] mult_zero_right add_Suc by simp
qed

text\<open>We define the extension of a function to the hyperdual numbers.\<close>
primcorec hypext :: "(('a :: real_normed_field) \<Rightarrow> 'a) \<Rightarrow> 'a hyperdual \<Rightarrow> 'a hyperdual" (\<open>*h* _\<close> [80] 80)
  where
    "Base ((*h* f) x) = f (Base x)"
  | "Eps1 ((*h* f) x) = Eps1 x * deriv f (Base x)"
  | "Eps2 ((*h* f) x) = Eps2 x * deriv f (Base x)"
  | "Eps12 ((*h* f) x) = Eps12 x * deriv f (Base x) + Eps1 x * Eps2 x * deriv (deriv f) (Base x)"

text\<open>This has the expected behaviour when expressed in terms of the units.\<close>
lemma hypext_Hyperdual_eq:
  "(*h* f) (Hyperdual a b c d) =
     Hyperdual (f a) (b * deriv f a) (c * deriv f a) (d * deriv f a + b * c * deriv (deriv f) a)"
  by (simp add: hypext.code)

lemma hypext_Hyperdual_eq_parts:
  "(*h* f) (Hyperdual a b c d) =
      f a *\<^sub>H ba + (b * deriv f a) *\<^sub>H e1 + (c * deriv f a) *\<^sub>H e2 +
         (d * deriv f a + b * c * deriv (deriv f) a) *\<^sub>H e12 "
  by (metis Hyperdual_eq hypext_Hyperdual_eq)

text\<open>
  The extension can be used to extract the function value, and first and second derivatives at x
  when applied to @{term "x *\<^sub>H re + e1 + e2 + 0 *\<^sub>H e12"}, which we denote by @{term "\<beta> x"}.
\<close>
definition hyperdualx :: "('a :: real_normed_field) \<Rightarrow> 'a hyperdual" ("\<beta>")
  where "\<beta> x = (Hyperdual x 1 1 0)"

lemma hyperdualx_sel [simp]:
  shows "Base (\<beta> x) = x"
    and "Eps1 (\<beta> x) = 1"
    and "Eps2 (\<beta> x) = 1"
    and "Eps12 (\<beta> x) = 0"
  by (simp_all add: hyperdualx_def)

lemma hypext_extract_eq:
  "(*h* f) (\<beta> x) = f x *\<^sub>H ba + deriv f x *\<^sub>H e1 + deriv f x *\<^sub>H e2 + deriv (deriv f) x *\<^sub>H e12"
  by (simp add: hypext_Hyperdual_eq_parts hyperdualx_def)

lemma Base_hypext:
  "Base ((*h* f) (\<beta> x)) = f x"
  by (simp add: hyperdualx_def)

lemma Eps1_hypext:
  "Eps1 ((*h* f) (\<beta> x)) = deriv f x"
  by (simp add: hyperdualx_def)

lemma Eps2_hypext:
  "Eps2 ((*h* f) (\<beta> x)) = deriv f x"
  by (simp add: hyperdualx_def)

lemma Eps12_hypext:
  "Eps12 ((*h* f) (\<beta> x)) = deriv (deriv f) x"
  by (simp add: hyperdualx_def)

subsubsection\<open>Convenience Interface\<close>

text\<open>Define a datatype to hold the function value, and the first and second derivative values.\<close>
datatype ('a :: real_normed_field) derivs = Derivs (Value: 'a) (First: 'a) (Second: 'a)

text\<open>
  Then we convert a hyperdual number to derivative values by extracting the base component, one of
  the first-order components, and the second-order component.
\<close>
fun hyperdual_to_derivs :: "('a :: real_normed_field) hyperdual \<Rightarrow> 'a derivs"
  where "hyperdual_to_derivs x = Derivs (Base x) (Eps1 x) (Eps12 x)"

text\<open>
  Finally we define way of converting any compatible function into one that yields the value and the
  derivatives.
\<close>
fun autodiff :: "('a :: real_normed_field \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a derivs"
  where "autodiff f = (\<lambda>x. hyperdual_to_derivs ((*h* f) (\<beta> x)))"

lemma autodiff_sel:
  "Value (autodiff f x) = Base ((*h* f) (\<beta> x))"
  "First (autodiff f x) = Eps1 ((*h* f) (\<beta> x))"
  "Second (autodiff f x) = Eps12 ((*h* f) (\<beta> x))"
  by simp_all

text\<open>The result contains the expected values.\<close>
lemma autodiff_extract_value:
  "Value (autodiff f x) = f x"
  by (simp del: hypext.simps add: Base_hypext)

lemma autodiff_extract_first:
  "First (autodiff f x) = deriv f x"
  by (simp del: hypext.simps add: Eps1_hypext)

lemma autodiff_extract_second:
  "Second (autodiff f x) = deriv (deriv f) x"
  by (simp del: hypext.simps add: Eps12_hypext)

text\<open>
  The derivative components of the result are actual derivatives if the function is sufficiently
  differentiable on that argument.
\<close>
lemma autodiff_first_derivative:
  assumes "f field_differentiable (at x)"
  shows "(f has_field_derivative First (autodiff f x)) (at x)"
  by (simp add: autodiff_extract_first DERIV_deriv_iff_field_differentiable assms)

lemma autodiff_second_derivative:
  assumes "f twice_field_differentiable_at x"
  shows "((deriv f) has_field_derivative Second (autodiff f x)) (at x)"
  by (simp add: autodiff_extract_second DERIV_deriv_iff_field_differentiable assms deriv_field_differentiable_at)

subsubsection\<open>Composition\<close>

text\<open>Composition of hyperdual extensions is the hyperdual extension of composition:\<close>
lemma hypext_compose:
  assumes "f twice_field_differentiable_at (Base x)"
      and "g twice_field_differentiable_at (f (Base x))"
    shows "(*h* (\<lambda>x. g (f x))) x = (*h* g) ((*h* f) x)"
proof (simp add: hyperdual_eq_iff, intro conjI disjI2)
  show goal1: "deriv (\<lambda>x. g (f x)) (Base x) = deriv f (Base x) * deriv g (f (Base x))"
  proof -
    have "deriv (\<lambda>x. g (f x)) (Base x) = deriv (g \<circ> f) (Base x)"
      by (simp add: comp_def)
    also have "... = deriv g (f (Base x)) * deriv f (Base x)"
      using assms by (simp add: deriv_chain once_field_differentiable_at)
    finally show ?thesis
      by (simp add: mult.commute deriv_chain)
  qed
  then show "deriv (\<lambda>x. g (f x)) (Base x) = deriv f (Base x) * deriv g (f (Base x))" .

  have first_diff: "(\<lambda>x. deriv g (f x)) field_differentiable at (Base x)"
    by (metis DERIV_chain2 assms deriv_field_differentiable_at field_differentiable_def once_field_differentiable_at)

  have "deriv (deriv g \<circ> f) (Base x) = deriv (deriv g) (f (Base x)) * deriv f (Base x)"
    using deriv_chain assms once_field_differentiable_at deriv_field_differentiable_at
    by blast
  then have deriv_deriv_comp: "deriv (\<lambda>x. deriv g (f x)) (Base x) = deriv (deriv g) (f (Base x)) * deriv f (Base x)"
    by (simp add: comp_def)

  have "deriv (deriv (\<lambda>x. g (f x))) (Base x) = deriv ((\<lambda>x. deriv f x * deriv g (f x))) (Base x)"
    using assms eventually_deriv_compose'[of f "Base x" g]
    by (simp add: mult.commute deriv_cong_ev)
  also have "... = deriv f (Base x) * deriv (\<lambda>x. deriv g (f x)) (Base x) + deriv (deriv f) (Base x) * deriv g (f (Base x))"
    using assms(1) first_diff by (simp add: deriv_field_differentiable_at)
  also have "... = deriv f (Base x) * deriv (deriv g) (f (Base x)) * deriv f (Base x) + deriv (deriv f) (Base x) * deriv g (f (Base x))"
    using deriv_deriv_comp by simp
  finally show "Eps12 x * deriv (\<lambda>x. g (f x)) (Base x) + Eps1 x * Eps2 x * deriv (deriv (\<lambda>x. g (f x))) (Base x) =
    (Eps12 x * deriv f (Base x) + Eps1 x * Eps2 x * deriv (deriv f) (Base x)) * deriv g (f (Base x)) +
    Eps1 x * deriv f (Base x) * (Eps2 x * deriv f (Base x)) * deriv (deriv g) (f (Base x))"
    by (simp add: goal1 field_simps)
qed

subsection\<open>Concrete Instances\<close>

subsubsection\<open>Constant\<close>

text\<open>Component embedding is an extension of the constant function.\<close>
lemma hypext_const [simp]:
  "(*h* (\<lambda>x. a)) x = of_comp a"
  by (simp add: of_comp_def hyperdual_eq_iff)

lemma "autodiff (\<lambda>x. a) = (\<lambda>x. Derivs a 0 0)"
  by simp

subsubsection\<open>Identity\<close>

text\<open>Identity is an extension of the component identity.\<close>
lemma hypext_ident:
  "(*h* (\<lambda>x. x)) x = x"
  by (simp add: hyperdual_eq_iff)

subsubsection\<open>Component Scalar Multiplication\<close>

text\<open>Component scaling is an extension of component constant multiplication:\<close>
lemma hypext_scaleH:
  "(*h* (\<lambda>x. k * x)) x = k *\<^sub>H x"
  by (simp add: hyperdual_eq_iff)

lemma hypext_fun_scaleH:
  assumes "f twice_field_differentiable_at (Base x)"
  shows "(*h* (\<lambda>x. k * f x)) x = k *\<^sub>H (*h* f) x"
  using assms by (simp add: hypext_compose hypext_scaleH)

text\<open>Unary minus is just an instance of constant multiplication:\<close>
lemma hypext_uminus:
  "(*h* uminus) x = - x"
  using hypext_scaleH[of "-1" x] by simp

subsubsection\<open>Real Scalar Multiplication\<close>

text\<open>Real scaling is an extension of component real scaling:\<close>
lemma hypext_scaleR:
  "(*h* (\<lambda>x. k *\<^sub>R x)) x = k *\<^sub>R x"
  by (auto simp add: hyperdual_eq_iff)

lemma hypext_fun_scaleR:
  assumes "f twice_field_differentiable_at (Base x)"
  shows "(*h* (\<lambda>x. k *\<^sub>R f x)) x = k *\<^sub>R (*h* f) x"
  using assms by (simp add: hypext_compose hypext_scaleR)

subsubsection\<open>Addition\<close>

text\<open>Addition of hyperdual extensions is a hyperdual extension of addition of functions.\<close>
lemma hypext_fun_add:
  assumes "f twice_field_differentiable_at (Base x)"
      and "g twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>x. f x + g x)) x = (*h* f) x + (*h* g) x"
proof (simp add: hyperdual_eq_iff distrib_left[symmetric], intro conjI disjI2)
  show goal1: "deriv (\<lambda>x. f x + g x) (Base x) = deriv f (Base x) + deriv g (Base x)"
    by (simp add: assms once_field_differentiable_at distrib_left)
  then show "deriv (\<lambda>x. f x + g x) (Base x) = deriv f (Base x) + deriv g (Base x)" .

  have "deriv (deriv (\<lambda>x. f x + g x)) (Base x) = deriv (\<lambda>w. deriv f w + deriv g w) (Base x)"
    by (simp add: assms deriv_cong_ev eventually_deriv_add)
  moreover have "Eps12 x * deriv f (Base x) + Eps12 x * deriv g (Base x) = Eps12 x * deriv (\<lambda>x. f x + g x) (Base x)"
    by (metis distrib_left goal1)
  ultimately show "Eps12 x * deriv (\<lambda>x. f x + g x) (Base x) +
    Eps1 x * Eps2 x * deriv (deriv (\<lambda>x. f x + g x)) (Base x) =
    Eps12 x * deriv f (Base x) + Eps1 x * Eps2 x * deriv (deriv f) (Base x) +
    (Eps12 x * deriv g (Base x) + Eps1 x * Eps2 x * deriv (deriv g) (Base x))"
    using deriv_add[OF deriv_field_differentiable_at deriv_field_differentiable_at, OF assms]
    by (simp add: distrib_left add.left_commute)
qed

lemma hypext_cadd [simp]:
  "(*h* (\<lambda>x. x + a)) x = x + of_comp a"
  by (auto simp add: hyperdual_eq_iff of_comp_def)

lemma hypext_fun_cadd:
  assumes "f twice_field_differentiable_at (Base x)"
  shows "(*h* (\<lambda>x. f x + a)) x = (*h* f) x + of_comp a"
  using assms hypext_compose[of f x "\<lambda>x. x + a"] by simp

subsubsection\<open>Component Linear Function\<close>

text\<open>Hyperdual linear function is an extension of the component linear function:\<close>
lemma hypext_linear:
  "(*h* (\<lambda>x. k * x + a)) x = k *\<^sub>H x + of_comp a"
  using hypext_fun_add[of "(*) k" x "\<lambda>x. a"]
  by (simp add: hypext_scaleH)

lemma hypext_fun_linear:
  assumes "f twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>x. k * f x + a)) x = k *\<^sub>H (*h* f) x + of_comp a"
  using assms hypext_compose[of f x "\<lambda>x. k * x + a"] by (simp add: hypext_linear)

subsubsection\<open>Real Linear Function\<close>

text\<open>We have the same for real scaling instead of component multiplication:\<close>
lemma hypext_linearR:
  "(*h* (\<lambda>x. k *\<^sub>R x + a)) x = k *\<^sub>R x + of_comp a"
  using hypext_fun_add[of "(*\<^sub>R) k" x "\<lambda>x. a"]
  by (simp add: hypext_scaleR)

lemma hypext_fun_linearR:
  assumes "f twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>x. k *\<^sub>R f x + a)) x = k *\<^sub>R (*h* f) x + of_comp a"
  using assms hypext_compose[of f x "\<lambda>x. k *\<^sub>R x + a"] by (simp add: hypext_linearR)

subsubsection\<open>Multiplication\<close>

text\<open>Extension of multiplication is multiplication of the functions' extensions.\<close>
lemma hypext_fun_mult:
  assumes "f twice_field_differentiable_at (Base x)"
      and "g twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>z. f z * g z)) x = (*h* f) x * (*h* g) x"
proof (simp add: hyperdual_eq_iff distrib_left[symmetric], intro conjI)
  show "Eps1 x * deriv (\<lambda>z. f z * g z) (Base x) =
        f (Base x) * (Eps1 x * deriv g (Base x)) + Eps1 x * deriv f (Base x) * g (Base x)"
   and "Eps2 x * deriv (\<lambda>z. f z * g z) (Base x) =
        f (Base x) * (Eps2 x * deriv g (Base x)) + Eps2 x * deriv f (Base x) * g (Base x)"
    using assms by (simp_all add: once_field_differentiable_at distrib_left)

  have
    "deriv (deriv (\<lambda>z. f z * g z)) (Base x) =
     f (Base x) * deriv (deriv g) (Base x) + 2 * deriv f (Base x) * deriv g (Base x) + deriv (deriv f) (Base x) * g (Base x)"
  proof -
    have "deriv (deriv (\<lambda>z. f z * g z)) (Base x) = deriv (\<lambda>z. f z * deriv g z + deriv f z * g z) (Base x)"
      using assms by (simp add: eventually_deriv_mult deriv_cong_ev)
    also have "... = (\<lambda>z. f z * deriv (deriv g) z + deriv f z * deriv g z + deriv f z * deriv g z + deriv (deriv f) z * g z) (Base x)"
      by (simp add: assms deriv_field_differentiable_at field_differentiable_mult once_field_differentiable_at)
    finally show ?thesis
      by simp
  qed
  then show
    "Eps12 x * deriv (\<lambda>z. f z * g z) (Base x) + Eps1 x * Eps2 x * deriv (deriv (\<lambda>z. f z * g z)) (Base x) =
     2 * (Eps1 x * (Eps2 x * (deriv f (Base x) * deriv g (Base x)))) +
     f (Base x) * (Eps12 x * deriv g (Base x) + Eps1 x * Eps2 x * deriv (deriv g) (Base x)) +
     (Eps12 x * deriv f (Base x) + Eps1 x * Eps2 x * deriv (deriv f) (Base x)) * g (Base x)"
     using assms by (simp add: once_field_differentiable_at field_simps)
qed

subsubsection\<open>Sine and Cosine\<close>

text\<open>The extended sin and cos at an arbitrary hyperdual.\<close>

lemma hypext_sin_Hyperdual:
  "(*h* sin) (Hyperdual a b c d) = sin a *\<^sub>H ba + (b *cos a) *\<^sub>H e1 + (c * cos a) *\<^sub>H e2 + (d * cos a - b * c * sin a) *\<^sub>H e12 "
  by (simp add: hypext_Hyperdual_eq_parts)

lemma hypext_cos_Hyperdual:
  "(*h* cos) (Hyperdual a b c d) = cos a *\<^sub>H ba - (b * sin a) *\<^sub>H e1 - (c * sin a) *\<^sub>H e2 - (d * sin a + b * c * cos a) *\<^sub>H e12 "
proof -
  have "of_comp (- (d * sin a) - b * c * cos a) * e12 = - (of_comp (d * sin a + b * c * cos a) * e12)"
    by (metis add_uminus_conv_diff minus_add_distrib mult_minus_left of_comp_minus)
  then show ?thesis
    by (simp add: hypext_Hyperdual_eq_parts of_comp_minus scaleH_times)
qed

lemma Eps1_hypext_sin [simp]:
  "Eps1 ((*h* sin) x) = Eps1 x * cos (Base x)"
  by simp

lemma Eps2_hypext_sin [simp]:
  "Eps2 ((*h* sin) x) = Eps2 x * cos (Base x)"
  by simp

lemma Eps12_hypext_sin [simp]:
  "Eps12 ((*h* sin) x) = Eps12 x * cos (Base x) - Eps1 x * Eps2 x * sin (Base x)"
  by simp

lemma hypext_sin_e1 [simp]:
  "(*h* sin) (x * e1) = e1 * x"
  by (simp add: e1_def hyperdual_eq_iff one_hyperdual_def)

lemma hypext_sin_e2 [simp]:
  "(*h* sin) (x * e2) = e2 * x"
  by (simp add: e2_def hyperdual_eq_iff one_hyperdual_def)

lemma hypext_sin_e12 [simp]:
  "(*h* sin) (x * e12) = e12 * x"
  by (simp add: e12_def hyperdual_eq_iff one_hyperdual_def)

lemma hypext_cos_e1 [simp]:
  "(*h* cos) (x * e1) = 1"
  by (simp add: e1_def hyperdual_eq_iff one_hyperdual_def)

lemma hypext_cos_e2 [simp]:
  "(*h* cos) (x * e2) = 1"
  by (simp add: e2_def hyperdual_eq_iff one_hyperdual_def)

lemma hypext_cos_e12 [simp]:
  "(*h* cos) (x * e12) = 1"
  by (simp add: e12_def hyperdual_eq_iff one_hyperdual_def)

text\<open>The extended sin and cos at @{term "\<beta> x"}.\<close>

lemma hypext_sin_extract:
  "(*h* sin) (\<beta> x) = sin x *\<^sub>H ba + cos x *\<^sub>H e1 + cos x *\<^sub>H e2 - sin x *\<^sub>H e12"
  by (simp add: hypext_sin_Hyperdual of_comp_minus scaleH_times hyperdualx_def)

lemma hypext_cos_extract:
  "(*h* cos) (\<beta> x) = cos x *\<^sub>H ba - sin x *\<^sub>H e1 - sin x *\<^sub>H e2 - cos x *\<^sub>H e12"
  by (simp add: hypext_cos_Hyperdual hyperdualx_def)

text\<open>Extracting the extended sin components at @{term "\<beta> x"}.\<close>

lemma Base_hypext_sin_extract [simp]:
  "Base ((*h* sin) (\<beta> x)) = sin x"
  by (rule Base_hypext)

lemma Eps2_hypext_sin_extract [simp]:
  "Eps2 ((*h* sin) (\<beta> x)) = cos x"
  using Eps2_hypext[of sin] by simp

lemma Eps12_hypext_sin_extract [simp]:
  "Eps12 ((*h* sin) (\<beta> x)) = - sin x"
  using Eps12_hypext[of sin] by simp

text\<open>Extracting the extended cos components at @{term "\<beta> x"}.\<close>

lemma Base_hypext_cos_extract [simp]:
  "Base ((*h* cos) (\<beta> x)) = cos x"
  by (rule Base_hypext)

lemma Eps2_hypext_cos_extract [simp]:
  "Eps2 ((*h* cos) (\<beta> x)) = - sin x"
  using Eps2_hypext[of cos] by simp

lemma Eps12_hypext_cos_extract [simp]:
  "Eps12 ((*h* cos) (\<beta> x)) = - cos x"
  using Eps12_hypext[of cos] by simp

text\<open>We get one of the key trigonometric properties for the extensions of sin and cos.\<close>

lemma "((*h* sin) x)\<^sup>2 + ((*h* cos) x)\<^sup>2 = 1"
  by (simp add: hyperdual_eq_iff one_hyperdual_def power2_eq_square field_simps)

(* example *)
lemma "(*h* sin) x + (*h* cos) x = (*h* (\<lambda>x. sin x + cos x)) x"
  by (simp add: hypext_fun_add)

subsubsection\<open>Exponential\<close>

text\<open>The exponential function extension behaves as expected.\<close>

lemma hypext_exp_Hyperdual:
  "(*h* exp) (Hyperdual a b c d) =
       exp a *\<^sub>H ba + (b * exp a) *\<^sub>H e1 + (c * exp a) *\<^sub>H e2 + (d * exp a + b * c * exp a) *\<^sub>H e12"
  by (simp add: hypext_Hyperdual_eq_parts)

lemma hypext_exp_extract:
  "(*h* exp) (\<beta> x) = exp x *\<^sub>H ba + exp x *\<^sub>H e1 + exp x *\<^sub>H e2 + exp x *\<^sub>H e12"
  by (simp add: hypext_extract_eq)

lemma hypext_exp_e1 [simp]:
  "(*h* exp) (x * e1) = 1 + e1 * x"
  by (simp add: e1_def hyperdual_eq_iff)

lemma hypext_exp_e2 [simp]:
  "(*h* exp) (x * e2) = 1 + e2 * x"
  by (simp add: e2_def hyperdual_eq_iff)

lemma hypext_exp_e12 [simp]:
  "(*h* exp) (x * e12) = 1 + e12 * x"
  by (simp add: e12_def hyperdual_eq_iff)

text\<open>Extracting the parts for the exponential function extension.\<close>

lemma Eps1_hypext_exp_extract [simp]:
  "Eps1 ((*h* exp) (\<beta> x)) = exp x"
  using Eps1_hypext[of exp] by simp

lemma Eps2_hypext_exp_extract [simp]:
  "Eps2 ((*h* exp) (\<beta> x)) = exp x"
  using Eps2_hypext[of exp] by simp

lemma Eps12_hypext_exp_extract [simp]:
  "Eps12 ((*h* exp) (\<beta> x)) = exp x"
  using Eps12_hypext[of exp] by simp

subsubsection\<open>Square Root\<close>
text\<open>Square root function extension.\<close>

lemma hypext_sqrt_Hyperdual_Hyperdual:
  assumes "a > 0"
  shows "(*h* sqrt) (Hyperdual a b c d) =
         Hyperdual (sqrt a) (b * inverse (sqrt a) / 2) (c * inverse (sqrt a) / 2)
           (d * inverse (sqrt a) / 2 - b * c * inverse (sqrt a ^ 3) / 4)"
  by (simp add: assms hypext_Hyperdual_eq)

lemma hypext_sqrt_Hyperdual:
      "a > 0 \<Longrightarrow> (*h* sqrt) (Hyperdual a b c d) =
       sqrt a *\<^sub>H ba + (b * inverse (sqrt a) / 2) *\<^sub>H e1 + (c * inverse (sqrt a) / 2) *\<^sub>H e2 +
       (d * inverse (sqrt a) / 2 - b * c * inverse (sqrt a ^ 3) / 4) *\<^sub>H e12"
  by (auto simp add: hypext_Hyperdual_eq_parts)

lemma hypext_sqrt_extract:
  "x > 0 \<Longrightarrow> (*h* sqrt) (\<beta> x) = sqrt x *\<^sub>H ba + (inverse (sqrt x) / 2) *\<^sub>H e1 +
        (inverse (sqrt x) / 2) *\<^sub>H e2 - (inverse (sqrt x ^ 3) / 4) *\<^sub>H e12"
  by (simp add: hypext_sqrt_Hyperdual hyperdualx_def of_comp_minus scaleH_times)

text\<open>Extracting the parts for the square root extension.\<close>

lemma Eps1_hypext_sqrt_extract [simp]:
  "x > 0 \<Longrightarrow> Eps1 ((*h* sqrt) (\<beta> x)) = inverse (sqrt x) / 2"
  using Eps1_hypext[of sqrt] by simp

lemma Eps2_hypext_sqrt_extract [simp]:
  "x > 0 \<Longrightarrow> Eps2 ((*h* sqrt) (\<beta> x)) = inverse (sqrt x) / 2"
  using Eps2_hypext[of sqrt] by simp

lemma Eps12_hypext_sqrt_extract [simp]:
  "x > 0 \<Longrightarrow> Eps12 ((*h* sqrt) (\<beta> x)) = - (inverse (sqrt x ^ 3) / 4)"
  using Eps12_hypext[of sqrt] by simp

(* example *)
lemma "Base x > 0 \<Longrightarrow> (*h* sin) x + (*h* sqrt) x = (*h* (\<lambda>x. sin x + sqrt x)) x"
  by (simp add: hypext_fun_add)

subsubsection\<open>Natural Power\<close>

lemma hypext_power:
  "(*h* (\<lambda>x. x ^ n)) x = x ^ n"
  by (simp add: hyperdual_eq_iff hyperdual_power)

lemma hypext_fun_power:
  assumes "f twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>x. (f x) ^ n)) x = ((*h* f) x) ^ n"
  using assms hypext_compose[of f x "\<lambda>x. x ^ n"] by (simp add: hypext_power)

lemma hypext_power_Hyperdual:
  "(*h* (\<lambda>x. x ^ n)) (Hyperdual a b c d) =
        a ^ n *\<^sub>H ba + (of_nat n * b * a ^ (n - 1)) *\<^sub>H e1 + (of_nat n * c * a ^ (n - 1)) *\<^sub>H e2 +
        (d * (of_nat n * a ^ (n - 1)) + b * c * (of_nat n * of_nat (n - 1) * a ^ (n - 2))) *\<^sub>H e12"
  by (simp add: hypext_Hyperdual_eq_parts algebra_simps)

lemma hypext_power_Hyperdual_parts:
  "(*h* (\<lambda>x. x ^ n)) (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) =
        a ^ n *\<^sub>H ba + (of_nat n * b * a ^ (n - 1)) *\<^sub>H e1 + (of_nat n * c * a ^ (n - 1)) *\<^sub>H e2 +
        (d * (of_nat n * a ^ (n - 1)) + b * c * (of_nat n * of_nat (n - 1) * a ^ (n - 2))) *\<^sub>H e12"
  by (simp add: Hyperdual_eq [symmetric] hypext_power_Hyperdual)

lemma hypext_power_extract:
  "(*h* (\<lambda>x. x ^ n)) (\<beta> x) =
      x ^ n *\<^sub>H ba + (of_nat n * x ^ (n - 1)) *\<^sub>H e1 + (of_nat n * x ^ (n - 1)) *\<^sub>H e2 +
      (of_nat n * of_nat (n - 1) * x ^ (n - 2)) *\<^sub>H e12"
  by (simp add: hypext_extract_eq)

lemma Eps1_hypext_power [simp]:
  "Eps1 ((*h* (\<lambda>x. x ^ n)) x) = of_nat n * Eps1 x * (Base x) ^ (n - 1)"
  by simp

lemma Eps2_hypext_power [simp]:
  "Eps2 ((*h* (\<lambda>x. x ^ n)) x) = of_nat n * Eps2 x * (Base x) ^ (n - 1)"
  by simp

lemma Eps12_hypext_power [simp]:
  "Eps12 ((*h* (\<lambda>x. x ^ n)) x) =
   Eps12 x * (of_nat n * Base x ^ (n - 1)) + Eps1 x * Eps2 x * (of_nat n * of_nat (n - 1) * Base x ^ (n - 2))"
  by simp

subsubsection\<open>Inverse\<close>

lemma hypext_inverse:
  assumes "Base x \<noteq> 0"
  shows "(*h* inverse) x = inverse x"
  using assms by (simp add: hyperdual_eq_iff inverse_eq_divide)

lemma hypext_fun_inverse:
  assumes "f twice_field_differentiable_at (Base x)"
      and "f (Base x) \<noteq> 0"
    shows "(*h* (\<lambda>x. inverse (f x))) x = inverse ((*h* f) x)"
  using assms hypext_compose[of f x inverse] by (simp add: hypext_inverse)

lemma hypext_inverse_Hyperdual:
  "a \<noteq> 0 \<Longrightarrow>
    (*h* inverse) (Hyperdual a b c d) =
    Hyperdual (inverse a) (- (b / a\<^sup>2)) (- (c / a\<^sup>2)) (2 * b * c / (a ^ 3) - d / a\<^sup>2)"
  by (simp add: hypext_Hyperdual_eq divide_inverse)

lemma hypext_inverse_Hyperdual_parts:
  "a \<noteq> 0 \<Longrightarrow>
    (*h* inverse) (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) =
    inverse a *\<^sub>H ba + - (b / a\<^sup>2) *\<^sub>H e1 + - (c / a\<^sup>2) *\<^sub>H e2 + (2 * b * c / a ^ 3 - d / a\<^sup>2) *\<^sub>H e12"
  by (metis Hyperdual_eq hypext_inverse_Hyperdual)

lemma inverse_Hyperdual_parts:
  "(a::'a::real_normed_field) \<noteq> 0 \<Longrightarrow>
    inverse (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) =
    inverse a *\<^sub>H ba + - (b / a\<^sup>2) *\<^sub>H e1 + - (c / a\<^sup>2) *\<^sub>H e2 + (2 * b * c / a ^ 3 - d / a\<^sup>2) *\<^sub>H e12"
  by (metis Hyperdual_eq hyperdual.sel(1) hypext_inverse hypext_inverse_Hyperdual_parts)

lemma hypext_inverse_extract:
  "x \<noteq> 0 \<Longrightarrow> (*h* inverse) (\<beta> x) = inverse x *\<^sub>H ba - (1 / x\<^sup>2) *\<^sub>H e1 - (1 / x\<^sup>2) *\<^sub>H e2 + (2 / x ^ 3) *\<^sub>H e12"
  by (simp add: hypext_extract_eq divide_inverse of_comp_minus scaleH_times)

lemma inverse_extract:
  "x \<noteq> 0 \<Longrightarrow> inverse (\<beta> x) = inverse x *\<^sub>H ba - (1 / x\<^sup>2) *\<^sub>H e1 - (1 / x\<^sup>2) *\<^sub>H e2 + (2 / x ^ 3) *\<^sub>H e12"
  by (metis hyperdual.sel(1) hyperdualx_def hypext_inverse hypext_inverse_extract)

lemma Eps1_hypext_inverse [simp]:
  "Base x \<noteq> 0 \<Longrightarrow> Eps1 ((*h* inverse) x) = - Eps1 x * (1 / (Base x)\<^sup>2)"
  by simp
lemma Eps1_inverse [simp]:
  "Base (x::'a::real_normed_field hyperdual) \<noteq> 0 \<Longrightarrow> Eps1 (inverse x) = - Eps1 x * (1 / (Base x)\<^sup>2)"
  by simp

lemma Eps2_hypext_inverse [simp]:
  "Base (x::'a::real_normed_field hyperdual) \<noteq> 0 \<Longrightarrow> Eps2 (inverse x) = - Eps2 x * (1 / (Base x)\<^sup>2)"
  by simp

lemma Eps12_hypext_inverse [simp]:
  "Base  (x::'a::real_normed_field hyperdual) \<noteq> 0
   \<Longrightarrow> Eps12 (inverse x) = Eps1 x * Eps2 x * (2/ (Base x ^ 3)) - Eps12 x / (Base x)\<^sup>2"
  by simp

subsubsection\<open>Division\<close>

lemma hypext_fun_divide:
  assumes "f twice_field_differentiable_at (Base x)"
      and "g twice_field_differentiable_at (Base x)"
      and "g (Base x) \<noteq> 0"
    shows "(*h* (\<lambda>x. f x / g x)) x = (*h* f) x / (*h* g) x"
proof -
  have "(\<lambda>x. inverse (g x)) twice_field_differentiable_at Base x"
    by (simp add: assms(2) assms(3) twice_field_differentiable_at_compose)
  moreover have "(*h* f) x * (*h* (\<lambda>x. inverse (g x))) x = (*h* f) x * inverse ((*h* g) x)"
    by (simp add: assms(2) assms(3) hypext_fun_inverse)
  ultimately have "(*h* (\<lambda>x. f x * inverse (g x))) x = (*h* f) x * inverse ((*h* g) x)"
    by (simp add: assms(1) hypext_fun_mult)
  then show ?thesis
    by (simp add: divide_inverse hyp_divide_inverse)
qed

subsubsection\<open>Polynomial\<close>

lemma hypext_polyn:
  fixes coef :: "nat \<Rightarrow> 'a :: {real_normed_field}"
    and n :: nat
  shows "(*h* (\<lambda>x. \<Sum>i<n. coef i * x^i)) x = (\<Sum>i<n. (coef i) *\<^sub>H (x^i))"
proof (induction n)
  case 0
  then show ?case
    by (simp add: zero_hyperdual_def)
next
  case hyp: (Suc n)

  have "(\<lambda>x. \<Sum>i<Suc n. coef i * x ^ i) = (\<lambda>x. (\<Sum>i<n. coef i * x ^ i) + coef n * x ^ n)"
   and "(\<lambda>x. \<Sum>i<Suc n. coef i *\<^sub>H x ^ i) = (\<lambda>x. (\<Sum>i<n. coef i *\<^sub>H x ^ i) + coef n *\<^sub>H x ^ n)"
    by (simp_all add: field_simps)

  then show ?case
  proof (simp)
    have "(\<lambda>x. coef n * x ^ n) twice_field_differentiable_at Base x"
      using twice_field_differentiable_at_compose[of "\<lambda>x. x ^ n" "Base x" "(*) (coef n)"]
      by simp
    then have "(*h* (\<lambda>x. (\<Sum>i<n. coef i * x ^ i) + coef n * x ^ n)) x =
          (*h* (\<lambda>x. (\<Sum>i<n. coef i * x ^ i))) x + (*h* (\<lambda>x. coef n * x ^ n)) x"
      by (simp add: hypext_fun_add)
    moreover have "(*h* (\<lambda>x. coef n * x ^ n)) x = coef n *\<^sub>H x ^ n"
      by (simp add: hypext_fun_scaleH hypext_power)
    ultimately have "(*h* (\<lambda>x. (\<Sum>i<n. coef i * x ^ i) + coef n * x ^ n)) x = (\<Sum>i<n. coef i *\<^sub>H x ^ i) + coef n *\<^sub>H x ^ n"
      using hyp by simp
    then show "(*h* (\<lambda>x. (\<Sum>i<n. coef i * x ^ i) + coef n * x ^ n)) x = (\<Sum>i<n. coef i *\<^sub>H x ^ i) + coef n *\<^sub>H x ^ n"
      by simp
  qed
qed

lemma hypext_fun_polyn:
    fixes coef :: "nat \<Rightarrow> 'a :: {real_normed_field}"
      and n :: nat
  assumes "f twice_field_differentiable_at (Base x)"
    shows "(*h* (\<lambda>x. \<Sum>i<n. coef i * (f x)^i)) x = (\<Sum>i<n. (coef i) *\<^sub>H (((*h* f) x)^i))"
  using assms hypext_compose[of f x "\<lambda>x. (\<Sum>i<n. coef i * x^i)"] by (simp add: hypext_polyn)

end
