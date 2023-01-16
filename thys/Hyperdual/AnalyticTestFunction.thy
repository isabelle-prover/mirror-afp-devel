(*  Title:   AnalyticTestFunction.thy
    Authors: Filip Smola and Jacques D. Fleuriot, University of Edinburgh, 2019-2021
*)

theory AnalyticTestFunction
  imports HyperdualFunctionExtension "HOL-Decision_Procs.Approximation"
begin

subsection\<open>Analytic Test Function\<close>
text\<open>
  We investigate the analytic test function used by Fike and Alonso in their
  2011 paper~\<^cite>\<open>"fike_alonso-2011"\<close> as a relatively non-trivial example.
  The function is defined as: @{term "\<lambda>x. exp x / (sqrt (sin x ^ 3 + cos x ^ 3))"}.
\<close>
definition fa_test :: "real \<Rightarrow> real"
  where "fa_test x = exp x / (sqrt (sin x ^ 3 + cos x ^ 3))"

text\<open>
  We define the same composition of functions but using the relevant hyperdual versions.
  Note that we implicitly use the facts that hyperdual extensions of plus, times and inverse are the
  same operations on hyperduals.
\<close>
definition hyp_fa_test :: "real hyperdual \<Rightarrow> real hyperdual"
  where "hyp_fa_test x = ((*h* exp) x) / ((*h* sqrt) (((*h* sin) x) ^ 3 + ((*h* cos) x) ^ 3))"

text\<open>We prove lemmas useful to show when this function is well defined.\<close>
lemma sin_cube_plus_cos_cube:
  "sin x ^ 3 + cos x ^ 3 = 1/2 * (sin x + cos x) * (2 - sin (2 * x))"
  for x :: "'a::{real_normed_field,banach}"
proof -
  have "sin x ^ 3 + cos x ^ 3 = (sin x + cos x) * (cos x ^ 2 - cos x * sin x + sin x ^ 2)"
    by (smt (z3) add.commute combine_common_factor diff_add_cancel distrib_left
          mult.commute mult.left_commute power2_eq_square power3_eq_cube)
  also have "\<dots> = (sin x + cos x) * (1 - cos x * sin x)"
    by simp
  finally show ?thesis
    by (smt (z3) mult.commute mult.left_neutral mult_2 nonzero_mult_div_cancel_left
          right_diff_distrib' sin_add times_divide_eq_left zero_neq_numeral)
qed

lemma sin_cube_plus_cos_cube_gt_zero_iff:
  "(sin x ^ 3 + cos x ^ 3 > 0) = (sin x + cos x > 0)"
  for x ::real
  by (smt (verit, best) cos_zero power3_eq_cube power_zero_numeral sin_cube_plus_cos_cube
       sin_le_one sin_zero zero_less_mult_iff)

lemma sin_plus_cos_eq_45:
  "sin x + cos x = sqrt 2 * sin (x + pi/4)"
  apply (simp add: sin_add sin_45 cos_45 )
  by (simp add: field_simps)

lemma sin_cube_plus_cos_cube_gt_zero_iff':
  "(sin x ^ 3 + cos x ^ 3 > 0) = (sin (x + pi/4) > 0)"
  by (smt (verit, best) mult_pos_pos real_sqrt_gt_0_iff
      sin_cube_plus_cos_cube_gt_zero_iff sin_plus_cos_eq_45 zero_less_mult_pos)

lemma sin_less_zero_pi:
  "\<lbrakk>- pi < x; x < 0\<rbrakk> \<Longrightarrow> sin x < 0"
  by (metis add.inverse_inverse add.inverse_neutral neg_less_iff_less sin_gt_zero sin_minus)

lemma sin_45_positive_intervals:
  "(sin (x + pi/4) > 0) = (x \<in> (\<Union>n::int. {-pi/4 + 2*pi*n <..< 3*pi/4 + 2*pi*n}))"
proof (standard ; (elim UnionE rangeE | -))
  obtain y :: real and n :: int
    where "x = y + 2*pi*n" and "- pi \<le> y" and "y \<le> pi"
    using sincos_principal_value sin_cos_eq_iff less_eq_real_def by metis
  note yn = this

  assume "0 < sin (x + pi / 4)"
  then have a: "0 < sin (y + pi / 4)"
    using yn by (metis sin_add sin_cos_eq_iff)
  then have "y \<in> {- pi / 4<..<3 * pi / 4}"
  proof (unfold greaterThanLessThan_iff, safe)
    show "- pi / 4 < y"
    proof (rule ccontr)
      assume "\<not> - pi / 4 < y"
      then have "y < - pi / 4 \<or> y = - pi / 4"
        by (simp add: not_less le_less)
      then show False
        using a sin_less_zero_pi[where x = "y + pi/4"] yn sin_zero
        by force
    qed
    show "y < 3 * pi / 4"
    proof (rule ccontr)
      assume "\<not> y < 3 * pi / 4"
      then have "pi \<le> y + pi/4"
        by (simp add: not_less)
      then show False
        using a sin_le_zero yn pi_ge_two by fastforce
    qed
  qed
  then have "x \<in> {- pi / 4 + 2*pi*n<..<3 * pi / 4 + 2*pi*n}"
    using yn greaterThanLessThan_iff by simp
  then show "x \<in> (\<Union>n::int. {- pi / 4 + 2*pi*n<..<3 * pi / 4 + 2*pi*n})"
    by blast
next
  fix X and n :: int
  assume "x \<in> X"
     and "X = {- pi / 4 + 2*pi*n<..<3 * pi / 4 + 2*pi*n}"
  then have "x \<in> {- pi / 4 + 2*pi*n<..<3 * pi / 4 + 2*pi*n}"
    by simp
  then obtain y :: real and n :: int
    where "x = y + 2*pi*n" and "- pi / 4 < y" and "y < 3 * pi / 4"
    by (smt (z3) greaterThanLessThan_iff)
  note yn = this

  have "0 < sin (y + pi / 4)"
    using sin_gt_zero yn by force
  then show "0 < sin (x + pi / 4)"
    using yn sin_cos_eq_iff[of "x + pi / 4" "y + pi / 4"] by simp
qed

text\<open>When the function is well defined our hyperdual definition is equal to the hyperdual extension.\<close>
lemma hypext_fa_test:
  assumes "Base x \<in> (\<Union>n::int. {-pi/4 + 2*pi*n <..< 3*pi/4 + 2*pi*n})"
  shows "(*h* fa_test) x = hyp_fa_test x"
proof -
  have inverse_sqrt_valid: "0 < sin (Base x) ^ 3 + cos (Base x) ^ 3"
    using assms sin_45_positive_intervals sin_cube_plus_cos_cube_gt_zero_iff' by force

  have "\<And>f. (\<lambda>x. (sin x) ^ 3) twice_field_differentiable_at Base x"
   and "\<And>f. (\<lambda>x. (cos x) ^ 3) twice_field_differentiable_at Base x"
    by (simp_all add: twice_field_differentiable_at_compose[OF _ twice_field_differentiable_at_power])
  then have "(*h* (\<lambda>x. sin x ^ 3 + cos x ^ 3)) x = (*h* sin) x ^ 3 + (*h* cos) x ^ 3"
        and d_sincos: "(\<lambda>x. sin x ^ 3 + cos x ^ 3) twice_field_differentiable_at Base x"
    using hypext_fun_add[of "\<lambda>x. sin x ^ 3" x "\<lambda>x. cos x ^ 3"]
    by (simp_all add: hypext_fun_power twice_field_differentiable_at_add)
  then have "(*h* (\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3))) x = (*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3)"
    using inverse_sqrt_valid hypext_compose[of "\<lambda>x. sin x ^ 3 + cos x ^ 3" x] by simp
  moreover have d_sqrt: "(\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3)) twice_field_differentiable_at Base x"
    using inverse_sqrt_valid d_sincos twice_field_differentiable_at_compose twice_field_differentiable_at_sqrt
    by blast
  ultimately have "(*h* (\<lambda>x. inverse (sqrt (sin x ^ 3 + cos x ^ 3)))) x = inverse ((*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3))"
    using inverse_sqrt_valid hypext_fun_inverse[of "\<lambda>x. sqrt (sin x ^ 3 + cos x ^ 3)" x]
    by simp
  moreover have "(\<lambda>x. inverse (sqrt (sin x ^ 3 + cos x ^ 3))) twice_field_differentiable_at Base x"
    using inverse_sqrt_valid d_sqrt real_sqrt_eq_zero_cancel_iff
          twice_field_differentiable_at_compose twice_field_differentiable_at_inverse
          less_numeral_extra(3)
    by force
  ultimately have
    "(*h* (\<lambda>x. exp x * inverse (sqrt (sin x ^ 3 + cos x ^ 3)))) x =
     (*h* exp) x * inverse ((*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3))"
    by (simp add: hypext_fun_mult)
  then have
    "(*h* (\<lambda>x. exp x / sqrt (sin x ^ 3 + cos x ^ 3))) x =
     (*h* exp) x / (*h* sqrt) ((*h* sin) x ^ 3 + (*h* cos) x ^ 3)"
    by (simp add: inverse_eq_divide hyp_divide_inverse)
  then show ?thesis
    unfolding fa_test_def hyp_fa_test_def .
qed

text\<open>
  We can show that our hyperdual extension gives (approximately) the same values as those found by
  Fike and Alonso when evaluated at @{term "1.5"}.
\<close>
lemma
  assumes "x = hyp_fa_test (\<beta> 1.5)"
  shows "\<bar>Base x - 4.4978\<bar> \<le> 0.00005"
    and "\<bar>Eps1 x - 4.0534\<bar> \<le> 0.00005"
    and "\<bar>Eps12 x - 9.4631\<bar> \<le> 0.00005"
proof -
  show "\<bar>Base x - 4.4978\<bar> \<le> 0.00005"
    by (simp add: assms hyp_fa_test_def, approximation 20)
  have d: "0 < sin (3/2 :: real) ^ 3 + cos (3/2 :: real) ^ 3"
    using sin_cube_plus_cos_cube_gt_zero_iff' sin_gt_zero pos_add_strict pi_gt3 by force
  show "\<bar>Eps1 x - 4.0534\<bar> \<le> 0.00005"
    by (simp add: assms hyp_fa_test_def d, approximation 22)
  show "\<bar>Eps12 x - 9.4631\<bar> \<le> 0.00005"
    by (simp add: assms hyp_fa_test_def d, approximation 24)
qed

text\<open>A number of additional lemmas that will be required to prove the derivatives:\<close>
lemma hypext_sqrt_hyperdual_parts:
      "a > 0 \<Longrightarrow>  (*h* sqrt) (a *\<^sub>H ba + b *\<^sub>H e1 + c *\<^sub>H e2 + d *\<^sub>H e12) =
       sqrt a *\<^sub>H ba + (b * inverse (sqrt a) / 2) *\<^sub>H e1 + (c * inverse (sqrt a) / 2) *\<^sub>H e2 +
       (d * inverse (sqrt a) / 2 - b * c * inverse (sqrt a ^ 3) / 4) *\<^sub>H e12"
  by (metis Hyperdual_eq hypext_sqrt_Hyperdual)

lemma cos_multiple: "cos (n * x) = 2 * cos x * cos ((n - 1) * x) - cos ((n - 2) * x)"
  for x :: "'a :: {banach,real_normed_field}"
proof -
  have "cos ((n - 1) * x + x) + cos ((n - 1) * x - x) = 2 * cos ((n - 1) * x) * cos x"
    by (simp add: cos_add cos_diff)
  then show ?thesis
    by (simp add: left_diff_distrib' eq_diff_eq)
qed

lemma sin_multiple: "sin (n * x) = 2 * cos x * sin ((n - 1) * x) - sin ((n - 2) * x)"
  for x :: "'a :: {banach,real_normed_field}"
proof -
  have "sin ((n - 1) * x + x) + sin ((n - 1) * x - x) = 2 * cos x * sin ((n - 1) * x)"
    by (simp add: sin_add sin_diff)
  then show ?thesis
    by (simp add: left_diff_distrib' eq_diff_eq)
qed

lemma power5:
  fixes z :: "'a :: monoid_mult"
  shows "z ^ 5 = z * z * z * z * z"
  by (simp add: mult.assoc power2_eq_square power_numeral_odd)

lemma power6:
  fixes z :: "'a :: monoid_mult"
  shows "z ^ 6 = z * z * z * z * z * z"
  by (simp add: mult.assoc power3_eq_cube power_numeral_even)

text\<open>
  We find the derivatives of @{const fa_test} by applying a Wengert list approach, as done by Fike
  and Alonso, to make the same composition but in hyperduals.
  We know that this is equal to the hyperdual extension which in turn gives us the derivatives.
\<close>
lemma Wengert_autodiff_fa_test:
  assumes "x \<in> (\<Union>n::int. {-pi/4 + 2*pi*n <..< 3*pi/4 + 2*pi*n})"
  shows "First (autodiff fa_test x) =
    (exp x * (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x))) /
        (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)"
    and "Second (autodiff fa_test x) =
    (exp x * (130 - 12 * cos (2 * x) +
              30 * cos (4 * x) + 12 * cos (6 * x) -
              111 * sin (2 * x) +
              48 * sin (4 * x) + 5 * sin (6 * x))) /
                (64 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)"
proof -
  have s3_c3_gt_zero: "(sin x) ^ 3 + (cos x) ^ 3 > 0"
    using assms sin_45_positive_intervals sin_cube_plus_cos_cube_gt_zero_iff' sin_gt_zero
    by force
   \<comment> \<open>Work out @{const hyp_fa_test} as Wengert list of basic operations\<close>
  let ?w0 = "\<beta> x"
  have w0: "?w0 = x *\<^sub>H ba + 1 *\<^sub>H e1 + 1 *\<^sub>H e2 + 0 *\<^sub>H e12"
    by (simp add: Hyperdual_eq hyperdualx_def)

  let ?w1 = "(*h* exp) ?w0"
  have w1: "?w1 = exp x *\<^sub>H ba + exp x *\<^sub>H e1 + exp x *\<^sub>H e2 + exp x *\<^sub>H e12"
    using hypext_exp_extract by blast

  let ?w2 = "(*h* sin) ?w0"
  have w2: "?w2 = sin x *\<^sub>H ba + cos x *\<^sub>H e1 + cos x *\<^sub>H e2 + - sin x *\<^sub>H e12"
    by (simp add: hypext_sin_extract of_comp_minus scaleH_times)

  let ?w3 = "(*h* (\<lambda>x. x ^ 3)) ?w2"
  have w3: "?w3 = (sin x) ^ 3 *\<^sub>H ba + (3 * cos x * (sin x)\<^sup>2) *\<^sub>H e1 + (3 * cos x * (sin x)\<^sup>2) *\<^sub>H e2 + - (3/4 * (sin x - 3 * sin (3 * x))) *\<^sub>H e12"
    by (simp add: w2 hypext_power_Hyperdual_parts power2_eq_square cos_times_cos sin_times_sin
          sin_times_cos distrib_left right_diff_distrib' divide_simps)

  let ?w4 = "(*h* cos) ?w0"
  have w4: "?w4 = cos x *\<^sub>H ba + - sin x *\<^sub>H e1 + - sin x *\<^sub>H e2 + - cos x *\<^sub>H e12"
    by (simp add: hypext_cos_extract of_comp_minus scaleH_times)

  let ?w5 = "(*h* (\<lambda>x. x ^ 3)) ?w4"
  have w5: "?w5 = (cos x) ^ 3 *\<^sub>H ba + - (3 * sin x * (cos x)\<^sup>2) *\<^sub>H e1 + - (3 * sin x * (cos x)\<^sup>2) *\<^sub>H e2 + - (3/4 * (cos x + 3 * cos (3 * x))) *\<^sub>H e12"
    by (simp add: w4 hypext_power_Hyperdual_parts sin_times_sin right_diff_distrib' cos_times_cos
              power2_eq_square distrib_left sin_times_cos divide_simps)

  let ?w6 = "?w3 + ?w5"
  have sqrt_pos: "Base ?w6 > 0"
      using s3_c3_gt_zero by auto
  have w6: "?w6 = (sin x ^ 3 + cos x ^ 3) *\<^sub>H ba +
                  (3 * cos x * sin x * (sin x - cos x)) *\<^sub>H e1 +
                  (3 * cos x * sin x * (sin x - cos x)) *\<^sub>H e2 +
                  - (3/4 * (sin x + cos x + 3 * cos (3 * x) - 3 * sin (3 * x))) *\<^sub>H e12"
    by (auto simp add: w3 w5 add_hyperdual_parts power2_eq_square right_diff_distrib' divide_simps)

  let ?w7 = "inverse ((*h* sqrt) ?w6)"
  have w7: "?w7 = inverse(sqrt(sin x ^ 3 + cos x ^ 3)) *\<^sub>H ba +
                  - ((3 * cos x * sin x * (sin x - cos x))/(2 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e1 +
                  - ((3 * cos x * sin x * (sin x - cos x))/(2 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e2 +
                  ((3 * (30 + 2 * cos (4 * x) - 41 * sin (2 * x) + 3 * sin (6 * x)))/(64 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)) *\<^sub>H e12"
    \<comment> \<open>Apply the functions in two steps, then simplify the result to match\<close>
  proof -
    let ?w7a = "(*h* sqrt) ?w6"
    have w7a: "?w7a =
      sqrt (sin x ^ 3 + cos x ^ 3) *\<^sub>H ba +
      ((3 * (cos x * (sin x * (sin x - cos x)))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / 2) *\<^sub>H e1 +
      ((3 * (cos x * (sin x * (sin x - cos x)))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / 2) *\<^sub>H e2 +
      (- ((3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / 8) +
       - 9 * (cos x * (sin x * ((sin x - cos x) * (cos x * (sin x * (sin x - cos x)))))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) / 4) *\<^sub>H e12"
      unfolding w6
      using sqrt_pos by (simp add: hypext_sqrt_hyperdual_parts mult.assoc)

    let ?w7b = "inverse ?w7a"
    have "?w7b =
      (1 / sqrt (sin x ^ 3 + cos x ^ 3)) *\<^sub>H ba +
      - (3 * (cos x * (sin x * (sin x - cos x))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / (2 * (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2)) *\<^sub>H e1 +
      - (3 * (cos x * (sin x * (sin x - cos x))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / (2 * (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2)) *\<^sub>H e2 +
      (9 * (cos x * (cos x * (sin x * (sin x * ((sin x - cos x) * ((sin x - cos x) * (inverse (sqrt (sin x ^ 3 + cos x ^ 3)) * inverse (sqrt (sin x ^ 3 + cos x ^ 3))))))))) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) -
        (- ((3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) / 8) -
        9 * (cos x * (sin x * ((sin x - cos x) * (cos x * (sin x * (sin x - cos x)))))) * inverse (sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) / 4) /
     (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2) *\<^sub>H e12"
      \<comment> \<open>Push the inverse in\<close>
      by (simp add: w7a inverse_hyperdual_parts)
    then have w7b: "?w7b =
      (inverse (sqrt (sin x ^ 3 + cos x ^ 3))) *\<^sub>H ba +
      - (3 * cos x * sin x * (sin x - cos x) / (2 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e1 +
      - (3 * cos x * sin x * (sin x - cos x) / (2 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e2 +
      (9 * cos x * cos x * sin x * sin x * ((sin x - cos x) * (sin x - cos x) / ((sqrt (sin x ^ 3 + cos x ^ 3)) ^ 2)) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) -
        (- ((3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3))) -
         9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3))
        / (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2) *\<^sub>H e12"
      \<comment> \<open>Simplify powers and parents\<close>
      by (simp add: power2_eq_square power3_eq_cube field_simps)

    have
      "9 * cos x * cos x * sin x * sin x * ((sin x - cos x) * (sin x - cos x)) / ((sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2 * (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)) -
       (- ((3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3))) -
          9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)) /
       (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2 =
       (90 + 6 * cos (4 * x) - 123 * sin (2 * x) + 9 * sin (6 * x)) / (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5)"
      \<comment> \<open>Equate the last component's coefficients\<close>
    proof -
      have
        "9 * cos x * cos x * sin x * sin x * ((sin x - cos x) * (sin x - cos x)) / ((sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2 * (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)) -
         (- ((3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3))) -
           9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)) /
         (sqrt (sin x ^ 3 + cos x ^ 3))\<^sup>2 =
         9 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) +
         ( (3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3)) +
           9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)) /
         (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 2"
          by (simp add: divide_simps)
      also have "... =
         9 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) +
         ( (3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3) +
           9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 2))"
        by (simp add: add_divide_distrib power2_eq_square power3_eq_cube mult.commute mult.left_commute)
      also have "... =
         9 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) +
         ( (3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3) +
           9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5))"
        by (simp add: mult.commute mult.left_commute)
      also have "... =
         9 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) +
         ( (3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) * (sin x ^ 3 + cos x ^ 3) / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5) +
           9 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x) / (4 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5))"
      proof -
        have "(sin x ^ 3 + cos x ^ 3) * inverse ((sqrt (sin x ^ 3 + cos x ^ 3)) ^ 2) = 1"
          using s3_c3_gt_zero by auto
        then have
          "1 / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3) =
           (sin x ^ 3 + cos x ^ 3) / ((sqrt (sin x ^ 3 + cos x ^ 3)) ^ 2) / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)"
          by (simp add: field_simps)
        then have
          "1 / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3) =
           (sin x ^ 3 + cos x ^ 3) / (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)"
          by auto
        then show ?thesis
          by (metis (mono_tags, lifting) divide_real_def inverse_eq_divide times_divide_eq_right)
      qed
      also have "... =
         ( 288 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) +
           (3 * sin x + 3 * cos x + 9 * cos (3 * x) - 9 * sin (3 * x)) * (sin x ^ 3 + cos x ^ 3) * 8 +
           144 * cos x * sin x * (sin x - cos x) * cos x * sin x * (sin x - cos x))
         / (64 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)"
        by (simp add: divide_simps)
      also have "... =
         ( 432 * cos x * cos x * sin x * sin x * (sin x - cos x) * (sin x - cos x) +
           (24 * sin x + 24 * cos x + 72 * cos (3 * x) - 72 * sin (3 * x)) * (sin x ^ 3 + cos x ^ 3))
         / (64 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)"
        by (simp add: divide_simps)
      finally show ?thesis
        \<comment> \<open>Having matched the denominators, prove the numerators equal\<close>
        by (simp, force intro:  disjI2 simp add: power2_eq_square power4_eq_xxxx power3_eq_cube cos_times_sin
            sin_times_cos cos_times_cos sin_times_sin right_diff_distrib power6 power5
            distrib_left distrib_right left_diff_distrib divide_simps)
    qed
    then show ?thesis
      \<comment> \<open>Put it all together\<close>
      by (simp add: w7b)
  qed

  let ?w8 = "?w1 * ?w7"
  have w8: "?w8 =
    ((exp x)/(sqrt(sin x ^ 3 + cos x ^ 3))) *\<^sub>H ba +
    ((exp x * (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x)))/(8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e1 +
    ((exp x * (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x)))/(8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)) *\<^sub>H e2 +
    ((exp x * (130 - 12 * cos (2 * x) + 30 * cos (4 * x) + 12 * cos (6 * x) - 111 * sin (2 * x) + 48 * sin (4 * x) +
               5 * sin (6 * x)))/(64 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 5)) *\<^sub>H e12"
  proof (auto simp add: w7 w1 times_hyperdual_parts)
    show "exp x * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) = exp x / sqrt (sin x ^ 3 + cos x ^ 3)"
      by (simp add: divide_inverse)

    have sqrt_sc3: "sqrt (sin x ^ 3 + cos x ^ 3) ^ 3 = (sin x ^ 3 + cos x ^ 3) * sqrt (sin x ^ 3 + cos x ^ 3)"
      using s3_c3_gt_zero
      by (simp add: power3_eq_cube)
    then have "inverse (sqrt (sin x ^ 3 + cos x ^ 3)) -
          (3 * cos x * sin x * (sin x - cos x)) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) =
          (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)"
      using sqrt_pos
      apply (simp add: right_diff_distrib' sin_times_sin cos_times_cos sin_times_cos cos_times_sin power3_eq_cube left_diff_distrib' divide_simps)
      by (simp add: distrib_right cos_times_cos)
    then show " exp x * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) -
           exp x * (3 * cos x * sin x * (sin x - cos x)) / (2 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3) =
          exp x * (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x)) / (8 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 3)"
      by (simp add: algebra_simps)

    have "sqrt (sin x ^ 3 + cos x ^ 3) ^ 8 =  (sin x ^ 3 + cos x ^ 3) ^ 4"
      using s3_c3_gt_zero
      by (smt mult_2 numeral_Bit0 power2_eq_square power_even_eq real_sqrt_mult_self)
    moreover have "sqrt (sin x ^ 3 + cos x ^ 3) ^ 5 =  (sin x ^ 3 + cos x ^ 3) ^ 2 * sqrt (sin x ^ 3 + cos x ^ 3)"
      by (simp add: mult.assoc power2_eq_square power5)
    ultimately
    have "(90 + 6 * cos (4 * x) - 123 * sin (2 * x) + 9 * sin (6 * x)) / (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) -
           3 * (cos x * ((sin x * (sin x - cos x)))) / sqrt (sin x ^ 3 + cos x ^ 3) ^ 3 +
           inverse (sqrt (sin x ^ 3 + cos x ^ 3)) =
           (130 - 12 * cos (2 * x) + 30 * cos (4 * x) + 12 * cos (6 * x) - 111 * sin (2 * x) + 48 * sin (4 * x) + 5 * sin (6 * x)) /
           (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5)"
      using sqrt_pos
      apply (simp add: sqrt_sc3 power2_eq_square divide_simps)
      by (simp add: distrib_right distrib_left power3_eq_cube sin_times_sin sin_times_cos
              cos_times_cos cos_times_sin right_diff_distrib' left_diff_distrib' divide_simps)
    moreover have "\<forall>r a b c. (a::real) * b - c * (a * r) = a * (b - c * r)"
      by (simp add: right_diff_distrib)
    ultimately show "exp x * (90 + 6 * cos (4 * x) - 123 * sin (2 * x) + 9 * sin (6 * x)) / (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5) -
               3 * (cos x * (exp x * (sin x * (sin x - cos x)))) / sqrt (sin x ^ 3 + cos x ^ 3) ^ 3 +
              exp x * inverse (sqrt (sin x ^ 3 + cos x ^ 3)) =
              exp x *
              (130 - 12 * cos (2 * x) + 30 * cos (4 * x) + 12 * cos (6 * x) - 111 * sin (2 * x) + 48 * sin (4 * x) + 5 * sin (6 * x)) /
              (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5)"
      by (metis (mono_tags, opaque_lifting) distrib_left mult.left_commute times_divide_eq_right)
  qed

  \<comment> \<open>Check that we have indeed computed the hyperdual extension of our analytic test function \<close>
  moreover have w8_eq_hyp_fa_test: "?w8 = (*h* fa_test) (\<beta> x)"
    using assms
    by (simp add: hyp_divide_inverse hyp_fa_test_def hypext_fa_test hypext_power)

  \<comment> \<open>Now simply show that "extraction" of first and second derivatives are as expected\<close>
  ultimately
  show "First (autodiff fa_test x) =
          (exp x * (3 * cos x + 5 * cos (3 * x) + 9 * sin x + sin (3 * x))) /
            (8 * (sqrt (sin x ^ 3 + cos x ^ 3)) ^ 3)"
  and
    "Second (autodiff fa_test x) =
        exp x * (130 - 12 * cos (2 * x) +
                  30 * cos (4 * x) + 12 * cos (6 * x) -
                   111 * sin (2 * x) + 48 * sin (4 * x) + 5 * sin (6 * x)) /
       (64 * sqrt (sin x ^ 3 + cos x ^ 3) ^ 5)"
    by (metis autodiff_sel hyperdual_comb_sel)+
qed

end
