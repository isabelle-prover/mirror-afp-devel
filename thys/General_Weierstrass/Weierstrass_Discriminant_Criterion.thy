theory Weierstrass_Discriminant_Criterion
  imports
    Weierstrass_Singularities
    "HOL-Algebra.Algebraic_Closure_Type"
begin

section \<open>Elimination identities\<close>

lemma four_discriminant_bezout:
  "4 * discriminant W =
    - (b2 W ^ 3 + 6 * b2 W ^ 2 * x - 30 * b2 W * b4 W -
        144 * b4 W * x + 108 * b6 W) * weierstrass_g W x +
      (b2 W ^ 3 * x + b2 W ^ 2 * b4 W + 4 * b2 W ^ 2 * x ^ 2 -
        28 * b2 W * b4 W * x + 6 * b2 W * b6 W -
        32 * b4 W ^ 2 - 96 * b4 W * x ^ 2 + 72 * b6 W * x) *
        weierstrass_h W x"
proof -
  note expanded = four_discriminant_expanded[of W]
  show ?thesis
    unfolding weierstrass_g_def weierstrass_h_def
    using expanded
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

lemma singular_affine_imp_g_zero:
  assumes "singular_affine_point W x y"
  shows "weierstrass_g W x = 0"
proof -
  from assms have F: "weierstrass_affine_poly W x y = 0"
    and dy: "weierstrass_affine_dy W x y = 0"
    by (simp_all add: singular_affine_point_def)
  note identity = affine_dy_squared_minus_g[of W x y]
  with F dy show ?thesis
    by simp
qed

lemma singular_affine_imp_h_zero:
  assumes "singular_affine_point W x y"
  shows "weierstrass_h W x = 0"
proof -
  from assms have dx: "weierstrass_affine_dx W x y = 0"
    and dy: "weierstrass_affine_dy W x y = 0"
    by (simp_all add: singular_affine_point_def)
  note identity = two_affine_dx_minus_a1_dy[of W x y]
  with dx dy show ?thesis
    by simp
qed

lemma twice_negative_half:
  fixes z :: "'a::field"
  assumes "(2 :: 'a) \<noteq> 0"
  shows "2 * (- z / 2) + z = 0"
  using assms by simp

lemma four_ne_zero_of_two_ne_zero:
  fixes dummy :: "'a::field"
  assumes two: "(2 :: 'a) \<noteq> 0"
  shows "(4 :: 'a) \<noteq> 0"
proof
  assume four: "(4 :: 'a) = 0"
  have product: "(2 :: 'a) * 2 = 0"
  proof -
    have "(2 :: 'a) * 2 = 4"
      by simp
    also have "... = 0"
      by (rule four)
    finally show ?thesis .
  qed
  have "(2 :: 'a) = 0 \<or> (2 :: 'a) = 0"
    using product by (simp only: mult_eq_0_iff)
  with two show False
    by blast
qed

lemma affine_singular_of_g_h:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes two: "(2 :: 'a) \<noteq> 0"
    and g: "weierstrass_g W x = 0"
    and h: "weierstrass_h W x = 0"
  shows "singular_affine_point W x (- (a1 W * x + a3 W) / 2)"
proof -
  let ?y = "- (a1 W * x + a3 W) / 2"
  have dy: "weierstrass_affine_dy W x ?y = 0"
    using twice_negative_half[OF two, of "a1 W * x + a3 W"]
    by (simp only: weierstrass_affine_dy_def add.assoc)
  have four: "(4 :: 'a) \<noteq> 0"
    by (rule four_ne_zero_of_two_ne_zero[OF two])
  note F_identity = affine_dy_squared_minus_g[of W x ?y]
  have F: "weierstrass_affine_poly W x ?y = 0"
    using F_identity dy g four by simp
  note dx_identity = two_affine_dx_minus_a1_dy[of W x ?y]
  have dx: "weierstrass_affine_dx W x ?y = 0"
    using dx_identity dy h two by simp
  show ?thesis
    unfolding singular_affine_point_def
    using F dx dy by blast
qed

lemma singular_affine_imp_discriminant_zero_odd:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes two: "(2 :: 'a) \<noteq> 0"
    and singular: "singular_affine_point W x y"
  shows "discriminant W = 0"
proof -
  have g: "weierstrass_g W x = 0"
    using singular by (rule singular_affine_imp_g_zero)
  have h: "weierstrass_h W x = 0"
    using singular by (rule singular_affine_imp_h_zero)
  have four: "(4 :: 'a) \<noteq> 0"
    by (rule four_ne_zero_of_two_ne_zero[OF two])
  have "4 * discriminant W = 0"
    using four_discriminant_bezout[of W x] g h by simp
  with four show ?thesis
    by simp
qed

section \<open>Characteristic two\<close>

lemma char_two_three:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "(3 :: 'a) = 1"
proof -
  have "(3 :: 'a) = 2 + 1"
    by simp
  also have "\<dots> = 1"
    by (simp add: two)
  finally show ?thesis .
qed

lemma char_two_four:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "(4 :: 'a) = 0"
proof -
  have "(4 :: 'a) = 2 + 2"
    by simp
  also have "\<dots> = 0"
    by (simp add: two)
  finally show ?thesis .
qed

lemma char_two_eight:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "(8 :: 'a) = 0"
proof -
  have "(8 :: 'a) = 4 + 4"
    by simp
  also have "\<dots> = 0"
    by (simp add: char_two_four[OF two])
  finally show ?thesis .
qed

lemma char_two_nine:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "(9 :: 'a) = 1"
proof -
  have "(9 :: 'a) = 8 + 1"
    by simp
  also have "\<dots> = 1"
    by (simp add: char_two_eight[OF two])
  finally show ?thesis .
qed

lemma char_two_twenty_seven:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "(27 :: 'a) = 1"
proof -
  have "(27 :: 'a) = 2 * 13 + 1"
    by simp
  also have "\<dots> = 1"
    by (simp add: two)
  finally show ?thesis .
qed

lemma char_two_neg:
  fixes x :: "'a::comm_ring_1"
  assumes two: "(2 :: 'a) = 0"
  shows "- x = x"
proof -
  have "x + x = 2 * x"
    by (simp add: algebra_simps)
  also have "\<dots> = 0"
    by (simp add: two)
  finally show ?thesis
    by (simp only: neg_eq_iff_add_eq_0)
qed

lemma b2_char_two:
  fixes W :: "'a::comm_ring_1 weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
  shows "b2 W = a1 W ^ 2"
  by (simp add: b2_def char_two_four[OF two])

lemma b4_char_two:
  fixes W :: "'a::comm_ring_1 weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
  shows "b4 W = a1 W * a3 W"
  by (simp add: b4_def two)

lemma b6_char_two:
  fixes W :: "'a::comm_ring_1 weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
  shows "b6 W = a3 W ^ 2"
  by (simp add: b6_def char_two_four[OF two])

lemma b8_char_two:
  fixes W :: "'a::comm_ring_1 weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
  shows "b8 W =
    a1 W ^ 2 * a6 W + a1 W * a3 W * a4 W +
      a2 W * a3 W ^ 2 + a4 W ^ 2"
  by (simp add: b8_def char_two_four[OF two] char_two_neg[OF two])

lemma discriminant_char_two_expanded:
  fixes W :: "'a::comm_ring_1 weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
  shows "discriminant W =
    a1 W ^ 6 * a6 W + a1 W ^ 5 * a3 W * a4 W +
      a1 W ^ 4 * a2 W * a3 W ^ 2 + a1 W ^ 4 * a4 W ^ 2 +
      a3 W ^ 4 + a1 W ^ 3 * a3 W ^ 3"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  have power_five: "\<And>x :: 'a. x ^ 5 = x * x ^ 4"
  proof -
    fix x :: 'a
    have "x ^ Suc 4 = x * x ^ 4"
      by (rule power_Suc)
    then show "x ^ 5 = x * x ^ 4"
      by simp
  qed
  have power_four: "\<And>x :: 'a. x ^ 4 = x * x * x * x"
  proof -
    fix x :: 'a
    have "x ^ Suc 3 = x * x ^ 3"
      by (rule power_Suc)
    then show "x ^ 4 = x * x * x * x"
      by (simp add: power3_eq_cube)
  qed
  have power_six: "\<And>x :: 'a. x ^ 6 = x * x * x * x * x * x"
  proof -
    fix x :: 'a
    have "x ^ Suc 5 = x * x ^ 5"
      by (rule power_Suc)
    then show "x ^ 6 = x * x * x * x * x * x"
      by (simp add: power_five power_four)
  qed
  have reduced:
    "discriminant W =
      (a1 W ^ 2) ^ 2 * b8 W + (a3 W ^ 2) ^ 2 +
        a1 W ^ 2 * (a1 W * a3 W) * a3 W ^ 2"
    unfolding discriminant_def
    apply (simp add: b2_char_two[OF two] b4_char_two[OF two]
        b6_char_two[OF two] char_two_eight[OF two]
        char_two_nine[OF two] char_two_twenty_seven[OF two]
        char_two_neg[OF two] algebra_simps)
    using two
    apply simp
    done
  show ?thesis
  proof (rule trans)
    show "discriminant W =
        (a1 W ^ 2) ^ 2 * b8 W + (a3 W ^ 2) ^ 2 +
          a1 W ^ 2 * (a1 W * a3 W) * a3 W ^ 2"
      by (rule reduced)
    show "(a1 W ^ 2) ^ 2 * b8 W + (a3 W ^ 2) ^ 2 +
          a1 W ^ 2 * (a1 W * a3 W) * a3 W ^ 2 =
        a1 W ^ 6 * a6 W + a1 W ^ 5 * a3 W * a4 W +
          a1 W ^ 4 * a2 W * a3 W ^ 2 + a1 W ^ 4 * a4 W ^ 2 +
          a3 W ^ 4 + a1 W ^ 3 * a3 W ^ 3"
      apply (subst b8_char_two[OF two, of W])
      unfolding W
      by (simp add: power_four power_five power_six
          power2_eq_square power3_eq_cube algebra_simps)
  qed
qed

lemma discriminant_char_two_a1_zero:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
    and a1: "a1 W = 0"
  shows "discriminant W = a3 W ^ 4"
proof -
  show ?thesis
    using discriminant_char_two_expanded[OF two, of W] a1
    by simp
qed

lemma scaled_power_eq:
  fixes q x n :: "'a::comm_semiring_1"
  assumes "q * x = n"
  shows "q ^ k * x ^ k = n ^ k"
proof -
  have "(q * x) ^ k = n ^ k"
    using assms by simp
  then show ?thesis
    by (simp only: power_mult_distrib)
qed

lemma scale_linear_six:
  fixes a c x :: "'a::comm_ring_1"
  shows "a ^ 6 * (c * x) = a ^ 5 * c * (a * x)"
  by (simp add: power_numeral_reduce algebra_simps)

lemma diff_rearrange:
  fixes a x y c :: "'a::comm_ring_1"
  assumes "a * y - x ^ 2 - c = 0"
  shows "y * a = x ^ 2 + c"
proof -
  have "a * y = x ^ 2 + c"
  proof -
    from assms have "a * y - (x ^ 2 + c) = 0"
      by (subst diff_diff_add [symmetric])
    then show ?thesis
      by (rule iffD2 [OF eq_iff_diff_eq_0])
  qed
  then show ?thesis
    by (subst mult.commute)
qed

lemma char_two_affine_certificate_raw:
  fixes A1 A2 A3 A4 A6 :: "'a::field"
  assumes two: "(2 :: 'a) = 0"
    and A1: "A1 \<noteq> 0"
  shows "A1 ^ 6 *
      (((((A3 / A1) ^ 2 + A4) / A1) ^ 2 +
        A1 * (A3 / A1) * (((A3 / A1) ^ 2 + A4) / A1) +
        A3 * (((A3 / A1) ^ 2 + A4) / A1)) -
        ((A3 / A1) ^ 3 + A2 * (A3 / A1) ^ 2 +
          A4 * (A3 / A1) + A6)) =
    A1 ^ 6 * A6 + A1 ^ 5 * A3 * A4 +
      A1 ^ 4 * A2 * A3 ^ 2 + A1 ^ 4 * A4 ^ 2 +
      A3 ^ 4 + A1 ^ 3 * A3 ^ 3"
proof -
  let ?x = "A3 / A1"
  let ?y = "(?x ^ 2 + A4) / A1"
  have ax: "A1 * ?x = A3"
    using A1 by simp
  have ay: "A1 * ?y = ?x ^ 2 + A4"
    using A1 by simp
  have ax2: "A1 ^ 2 * ?x ^ 2 = A3 ^ 2"
    by (rule scaled_power_eq[OF ax])
  have ax3: "A1 ^ 3 * ?x ^ 3 = A3 ^ 3"
    by (rule scaled_power_eq[OF ax])
  have ax4: "A1 ^ 4 * ?x ^ 4 = A3 ^ 4"
    by (rule scaled_power_eq[OF ax])
  have ay2: "A1 ^ 2 * ?y ^ 2 = (?x ^ 2 + A4) ^ 2"
    by (rule scaled_power_eq[OF ay])
  have square_sum: "(?x ^ 2 + A4) ^ 2 = ?x ^ 4 + A4 ^ 2"
    using two by (simp add: power2_sum power_mult)
  have yscale:
      "A1 ^ 6 * ?y ^ 2 = A3 ^ 4 + A1 ^ 4 * A4 ^ 2"
  proof -
    have "A1 ^ 6 * ?y ^ 2 = A1 ^ 4 * (A1 ^ 2 * ?y ^ 2)"
      by (simp add: power_Suc algebra_simps)
    also have "... = A1 ^ 4 * (?x ^ 2 + A4) ^ 2"
      using ay2 by simp
    also have "... = A1 ^ 4 * (?x ^ 4 + A4 ^ 2)"
      by (simp only: square_sum)
    also have "... = A3 ^ 4 + A1 ^ 4 * A4 ^ 2"
      using ax4 by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have cross:
      "A1 ^ 6 * (A1 * ?x * ?y + A3 * ?y) = 0"
  proof -
    have "A1 * ?x * ?y + A3 * ?y = A3 * ?y + A3 * ?y"
      using ax by simp
    also have "... = 2 * (A3 * ?y)"
      by (simp add: algebra_simps)
    also have "... = 0"
      using two by simp
    finally show ?thesis
      by simp
  qed
  have xcube:
      "A1 ^ 6 * ?x ^ 3 = A1 ^ 3 * A3 ^ 3"
  proof -
    have "A1 ^ 6 * ?x ^ 3 = A1 ^ 3 * (A1 ^ 3 * ?x ^ 3)"
      by (simp add: power_Suc algebra_simps)
    also have "... = A1 ^ 3 * A3 ^ 3"
      using ax3 by simp
    finally show ?thesis .
  qed
  have xsquare:
      "A1 ^ 6 * (A2 * ?x ^ 2) = A1 ^ 4 * A2 * A3 ^ 2"
  proof -
    have "A1 ^ 6 * (A2 * ?x ^ 2) =
        A1 ^ 4 * A2 * (A1 ^ 2 * ?x ^ 2)"
      by (simp add: power_Suc algebra_simps)
    also have "... = A1 ^ 4 * A2 * A3 ^ 2"
      using ax2 by simp
    finally show ?thesis .
  qed
  have xlinear:
      "A1 ^ 6 * (A4 * ?x) = A1 ^ 5 * A3 * A4"
  proof -
    have "A1 ^ 6 * (A4 * ?x) = A1 ^ 5 * A4 * (A1 * ?x)"
      by (rule scale_linear_six)
    also have "... = A1 ^ 5 * A3 * A4"
      using ax by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "A1 ^ 6 *
      (((?y ^ 2 + A1 * ?x * ?y + A3 * ?y) -
        (?x ^ 3 + A2 * ?x ^ 2 + A4 * ?x + A6))) =
      A1 ^ 6 * ?y ^ 2 +
        A1 ^ 6 * (A1 * ?x * ?y + A3 * ?y) -
        (A1 ^ 6 * ?x ^ 3 + A1 ^ 6 * (A2 * ?x ^ 2) +
          A1 ^ 6 * (A4 * ?x) + A1 ^ 6 * A6)"
    by (simp add: algebra_simps)
  also have "... = (A3 ^ 4 + A1 ^ 4 * A4 ^ 2) -
      (A1 ^ 3 * A3 ^ 3 + A1 ^ 4 * A2 * A3 ^ 2 +
        A1 ^ 5 * A3 * A4 + A1 ^ 6 * A6)"
    by (simp only: yscale cross xcube xsquare xlinear add_0_right)
  also have "... = A1 ^ 6 * A6 + A1 ^ 5 * A3 * A4 +
      A1 ^ 4 * A2 * A3 ^ 2 + A1 ^ 4 * A4 ^ 2 +
      A3 ^ 4 + A1 ^ 3 * A3 ^ 3"
    using two
    by (simp add: char_two_neg[OF two] algebra_simps)
  finally show ?thesis .
qed

lemma discriminant_char_two_certificate:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
    and a1: "a1 W \<noteq> 0"
  shows "a1 W ^ 6 *
      weierstrass_affine_poly W (a3 W / a1 W)
        (((a3 W / a1 W) ^ 2 + a4 W) / a1 W) =
    discriminant W"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  have A1: "A1 \<noteq> 0"
    using a1 unfolding W by simp
  note raw = char_two_affine_certificate_raw[OF two A1]
  have polynomial:
    "a1 W ^ 6 *
        weierstrass_affine_poly W (a3 W / a1 W)
          (((a3 W / a1 W) ^ 2 + a4 W) / a1 W) =
      a1 W ^ 6 * a6 W + a1 W ^ 5 * a3 W * a4 W +
        a1 W ^ 4 * a2 W * a3 W ^ 2 + a1 W ^ 4 * a4 W ^ 2 +
        a3 W ^ 4 + a1 W ^ 3 * a3 W ^ 3"
    unfolding W weierstrass_affine_poly_def
    using raw by simp
  show ?thesis
    using polynomial discriminant_char_two_expanded[OF two, of W]
    by simp
qed

lemma singular_affine_imp_discriminant_zero_char_two:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
    and singular: "singular_affine_point W x y"
  shows "discriminant W = 0"
proof (cases "a1 W = 0")
  case True
  from singular have dy: "weierstrass_affine_dy W x y = 0"
    by (simp add: singular_affine_point_def)
  have a3: "a3 W = 0"
    using dy two True
    unfolding weierstrass_affine_dy_def
    by simp
  show ?thesis
    using discriminant_char_two_a1_zero[OF two True] a3 by simp
next
  case False
  from singular have F: "weierstrass_affine_poly W x y = 0"
    and dx: "weierstrass_affine_dx W x y = 0"
    and dy: "weierstrass_affine_dy W x y = 0"
    by (simp_all add: singular_affine_point_def)
  have invA1: "a1 W * inverse (a1 W) = 1"
    using False by simp
  have dy': "a1 W * x = a3 W"
    using dy
    by (simp add: weierstrass_affine_dy_def two add_eq_0_iff2
        char_two_neg[OF two])
  have x: "x = a3 W / a1 W"
  proof (rule eq_divide_imp[OF False])
    show "x * a1 W = a3 W"
      using dy' by (simp only: mult.commute)
  qed
  have three: "(3 :: 'a) = 1"
    using char_two_three[OF two] .
  have dx':
    "a1 W * y - x ^ 2 - a4 W = 0"
    using dx
    by (simp add: weierstrass_affine_dx_def two three)
  have ay: "y * a1 W = x ^ 2 + a4 W"
    by (rule diff_rearrange[OF dx'])
  have y: "y = ((a3 W / a1 W) ^ 2 + a4 W) / a1 W"
    unfolding x
  proof (rule eq_divide_imp[OF False])
    show "y * a1 W = (a3 W / a1 W) ^ 2 + a4 W"
      using ay unfolding x .
  qed
  note certificate = discriminant_char_two_certificate[OF two False]
  show ?thesis
    using certificate F
    unfolding x y
    by simp
qed

lemma discriminant_zero_imp_affine_singular_char_two:
  fixes W :: "'a::alg_closed_field weierstrass_coeffs"
  assumes two: "(2 :: 'a) = 0"
    and delta: "discriminant W = 0"
  shows "\<exists>x y. singular_affine_point W x y"
proof (cases "a1 W = 0")
  case False
  let ?x = "a3 W / a1 W"
  let ?y = "((a3 W / a1 W) ^ 2 + a4 W) / a1 W"
  have invA1: "a1 W * inverse (a1 W) = 1"
    using False by simp
  have three: "(3 :: 'a) = 1"
    using char_two_three[OF two] .
  note certificate = discriminant_char_two_certificate[OF two False]
  have F: "weierstrass_affine_poly W ?x ?y = 0"
    using certificate delta False by simp
  have ax: "a1 W * ?x = a3 W"
    using False by (simp add: mult.commute)
  have ay: "a1 W * ?y = ?x ^ 2 + a4 W"
    using False by (simp add: mult.commute)
  have dx: "weierstrass_affine_dx W ?x ?y = 0"
    using ay
    by (simp add: weierstrass_affine_dx_def two three
        char_two_neg[OF two])
  have dy: "weierstrass_affine_dy W ?x ?y = 0"
    using ax
    by (simp add: weierstrass_affine_dy_def two char_two_neg[OF two])
  show ?thesis
    unfolding singular_affine_point_def
    using F dx dy by blast
next
  case True
  have a3pow: "a3 W ^ 4 = 0"
    using discriminant_char_two_a1_zero[OF two True] delta by simp
  then have a3: "a3 W = 0"
    by simp
  obtain x where x: "x ^ 2 = a4 W"
    using nth_root_exists[of 2 "a4 W"] by auto
  obtain y where y:
      "y ^ 2 = x ^ 3 + a2 W * x ^ 2 + a4 W * x + a6 W"
    using nth_root_exists[of 2
      "x ^ 3 + a2 W * x ^ 2 + a4 W * x + a6 W"] by auto
  have F: "weierstrass_affine_poly W x y = 0"
    unfolding weierstrass_affine_poly_def
    using True a3 y by simp
  have dx: "weierstrass_affine_dx W x y = 0"
    unfolding weierstrass_affine_dx_def
    using True x
    by (simp add: two char_two_three[OF two] char_two_neg[OF two])
  have dy: "weierstrass_affine_dy W x y = 0"
    unfolding weierstrass_affine_dy_def
    by (simp add: two True a3)
  show ?thesis
    unfolding singular_affine_point_def
    using F dx dy by blast
qed

section \<open>Odd characteristic\<close>

lemma scale_quadratic:
  fixes q x b c :: "'a::comm_ring_1"
  shows "q ^ 2 * (6 * x ^ 2 + b * x + c) =
    6 * (q ^ 2 * x ^ 2) + b * q * (q * x) + c * q ^ 2"
  by (simp add: power2_eq_square algebra_simps)

lemma c4_h_n_square:
  fixes b c d :: "'a::comm_ring_1"
  shows "(18 * d - b * c) ^ 2 =
    324 * d ^ 2 - 36 * b * c * d + b ^ 2 * c ^ 2"
  by (simp add: power2_eq_square algebra_simps)

lemma c4_h_q_square:
  fixes b c :: "'a::comm_ring_1"
  shows "(b ^ 2 - 24 * c) ^ 2 =
    b ^ 4 - 48 * b ^ 2 * c + 576 * c ^ 2"
  by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)

lemma c4_h_middle:
  fixes b c d :: "'a::comm_ring_1"
  shows "b * (b ^ 2 - 24 * c) * (18 * d - b * c) =
    18 * b ^ 3 * d - b ^ 4 * c - 432 * b * c * d +
      24 * b ^ 2 * c ^ 2"
  by (simp add: power2_eq_square power3_eq_cube power4_eq_xxxx
      algebra_simps)

lemma c4_h_polynomial:
  fixes b c d :: "'a::comm_ring_1"
  shows "6 * (18 * d - b * c) ^ 2 +
      b * (b ^ 2 - 24 * c) * (18 * d - b * c) +
      c * (b ^ 2 - 24 * c) ^ 2 =
    18 * (b ^ 3 * d - b ^ 2 * c ^ 2 - 36 * b * c * d +
      32 * c ^ 3 + 108 * d ^ 2)"
proof -
  note n2 = c4_h_n_square[of d b c]
  note q2 = c4_h_q_square[of b c]
  note middle = c4_h_middle[of b c d]
  show ?thesis
    apply (subst n2)
    apply (subst middle)
    apply (subst q2)
    by (simp add: power2_eq_square power3_eq_cube algebra_simps)
qed

lemma c4_candidate_h_raw:
  fixes b c d :: "'a::field"
  assumes "b ^ 2 - 24 * c \<noteq> 0"
  shows "(b ^ 2 - 24 * c) ^ 2 *
      (6 * ((18 * d - b * c) / (b ^ 2 - 24 * c)) ^ 2 +
        b * ((18 * d - b * c) / (b ^ 2 - 24 * c)) + c) =
    18 * (b ^ 3 * d - b ^ 2 * c ^ 2 - 36 * b * c * d +
      32 * c ^ 3 + 108 * d ^ 2)"
proof -
  let ?q = "b ^ 2 - 24 * c"
  let ?n = "18 * d - b * c"
  let ?x = "?n / ?q"
  have qx: "?q * ?x = ?n"
    using assms by simp
  have q2x2: "?q ^ 2 * ?x ^ 2 = ?n ^ 2"
    by (rule scaled_power_eq[OF qx])
  have "?q ^ 2 * (6 * ?x ^ 2 + b * ?x + c) =
      6 * (?q ^ 2 * ?x ^ 2) + b * ?q * (?q * ?x) + c * ?q ^ 2"
    by (rule scale_quadratic)
  also have "... = 6 * ?n ^ 2 + b * ?q * ?n + c * ?q ^ 2"
    using qx q2x2 by simp
  also have "... = 18 * (b ^ 3 * d - b ^ 2 * c ^ 2 -
      36 * b * c * d + 32 * c ^ 3 + 108 * d ^ 2)"
    by (rule c4_h_polynomial)
  finally show ?thesis .
qed

lemma c4_candidate_h_certificate:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes c4: "c4 W \<noteq> 0"
  shows "c4 W ^ 2 *
      weierstrass_h W ((18 * b6 W - b2 W * b4 W) / c4 W) =
    -72 * discriminant W"
proof -
  note raw = c4_candidate_h_raw[
    OF c4[unfolded c4_def], of "b6 W"]
  note expanded = four_discriminant_expanded[of W]
  have E:
    "b2 W ^ 3 * b6 W - b2 W ^ 2 * b4 W ^ 2 -
        36 * b2 W * b4 W * b6 W + 32 * b4 W ^ 3 +
        108 * b6 W ^ 2 =
      - (4 * discriminant W)"
    by (simp only: expanded; simp add: algebra_simps)
  show ?thesis
    unfolding c4_def weierstrass_h_def
  proof (rule trans)
    show "(b2 W ^ 2 - 24 * b4 W) ^ 2 *
        (6 * ((18 * b6 W - b2 W * b4 W) /
            (b2 W ^ 2 - 24 * b4 W)) ^ 2 +
          b2 W * ((18 * b6 W - b2 W * b4 W) /
            (b2 W ^ 2 - 24 * b4 W)) +
          b4 W) =
        18 * (b2 W ^ 3 * b6 W - b2 W ^ 2 * b4 W ^ 2 -
          36 * b2 W * b4 W * b6 W + 32 * b4 W ^ 3 +
          108 * b6 W ^ 2)"
      by (rule raw)
    show "18 * (b2 W ^ 3 * b6 W - b2 W ^ 2 * b4 W ^ 2 -
          36 * b2 W * b4 W * b6 W + 32 * b4 W ^ 3 +
          108 * b6 W ^ 2) =
        -72 * discriminant W"
      apply (subst E)
      by (simp add: algebra_simps)
  qed
qed

lemma bezout_coefficient_rearrange:
  fixes b c d x :: "'a::comm_ring_1"
  shows "b ^ 3 + 6 * b ^ 2 * x - 30 * b * c -
      144 * c * x + 108 * d =
    b ^ 3 - 30 * b * c + 108 * d + 6 * ((b ^ 2 - 24 * c) * x)"
proof -
  have x_terms:
      "6 * b ^ 2 * x - 144 * c * x = 6 * ((b ^ 2 - 24 * c) * x)"
    by (simp only: right_diff_distrib left_diff_distrib;
        simp add: algebra_simps)
  have "b ^ 3 + 6 * b ^ 2 * x - 30 * b * c -
      144 * c * x + 108 * d =
      b ^ 3 - 30 * b * c + 108 * d +
        (6 * b ^ 2 * x - 144 * c * x)"
    by (simp only: diff_conv_add_uminus; simp add: ac_simps)
  also have "... = b ^ 3 - 30 * b * c + 108 * d +
      6 * ((b ^ 2 - 24 * c) * x)"
    by (simp only: x_terms)
  finally show ?thesis .
qed

lemma c4_candidate_bezout_coefficient:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes c4: "c4 W \<noteq> 0"
  shows "b2 W ^ 3 +
      6 * b2 W ^ 2 * ((18 * b6 W - b2 W * b4 W) / c4 W) -
      30 * b2 W * b4 W -
      144 * b4 W * ((18 * b6 W - b2 W * b4 W) / c4 W) +
      108 * b6 W =
    - c6 W"
proof -
  let ?q = "b2 W ^ 2 - 24 * b4 W"
  let ?n = "18 * b6 W - b2 W * b4 W"
  let ?x = "?n / ?q"
  have q: "?q \<noteq> 0"
    using c4 unfolding c4_def .
  have qx: "?q * ?x = ?n"
    using q by simp
  have "b2 W ^ 3 + 6 * b2 W ^ 2 * ?x -
      30 * b2 W * b4 W - 144 * b4 W * ?x + 108 * b6 W =
      b2 W ^ 3 - 30 * b2 W * b4 W + 108 * b6 W +
        6 * (?q * ?x)"
    by (rule bezout_coefficient_rearrange)
  also have "... = b2 W ^ 3 - 30 * b2 W * b4 W +
      108 * b6 W + 6 * ?n"
    by (simp only: qx)
  also have "... = - c6 W"
    unfolding c6_def
    by (simp add: algebra_simps)
  finally show ?thesis
    unfolding c4_def .
qed

lemma c4_candidate_g_from_h_delta:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes c4: "c4 W \<noteq> 0"
    and delta: "discriminant W = 0"
    and h: "weierstrass_h W
      ((18 * b6 W - b2 W * b4 W) / c4 W) = 0"
  shows "weierstrass_g W
    ((18 * b6 W - b2 W * b4 W) / c4 W) = 0"
proof -
  let ?x = "(18 * b6 W - b2 W * b4 W) / c4 W"
  have c6: "c6 W \<noteq> 0"
  proof
    assume "c6 W = 0"
    with c4_c6_discriminant_identity[of W] delta
    have "c4 W ^ 3 = 0"
      by simp
    with c4 show False
      by simp
  qed
  note coefficient = c4_candidate_bezout_coefficient[OF c4]
  note bezout = four_discriminant_bezout[of W ?x]
  have reduced:
      "0 = -
        (b2 W ^ 3 + 6 * b2 W ^ 2 * ?x -
          30 * b2 W * b4 W - 144 * b4 W * ?x + 108 * b6 W) *
        weierstrass_g W ?x"
  proof -
    have "0 = 4 * discriminant W"
      using delta by simp
    also have "... = -
        (b2 W ^ 3 + 6 * b2 W ^ 2 * ?x -
          30 * b2 W * b4 W - 144 * b4 W * ?x + 108 * b6 W) *
        weierstrass_g W ?x +
        (b2 W ^ 3 * ?x + b2 W ^ 2 * b4 W +
          4 * b2 W ^ 2 * ?x ^ 2 - 28 * b2 W * b4 W * ?x +
          6 * b2 W * b6 W - 32 * b4 W ^ 2 -
          96 * b4 W * ?x ^ 2 + 72 * b6 W * ?x) *
        weierstrass_h W ?x"
      by (rule bezout)
    also have "... = -
        (b2 W ^ 3 + 6 * b2 W ^ 2 * ?x -
          30 * b2 W * b4 W - 144 * b4 W * ?x + 108 * b6 W) *
        weierstrass_g W ?x"
      by (simp only: h mult_zero_right add_0_right)
    finally show ?thesis .
  qed
  have "0 = c6 W * weierstrass_g W ?x"
    using reduced
    by (simp only: coefficient minus_minus)
  with c6 show ?thesis
    by simp
qed

lemma square_twelve_scale:
  fixes b x :: "'a::comm_ring_1"
  shows "144 * b * x ^ 2 = b * (12 * x) ^ 2"
  by (simp add: power2_eq_square algebra_simps)

lemma zero_h_rearrange:
  fixes x b c :: "'a::comm_ring_1"
  shows "24 * (6 * x ^ 2 + b * x + c) =
    (12 * x) ^ 2 + 2 * b * (12 * x) + 24 * c"
  by (simp add: power2_eq_square algebra_simps)

lemma zero_g_rearrange:
  fixes x b c d :: "'a::comm_ring_1"
  shows "216 * (4 * x ^ 3 + b * x ^ 2 + 2 * c * x + d) =
    72 * x ^ 2 * (12 * x + 3 * b) +
      36 * c * (12 * x) + 216 * d"
  by (simp add: power2_eq_square power3_eq_cube algebra_simps)

lemma zero_c_invariant_h_raw:
  fixes b c :: "'a::field"
  assumes "(12 :: 'a) \<noteq> 0"
  shows "24 * (6 * (- b / 12) ^ 2 + b * (- b / 12) + c) =
    - (b ^ 2 - 24 * c)"
proof -
  let ?x = "- b / 12"
  have qx: "12 * ?x = - b"
    using assms by simp
  have "24 * (6 * ?x ^ 2 + b * ?x + c) =
      (12 * ?x) ^ 2 + 2 * b * (12 * ?x) + 24 * c"
    by (rule zero_h_rearrange)
  also have "... = - (b ^ 2 - 24 * c)"
    using qx by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

lemma zero_c_invariant_g_raw:
  fixes b c d :: "'a::field"
  assumes "(12 :: 'a) \<noteq> 0"
  shows "216 * (4 * (- b / 12) ^ 3 + b * (- b / 12) ^ 2 +
      2 * c * (- b / 12) + d) =
    b ^ 3 - 36 * b * c + 216 * d"
proof -
  let ?x = "- b / 12"
  have qx: "12 * ?x = - b"
    using assms by simp
  have qx2: "(12 * ?x) ^ 2 = (- b) ^ 2"
    using qx by simp
  have "216 * (4 * ?x ^ 3 + b * ?x ^ 2 + 2 * c * ?x + d) =
      72 * ?x ^ 2 * (12 * ?x + 3 * b) +
        36 * c * (12 * ?x) + 216 * d"
    by (rule zero_g_rearrange)
  also have "... = 144 * b * ?x ^ 2 - 36 * b * c + 216 * d"
    using qx by (simp add: algebra_simps)
  also have "... = b * (12 * ?x) ^ 2 - 36 * b * c + 216 * d"
    by (simp only: square_twelve_scale)
  also have "... = b * (- b) ^ 2 - 36 * b * c + 216 * d"
    by (simp only: qx2)
  also have "... = b ^ 3 - 36 * b * c + 216 * d"
    by (simp add: power2_eq_square power3_eq_cube algebra_simps)
  finally show ?thesis .
qed

lemma zero_c_invariant_h_certificate:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes "(12 :: 'a) \<noteq> 0"
  shows "24 * weierstrass_h W (- b2 W / 12) = - c4 W"
  using zero_c_invariant_h_raw[OF assms, of "b2 W" "b4 W"]
  by (simp add: weierstrass_h_def c4_def)

lemma zero_c_invariant_g_certificate:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes "(12 :: 'a) \<noteq> 0"
  shows "216 * weierstrass_g W (- b2 W / 12) = - c6 W"
  using zero_c_invariant_g_raw[OF assms, of "b2 W" "b4 W" "b6 W"]
  by (simp add: weierstrass_g_def c6_def)

lemma discriminant_zero_imp_affine_singular_odd:
  fixes W :: "'a::alg_closed_field weierstrass_coeffs"
  assumes two: "(2 :: 'a) \<noteq> 0"
    and delta: "discriminant W = 0"
  shows "\<exists>x y. singular_affine_point W x y"
proof (cases "c4 W = 0")
  case False
  let ?x = "(18 * b6 W - b2 W * b4 W) / c4 W"
  note h_certificate = c4_candidate_h_certificate[OF False]
  have h: "weierstrass_h W ?x = 0"
    using h_certificate delta False by simp
  have g: "weierstrass_g W ?x = 0"
    by (rule c4_candidate_g_from_h_delta[OF False delta h])
  have "singular_affine_point W ?x (- (a1 W * ?x + a3 W) / 2)"
    using affine_singular_of_g_h[OF two g h] .
  then show ?thesis
    by blast
next
  case c4zero: True
  note invariant_identity = c4_c6_discriminant_identity[of W]
  have c6zero: "c6 W = 0"
    using invariant_identity c4zero delta by simp
  show ?thesis
  proof (cases "(3 :: 'a) = 0")
    case three: True
    have four: "(4 :: 'a) = 1"
    proof -
      have "(4 :: 'a) = 3 + 1"
        by simp
      also have "... = 0 + 1"
        using three by simp
      also have "... = 1"
        by simp
      finally show ?thesis .
    qed
    have six: "(6 :: 'a) = 0"
    proof -
      have "(6 :: 'a) = 2 * 3"
        by simp
      also have "... = 0"
        using three by simp
      finally show ?thesis .
    qed
    have eight: "(8 :: 'a) = -1"
    proof -
      have "(8 :: 'a) = 3 * 3 - 1"
        by simp
      also have "... = 0 * 0 - 1"
        using three by simp
      also have "... = -1"
        by simp
      finally show ?thesis .
    qed
    have nine: "(9 :: 'a) = 0"
    proof -
      have "(9 :: 'a) = 3 * 3"
        by simp
      also have "... = 0"
        using three by simp
      finally show ?thesis .
    qed
    have twenty_four: "(24 :: 'a) = 0"
    proof -
      have "(24 :: 'a) = 8 * 3"
        by simp
      also have "... = 0"
        using three by simp
      finally show ?thesis .
    qed
    have twenty_seven: "(27 :: 'a) = 0"
    proof -
      have "(27 :: 'a) = 9 * 3"
        by simp
      also have "... = 0"
        using three by simp
      finally show ?thesis .
    qed
    have c4eq: "b2 W ^ 2 - 24 * b4 W = 0"
      using c4zero unfolding c4_def .
    have b2pow: "b2 W ^ 2 = 0"
      using c4eq twenty_four by simp
    then have b2zero: "b2 W = 0"
      by simp
    have deltaeq:
      "-(b2 W ^ 2) * b8 W - 8 * b4 W ^ 3 - 27 * b6 W ^ 2 +
          9 * b2 W * b4 W * b6 W = 0"
      using delta unfolding discriminant_def .
    have b4pow: "b4 W ^ 3 = 0"
      using deltaeq b2zero eight nine twenty_seven
      by simp
    then have b4zero: "b4 W = 0"
      by simp
    obtain x where x: "x ^ 3 = - b6 W"
      using nth_root_exists[of 3 "- b6 W"] by auto
    have g: "weierstrass_g W x = 0"
      unfolding weierstrass_g_def
      using four b2zero b4zero x by simp
    have h: "weierstrass_h W x = 0"
      unfolding weierstrass_h_def
      using six b2zero b4zero by simp
    have "singular_affine_point W x (- (a1 W * x + a3 W) / 2)"
      using affine_singular_of_g_h[OF two g h] .
    then show ?thesis
      by blast
  next
    case three: False
    have twelve_as_product: "(12 :: 'a) = 2 * 2 * 3"
      by simp
    have twelve: "(12 :: 'a) \<noteq> 0"
    proof
      assume twelve_zero: "(12 :: 'a) = 0"
      have product_zero: "(2 :: 'a) * 2 * 3 = 0"
      proof -
        have "(2 :: 'a) * 2 * 3 = 12"
          by simp
        also have "... = 0"
          by (rule twelve_zero)
        finally show ?thesis .
      qed
      have product_nonzero: "(2 :: 'a) * 2 * 3 \<noteq> 0"
      proof
        assume product_zero: "(2 :: 'a) * 2 * 3 = 0"
        have "((2 :: 'a) = 0 \<or> (2 :: 'a) = 0) \<or> (3 :: 'a) = 0"
          using product_zero by (simp only: mult_eq_0_iff)
        with two three show False
          by blast
      qed
      with product_zero show False
        by contradiction
    qed
    have inv12: "(12 :: 'a) * inverse 12 = 1"
      using twelve by simp
    let ?x = "- b2 W / 12"
    have twenty_four_as_product: "(24 :: 'a) = 2 * 12"
      by simp
    have twenty_four: "(24 :: 'a) \<noteq> 0"
    proof
      assume twenty_four_zero: "(24 :: 'a) = 0"
      have product_zero: "(2 :: 'a) * 12 = 0"
      proof -
        have "(2 :: 'a) * 12 = 24"
          by simp
        also have "... = 0"
          by (rule twenty_four_zero)
        finally show ?thesis .
      qed
      have product_nonzero: "(2 :: 'a) * 12 \<noteq> 0"
      proof
        assume product_zero: "(2 :: 'a) * 12 = 0"
        have "(2 :: 'a) = 0 \<or> (12 :: 'a) = 0"
          using product_zero by (simp only: mult_eq_0_iff)
        with two twelve show False
          by blast
      qed
      with product_zero show False
        by contradiction
    qed
    have two_hundred_sixteen_as_product:
      "(216 :: 'a) = 2 * 3 * 3 * 12"
      by simp
    have two_hundred_sixteen: "(216 :: 'a) \<noteq> 0"
    proof
      assume two_hundred_sixteen_zero: "(216 :: 'a) = 0"
      have product_zero: "(2 :: 'a) * 3 * 3 * 12 = 0"
      proof -
        have "(2 :: 'a) * 3 * 3 * 12 = 216"
          by simp
        also have "... = 0"
          by (rule two_hundred_sixteen_zero)
        finally show ?thesis .
      qed
      have product_nonzero: "(2 :: 'a) * 3 * 3 * 12 \<noteq> 0"
      proof
        assume product_zero: "(2 :: 'a) * 3 * 3 * 12 = 0"
        have "(((2 :: 'a) = 0 \<or> (3 :: 'a) = 0) \<or>
            (3 :: 'a) = 0) \<or> (12 :: 'a) = 0"
          using product_zero by (simp only: mult_eq_0_iff)
        with two three twelve show False
          by blast
      qed
      with product_zero show False
        by contradiction
    qed
    note g_certificate = zero_c_invariant_g_certificate[OF twelve, of W]
    note h_certificate = zero_c_invariant_h_certificate[OF twelve, of W]
    have g: "weierstrass_g W ?x = 0"
      using g_certificate c6zero two_hundred_sixteen by simp
    have h: "weierstrass_h W ?x = 0"
      using h_certificate c4zero twenty_four by simp
    have "singular_affine_point W ?x (- (a1 W * ?x + a3 W) / 2)"
      using affine_singular_of_g_h[OF two g h] .
    then show ?thesis
      by blast
  qed
qed

section \<open>The discriminant criterion\<close>

lemma singular_affine_imp_discriminant_zero:
  fixes W :: "'a::field weierstrass_coeffs"
  assumes "singular_affine_point W x y"
  shows "discriminant W = 0"
proof (cases "(2 :: 'a) = 0")
  case True
  show ?thesis
    using singular_affine_imp_discriminant_zero_char_two[OF True assms] .
next
  case False
  show ?thesis
    using singular_affine_imp_discriminant_zero_odd[OF False assms] .
qed

theorem projective_singular_iff_discriminant_zero:
  fixes W :: "'a::alg_closed_field weierstrass_coeffs"
  shows "(\<exists>p. singular_projective_point W p) \<longleftrightarrow>
    discriminant W = 0"
proof -
  have affine:
    "(\<exists>x y. singular_affine_point W x y) \<longleftrightarrow>
      discriminant W = 0"
  proof
    assume "\<exists>x y. singular_affine_point W x y"
    then show "discriminant W = 0"
      using singular_affine_imp_discriminant_zero by blast
  next
    assume delta: "discriminant W = 0"
    show "\<exists>x y. singular_affine_point W x y"
    proof (cases "(2 :: 'a) = 0")
      case True
      show ?thesis
        using discriminant_zero_imp_affine_singular_char_two[OF True delta] .
    next
      case False
      show ?thesis
        using discriminant_zero_imp_affine_singular_odd[OF False delta] .
    qed
  qed
  show ?thesis
    using projective_singular_iff_affine_singular[of W] affine by blast
qed

lemma b2_map_to_ac [simp]:
  "b2 (map_weierstrass_coeffs to_ac W) = to_ac (b2 W)"
  by (simp add: b2_def)

lemma b4_map_to_ac [simp]:
  "b4 (map_weierstrass_coeffs to_ac W) = to_ac (b4 W)"
  by (simp add: b4_def)

lemma b6_map_to_ac [simp]:
  "b6 (map_weierstrass_coeffs to_ac W) = to_ac (b6 W)"
  by (simp add: b6_def)

lemma b8_map_to_ac [simp]:
  "b8 (map_weierstrass_coeffs to_ac W) = to_ac (b8 W)"
  by (simp add: b8_def)

lemma c4_map_to_ac [simp]:
  "c4 (map_weierstrass_coeffs to_ac W) = to_ac (c4 W)"
  by (simp add: c4_def)

lemma c6_map_to_ac [simp]:
  "c6 (map_weierstrass_coeffs to_ac W) = to_ac (c6 W)"
  by (simp add: c6_def)

lemma discriminant_map_to_ac [simp]:
  "discriminant (map_weierstrass_coeffs to_ac W) =
    to_ac (discriminant W)"
  by (simp add: discriminant_def)

definition projective_weierstrass_nonsingular ::
    "'a::field weierstrass_coeffs \<Rightarrow> bool"
  where
  "projective_weierstrass_nonsingular W \<longleftrightarrow>
    projective_weierstrass_nonsingular_over
      (map_weierstrass_coeffs to_ac W)"

theorem weierstrass_nonsingular_iff:
  fixes W :: "'a::field weierstrass_coeffs"
  shows "projective_weierstrass_nonsingular W \<longleftrightarrow>
    discriminant W \<noteq> 0"
  unfolding projective_weierstrass_nonsingular_def
    projective_weierstrass_nonsingular_over_def
  using projective_singular_iff_discriminant_zero[
    of "map_weierstrass_coeffs to_ac W"]
  by simp

end
