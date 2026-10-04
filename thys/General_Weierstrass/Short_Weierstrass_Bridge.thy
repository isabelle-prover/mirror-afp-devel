theory Short_Weierstrass_Bridge
  imports
    Weierstrass_j_Invariant
    "Elliptic_Curves_Group_Law.Elliptic_Axclass"
begin

section \<open>Specialization to short Weierstrass equations\<close>

lemma discriminant_short_weierstrass:
  fixes A B :: "'a::comm_ring_1"
  shows "discriminant (short_weierstrass_coeffs A B) =
    -16 * (4 * A ^ 3 + 27 * B ^ 2)"
  unfolding discriminant_def b2_def b4_def b6_def b8_def
    short_weierstrass_coeffs_def
  by (simp add: algebra_simps power2_eq_square power3_eq_cube)

lemma on_weierstrass_affine_short:
  fixes A B x y :: "'a::comm_ring_1"
  shows "on_weierstrass_affine (short_weierstrass_coeffs A B) x y
    \<longleftrightarrow> y ^ 2 = x ^ 3 + A * x + B"
  unfolding on_weierstrass_affine_def short_weierstrass_coeffs_def
  by simp

lemma on_weierstrass_affine_short_iff_on_curve:
  fixes A B x y :: "'a::ell_field"
  shows "on_weierstrass_affine (short_weierstrass_coeffs A B) x y
    \<longleftrightarrow> on_curve A B (Point x y)"
  unfolding on_curve_def
  by (simp add: on_weierstrass_affine_short)

theorem projective_weierstrass_nonsingular_short_iff:
  fixes A B :: "'a::ell_field"
  shows "projective_weierstrass_nonsingular
      (short_weierstrass_coeffs A B)
    \<longleftrightarrow> nonsingular A B"
proof -
  have two: "(2 :: 'a) \<noteq> 0"
    by (rule two_not_zero)
  have four: "(4 :: 'a) \<noteq> 0"
    by (rule four_ne_zero_of_two_ne_zero[OF two])
  have sixteen: "(16 :: 'a) \<noteq> 0"
  proof
    assume sixteen_zero: "(16 :: 'a) = 0"
    have product_zero: "(4 :: 'a) * 4 = 0"
    proof -
      have "(4 :: 'a) * 4 = 16"
        by simp
      also have "... = 0"
        by (rule sixteen_zero)
      finally show ?thesis .
    qed
    have "(4 :: 'a) = 0 \<or> (4 :: 'a) = 0"
      using product_zero by (simp only: mult_eq_0_iff)
    with four show False
      by blast
  qed
  have neg_sixteen: "(-16 :: 'a) \<noteq> 0"
    using sixteen by simp
  have delta_iff:
    "discriminant (short_weierstrass_coeffs A B) \<noteq> 0
      \<longleftrightarrow> 4 * A ^ 3 + 27 * B ^ 2 \<noteq> 0"
    unfolding discriminant_short_weierstrass
    using neg_sixteen
    by (simp only: mult_eq_0_iff; blast)
  show ?thesis
    unfolding nonsingular_def
    using weierstrass_nonsingular_iff[
      of "short_weierstrass_coeffs A B"] delta_iff
    by blast
qed

end
