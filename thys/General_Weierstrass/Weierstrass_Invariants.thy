theory Weierstrass_Invariants
  imports Weierstrass_Coefficients
begin

section \<open>Standard invariants\<close>

definition b2 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where "b2 W = a1 W ^ 2 + 4 * a2 W"

definition b4 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where "b4 W = 2 * a4 W + a1 W * a3 W"

definition b6 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where "b6 W = a3 W ^ 2 + 4 * a6 W"

definition b8 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where
  "b8 W =
    a1 W ^ 2 * a6 W + 4 * a2 W * a6 W - a1 W * a3 W * a4 W +
      a2 W * a3 W ^ 2 - a4 W ^ 2"

definition c4 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where "c4 W = b2 W ^ 2 - 24 * b4 W"

definition c6 :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where "c6 W = -(b2 W ^ 3) + 36 * b2 W * b4 W - 216 * b6 W"

definition discriminant :: "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a"
  where
  "discriminant W =
    -(b2 W ^ 2) * b8 W - 8 * b4 W ^ 3 - 27 * b6 W ^ 2 +
      9 * b2 W * b4 W * b6 W"

lemma b2_b6_minus_b4_squared:
  "b2 W * b6 W - b4 W ^ 2 = 4 * b8 W"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  show ?thesis
    unfolding W b2_def b4_def b6_def b8_def
    by (simp add: algebra_simps power2_eq_square)
qed

theorem c4_c6_discriminant_identity:
  "c4 W ^ 3 - c6 W ^ 2 = 1728 * discriminant W"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  show ?thesis
    unfolding W b2_def b4_def b6_def b8_def c4_def c6_def discriminant_def
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

lemma four_discriminant_expanded:
  "4 * discriminant W =
    -(b2 W ^ 3) * b6 W + b2 W ^ 2 * b4 W ^ 2 -
      32 * b4 W ^ 3 - 108 * b6 W ^ 2 +
      36 * b2 W * b4 W * b6 W"
proof -
 obtain A1 A2 A3 A4 A6 where W:
   "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
   by (cases W) blast
 show ?thesis
   unfolding W b2_def b4_def b6_def b8_def discriminant_def
   by (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

end
