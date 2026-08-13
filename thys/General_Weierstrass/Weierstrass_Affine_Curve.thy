theory Weierstrass_Affine_Curve
  imports Weierstrass_Invariants
begin

section \<open>The affine equation\<close>

definition weierstrass_affine_poly ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_affine_poly W x y =
    y ^ 2 + a1 W * x * y + a3 W * y -
      (x ^ 3 + a2 W * x ^ 2 + a4 W * x + a6 W)"

definition on_weierstrass_affine ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "on_weierstrass_affine W x y \<longleftrightarrow>
    y ^ 2 + a1 W * x * y + a3 W * y =
      x ^ 3 + a2 W * x ^ 2 + a4 W * x + a6 W"

lemma on_weierstrass_affine_iff_poly_zero:
  "on_weierstrass_affine W x y \<longleftrightarrow>
    weierstrass_affine_poly W x y = 0"
  unfolding on_weierstrass_affine_def weierstrass_affine_poly_def
  by simp

end
