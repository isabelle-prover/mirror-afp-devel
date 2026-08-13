theory Weierstrass_Singularities
  imports Weierstrass_Projective_Curve
begin

section \<open>Formal partial derivatives\<close>

definition weierstrass_projective_dx ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_projective_dx W X Y Z =
    a1 W * Y * Z - 3 * X ^ 2 - 2 * a2 W * X * Z - a4 W * Z ^ 2"

definition weierstrass_projective_dy ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_projective_dy W X Y Z =
    2 * Y * Z + a1 W * X * Z + a3 W * Z ^ 2"

definition weierstrass_projective_dz ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_projective_dz W X Y Z =
    Y ^ 2 + a1 W * X * Y + 2 * a3 W * Y * Z -
      a2 W * X ^ 2 - 2 * a4 W * X * Z - 3 * a6 W * Z ^ 2"

lemma weierstrass_projective_dx_scale:
  "weierstrass_projective_dx W (u * X) (u * Y) (u * Z) =
    u ^ 2 * weierstrass_projective_dx W X Y Z"
  by (simp add: weierstrass_projective_dx_def algebra_simps power2_eq_square)

lemma weierstrass_projective_dy_scale:
  "weierstrass_projective_dy W (u * X) (u * Y) (u * Z) =
    u ^ 2 * weierstrass_projective_dy W X Y Z"
  by (simp add: weierstrass_projective_dy_def algebra_simps power2_eq_square)

lemma weierstrass_projective_dz_scale:
  "weierstrass_projective_dz W (u * X) (u * Y) (u * Z) =
    u ^ 2 * weierstrass_projective_dz W X Y Z"
  by (simp add: weierstrass_projective_dz_def algebra_simps power2_eq_square)

lemma weierstrass_projective_euler:
  "X * weierstrass_projective_dx W X Y Z +
      Y * weierstrass_projective_dy W X Y Z +
      Z * weierstrass_projective_dz W X Y Z =
    3 * weierstrass_projective_poly W X Y Z"
  by (simp add: weierstrass_projective_dx_def weierstrass_projective_dy_def
      weierstrass_projective_dz_def weierstrass_projective_poly_def
      algebra_simps power2_eq_square power3_eq_cube)

section \<open>Singular points\<close>

definition singular_projective_point ::
    "'a::field weierstrass_coeffs \<Rightarrow>
      'a weierstrass_projective_coords \<Rightarrow> bool"
  where
  "singular_projective_point W =
    (\<lambda>(X, Y, Z).
      projective_coords_valid (X, Y, Z) \<and>
      weierstrass_projective_poly W X Y Z = 0 \<and>
      weierstrass_projective_dx W X Y Z = 0 \<and>
      weierstrass_projective_dy W X Y Z = 0 \<and>
      weierstrass_projective_dz W X Y Z = 0)"

lemma singular_projective_point_on_curve:
  "singular_projective_point W p \<Longrightarrow> on_projective_weierstrass W p"
  by (induct p rule: prod_induct3)
    (simp add: singular_projective_point_def on_projective_weierstrass_def)

theorem singular_projective_point_scale_iff:
  fixes u :: "'a::field"
  assumes "u \<noteq> 0"
  shows "singular_projective_point W (scale_projective u p) \<longleftrightarrow>
    singular_projective_point W p"
  using assms
  by (induct p rule: prod_induct3)
    (simp add: singular_projective_point_def projective_coords_valid_def
      weierstrass_projective_poly_scale weierstrass_projective_dx_scale
      weierstrass_projective_dy_scale weierstrass_projective_dz_scale assms)

theorem point_at_infinity_nonsingular:
  "\<not> singular_projective_point W weierstrass_infinity"
  by (simp add: singular_projective_point_def weierstrass_infinity_def
      projective_coords_valid_def weierstrass_projective_dz_def)

lemma singular_projective_point_imp_z_nonzero:
  assumes "singular_projective_point W (X, Y, Z)"
  shows "Z \<noteq> 0"
proof
  assume Z0: "Z = 0"
  with assms have "X = 0" and "Y = 0"
    by (auto simp: singular_projective_point_def projective_coords_valid_def
        weierstrass_projective_poly_def weierstrass_projective_dz_def)
  with assms Z0 show False
    by (simp add: singular_projective_point_def projective_coords_valid_def)
qed

section \<open>The affine chart\<close>

definition weierstrass_affine_dx ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_affine_dx W x y =
    a1 W * y - 3 * x ^ 2 - 2 * a2 W * x - a4 W"

definition weierstrass_affine_dy ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_affine_dy W x y = 2 * y + a1 W * x + a3 W"

definition singular_affine_point ::
    "'a::field weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "singular_affine_point W x y \<longleftrightarrow>
    weierstrass_affine_poly W x y = 0 \<and>
    weierstrass_affine_dx W x y = 0 \<and>
    weierstrass_affine_dy W x y = 0"

lemma weierstrass_projective_dx_affine [simp]:
  "weierstrass_projective_dx W x y 1 = weierstrass_affine_dx W x y"
  by (simp add: weierstrass_projective_dx_def weierstrass_affine_dx_def)

lemma weierstrass_projective_dy_affine [simp]:
  "weierstrass_projective_dy W x y 1 = weierstrass_affine_dy W x y"
  by (simp add: weierstrass_projective_dy_def weierstrass_affine_dy_def)

lemma weierstrass_projective_dz_affine:
  "weierstrass_projective_dz W x y 1 =
    3 * weierstrass_affine_poly W x y -
      x * weierstrass_affine_dx W x y -
      y * weierstrass_affine_dy W x y"
  by (simp add: weierstrass_projective_dz_def weierstrass_affine_poly_def
      weierstrass_affine_dx_def weierstrass_affine_dy_def
      algebra_simps power2_eq_square power3_eq_cube)

lemma singular_projective_affine_iff:
  "singular_projective_point W (affine_to_projective x y) \<longleftrightarrow>
    singular_affine_point W x y"
  by (auto simp: singular_projective_point_def singular_affine_point_def
      affine_to_projective_def projective_coords_valid_def
      weierstrass_projective_dz_affine)

theorem projective_singular_iff_affine_singular:
  "(\<exists>p. singular_projective_point W p) \<longleftrightarrow>
    (\<exists>x y. singular_affine_point W x y)"
proof
  assume "\<exists>p. singular_projective_point W p"
  then obtain X Y Z where singular: "singular_projective_point W (X, Y, Z)"
    by (metis prod_cases3)
  have Z: "Z \<noteq> 0"
    using singular by (rule singular_projective_point_imp_z_nonzero)
  have invZ: "inverse Z \<noteq> 0"
    using Z by simp
  have scale:
    "scale_projective (inverse Z) (X, Y, Z) =
      affine_to_projective (X / Z) (Y / Z)"
    using Z
    by (simp add: affine_to_projective_def field_class.field_divide_inverse)
  have "singular_projective_point W
      (affine_to_projective (X / Z) (Y / Z))"
    using singular_projective_point_scale_iff[OF invZ, of W "(X, Y, Z)"]
      singular
    unfolding scale
    by blast
  then show "\<exists>x y. singular_affine_point W x y"
    using singular_projective_affine_iff by blast
next
  assume "\<exists>x y. singular_affine_point W x y"
  then obtain x y where "singular_affine_point W x y"
    by blast
  then show "\<exists>p. singular_projective_point W p"
    using singular_projective_affine_iff by blast
qed

definition projective_weierstrass_nonsingular_over ::
    "'a::field weierstrass_coeffs \<Rightarrow> bool"
  where
  "projective_weierstrass_nonsingular_over W \<longleftrightarrow>
    \<not> (\<exists>p. singular_projective_point W p)"

lemma projective_weierstrass_nonsingular_over_iff:
  "projective_weierstrass_nonsingular_over W \<longleftrightarrow>
    \<not> (\<exists>x y. singular_affine_point W x y)"
  unfolding projective_weierstrass_nonsingular_over_def
  using projective_singular_iff_affine_singular by blast

section \<open>Elimination polynomials\<close>

definition weierstrass_g ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_g W x =
    4 * x ^ 3 + b2 W * x ^ 2 + 2 * b4 W * x + b6 W"

definition weierstrass_h ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_h W x = 6 * x ^ 2 + b2 W * x + b4 W"

lemma affine_dy_squared_minus_g:
  "weierstrass_affine_dy W x y ^ 2 - weierstrass_g W x =
    4 * weierstrass_affine_poly W x y"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  show ?thesis
    unfolding W weierstrass_affine_dy_def weierstrass_g_def
      weierstrass_affine_poly_def b2_def b4_def b6_def
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

lemma two_affine_dx_minus_a1_dy:
  "2 * weierstrass_affine_dx W x y -
      a1 W * weierstrass_affine_dy W x y =
    - weierstrass_h W x"
proof -
  obtain A1 A2 A3 A4 A6 where W:
    "W = \<lparr>a1 = A1, a2 = A2, a3 = A3, a4 = A4, a6 = A6\<rparr>"
    by (cases W) blast
  show ?thesis
    unfolding W weierstrass_affine_dx_def weierstrass_affine_dy_def
      weierstrass_h_def b2_def b4_def
    by (simp add: algebra_simps power2_eq_square)
qed

end
