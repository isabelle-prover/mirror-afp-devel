theory Weierstrass_Projective_Curve
  imports Weierstrass_Affine_Curve
begin

section \<open>Homogeneous coordinates\<close>

type_synonym 'a weierstrass_projective_coords = "'a \<times> 'a \<times> 'a"

definition scale_projective ::
    "'a::times \<Rightarrow> 'a weierstrass_projective_coords \<Rightarrow>
      'a weierstrass_projective_coords"
  where
  "scale_projective u = (\<lambda>(X, Y, Z). (u * X, u * Y, u * Z))"

lemma scale_projective_simps [simp]:
  "scale_projective u (X, Y, Z) = (u * X, u * Y, u * Z)"
  by (simp add: scale_projective_def)

definition projective_coords_valid ::
    "'a::zero weierstrass_projective_coords \<Rightarrow> bool"
  where
  "projective_coords_valid = (\<lambda>(X, Y, Z). X \<noteq> 0 \<or> Y \<noteq> 0 \<or> Z \<noteq> 0)"

definition projectively_equivalent ::
    "'a::field weierstrass_projective_coords \<Rightarrow>
      'a weierstrass_projective_coords \<Rightarrow> bool"
  where
  "projectively_equivalent p q \<longleftrightarrow>
    (\<exists>u. u \<noteq> 0 \<and> q = scale_projective u p)"

lemma scale_projective_one [simp]:
  "scale_projective 1 p = p"
  for p :: "'a::monoid_mult weierstrass_projective_coords"
  by (induct p rule: prod_induct3) simp

lemma scale_projective_mult:
  "scale_projective u (scale_projective v p) = scale_projective (u * v) p"
  for p :: "'a::monoid_mult weierstrass_projective_coords"
  by (induct p rule: prod_induct3) (simp add: mult.assoc)

lemma projective_coords_valid_scale_iff:
  "projective_coords_valid (scale_projective u p) \<longleftrightarrow>
    u \<noteq> 0 \<and> projective_coords_valid p"
  for u :: "'a::field"
  by (induct p rule: prod_induct3)
    (auto simp: projective_coords_valid_def)

lemma projectively_equivalent_refl [simp]:
  "projectively_equivalent p p"
  unfolding projectively_equivalent_def
  by (rule exI[of _ 1]) simp

lemma projectively_equivalent_sym:
  "projectively_equivalent p q \<Longrightarrow> projectively_equivalent q p"
  unfolding projectively_equivalent_def
proof -
  assume "\<exists>u. u \<noteq> 0 \<and> q = scale_projective u p"
  then obtain u where u: "u \<noteq> 0" "q = scale_projective u p"
    by blast
  show "\<exists>v. v \<noteq> 0 \<and> p = scale_projective v q"
  proof (intro exI[of _ "inverse u"] conjI)
    show "inverse u \<noteq> 0"
      using u by simp
    show "p = scale_projective (inverse u) q"
      unfolding u(2) scale_projective_mult
      using u by simp
  qed
qed

lemma projectively_equivalent_trans:
  "projectively_equivalent p q \<Longrightarrow>
    projectively_equivalent q r \<Longrightarrow>
    projectively_equivalent p r"
  unfolding projectively_equivalent_def
proof -
  assume "\<exists>u. u \<noteq> 0 \<and> q = scale_projective u p"
    and "\<exists>v. v \<noteq> 0 \<and> r = scale_projective v q"
  then obtain u v where uv:
      "u \<noteq> 0" "v \<noteq> 0"
      "q = scale_projective u p" "r = scale_projective v q"
    by blast
  show "\<exists>w. w \<noteq> 0 \<and> r = scale_projective w p"
    using uv
    by (intro exI[of _ "v * u"]) (simp add: scale_projective_mult)
qed

section \<open>The projective cubic\<close>

definition weierstrass_projective_poly ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "weierstrass_projective_poly W X Y Z =
    Y ^ 2 * Z + a1 W * X * Y * Z + a3 W * Y * Z ^ 2 -
      (X ^ 3 + a2 W * X ^ 2 * Z + a4 W * X * Z ^ 2 + a6 W * Z ^ 3)"

definition on_projective_weierstrass ::
    "'a::comm_ring_1 weierstrass_coeffs \<Rightarrow>
      'a weierstrass_projective_coords \<Rightarrow> bool"
  where
  "on_projective_weierstrass W =
    (\<lambda>(X, Y, Z).
      projective_coords_valid (X, Y, Z) \<and>
      weierstrass_projective_poly W X Y Z = 0)"

lemma weierstrass_projective_poly_scale:
  "weierstrass_projective_poly W (u * X) (u * Y) (u * Z) =
    u ^ 3 * weierstrass_projective_poly W X Y Z"
  by (simp add: weierstrass_projective_poly_def algebra_simps
      power2_eq_square power3_eq_cube)

lemma on_projective_weierstrass_scale_iff:
  fixes u :: "'a::field"
  assumes "u \<noteq> 0"
  shows "on_projective_weierstrass W (scale_projective u p) \<longleftrightarrow>
    on_projective_weierstrass W p"
  using assms
  by (induct p rule: prod_induct3)
    (simp add: on_projective_weierstrass_def projective_coords_valid_def
      weierstrass_projective_poly_scale assms)

definition affine_to_projective ::
    "'a::one \<Rightarrow> 'a \<Rightarrow> 'a weierstrass_projective_coords"
  where
  "affine_to_projective x y = (x, y, 1)"

lemma weierstrass_projective_poly_affine [simp]:
  "weierstrass_projective_poly W x y 1 = weierstrass_affine_poly W x y"
  by (simp add: weierstrass_projective_poly_def weierstrass_affine_poly_def)

theorem on_projective_weierstrass_affine:
  "on_projective_weierstrass W (affine_to_projective x y) \<longleftrightarrow>
    on_weierstrass_affine W x y"
  by (simp add: affine_to_projective_def on_projective_weierstrass_def
      projective_coords_valid_def on_weierstrass_affine_iff_poly_zero)

theorem on_projective_weierstrass_chart:
  fixes X Y Z :: "'a::field"
  assumes "Z \<noteq> 0"
  shows "on_projective_weierstrass W (X, Y, Z) \<longleftrightarrow>
    on_weierstrass_affine W (X / Z) (Y / Z)"
proof -
  have invZ: "inverse Z \<noteq> 0"
    using assms by simp
  have scale:
    "scale_projective (inverse Z) (X, Y, Z) =
      affine_to_projective (X / Z) (Y / Z)"
    using assms
    by (simp add: affine_to_projective_def field_class.field_divide_inverse)
  have scaled:
    "on_projective_weierstrass W
        (affine_to_projective (X / Z) (Y / Z)) \<longleftrightarrow>
      on_projective_weierstrass W (X, Y, Z)"
    using on_projective_weierstrass_scale_iff[OF invZ, of W "(X, Y, Z)"]
    unfolding scale .
  show ?thesis
    using scaled on_projective_weierstrass_affine[of W "X / Z" "Y / Z"]
    by blast
qed

definition weierstrass_infinity ::
    "'a::zero_neq_one weierstrass_projective_coords"
  where
  "weierstrass_infinity = (0, 1, 0)"

lemma weierstrass_infinity_on_curve [simp]:
  "on_projective_weierstrass W weierstrass_infinity"
  by (simp add: on_projective_weierstrass_def projective_coords_valid_def
      weierstrass_infinity_def weierstrass_projective_poly_def)

lemma on_projective_weierstrass_at_infinity_iff:
  "on_projective_weierstrass W (X, Y, 0) \<longleftrightarrow>
    X = 0 \<and> Y \<noteq> 0"
  for X Y :: "'a::field"
  by (auto simp: on_projective_weierstrass_def projective_coords_valid_def
      weierstrass_projective_poly_def)

theorem projective_weierstrass_at_infinity:
  assumes "on_projective_weierstrass W (X, Y, 0)"
  shows "projectively_equivalent (X, Y, 0) weierstrass_infinity"
proof -
  from assms have X: "X = 0" and Y: "Y \<noteq> 0"
    by (simp_all add: on_projective_weierstrass_at_infinity_iff)
  show ?thesis
    unfolding projectively_equivalent_def
  proof (intro exI[of _ "inverse Y"] conjI)
    show "inverse Y \<noteq> 0"
      using Y by simp
    show "weierstrass_infinity =
      scale_projective (inverse Y) (X, Y, 0)"
      using X Y by (simp add: weierstrass_infinity_def)
  qed
qed

end
