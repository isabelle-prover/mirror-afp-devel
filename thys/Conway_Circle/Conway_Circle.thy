(*  Title:      Conway_Circle.thy
    Author:     Arthur Freitas Ramos, 2026
    Author:     David Barros Hulak, 2026
    Author:     Ruy J. G. B. de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

Conway's Circle Theorem.

Let ABC be a nondegenerate triangle in the Euclidean plane.  At each
vertex, extend the two adjacent side-lines past that vertex by the length
of the side opposite that vertex:

  * past A, the two adjacent sides AB and AC are extended by a = |BC|,
    giving A_c on line AB and A_b on line AC;
  * past B, the two adjacent sides BA and BC are extended by b = |CA|,
    giving B_c on line AB and B_a on line BC;
  * past C, the two adjacent sides CA and CB are extended by c = |AB|,
    giving C_b on line AC and C_a on line BC.

Then the six points  A_b, A_c, B_a, B_c, C_a, C_b  lie on a single circle
centered at the incenter of triangle ABC.

The radius is  sqrt(r^2 + s^2)  where  r  is the inradius and  s  is the
semiperimeter.

Reference: see @{cite "honsberger1995episodes"}, @{cite "evans2002conicCenters"},
and the construction recorded in @{cite "mathworldConwayCircle"}.
*)

theory Conway_Circle
  imports "HOL-Analysis.Analysis"
begin

(*<*)
text \<open>
  We use elementary vector coordinates.  The side lengths are named in the
  usual way: \<open>a = |BC|\<close>, \<open>b = |CA|\<close>, and \<open>c = |AB|\<close>.
\<close>
(*>*)

definition triangle_semiperimeter :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real"
  where "triangle_semiperimeter A B C =
    (dist B C + dist C A + dist A B) / 2"

definition triangle_incenter :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "triangle_incenter A B C =
    (let a = dist B C; b = dist C A; c = dist A B in
      inverse (a + b + c) *\<^sub>R (a *\<^sub>R A + b *\<^sub>R B + c *\<^sub>R C))"

definition conway_point_past_first :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "conway_point_past_first X Y d = X + (d / dist X Y) *\<^sub>R (X - Y)"

definition conway_point_past_second :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "conway_point_past_second X Y d = Y + (d / dist X Y) *\<^sub>R (Y - X)"

definition side_contact_point :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a"
  where "side_contact_point X Y p q =
    (let L = dist X Y; s = (p + q + L) / 2 in X + ((s - p) / L) *\<^sub>R (Y - X))"

definition conway_A_c :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_A_c A B C = conway_point_past_first A B (dist B C)"

definition conway_B_c :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_B_c A B C = conway_point_past_second A B (dist C A)"

definition conway_A_b :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_A_b A B C = conway_point_past_first A C (dist B C)"

definition conway_C_b :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_C_b A B C = conway_point_past_second A C (dist A B)"

definition conway_B_a :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_B_a A B C = conway_point_past_first B C (dist C A)"

definition conway_C_a :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "conway_C_a A B C = conway_point_past_second B C (dist A B)"

definition contact_AB :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "contact_AB A B C = side_contact_point A B (dist B C) (dist C A)"

definition contact_AC :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "contact_AC A B C = side_contact_point A C (dist B C) (dist A B)"

definition contact_BC :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2"
  where "contact_BC A B C = side_contact_point B C (dist C A) (dist A B)"

definition triangle_inradius :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real"
  where "triangle_inradius A B C =
    dist (triangle_incenter A B C) (contact_AB A B C)"

lemma noncollinear_triangle_distinct:
  assumes "\<not> collinear {A, B, C}"
  shows "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
proof -
  show "A \<noteq> B"
  proof
    assume "A = B"
    then have "{A, B, C} = {A, C}"
      by auto
    then have "collinear {A, B, C}"
      by simp
    with assms show False
      by contradiction
  qed
  show "A \<noteq> C"
  proof
    assume "A = C"
    then have "{A, B, C} = {B, C}"
      by auto
    then have "collinear {A, B, C}"
      by simp
    with assms show False
      by contradiction
  qed
  show "B \<noteq> C"
  proof
    assume "B = C"
    then have "{A, B, C} = {A, C}"
      by auto
    then have "collinear {A, B, C}"
      by simp
    with assms show False
      by contradiction
  qed
qed

lemma inner_side_vectors:
  fixes X Y Z :: "'a::real_inner"
  shows "(Z - X) \<bullet> (Y - X) =
    ((dist Z X)\<^sup>2 + (dist X Y)\<^sup>2 - (dist Y Z)\<^sup>2) / 2"
proof -
  have "(Z - X) \<bullet> (Y - X) =
    (((norm (Z - X))\<^sup>2 + (norm (Y - X))\<^sup>2) - (norm ((Z - X) - (Y - X)))\<^sup>2) / 2"
    by (rule dot_norm_neg)
  also have "... = ((dist Z X)\<^sup>2 + (dist X Y)\<^sup>2 - (dist Y Z)\<^sup>2) / 2"
    by (simp add: dist_norm norm_minus_commute)
  finally show ?thesis .
qed

lemma weighted_incenter_side_contact_orthogonal:
  fixes X Y Z :: "'a::real_inner"
  assumes "X \<noteq> Y"
  defines "a \<equiv> dist Y Z"
  defines "b \<equiv> dist Z X"
  defines "c \<equiv> dist X Y"
  defines "S \<equiv> a + b + c"
  defines "I \<equiv> inverse S *\<^sub>R (a *\<^sub>R X + b *\<^sub>R Y + c *\<^sub>R Z)"
  defines "T \<equiv> side_contact_point X Y a b"
  shows "orthogonal (I - T) (Y - X)"
proof -
  have cpos: "0 < c"
    using assms unfolding c_def by simp
  have a_nonneg: "0 \<le> a"
    unfolding a_def by simp
  have b_nonneg: "0 \<le> b"
    unfolding b_def by simp
  have Spos: "0 < S"
    using a_nonneg b_nonneg cpos unfolding S_def by linarith
  define u where "u = Y - X"
  define v where "v = Z - X"
  have incenter_translate:
    "I - X = inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v)"
  proof -
    have numerator:
      "a *\<^sub>R X + b *\<^sub>R Y + c *\<^sub>R Z =
        S *\<^sub>R X + (b *\<^sub>R (Y - X) + c *\<^sub>R (Z - X))"
      unfolding S_def by (simp add: algebra_simps scaleR_diff_right)
    have "I = X + inverse S *\<^sub>R (b *\<^sub>R (Y - X) + c *\<^sub>R (Z - X))"
      unfolding I_def numerator
      using Spos by (simp add: scaleR_add_right)
    then show ?thesis
      unfolding u_def v_def by simp
  qed
  have contact_translate:
    "T - X = ((b + c - a) / (2 * c)) *\<^sub>R u"
    unfolding T_def side_contact_point_def a_def b_def c_def Let_def
    by (simp add: field_simps u_def)
  have side_square: "u \<bullet> u = c\<^sup>2"
  proof -
    have "(Y - X) \<bullet> (Y - X) = (norm (Y - X))\<^sup>2"
      by (simp add: power2_norm_eq_inner)
    also have "... = c\<^sup>2"
      unfolding c_def by (simp add: dist_norm norm_minus_commute)
    finally show ?thesis
      unfolding u_def .
  qed
  have side_cross: "v \<bullet> u = (b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2"
    unfolding u_def v_def a_def b_def c_def by (rule inner_side_vectors)
  have "(I - T) \<bullet> (Y - X) =
      ((I - X) - (T - X)) \<bullet> u"
    unfolding u_def by simp
  also have "... =
      (inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
        ((b + c - a) / (2 * c)) *\<^sub>R u) \<bullet> u"
    unfolding incenter_translate contact_translate by simp
  also have "... =
      inverse S * (b * c\<^sup>2 + c * ((b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2)) -
      ((b + c - a) / (2 * c)) * c\<^sup>2"
    by (simp add: inner_simps side_square side_cross)
  also have "... = 0"
    using cpos Spos
    by (simp add: field_simps power2_eq_square S_def)
  finally have "(I - T) \<bullet> (Y - X) = 0" .
  then show ?thesis
    unfolding orthogonal_def by simp
qed

lemma incenter_contact_dist_sq_scalar:
  fixes a b c S :: real
  assumes "c \<noteq> 0"
    and "S \<noteq> 0"
    and "S = a + b + c"
  shows
    "(inverse S * b - (b + c - a) / (2 * c))\<^sup>2 * c\<^sup>2 +
      (inverse S * c)\<^sup>2 * b\<^sup>2 +
      2 * (inverse S * b - (b + c - a) / (2 * c)) * (inverse S * c) *
        ((b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2) =
    ((b + c - a) * (a + c - b) * (a + b - c)) / (4 * S)"
proof -
  define D where "D = a\<^sup>2 - b\<^sup>2 - c\<^sup>2"
  have alpha_eq:
    "inverse S * b - (b + c - a) / (2 * c) = D / (2 * c * S)"
    using assms unfolding D_def
    by (simp add: field_simps power2_eq_square)
  have beta_eq: "inverse S * c = c / S"
    by (simp add: divide_inverse mult.commute)
  have cross_eq: "(b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2 = - D / 2"
    unfolding D_def by simp
  have
    "(inverse S * b - (b + c - a) / (2 * c))\<^sup>2 * c\<^sup>2 +
      (inverse S * c)\<^sup>2 * b\<^sup>2 +
      2 * (inverse S * b - (b + c - a) / (2 * c)) * (inverse S * c) *
        ((b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2) =
    (D / (2 * c * S))\<^sup>2 * c\<^sup>2 + (c / S)\<^sup>2 * b\<^sup>2 +
      2 * (D / (2 * c * S)) * (c / S) * (- D / 2)"
    by (simp add: alpha_eq beta_eq cross_eq)
  also have "... = (4 * b\<^sup>2 * c\<^sup>2 - D\<^sup>2) / (4 * S\<^sup>2)"
    using assms(1,2) by (simp add: field_simps power2_eq_square)
  also have "... = ((2 * b * c - D) * (2 * b * c + D)) / (4 * S\<^sup>2)"
    by (simp add: power2_eq_square algebra_simps)
  also have "... =
      (((b + c)\<^sup>2 - a\<^sup>2) * (a\<^sup>2 - (b - c)\<^sup>2)) / (4 * S\<^sup>2)"
    unfolding D_def by (simp add: power2_eq_square algebra_simps)
  also have "... =
      ((S * (b + c - a)) * ((a + c - b) * (a + b - c))) / (4 * S\<^sup>2)"
    using assms by (simp add: power2_eq_square algebra_simps)
  also have "... =
      ((b + c - a) * (a + c - b) * (a + b - c)) / (4 * S)"
    using assms(2) by (simp add: field_simps power2_eq_square)
  finally show ?thesis .
qed

lemma weighted_incenter_side_contact_dist_sq:
  fixes X Y Z :: "'a::real_inner"
  assumes "X \<noteq> Y"
  defines "a \<equiv> dist Y Z"
  defines "b \<equiv> dist Z X"
  defines "c \<equiv> dist X Y"
  defines "S \<equiv> a + b + c"
  defines "I \<equiv> inverse S *\<^sub>R (a *\<^sub>R X + b *\<^sub>R Y + c *\<^sub>R Z)"
  defines "T \<equiv> side_contact_point X Y a b"
  shows "(dist I T)\<^sup>2 =
    ((b + c - a) * (a + c - b) * (a + b - c)) / (4 * S)"
proof -
  have cpos: "0 < c"
    using assms unfolding c_def by simp
  have a_nonneg: "0 \<le> a"
    unfolding a_def by simp
  have b_nonneg: "0 \<le> b"
    unfolding b_def by simp
  have Spos: "0 < S"
    using a_nonneg b_nonneg cpos unfolding S_def by linarith
  define u where "u = Y - X"
  define v where "v = Z - X"
  have incenter_translate:
    "I - X = inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v)"
  proof -
    have numerator:
      "a *\<^sub>R X + b *\<^sub>R Y + c *\<^sub>R Z =
        S *\<^sub>R X + (b *\<^sub>R (Y - X) + c *\<^sub>R (Z - X))"
      unfolding S_def by (simp add: algebra_simps scaleR_diff_right)
    have "I = X + inverse S *\<^sub>R (b *\<^sub>R (Y - X) + c *\<^sub>R (Z - X))"
      unfolding I_def numerator
      using Spos by (simp add: scaleR_add_right)
    then show ?thesis
      unfolding u_def v_def by simp
  qed
  have contact_translate:
    "T - X = ((b + c - a) / (2 * c)) *\<^sub>R u"
    unfolding T_def side_contact_point_def a_def b_def c_def Let_def
    by (simp add: field_simps u_def)
  have diff_translate:
    "I - T =
      inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
      ((b + c - a) / (2 * c)) *\<^sub>R u"
  proof -
    have "I - T = (I - X) - (T - X)"
      by simp
    also have "... =
      inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
      ((b + c - a) / (2 * c)) *\<^sub>R u"
      unfolding incenter_translate contact_translate ..
    finally show ?thesis .
  qed
  have side_square: "u \<bullet> u = c\<^sup>2"
  proof -
    have "(Y - X) \<bullet> (Y - X) = (norm (Y - X))\<^sup>2"
      by (simp add: power2_norm_eq_inner)
    also have "... = c\<^sup>2"
      unfolding c_def by (simp add: dist_norm norm_minus_commute)
    finally show ?thesis
      unfolding u_def .
  qed
  have vertex_square: "v \<bullet> v = b\<^sup>2"
  proof -
    have "(Z - X) \<bullet> (Z - X) = (norm (Z - X))\<^sup>2"
      by (simp add: power2_norm_eq_inner)
    also have "... = b\<^sup>2"
      unfolding b_def by (simp add: dist_norm norm_minus_commute)
    finally show ?thesis
      unfolding v_def .
  qed
  have side_cross: "v \<bullet> u = (b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2"
    unfolding u_def v_def a_def b_def c_def by (rule inner_side_vectors)
  have side_cross': "u \<bullet> v = (b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2"
    using side_cross by (simp add: inner_commute)
  define alpha where "alpha = inverse S * b - ((b + c - a) / (2 * c))"
  define beta where "beta = inverse S * c"
  have linear_diff:
    "inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
      ((b + c - a) / (2 * c)) *\<^sub>R u =
      alpha *\<^sub>R u + beta *\<^sub>R v"
    unfolding alpha_def beta_def
    by (simp add: algebra_simps scaleR_add_right scaleR_diff_left)
  have "(dist I T)\<^sup>2 = (I - T) \<bullet> (I - T)"
    by (simp add: dist_norm power2_norm_eq_inner)
  also have "... =
      (inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
        ((b + c - a) / (2 * c)) *\<^sub>R u) \<bullet>
      (inverse S *\<^sub>R (b *\<^sub>R u + c *\<^sub>R v) -
        ((b + c - a) / (2 * c)) *\<^sub>R u)"
    unfolding diff_translate ..
  also have "... =
      (alpha *\<^sub>R u + beta *\<^sub>R v) \<bullet> (alpha *\<^sub>R u + beta *\<^sub>R v)"
    unfolding linear_diff ..
  also have "... =
      alpha\<^sup>2 * c\<^sup>2 + beta\<^sup>2 * b\<^sup>2 +
      2 * alpha * beta * ((b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2)"
    by (simp add: inner_simps side_square vertex_square side_cross side_cross'
        power2_eq_square algebra_simps) algebra
  also have "... =
      (inverse S * b - ((b + c - a) / (2 * c)))\<^sup>2 * c\<^sup>2 +
      (inverse S * c)\<^sup>2 * b\<^sup>2 +
      2 * (inverse S * b - ((b + c - a) / (2 * c))) *
        (inverse S * c) * ((b\<^sup>2 + c\<^sup>2 - a\<^sup>2) / 2)"
    unfolding alpha_def beta_def ..
  also have "... =
      ((b + c - a) * (a + c - b) * (a + b - c)) / (4 * S)"
  proof (rule incenter_contact_dist_sq_scalar)
    show "c \<noteq> 0"
      using cpos by simp
    show "S \<noteq> 0"
      using Spos by simp
    show "S = a + b + c"
      unfolding S_def ..
  qed
  finally show ?thesis .
qed

lemma triangle_incenter_contact_AB_orthogonal:
  fixes A B C :: "real ^ 2"
  assumes "A \<noteq> B"
  shows "orthogonal (triangle_incenter A B C - contact_AB A B C) (B - A)"
  using weighted_incenter_side_contact_orthogonal[OF assms, of C]
  unfolding triangle_incenter_def contact_AB_def Let_def
  by simp

lemma triangle_incenter_contact_AC_orthogonal:
  fixes A B C :: "real ^ 2"
  assumes "A \<noteq> C"
  shows "orthogonal (triangle_incenter A B C - contact_AC A B C) (C - A)"
  using weighted_incenter_side_contact_orthogonal[OF assms, of B]
  unfolding triangle_incenter_def contact_AC_def Let_def
  by (simp add: algebra_simps dist_commute)

lemma triangle_incenter_contact_BC_orthogonal:
  fixes A B C :: "real ^ 2"
  assumes "B \<noteq> C"
  shows "orthogonal (triangle_incenter A B C - contact_BC A B C) (C - B)"
  using weighted_incenter_side_contact_orthogonal[OF assms, of A]
  unfolding triangle_incenter_def contact_BC_def Let_def
  by (simp add: algebra_simps dist_commute)

lemma triangle_inradius_nonneg [simp]: "0 \<le> triangle_inradius A B C"
  unfolding triangle_inradius_def by simp

lemma triangle_incenter_contact_AB_dist:
  "dist (triangle_incenter A B C) (contact_AB A B C) = triangle_inradius A B C"
  unfolding triangle_inradius_def ..

lemma triangle_incenter_contact_AC_dist:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  shows "dist (triangle_incenter A B C) (contact_AC A B C) = triangle_inradius A B C"
proof -
  let ?I = "triangle_incenter A B C"
  let ?a = "dist B C"
  let ?b = "dist C A"
  let ?c = "dist A B"
  let ?H = "((?b + ?c - ?a) * (?a + ?c - ?b) * (?a + ?b - ?c)) /
    (4 * (?a + ?b + ?c))"
  have sides: "A \<noteq> B" "A \<noteq> C"
    using noncollinear_triangle_distinct[OF triangle] by blast+
  have AB_sq: "(dist ?I (contact_AB A B C))\<^sup>2 = ?H"
    using weighted_incenter_side_contact_dist_sq[OF sides(1), of C]
    unfolding triangle_incenter_def contact_AB_def Let_def
    by (simp add: dist_commute algebra_simps)
  have AC_sq: "(dist ?I (contact_AC A B C))\<^sup>2 = ?H"
    using weighted_incenter_side_contact_dist_sq[OF sides(2), of B]
    unfolding triangle_incenter_def contact_AC_def Let_def
    by (simp add: dist_commute algebra_simps)
  show ?thesis
    unfolding triangle_inradius_def
  proof (rule power2_eq_imp_eq)
    show "(dist ?I (contact_AC A B C))\<^sup>2 =
        (dist ?I (contact_AB A B C))\<^sup>2"
      using AC_sq AB_sq by simp
    show "0 \<le> dist ?I (contact_AC A B C)"
      by simp
    show "0 \<le> dist ?I (contact_AB A B C)"
      by simp
  qed
qed

lemma triangle_incenter_contact_BC_dist:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  shows "dist (triangle_incenter A B C) (contact_BC A B C) = triangle_inradius A B C"
proof -
  let ?I = "triangle_incenter A B C"
  let ?a = "dist B C"
  let ?b = "dist C A"
  let ?c = "dist A B"
  let ?H = "((?b + ?c - ?a) * (?a + ?c - ?b) * (?a + ?b - ?c)) /
    (4 * (?a + ?b + ?c))"
  have sides: "A \<noteq> B" "B \<noteq> C"
    using noncollinear_triangle_distinct[OF triangle] by blast+
  have AB_sq: "(dist ?I (contact_AB A B C))\<^sup>2 = ?H"
    using weighted_incenter_side_contact_dist_sq[OF sides(1), of C]
    unfolding triangle_incenter_def contact_AB_def Let_def
    by (simp add: dist_commute algebra_simps)
  have BC_sq: "(dist ?I (contact_BC A B C))\<^sup>2 = ?H"
    using weighted_incenter_side_contact_dist_sq[OF sides(2), of A]
    unfolding triangle_incenter_def contact_BC_def Let_def
    by (simp add: dist_commute algebra_simps)
  show ?thesis
    unfolding triangle_inradius_def
  proof (rule power2_eq_imp_eq)
    show "(dist ?I (contact_BC A B C))\<^sup>2 =
        (dist ?I (contact_AB A B C))\<^sup>2"
      using BC_sq AB_sq by simp
    show "0 \<le> dist ?I (contact_BC A B C)"
      by simp
    show "0 \<le> dist ?I (contact_AB A B C)"
      by simp
  qed
qed

lemma triangle_incenter_contacts_dist:
  fixes A B C :: "real ^ 2"
  assumes "\<not> collinear {A, B, C}"
  shows
    "dist (triangle_incenter A B C) (contact_AB A B C) = triangle_inradius A B C"
    "dist (triangle_incenter A B C) (contact_AC A B C) = triangle_inradius A B C"
    "dist (triangle_incenter A B C) (contact_BC A B C) = triangle_inradius A B C"
proof -
  show "dist (triangle_incenter A B C) (contact_AB A B C) = triangle_inradius A B C"
    by (rule triangle_incenter_contact_AB_dist)
  show "dist (triangle_incenter A B C) (contact_AC A B C) = triangle_inradius A B C"
    by (rule triangle_incenter_contact_AC_dist[OF assms])
  show "dist (triangle_incenter A B C) (contact_BC A B C) = triangle_inradius A B C"
    by (rule triangle_incenter_contact_BC_dist[OF assms])
qed

lemma triangle_incenter_contacts_orthogonal:
  fixes A B C :: "real ^ 2"
  assumes "\<not> collinear {A, B, C}"
  shows
    "orthogonal (triangle_incenter A B C - contact_AB A B C) (B - A)"
    "orthogonal (triangle_incenter A B C - contact_AC A B C) (C - A)"
    "orthogonal (triangle_incenter A B C - contact_BC A B C) (C - B)"
proof -
  have sides: "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
    using noncollinear_triangle_distinct[OF assms] by blast+
  show "orthogonal (triangle_incenter A B C - contact_AB A B C) (B - A)"
    by (rule triangle_incenter_contact_AB_orthogonal[OF sides(1)])
  show "orthogonal (triangle_incenter A B C - contact_AC A B C) (C - A)"
    by (rule triangle_incenter_contact_AC_orthogonal[OF sides(2)])
  show "orthogonal (triangle_incenter A B C - contact_BC A B C) (C - B)"
    by (rule triangle_incenter_contact_BC_orthogonal[OF sides(3)])
qed

lemma dist_conway_point_past_first:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> d"
  shows "dist X (conway_point_past_first X Y d) = d"
proof -
  have "0 < dist X Y"
    using assms by simp
  then show ?thesis
    using assms
    unfolding conway_point_past_first_def
    by (simp add: dist_norm norm_minus_commute)
qed

lemma dist_conway_point_past_second:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> d"
  shows "dist Y (conway_point_past_second X Y d) = d"
proof -
  have "0 < dist X Y"
    using assms by simp
  then show ?thesis
    using assms
    unfolding conway_point_past_second_def
    by (simp add: dist_norm norm_minus_commute)
qed

lemma conway_point_past_first_contact:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y"
  shows "conway_point_past_first X Y p =
    side_contact_point X Y p q - (((p + q + dist X Y) / 2) / dist X Y) *\<^sub>R (Y - X)"
proof -
  let ?L = "dist X Y"
  let ?s = "(p + q + ?L) / 2"
  have Lpos: "0 < ?L"
    using assms by simp
  have scalar: "((?s - p) / ?L - ?s / ?L) = - (p / ?L)"
    using Lpos by (simp add: field_simps)
  have "side_contact_point X Y p q - (?s / ?L) *\<^sub>R (Y - X) =
      X + ((?s - p) / ?L) *\<^sub>R (Y - X) - (?s / ?L) *\<^sub>R (Y - X)"
    unfolding side_contact_point_def Let_def by simp
  also have "... = X + (((?s - p) / ?L - ?s / ?L) *\<^sub>R (Y - X))"
    by (simp add: scaleR_diff_left [symmetric])
  also have "... = X + (-(p / ?L) *\<^sub>R (Y - X))"
    using scalar by simp
  also have "... = X + (p / ?L) *\<^sub>R (X - Y)"
    by (simp add: scaleR_right_diff_distrib)
  also have "... = conway_point_past_first X Y p"
    unfolding conway_point_past_first_def ..
  finally show ?thesis
    by (rule sym)
qed

lemma conway_point_past_second_contact:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y"
  shows "conway_point_past_second X Y q =
    side_contact_point X Y p q + (((p + q + dist X Y) / 2) / dist X Y) *\<^sub>R (Y - X)"
proof -
  let ?L = "dist X Y"
  let ?s = "(p + q + ?L) / 2"
  have Lpos: "0 < ?L"
    using assms by simp
  have scalar: "((?s - p) / ?L + ?s / ?L) = 1 + q / ?L"
    using Lpos by (simp add: field_simps)
  have "side_contact_point X Y p q + (?s / ?L) *\<^sub>R (Y - X) =
      X + ((?s - p) / ?L) *\<^sub>R (Y - X) + (?s / ?L) *\<^sub>R (Y - X)"
    unfolding side_contact_point_def Let_def by simp
  also have "... = X + (((?s - p) / ?L + ?s / ?L) *\<^sub>R (Y - X))"
    by (simp add: scaleR_left_distrib [symmetric])
  also have "... = X + (1 + q / ?L) *\<^sub>R (Y - X)"
    using scalar by simp
  also have "... = Y + (q / ?L) *\<^sub>R (Y - X)"
    by (simp add: scaleR_left_distrib)
  also have "... = conway_point_past_second X Y q"
    unfolding conway_point_past_second_def ..
  finally show ?thesis
    by (rule sym)
qed

lemma dist_side_contact_first:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> p" "0 \<le> q"
  shows "dist (side_contact_point X Y p q) (conway_point_past_first X Y p) =
    (p + q + dist X Y) / 2"
proof -
  let ?s = "(p + q + dist X Y) / 2"
  have Lpos: "0 < dist X Y"
    using assms by simp
  have spos: "0 \<le> ?s"
    using assms Lpos by simp
  have point_eq:
    "conway_point_past_first X Y p =
      side_contact_point X Y p q - (?s / dist X Y) *\<^sub>R (Y - X)"
    by (rule conway_point_past_first_contact[OF assms(1)])
  have diff_eq:
    "side_contact_point X Y p q - conway_point_past_first X Y p =
      (?s / dist X Y) *\<^sub>R (Y - X)"
    using point_eq by simp
  have "dist (side_contact_point X Y p q) (conway_point_past_first X Y p) =
      norm ((?s / dist X Y) *\<^sub>R (Y - X))"
    by (simp add: dist_norm diff_eq)
  also have "... = abs (?s / dist X Y) * norm (Y - X)"
    by simp
  also have "... = (?s / dist X Y) * dist X Y"
    using Lpos spos by (simp add: dist_norm norm_minus_commute)
  also have "... = ?s"
    using Lpos by simp
  finally show ?thesis .
qed

lemma dist_side_contact_second:
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> p" "0 \<le> q"
  shows "dist (side_contact_point X Y p q) (conway_point_past_second X Y q) =
    (p + q + dist X Y) / 2"
proof -
  let ?s = "(p + q + dist X Y) / 2"
  have Lpos: "0 < dist X Y"
    using assms by simp
  have spos: "0 \<le> ?s"
    using assms Lpos by simp
  have point_eq:
    "conway_point_past_second X Y q =
      side_contact_point X Y p q + (?s / dist X Y) *\<^sub>R (Y - X)"
    by (rule conway_point_past_second_contact[OF assms(1)])
  have diff_eq:
    "side_contact_point X Y p q - conway_point_past_second X Y q =
      - (?s / dist X Y) *\<^sub>R (Y - X)"
    using point_eq by simp
  have "dist (side_contact_point X Y p q) (conway_point_past_second X Y q) =
      norm ((?s / dist X Y) *\<^sub>R (Y - X))"
    by (simp add: dist_norm diff_eq)
  also have "... = abs (?s / dist X Y) * norm (Y - X)"
    by simp
  also have "... = (?s / dist X Y) * dist X Y"
    using Lpos spos by (simp add: dist_norm norm_minus_commute)
  also have "... = ?s"
    using Lpos by simp
  finally show ?thesis .
qed

lemma dist_side_contact_first':
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> p" "0 \<le> q"
  shows "dist (conway_point_past_first X Y p) (side_contact_point X Y p q) =
    (p + q + dist X Y) / 2"
  using dist_side_contact_first[OF assms] by (simp add: dist_commute)

lemma dist_side_contact_second':
  fixes X Y :: "'a::real_normed_vector"
  assumes "X \<noteq> Y" "0 \<le> p" "0 \<le> q"
  shows "dist (conway_point_past_second X Y q) (side_contact_point X Y p q) =
    (p + q + dist X Y) / 2"
  using dist_side_contact_second[OF assms] by (simp add: dist_commute)

lemma orthogonal_conway_point_past_first_contact:
  fixes X Y v :: "'a::real_inner"
  assumes "X \<noteq> Y" "orthogonal v (Y - X)"
  shows "orthogonal v (conway_point_past_first X Y p - side_contact_point X Y p q)"
proof -
  let ?s = "(p + q + dist X Y) / 2"
  have point_eq:
    "conway_point_past_first X Y p - side_contact_point X Y p q =
      - (?s / dist X Y) *\<^sub>R (Y - X)"
    using conway_point_past_first_contact[OF assms(1), where p=p and q=q] by simp
  show ?thesis
    using assms(2) unfolding point_eq orthogonal_def by simp
qed

lemma orthogonal_conway_point_past_second_contact:
  fixes X Y v :: "'a::real_inner"
  assumes "X \<noteq> Y" "orthogonal v (Y - X)"
  shows "orthogonal v (conway_point_past_second X Y q - side_contact_point X Y p q)"
proof -
  let ?s = "(p + q + dist X Y) / 2"
  have point_eq:
    "conway_point_past_second X Y q - side_contact_point X Y p q =
      (?s / dist X Y) *\<^sub>R (Y - X)"
    using conway_point_past_second_contact[OF assms(1), where p=p and q=q] by simp
  show ?thesis
    using assms(2) unfolding point_eq orthogonal_def by simp
qed

lemma dist_from_orthogonal_foot:
  fixes I T P :: "'a::real_inner"
  assumes orth: "orthogonal (I - T) (P - T)"
    and IT: "dist I T = r"
    and TP: "dist T P = s"
    and r_nonneg: "0 \<le> r"
    and s_nonneg: "0 \<le> s"
  shows "dist I P = sqrt (r\<^sup>2 + s\<^sup>2)"
proof -
  have inner_flip: "(I - T) \<bullet> (T - P) = - ((I - T) \<bullet> (P - T))"
    by (simp add: inner_diff_right)
  have orth': "orthogonal (I - T) (T - P)"
    using orth inner_flip by (simp add: orthogonal_def)
  have Pythagoras:
    "(norm ((I - T) + (T - P)))\<^sup>2 =
      (norm (I - T))\<^sup>2 + (norm (T - P))\<^sup>2"
    by (rule norm_add_Pythagorean[OF orth'])
  have square_dist:
    "(dist I P)\<^sup>2 = r\<^sup>2 + s\<^sup>2"
    using Pythagoras IT TP
    by (simp add: dist_norm norm_minus_commute)
  have "dist I P = sqrt ((dist I P)\<^sup>2)"
    by simp
  also have "... = sqrt (r\<^sup>2 + s\<^sup>2)"
    using square_dist by simp
  finally show ?thesis .
qed

lemma conway_points_have_declared_lengths:
  assumes "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
  shows
    "dist A (conway_A_c A B C) = dist B C"
    "dist B (conway_B_c A B C) = dist C A"
    "dist A (conway_A_b A B C) = dist B C"
    "dist C (conway_C_b A B C) = dist A B"
    "dist B (conway_B_a A B C) = dist C A"
    "dist C (conway_C_a A B C) = dist A B"
  using assms
  unfolding conway_A_c_def conway_B_c_def conway_A_b_def conway_C_b_def
    conway_B_a_def conway_C_a_def
  by (simp_all add: dist_conway_point_past_first dist_conway_point_past_second)

lemma conway_points_about_contacts:
  assumes "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
  defines "s \<equiv> triangle_semiperimeter A B C"
  shows
    "dist (contact_AB A B C) (conway_A_c A B C) = s"
    "dist (contact_AB A B C) (conway_B_c A B C) = s"
    "dist (contact_AC A B C) (conway_A_b A B C) = s"
    "dist (contact_AC A B C) (conway_C_b A B C) = s"
    "dist (contact_BC A B C) (conway_B_a A B C) = s"
    "dist (contact_BC A B C) (conway_C_a A B C) = s"
  using assms
  unfolding s_def triangle_semiperimeter_def
    contact_AB_def contact_AC_def contact_BC_def
    conway_A_c_def conway_B_c_def conway_A_b_def conway_C_b_def
    conway_B_a_def conway_C_a_def
  by (simp_all add: dist_side_contact_first dist_side_contact_second
      dist_side_contact_first' dist_side_contact_second' dist_commute)

lemma conway_points_on_circle_from_contact_feet:
  fixes A B C I :: "real ^ 2"
  assumes sides: "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
    and r_nonneg: "0 \<le> r"
    and foot_AB: "dist I (contact_AB A B C) = r"
      "orthogonal (I - contact_AB A B C) (B - A)"
    and foot_AC: "dist I (contact_AC A B C) = r"
      "orthogonal (I - contact_AC A B C) (C - A)"
    and foot_BC: "dist I (contact_BC A B C) = r"
      "orthogonal (I - contact_BC A B C) (C - B)"
  defines "s \<equiv> triangle_semiperimeter A B C"
  shows
    "dist I (conway_A_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_A_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
proof -
  have s_nonneg: "0 \<le> s"
    unfolding s_def triangle_semiperimeter_def by simp
  have contact_dists:
    "dist (contact_AB A B C) (conway_A_c A B C) = s"
    "dist (contact_AB A B C) (conway_B_c A B C) = s"
    "dist (contact_AC A B C) (conway_A_b A B C) = s"
    "dist (contact_AC A B C) (conway_C_b A B C) = s"
    "dist (contact_BC A B C) (conway_B_a A B C) = s"
    "dist (contact_BC A B C) (conway_C_a A B C) = s"
    using conway_points_about_contacts[OF sides, folded s_def] .
  have orth_Ac:
    "orthogonal (I - contact_AB A B C) (conway_A_c A B C - contact_AB A B C)"
    using foot_AB(2)
    unfolding conway_A_c_def contact_AB_def
    by (rule orthogonal_conway_point_past_first_contact[OF sides(1)])
  have orth_Bc:
    "orthogonal (I - contact_AB A B C) (conway_B_c A B C - contact_AB A B C)"
    using foot_AB(2)
    unfolding conway_B_c_def contact_AB_def
    by (rule orthogonal_conway_point_past_second_contact[OF sides(1)])
  have orth_Ab:
    "orthogonal (I - contact_AC A B C) (conway_A_b A B C - contact_AC A B C)"
    using foot_AC(2)
    unfolding conway_A_b_def contact_AC_def
    by (rule orthogonal_conway_point_past_first_contact[OF sides(2)])
  have orth_Cb:
    "orthogonal (I - contact_AC A B C) (conway_C_b A B C - contact_AC A B C)"
    using foot_AC(2)
    unfolding conway_C_b_def contact_AC_def
    by (rule orthogonal_conway_point_past_second_contact[OF sides(2)])
  have orth_Ba:
    "orthogonal (I - contact_BC A B C) (conway_B_a A B C - contact_BC A B C)"
    using foot_BC(2)
    unfolding conway_B_a_def contact_BC_def
    by (rule orthogonal_conway_point_past_first_contact[OF sides(3)])
  have orth_Ca:
    "orthogonal (I - contact_BC A B C) (conway_C_a A B C - contact_BC A B C)"
    using foot_BC(2)
    unfolding conway_C_a_def contact_BC_def
    by (rule orthogonal_conway_point_past_second_contact[OF sides(3)])
  show "dist I (conway_A_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Ac foot_AB(1) contact_dists(1) r_nonneg s_nonneg])
  show "dist I (conway_B_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Bc foot_AB(1) contact_dists(2) r_nonneg s_nonneg])
  show "dist I (conway_A_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Ab foot_AC(1) contact_dists(3) r_nonneg s_nonneg])
  show "dist I (conway_C_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Cb foot_AC(1) contact_dists(4) r_nonneg s_nonneg])
  show "dist I (conway_B_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Ba foot_BC(1) contact_dists(5) r_nonneg s_nonneg])
  show "dist I (conway_C_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    by (rule dist_from_orthogonal_foot[OF orth_Ca foot_BC(1) contact_dists(6) r_nonneg s_nonneg])
qed

lemma conway_points_on_circle_from_noncollinear_contact_feet:
  fixes A B C I :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
    and r_nonneg: "0 \<le> r"
    and foot_AB: "dist I (contact_AB A B C) = r"
      "orthogonal (I - contact_AB A B C) (B - A)"
    and foot_AC: "dist I (contact_AC A B C) = r"
      "orthogonal (I - contact_AC A B C) (C - A)"
    and foot_BC: "dist I (contact_BC A B C) = r"
      "orthogonal (I - contact_BC A B C) (C - B)"
  defines "s \<equiv> triangle_semiperimeter A B C"
  shows
    "dist I (conway_A_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_A_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
proof -
  have sides: "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
    using noncollinear_triangle_distinct[OF triangle] by blast+
  show "dist I (conway_A_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    and "dist I (conway_B_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    and "dist I (conway_A_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    and "dist I (conway_C_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    and "dist I (conway_B_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    and "dist I (conway_C_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    using conway_points_on_circle_from_contact_feet
      [OF sides r_nonneg foot_AB foot_AC foot_BC, folded s_def] .
qed

theorem conway_circle_theorem:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  defines "I \<equiv> triangle_incenter A B C"
  defines "r \<equiv> triangle_inradius A B C"
  defines "s \<equiv> triangle_semiperimeter A B C"
  defines "A_c \<equiv> conway_A_c A B C"
  defines "B_c \<equiv> conway_B_c A B C"
  defines "A_b \<equiv> conway_A_b A B C"
  defines "C_b \<equiv> conway_C_b A B C"
  defines "B_a \<equiv> conway_B_a A B C"
  defines "C_a \<equiv> conway_C_a A B C"
  shows
    "dist I A_c = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I B_c = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I A_b = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I C_b = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I B_a = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I C_a = sqrt (r\<^sup>2 + s\<^sup>2)"
proof -
  have foot_dists:
    "dist I (contact_AB A B C) = r"
    "dist I (contact_AC A B C) = r"
    "dist I (contact_BC A B C) = r"
    using triangle_incenter_contacts_dist[OF triangle]
    unfolding I_def r_def by simp_all
  have foot_orthogonal:
    "orthogonal (I - contact_AB A B C) (B - A)"
    "orthogonal (I - contact_AC A B C) (C - A)"
    "orthogonal (I - contact_BC A B C) (C - B)"
    using triangle_incenter_contacts_orthogonal[OF triangle]
    unfolding I_def by simp_all
  have r_nonneg: "0 \<le> r"
    unfolding r_def by simp
  have circle:
    "dist I (conway_A_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_c A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_A_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_b A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_B_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    "dist I (conway_C_a A B C) = sqrt (r\<^sup>2 + s\<^sup>2)"
    using conway_points_on_circle_from_noncollinear_contact_feet
      [OF triangle r_nonneg foot_dists(1) foot_orthogonal(1)
        foot_dists(2) foot_orthogonal(2) foot_dists(3) foot_orthogonal(3),
        folded s_def] .
  show "dist I A_c = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding A_c_def by (rule circle(1))
  show "dist I B_c = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding B_c_def by (rule circle(2))
  show "dist I A_b = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding A_b_def by (rule circle(3))
  show "dist I C_b = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding C_b_def by (rule circle(4))
  show "dist I B_a = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding B_a_def by (rule circle(5))
  show "dist I C_a = sqrt (r\<^sup>2 + s\<^sup>2)"
    unfolding C_a_def by (rule circle(6))
qed


subsection \<open>Wrapper formulations\<close>

text \<open>
  The headline theorem above proves six separate distance equations.  For
  downstream use we package the result in two equivalent forms: as a
  subset of an explicit @{const sphere} centred at the incenter, and as a
  single bounded-universal statement over the explicit six-point set.
  We also expose the construction correctness as a separate theorem: each
  Conway point lies on the intended side line and is at the declared
  distance from the adjacent vertex.
\<close>

lemma conway_point_past_first_on_line:
  fixes X Y :: "'a::real_normed_vector"
  shows "conway_point_past_first X Y d = X + (- (d / dist X Y)) *\<^sub>R (Y - X)"
  unfolding conway_point_past_first_def
  by (simp add: scaleR_minus_right algebra_simps)

lemma conway_point_past_second_on_line:
  fixes X Y :: "'a::real_normed_vector"
  shows "conway_point_past_second X Y d
            = X + (1 + d / dist X Y) *\<^sub>R (Y - X)"
  unfolding conway_point_past_second_def
  by (simp add: scaleR_left_distrib)

theorem conway_construction_correct:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  shows
    \<comment> \<open>The six Conway points lie on the three side lines of the triangle.\<close>
    "\<exists>t::real. conway_A_c A B C = A + t *\<^sub>R (B - A)"
    "\<exists>t::real. conway_B_c A B C = A + t *\<^sub>R (B - A)"
    "\<exists>t::real. conway_A_b A B C = A + t *\<^sub>R (C - A)"
    "\<exists>t::real. conway_C_b A B C = A + t *\<^sub>R (C - A)"
    "\<exists>t::real. conway_B_a A B C = B + t *\<^sub>R (C - B)"
    "\<exists>t::real. conway_C_a A B C = B + t *\<^sub>R (C - B)"
    \<comment> \<open>Their distances from the adjacent vertex equal the opposite side length.\<close>
    "dist A (conway_A_c A B C) = dist B C"
    "dist B (conway_B_c A B C) = dist C A"
    "dist A (conway_A_b A B C) = dist B C"
    "dist C (conway_C_b A B C) = dist A B"
    "dist B (conway_B_a A B C) = dist C A"
    "dist C (conway_C_a A B C) = dist A B"
proof -
  have sides: "A \<noteq> B" "A \<noteq> C" "B \<noteq> C"
    using noncollinear_triangle_distinct[OF triangle] by blast+
  show
    "\<exists>t::real. conway_A_c A B C = A + t *\<^sub>R (B - A)"
    unfolding conway_A_c_def
    using conway_point_past_first_on_line[of A B "dist B C"] by blast
  show
    "\<exists>t::real. conway_B_c A B C = A + t *\<^sub>R (B - A)"
    unfolding conway_B_c_def
    using conway_point_past_second_on_line[of A B "dist C A"] by blast
  show
    "\<exists>t::real. conway_A_b A B C = A + t *\<^sub>R (C - A)"
    unfolding conway_A_b_def
    using conway_point_past_first_on_line[of A C "dist B C"] by blast
  show
    "\<exists>t::real. conway_C_b A B C = A + t *\<^sub>R (C - A)"
    unfolding conway_C_b_def
    using conway_point_past_second_on_line[of A C "dist A B"] by blast
  show
    "\<exists>t::real. conway_B_a A B C = B + t *\<^sub>R (C - B)"
    unfolding conway_B_a_def
    using conway_point_past_first_on_line[of B C "dist C A"] by blast
  show
    "\<exists>t::real. conway_C_a A B C = B + t *\<^sub>R (C - B)"
    unfolding conway_C_a_def
    using conway_point_past_second_on_line[of B C "dist A B"] by blast
  show
    "dist A (conway_A_c A B C) = dist B C"
    "dist B (conway_B_c A B C) = dist C A"
    "dist A (conway_A_b A B C) = dist B C"
    "dist C (conway_C_b A B C) = dist A B"
    "dist B (conway_B_a A B C) = dist C A"
    "dist C (conway_C_a A B C) = dist A B"
    using conway_points_have_declared_lengths[OF sides] by blast+
qed

definition conway_points :: "real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> real ^ 2 \<Rightarrow> (real ^ 2) set"
  where "conway_points A B C =
    {conway_A_c A B C, conway_B_c A B C, conway_A_b A B C,
     conway_C_b A B C, conway_B_a A B C, conway_C_a A B C}"

corollary conway_circle_theorem_sphere:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  shows
    "conway_points A B C
       \<subseteq> sphere (triangle_incenter A B C)
                 (sqrt ((triangle_inradius A B C)\<^sup>2
                        + (triangle_semiperimeter A B C)\<^sup>2))"
  using conway_circle_theorem[OF triangle]
  unfolding conway_points_def sphere_def by auto

corollary conway_circle_theorem_set:
  fixes A B C :: "real ^ 2"
  assumes triangle: "\<not> collinear {A, B, C}"
  shows
    "\<forall>P \<in> conway_points A B C.
       dist (triangle_incenter A B C) P
         = sqrt ((triangle_inradius A B C)\<^sup>2
                 + (triangle_semiperimeter A B C)\<^sup>2)"
  using conway_circle_theorem[OF triangle]
  unfolding conway_points_def by auto

end
