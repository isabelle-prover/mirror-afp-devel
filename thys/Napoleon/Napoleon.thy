(*  Title:      Napoleon.thy
    Author:     Arthur Freitas Ramos, 2026
    Maintainer: Arthur Freitas Ramos

    Napoleon's theorem in complex coordinates.

    The proof reuses the published Morley_Theorem session for its
    equilateral-triangle characterization instead of duplicating that
    infrastructure here.
*)

theory Napoleon
  imports
    "HOL-Decision_Procs.Commutative_Ring"
    "Morley_Theorem.Complex_Triangles"
begin

section \<open>Napoleon's construction\<close>

text \<open>
  A complex number \<open>s\<close> equal to \<open>cis (pi/3)\<close> or
  \<open>cis (-pi/3)\<close> rotates a directed side through one of the two
  equilateral-triangle angles.  The apex and the centre of the resulting
  equilateral triangle are defined parametrically so that the same algebraic
  lemmas cover both orientations.
\<close>

definition napoleon_apex :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "napoleon_apex s x y = x + s * (y - x)"

definition napoleon_centre :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "napoleon_centre s x y =
    (x + y + napoleon_apex s x y) / 3"

lemma napoleon_apex_displacement:
  "napoleon_apex s x y - x = s * (y - x)"
  by (simp add: napoleon_apex_def)

lemma equilateral_on_side:
  fixes x y s :: complex
  assumes "x \<noteq> y"
    and "s = cis (pi / 3) \<or> s = cis (-pi / 3)"
  shows
    "cdist y x = cdist (napoleon_apex s x y) x \<and>
     cdist (napoleon_apex s x y) x = cdist (napoleon_apex s x y) y"
proof -
  have hyx: "y \<noteq> x" using assms(1) by auto
  have hrot:
    "napoleon_apex s x y - x = cis (pi / 3) * (y - x) \<or>
       napoleon_apex s x y - x = cis (-pi / 3) * (y - x)"
    using assms(2) by (auto simp add: napoleon_apex_def)
  have h' :
      "cdist y x = cdist (napoleon_apex s x y) x \<and>
       cdist (napoleon_apex s x y) x = cdist (napoleon_apex s x y) y"
    using equilateral_caracterization[
      THEN iffD2, of y x "napoleon_apex s x y", OF hyx] hrot by blast
  show ?thesis using h' by (simp add: cdist_commute)
qed

section \<open>Algebra of the three centres\<close>

lemma cis_pi3_square:
  "(cis (pi / 3) :: complex) ^ 2 = cis (pi / 3) - 1"
  by (auto intro: complex_eqI
      simp: cis.code cos_60 sin_60 power2_eq_square algebra_simps)

lemma cis_minus_pi3_square:
  "(cis (-pi / 3) :: complex) ^ 2 = cis (-pi / 3) - 1"
  by (auto intro: complex_eqI
      simp: cis.code cos_60 sin_60 power2_eq_square algebra_simps)

lemma one_minus_cis_pi3:
  "(1 :: complex) - cis (pi / 3) = cis (-pi / 3)"
  by (auto intro: complex_eqI
      simp: cis.code cos_60 sin_60 algebra_simps)

lemma one_minus_cis_minus_pi3:
  "(1 :: complex) - cis (-pi / 3) = cis (pi / 3)"
  by (auto intro: complex_eqI
      simp: cis.code cos_60 sin_60 algebra_simps)

lemma napoleon_centre_cycle:
  fixes a b c s :: complex
  assumes "s ^ 2 = s - 1"
  shows
    "napoleon_centre s c a - napoleon_centre s a b =
       (1 - s) * (napoleon_centre s b c - napoleon_centre s a b)"
proof -
  have hsquare': "s * s = s - 1"
    using assms by (simp add: power2_eq_square)
  have hmult: "s * (s * z) = (s - 1) * z" for z :: complex
    by (simp add: hsquare' mult.assoc[symmetric] algebra_simps)
  from hsquare'
  show "napoleon_centre s c a - napoleon_centre s a b =
      (1 - s) * (napoleon_centre s b c - napoleon_centre s a b)"
    unfolding napoleon_centre_def napoleon_apex_def
    by (simp add: hmult algebra_simps field_simps)
qed

lemma napoleon_centres_equilateral:
  fixes a b c s :: complex
  assumes hsquare: "s ^ 2 = s - 1"
    and hroot: "1 - s = cis (pi / 3) \<or> 1 - s = cis (-pi / 3)"
  shows
    "cdist (napoleon_centre s b c) (napoleon_centre s a b) =
       cdist (napoleon_centre s c a) (napoleon_centre s a b) \<and>
     cdist (napoleon_centre s c a) (napoleon_centre s a b) =
       cdist (napoleon_centre s c a) (napoleon_centre s b c)"
proof -
  have hdiff:
      "napoleon_centre s c a - napoleon_centre s a b =
        (1 - s) * (napoleon_centre s b c - napoleon_centre s a b)"
    by (rule napoleon_centre_cycle[OF hsquare])
  show ?thesis
  proof (cases "napoleon_centre s b c = napoleon_centre s a b")
    case True
    have hca:
        "napoleon_centre s c a = napoleon_centre s a b"
      using hdiff True by simp
    show ?thesis by (simp add: True hca)
  next
    case False
    have hrot:
        "napoleon_centre s c a - napoleon_centre s a b =
            cis (pi / 3) * (napoleon_centre s b c - napoleon_centre s a b) \<or>
         napoleon_centre s c a - napoleon_centre s a b =
            cis (-pi / 3) * (napoleon_centre s b c - napoleon_centre s a b)"
      using hdiff hroot by (auto simp add: hdiff)
    have h' :
        "cdist (napoleon_centre s b c) (napoleon_centre s a b) =
           cdist (napoleon_centre s c a) (napoleon_centre s a b) \<and>
         cdist (napoleon_centre s c a) (napoleon_centre s a b) =
           cdist (napoleon_centre s c a) (napoleon_centre s b c)"
      using equilateral_caracterization[
        THEN iffD2, of "napoleon_centre s b c" "napoleon_centre s a b"
           "napoleon_centre s c a", OF False] hrot by blast
    show ?thesis by (rule h')
  qed
qed

section \<open>External orientation and Napoleon's theorem\<close>

text \<open>
  The sign of the oriented area of the triangle is the sign of the
  imaginary part of the quotient below.  Choosing the opposite rotation
  makes the equilateral triangle on the directed side \<open>a b\<close> lie on
  the exterior side; the same choice works cyclically on \<open>b c\<close> and
  \<open>c a\<close>.  This exteriority claim is formalized by
  \<open>external_side\<close>: the signed side orientations of the third vertex
  and the constructed apex have strictly negative product.
\<close>

definition napoleon_external_rotation :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where
    "napoleon_external_rotation a b c =
      (if 0 < Im ((c - a) / (b - a))
       then cis (-pi / 3)
       else cis (pi / 3))"

definition side_orientation :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real"
  where "side_orientation a b x = Im ((x - a) / (b - a))"

definition external_side :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  where
    "external_side a b c x \<longleftrightarrow>
       side_orientation a b c * side_orientation a b x < 0"

lemma napoleon_external_rotation_cases:
  "napoleon_external_rotation a b c = cis (pi / 3) \<or>
   napoleon_external_rotation a b c = cis (-pi / 3)"
  unfolding napoleon_external_rotation_def
  by (split if_split; simp)

lemma napoleon_external_rotation_square:
  "napoleon_external_rotation a b c ^ 2 =
     napoleon_external_rotation a b c - 1"
proof (cases "0 < Im ((c - a) / (b - a))")
  case True
  show ?thesis
    unfolding napoleon_external_rotation_def
    using cis_minus_pi3_square True by (simp add: True)
next
  case False
  show ?thesis
    unfolding napoleon_external_rotation_def
    using cis_pi3_square False by (simp add: False)
qed

lemma napoleon_external_rotation_one_minus:
  "1 - napoleon_external_rotation a b c = cis (pi / 3) \<or>
   1 - napoleon_external_rotation a b c = cis (-pi / 3)"
proof (cases "0 < Im ((c - a) / (b - a))")
  case True
  show ?thesis
    unfolding napoleon_external_rotation_def
    using one_minus_cis_minus_pi3 True by (simp add: True)
next
  case False
  show ?thesis
    unfolding napoleon_external_rotation_def
    using one_minus_cis_pi3 False by (simp add: False)
qed

lemma oriented_area_cycle:
  "Im ((c - a) * cnj (b - a)) =
     Im ((a - b) * cnj (c - b))"
  by (simp add: algebra_simps)

lemma napoleon_external_rotation_cyclic:
  "napoleon_external_rotation a b c =
     napoleon_external_rotation b c a"
proof -
  have hleft:
      "0 < Im ((c - a) / (b - a)) \<longleftrightarrow>
       0 < Im ((c - a) * cnj (b - a))"
    using Im_complex_div_gt_0[of "(c - a)" "(b - a)"] by simp
  have hright:
      "0 < Im ((a - b) / (c - b)) \<longleftrightarrow>
       0 < Im ((a - b) * cnj (c - b))"
    using Im_complex_div_gt_0[of "(a - b)" "(c - b)"] by simp
  have harea:
      "Im ((c - a) * cnj (b - a)) =
       Im ((a - b) * cnj (c - b))"
    by (rule oriented_area_cycle)
  have hpos:
      "0 < Im ((c - a) / (b - a)) \<longleftrightarrow>
       0 < Im ((a - b) / (c - b))"
    using hleft hright harea by (simp add: harea)
  show ?thesis
    unfolding napoleon_external_rotation_def
    using hpos by simp
qed

lemma noncollinear_distinct:
  assumes "\<not> collinear a b c"
  shows "a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a"
proof -
  have hab: "a \<noteq> b"
    using assms unfolding collinear_def by auto
  have hbc: "b \<noteq> c"
  proof
    assume "b = c"
    with hab have "collinear a b c"
      by (simp add: collinear_def)
    with assms show False by contradiction
  qed
  have hca: "c \<noteq> a"
  proof
    assume "c = a"
    with hab have "collinear a b c"
      by (simp add: collinear_def)
    with assms show False by contradiction
  qed
  show ?thesis by (intro conjI; fact)
qed

lemma side_orientation_nonzero:
  assumes hncol: "\<not> collinear a b c"
  shows "side_orientation a b c \<noteq> 0"
  using hncol unfolding side_orientation_def collinear_def by auto

lemma side_orientation_apex:
  fixes a b s :: complex
  assumes "a \<noteq> b"
  shows
    "side_orientation a b (napoleon_apex s a b) = Im s"
proof -
  have hba: "b - a \<noteq> (0 :: complex)" using assms by auto
  have hratio:
      "(napoleon_apex s a b - a) / (b - a) = s"
    unfolding napoleon_apex_def
    using hba by (simp add: field_simps)
  show ?thesis
    unfolding side_orientation_def
    using hratio by simp
qed

lemma Im_cis_pi3_pos:
  "0 < Im (cis (pi / 3) :: complex)"
proof -
  have hroot: "0 < sqrt (3 :: real)"
    by (rule real_sqrt_gt_zero) simp
  show ?thesis by (simp add: cis.code sin_60 hroot)
qed

lemma Im_cis_minus_pi3_neg:
  "Im (cis (-pi / 3) :: complex) < 0"
proof -
  have hroot: "0 < sqrt (3 :: real)"
    by (rule real_sqrt_gt_zero) simp
  show ?thesis by (simp add: cis.code sin_60 hroot)
qed

lemma napoleon_external_side:
  fixes a b c :: complex
  assumes hncol: "\<not> collinear a b c"
  shows
    "external_side a b c
       (napoleon_apex (napoleon_external_rotation a b c) a b)"
proof -
  obtain hab hbc hca where "a \<noteq> b" "b \<noteq> c" "c \<noteq> a"
    using noncollinear_distinct[OF hncol] by blast
  have hside: "side_orientation a b c \<noteq> 0"
    by (rule side_orientation_nonzero[OF hncol])
  show ?thesis
    unfolding external_side_def
  proof (cases "0 < side_orientation a b c")
    case True
    have hcond: "0 < Im ((c - a) / (b - a))"
      using True by (simp add: side_orientation_def)
    have hrot:
        "napoleon_external_rotation a b c = cis (-pi / 3)"
      unfolding napoleon_external_rotation_def side_orientation_def
      using hcond by simp
    have hapex:
        "side_orientation a b
           (napoleon_apex (napoleon_external_rotation a b c) a b) < 0"
      using side_orientation_apex[OF \<open>a \<noteq> b\<close>]
        Im_cis_minus_pi3_neg hrot by simp
    show "side_orientation a b c *
        side_orientation a b
          (napoleon_apex (napoleon_external_rotation a b c) a b) < 0"
      by (rule mult_pos_neg[OF True hapex])
  next
    case False
    have hside_neg: "side_orientation a b c < 0"
      using hside False by linarith
    have hcond: "\<not> 0 < Im ((c - a) / (b - a))"
      using False by (simp add: side_orientation_def)
    have hrot:
        "napoleon_external_rotation a b c = cis (pi / 3)"
      unfolding napoleon_external_rotation_def side_orientation_def
      using hcond by simp
    have hapex:
        "0 < side_orientation a b
           (napoleon_apex (napoleon_external_rotation a b c) a b)"
      using side_orientation_apex[OF \<open>a \<noteq> b\<close>]
        Im_cis_pi3_pos hrot by simp
    show "side_orientation a b c *
        side_orientation a b
          (napoleon_apex (napoleon_external_rotation a b c) a b) < 0"
      by (rule mult_neg_pos[OF hside_neg hapex])
  qed
qed

lemma napoleon_external_construction:
  assumes hncol: "\<not> collinear a b c"
  shows
    "cdist b a =
       cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a =
       cdist (napoleon_apex (napoleon_external_rotation a b c) a b) b \<and>
     cdist c b =
       cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b =
       cdist (napoleon_apex (napoleon_external_rotation a b c) b c) c \<and>
     cdist a c =
       cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c =
       cdist (napoleon_apex (napoleon_external_rotation a b c) c a) a \<and>
     external_side a b c
       (napoleon_apex (napoleon_external_rotation a b c) a b) \<and>
     external_side b c a
       (napoleon_apex (napoleon_external_rotation a b c) b c) \<and>
     external_side c a b
       (napoleon_apex (napoleon_external_rotation a b c) c a)"
proof -
  obtain hab hbc hca where "a \<noteq> b" "b \<noteq> c" "c \<noteq> a"
    using noncollinear_distinct[OF hncol] by blast
  have hs:
      "napoleon_external_rotation a b c = cis (pi / 3) \<or>
       napoleon_external_rotation a b c = cis (-pi / 3)"
    by (rule napoleon_external_rotation_cases)
  have hab':
      "cdist b a =
         cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a \<and>
       cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a =
         cdist (napoleon_apex (napoleon_external_rotation a b c) a b) b"
    using equilateral_on_side[of a b "napoleon_external_rotation a b c"]
      \<open>a \<noteq> b\<close> hs by blast
  have hbc':
      "cdist c b =
         cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b \<and>
       cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b =
         cdist (napoleon_apex (napoleon_external_rotation a b c) b c) c"
    using equilateral_on_side[of b c "napoleon_external_rotation a b c"]
      \<open>b \<noteq> c\<close> hs by blast
  have hca':
      "cdist a c =
         cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c \<and>
       cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c =
         cdist (napoleon_apex (napoleon_external_rotation a b c) c a) a"
    using equilateral_on_side[of c a "napoleon_external_rotation a b c"]
      \<open>c \<noteq> a\<close> hs by blast
  have hside_ab:
      "external_side a b c
         (napoleon_apex (napoleon_external_rotation a b c) a b)"
    by (rule napoleon_external_side[OF hncol])
  have hncol_bca: "\<not> collinear b c a"
    using hncol by (metis collinear_sym1 collinear_sym2)
  have hncol_cab: "\<not> collinear c a b"
    using hncol by (metis collinear_sym1 collinear_sym2)
  have hrot_bc:
      "napoleon_external_rotation a b c =
       napoleon_external_rotation b c a"
    by (rule napoleon_external_rotation_cyclic)
  have hrot_ca:
      "napoleon_external_rotation a b c =
       napoleon_external_rotation c a b"
    using napoleon_external_rotation_cyclic[of a b c]
      napoleon_external_rotation_cyclic[of b c a] by simp
  have hside_bc0:
      "external_side b c a
         (napoleon_apex (napoleon_external_rotation b c a) b c)"
    by (rule napoleon_external_side[OF hncol_bca])
  have hside_bc:
      "external_side b c a
         (napoleon_apex (napoleon_external_rotation a b c) b c)"
    using hside_bc0 hrot_bc by (simp add: hrot_bc)
  have hside_ca0:
      "external_side c a b
         (napoleon_apex (napoleon_external_rotation c a b) c a)"
    by (rule napoleon_external_side[OF hncol_cab])
  have hside_ca:
      "external_side c a b
         (napoleon_apex (napoleon_external_rotation a b c) c a)"
    using hside_ca0 hrot_ca by (simp add: hrot_ca)
  show ?thesis using hab' hbc' hca' hside_ab hside_bc hside_ca by blast
qed

theorem napoleon_theorem:
  fixes a b c :: complex
  assumes hncol: "\<not> collinear a b c"
  shows
    "cdist (napoleon_centre (napoleon_external_rotation a b c) b c)
       (napoleon_centre (napoleon_external_rotation a b c) a b) =
       cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
         (napoleon_centre (napoleon_external_rotation a b c) a b) \<and>
     cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
       (napoleon_centre (napoleon_external_rotation a b c) a b) =
       cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
         (napoleon_centre (napoleon_external_rotation a b c) b c)"
  using napoleon_centres_equilateral[
    OF napoleon_external_rotation_square
       napoleon_external_rotation_one_minus]
  by blast

theorem napoleon_external_theorem:
  fixes a b c :: complex
  assumes hncol: "\<not> collinear a b c"
  shows
    "(cdist b a =
       cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) a b) a =
       cdist (napoleon_apex (napoleon_external_rotation a b c) a b) b \<and>
     cdist c b =
       cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) b c) b =
       cdist (napoleon_apex (napoleon_external_rotation a b c) b c) c \<and>
     cdist a c =
       cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c \<and>
     cdist (napoleon_apex (napoleon_external_rotation a b c) c a) c =
       cdist (napoleon_apex (napoleon_external_rotation a b c) c a) a \<and>
     external_side a b c
       (napoleon_apex (napoleon_external_rotation a b c) a b) \<and>
     external_side b c a
       (napoleon_apex (napoleon_external_rotation a b c) b c) \<and>
     external_side c a b
       (napoleon_apex (napoleon_external_rotation a b c) c a)) \<and>
     (cdist (napoleon_centre (napoleon_external_rotation a b c) b c)
        (napoleon_centre (napoleon_external_rotation a b c) a b) =
        cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
          (napoleon_centre (napoleon_external_rotation a b c) a b) \<and>
      cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
        (napoleon_centre (napoleon_external_rotation a b c) a b) =
        cdist (napoleon_centre (napoleon_external_rotation a b c) c a)
          (napoleon_centre (napoleon_external_rotation a b c) b c))"
  using napoleon_external_construction[OF hncol]
    napoleon_theorem[OF hncol]
  by blast

end
