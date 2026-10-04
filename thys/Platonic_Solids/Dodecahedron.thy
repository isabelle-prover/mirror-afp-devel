section\<open>Dodecahedron\<close>

theory Dodecahedron
  imports
    Computation
    "HOL-Library.Quadratic_Discriminant"
begin

subsection\<open>Definition\<close>

definition std_dodecahedron :: "(real, 3) vec set"
  where "std_dodecahedron \<equiv> convex hull
    {vector [1, 1, 1], vector [1, 1, -1],
     vector [1, -1, 1], vector [1, -1, -1],
     vector [-1, 1, 1], vector [-1, 1, -1],
     vector [-1, -1, 1], vector [-1, -1, -1],
     vector [0, inverse \<phi>, \<phi>], vector[ 0, inverse \<phi>, -\<phi>],
     vector [0, -inverse \<phi>, \<phi>], vector [0, -inverse \<phi>, -\<phi>],
     vector [inverse \<phi>, \<phi>, 0], vector [inverse \<phi>, -\<phi>, 0],
     vector [-inverse \<phi>, \<phi>, 0], vector [-inverse \<phi>, -\<phi>, 0],
     vector [\<phi>, 0, inverse \<phi>], vector [-\<phi>, 0, inverse \<phi>],
     vector [\<phi>, 0, -inverse \<phi>], vector [-\<phi>, 0, -inverse \<phi>]}"

lemma std_dodecahedron_explicit:
  shows "std_dodecahedron = convex hull
    { vector[1, 1, 1],
      vector[1, 1, -1],
      vector[1, -1, 1],
      vector[1, -1, -1],
      vector[-1, 1, 1],
      vector[-1, 1, -1],
      vector[-1, -1, 1],
      vector[-1, -1, -1],
      vector[0, -1 / 2 + 1 / 2 * sqrt(5), 1 / 2 + 1 / 2 * sqrt(5)],
      vector[0, -1 / 2 + 1 / 2 * sqrt(5), -1 / 2 + -1 / 2 * sqrt(5)],
      vector[0, 1 / 2 + -1 / 2 * sqrt(5), 1 / 2 + 1 / 2 * sqrt(5)],
      vector[0, 1 / 2 + -1 / 2 * sqrt(5), -1 / 2 + -1 / 2 * sqrt(5)],
      vector[-1 / 2 + 1 / 2 * sqrt(5), 1 / 2 + 1 / 2 * sqrt(5), 0],
      vector[-1 / 2 + 1 / 2 * sqrt(5), -1 / 2 + -1 / 2 * sqrt(5), 0],
      vector[1 / 2 + -1 / 2 * sqrt(5), 1 / 2 + 1 / 2 * sqrt(5), 0],
      vector[1 / 2 + -1 / 2 * sqrt(5), -1 / 2 + -1 / 2 * sqrt(5), 0],
      vector[1 / 2 + 1 / 2 * sqrt(5), 0, -1 / 2 + 1 / 2 * sqrt(5)],
      vector[-1 / 2 + -1 / 2 * sqrt(5), 0, -1 / 2 + 1 / 2 * sqrt(5)],
      vector[1 / 2 + 1 / 2 * sqrt(5), 0, 1 / 2 + -1 / 2 * sqrt(5)],
      vector[-1 / 2 + -1 / 2 * sqrt(5), 0, 1 / 2 + -1 / 2 * sqrt(5)]}"
proof -
  have "inverse \<phi> = 2 / (1 + sqrt 5)" by simp
  also have "... = (2 * (1 - sqrt 5)) / ((1 + sqrt 5) * (1 - sqrt 5))"
    by (metis mult.commute nonzero_mult_divide_mult_cancel_right2 numeral_eq_one_iff real_sqrt_eq_1_iff right_minus_eq
        verit_eq_simplify(12))
  also have "... = (2 - 2 * sqrt 5) / (-4)"
    using square_diff_square_factored[of "1" "sqrt 5"] by auto
  finally have "inverse \<phi> = -1/2 + 1/2 * sqrt 5"
    by argo
  moreover have golden: "\<phi> = 1/2 + 1/2 * sqrt 5"
    by auto
  ultimately have golden_inverse: "inverse (1/2 + 1/2 * sqrt 5) = -1/2 + 1/2 * sqrt 5"
    by auto
  show ?thesis
    unfolding std_dodecahedron_def golden golden_inverse
    by simp
qed

lemma std_dodecahedron_eq:
  shows "std_dodecahedron = convex hull
    { vector[rat5 1 0, rat5 1 0, rat5 1 0],
      vector[rat5 1 0, rat5 1 0, rat5 (-1) 0],
      vector[rat5 1 0, rat5 (-1) 0, rat5 1 0],
      vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0],
      vector[rat5 (-1) 0, rat5 1 0, rat5 1 0],
      vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0],
      vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0],
      vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0],
      vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)],
      vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)],
      vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)],
      vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)],
      vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0],
      vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0],
      vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0],
      vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0],
      vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)],
      vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)],
      vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)],
      vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)]}"
  unfolding std_dodecahedron_explicit rat5_def
  by (simp add: of_rat_divide of_rat_minus)

lemma dodecahedron_fulldim:
  shows "aff_dim std_dodecahedron = 3"
  unfolding std_dodecahedron_def
  apply (rule polytope_3D)
  by (simp add: vector3_sub vector3_cross vector3_dot vector3_eq_0)+

lemma dodecahedron_polyhedron:
  shows "polyhedron std_dodecahedron"
  by (simp add: std_dodecahedron_def polytope_convex_hull polytope_imp_polyhedron)

subsection\<open>Facets, edges, and vertices\<close>

lemma dodecahedron_facets:
  fixes f :: "(real^3) set"
  shows "f face_of std_dodecahedron \<and> aff_dim f = 2 \<longleftrightarrow>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]}"
  unfolding std_dodecahedron_eq
  apply (simp only: compute_faces_2 finite_insert finite.emptyI)
  apply (simp only: compute_faces_2_step_1 bex_empty simp_thms(31))
  apply (simp only: compute_faces_2_step_2 bex_empty simp_thms(31))
  apply (simp only: empty_iff ball_insert bex_empty bex_simps(5) ball_simps(5) simp_thms(21,31))
  apply (simp only: vector3_sub vector3_cross vector3_eq_0 rat5_add rat5_sub rat5_mul rat5_eq)
  apply (simp add: vector3_eq_0 vector3_dot rat5_add rat5_sub rat5_mul rat5_le rat5_eq rat5_eq_0 Let_def)
    \<comment> \<open>very slow, ca 600s\<close>
  apply (simp only: insert_commute)
  by linarith

lemma dodecahedron_facet1_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v4 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 1 (-1), rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v5} \<or> e = convex hull {v2, v4} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v3, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 1 1"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet2_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v4 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 1 0] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 1 (-1), rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v5} \<or> e = convex hull {v2, v4} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v3, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-1) (-1)"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet3_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 1 0] :: real^3"
      and "v4 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-3) 1, rat5 0 0, rat5 (-1) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 2 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet4_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v4 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 3 (-1), rat5 0 0, rat5 (-1) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-2) 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet5_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 1 (-1), rat5 (-3) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v4} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v3, v5} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 2 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet6_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 (-1) 1, rat5 (-3) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v4} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v3, v5} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-2) 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet7_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 (-1) 1, rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v4} \<or> e = convex hull {v1, v5} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-1) (-1)"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet8_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 1 (-1), rat5 3 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v4} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v3, v5} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-2) 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet9_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 1 0, rat5 1 0] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 1 0] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 (-1) 1, rat5 3 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v4} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v3, v5} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 2 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet10_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v4 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v5 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 1 0] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 (-1) 1, rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v4} \<or> e = convex hull {v1, v5} \<or> e = convex hull {v2, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 1 1"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet11_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 1 0] :: real^3"
      and "v4 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-3) 1, rat5 0 0, rat5 1 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 (-2) 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma dodecahedron_facet12_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
      and "v3 \<equiv> vector[rat5 1 0, rat5 1 0, rat5 (-1) 0] :: real^3"
      and "v4 \<equiv> vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "v5 \<equiv> vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 3 (-1), rat5 0 0, rat5 1 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3, v4, v5}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v5} \<or> e = convex hull {v3, v4} \<or> e = convex hull {v4, v5})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3, v4, v5} \<Longrightarrow> n \<bullet> x = rat5 2 0"
    unfolding assms
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3, v4, v5}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemmas dodecahedron_facet_edges =
  dodecahedron_facet1_edges dodecahedron_facet2_edges dodecahedron_facet3_edges
  dodecahedron_facet4_edges dodecahedron_facet5_edges dodecahedron_facet6_edges
  dodecahedron_facet7_edges dodecahedron_facet8_edges dodecahedron_facet9_edges
  dodecahedron_facet10_edges dodecahedron_facet11_edges dodecahedron_facet12_edges

lemma dodecahedron_edges_per_face:
  assumes "f face_of std_dodecahedron"
      and "aff_dim f = 2"
  shows "card {e. e face_of std_dodecahedron \<and> aff_dim e = 1 \<and> e \<subseteq> f} = 5"
  using conjI[OF assms] unfolding dodecahedron_facets face_edge_set_eq[OF assms(1)]
  apply (elim disjE forw_subst)
  unfolding dodecahedron_facet_edges set_cases card_5_iff
    segment_convex_hull[symmetric] closed_segment_eq
  by (simp_all add: vector3_eq doubleton_eq_iff rat5_eq)

lemma dodecahedron_edges:
  "e face_of std_dodecahedron \<and> aff_dim e = 1 \<longleftrightarrow>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 1 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  then obtain f where f_facts: "f face_of std_dodecahedron \<and> aff_dim f = 2" "e face_of f \<and> aff_dim e = 1"
    using dodecahedron_polyhedron dodecahedron_fulldim edge_belongs_to_face
    by blast
  show ?rhs
    using f_facts unfolding dodecahedron_facets
    apply (elim disjE) apply (all \<open>hypsubst_thin\<close>)
    unfolding dodecahedron_facet_edges
    by linarith+
next
  assume "?rhs"
  then show "?lhs"
    using dodecahedron_facets dodecahedron_facet_edges
    by (smt (verit, ccfv_threshold) face_of_trans insertI1 insert_commute mem_Collect_eq)
qed

lemma dodecahedron_vertices:
  shows "(v face_of std_dodecahedron \<and> aff_dim v = 0) =
         (v = {vector[rat5 1 0, rat5 1 0, rat5 1 0]} \<or>
          v = {vector[rat5 1 0, rat5 1 0, rat5 (-1) 0]} \<or>
          v = {vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]} \<or>
          v = {vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]} \<or>
          v = {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} \<or>
          v = {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)]} \<or>
          v = {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)]} \<or>
          v = {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)]} \<or>
          v = {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)]})"
  (is "?lhs = ?rhs")
proof
  assume *: "?lhs"
  then obtain e where "e face_of std_dodecahedron" "aff_dim e = 1" "v face_of e"
    using dodecahedron_polyhedron dodecahedron_fulldim vertex_belongs_to_edge
    by blast
  show "?rhs"
    using conjI[OF \<open>e face_of std_dodecahedron\<close> \<open>aff_dim e = 1\<close>]
    unfolding dodecahedron_edges
    using vertices_of_edge[OF _ \<open>v face_of e\<close>] *
    by metis+
next
  assume "?rhs"
  then show "?lhs"
    apply (elim disjE forw_subst)
    by (smt (z3) aff_dim_sing extreme_point_of_segment face_of_singleton face_of_trans
        segment_convex_hull dodecahedron_edges)+
qed

lemma dodecahedron_edges_per_vertex:
  assumes "v face_of std_dodecahedron"
      and "aff_dim v = 0"
  shows "card {e. e face_of std_dodecahedron \<and> aff_dim e = 1 \<and> v \<subseteq> e} = 3"
  unfolding vertex_edge_set_eq[OF assms(1)]
  using conjI[OF assms]
  unfolding dodecahedron_vertices conj_assoc[symmetric] dodecahedron_edges
  by (elim disjE forw_subst) edges_per_vertex+

subsection\<open>Regularity\<close>

lemma dodecahedron_congruent_edges:
  assumes "e1 face_of std_dodecahedron \<and> aff_dim e1 = 1"
      and "e2 face_of std_dodecahedron \<and> aff_dim e2 = 1"
    shows "e1 congruent e2"
proof -
  let ?edges =
    "{convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]}}"
  have "e1 \<in> ?edges" "e2 \<in> ?edges"
    using assms unfolding dodecahedron_edges
    by auto
  moreover have "\<forall>e\<in>?edges.
          convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)]} congruent e"
    apply (simp only: ball_simps(7) Set.ball_empty simp_thms(21))
    unfolding conj_assoc[symmetric] segment_convex_hull[symmetric]
    apply (rule conjI)+
    apply (all \<open>rule congruent_segments\<close>)
    unfolding dist_norm vector3_sub
    apply (simp_all add: norm_eq rat5_sub del: cancel_comm_monoid_add_class.diff_cancel diff_self)
    by (simp_all add: vector3_dot rat5_mul rat5_add rat5_eq)
  ultimately show ?thesis
    using congruent_set by meson
qed

lemma dodecahedron_congruent_faces:
  assumes "f1 face_of std_dodecahedron \<and> aff_dim f1 = 2"
      and "f2 face_of std_dodecahedron \<and> aff_dim f2 = 2"
    shows "f1 congruent f2"
proof -
  let ?faces =
    "{convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]}}"
  have "f1 \<in> ?faces" "f2 \<in> ?faces"
    using assms dodecahedron_facets
    by auto
  moreover have "\<forall>f\<in>?faces.
          convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} congruent f"
    apply (simp only: ball_simps(7) Set.ball_empty simp_thms(21))
    unfolding conj_assoc[symmetric]
    by (rule conjI)+ show_congruence+
  ultimately show ?thesis
    using congruent_set by meson
qed

lemma dodecahedron_facet1_equiangular:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)] :: real^3"
  defines "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)] :: real^3"
  defines "v3 \<equiv> vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
  defines "v4 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0] :: real^3"
  defines "v5 \<equiv> vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0] :: real^3"
  shows "equiangular (convex hull {v1, v2, v3, v4, v5}) (3 * pi / 5)"
  unfolding equiangular_def
proof (clarify)
  fix e1 e2 v
  assume *: "e1 face_of convex hull {v1, v2, v3, v4, v5}" "aff_dim e1 = 1"
            "e2 face_of convex hull {v1, v2, v3, v4, v5}" "aff_dim e2 = 1"
            "e1 \<noteq> e2" "v extreme_point_of e1" "v extreme_point_of e2"
  have "arccos (1/4 - 1/4 * sqrt 5) = 3 * pi / 5"
  proof (rule arccos_unique)
    show "0 \<le> 3 * pi / 5" by simp
    show "3 * pi / 5 \<le> pi" by simp

    define t where "t = 3 * pi / 5"
    define c where "c = cos t"
    define s where "s = sin t"

    have "cos (3 * t) = cos (2 * t + t)" by simp
    also have "... = (2 * c^2 - 1) * c - 2 * s^2 * c"
      unfolding cos_add c_def s_def
      by (simp add: cos_double_cos power2_eq_square sin_double)
    finally have cos_3t: "cos (3 * t) = 4 * c^3 - 3 * c"
      unfolding sin_squared_eq c_def s_def by algebra

    have "sin (3 * t) = sin (2 * t + t)" by simp
    also have "... = 2 * s * c^2 + (1 - 2 * s^2) * s"
      unfolding sin_add c_def s_def
      by (simp add: cos_double_sin power2_eq_square sin_double)
    finally have sin_3t: "sin (3 * t) = 3 * s - 4 * s^3"
      unfolding cos_squared_eq c_def s_def by algebra

    have "cos (5 * t) = cos (3 * t + 2 * t)" by simp
    also have "... = cos (3 * t) * cos (2 * t) - sin (3 * t) * sin (2 * t)"
      using cos_add by blast
    also have "... = (4 * c^3 - 3 * c) * (2 * c^2 - 1) - (3 * s - 4 * s^3) * 2 * s * c"
      by (simp add: cos_3t sin_3t c_def s_def cos_double_cos sin_double)
    also have "... = (4 * c^3 - 3 * c) * (2 * c^2 - 1) - 6 * s^2 * c + 8 * (s^2)^2 * c"
      by algebra
    also have "... = (4 * c^3 - 3 * c) * (2 * c^2 - 1) - 6 * (1 - c^2) * c + 8 * (1 - c^2)^2 * c"
      unfolding sin_squared_eq c_def s_def by blast
    finally have "cos (5 * t) = 16 * c^5 - 20 * c^3 + 5 * c"
      by algebra
    moreover have "cos (5 * t) = -1"
      unfolding t_def by simp
    ultimately have "16 * c^5 - 20 * c^3 + 5 * c + 1 = 0"
      by simp
    then have "(c + 1) * (4 * c^2 - 2 * c - 1)^2 = 0"
      by algebra
    then have "c + 1 = 0 \<or> 4 * c^2 - 2 * c - 1 = 0"
      by simp

    have "\<exists>!x. 0 \<le> x \<and> x \<le> pi \<and> cos x = - 1"
      using cos_total[of "-1"] by linarith
    moreover have "0 \<le> pi \<and> pi \<le> pi \<and> cos pi = -1"
      using cos_pi by simp
    moreover have "3 * pi / 5 \<noteq> pi" "0 \<le> 3 * pi / 5 \<and> 3 * pi / 5 \<le> pi"
      by auto
    ultimately have "c \<noteq> -1"
      unfolding c_def t_def by blast
    then have "c + 1 \<noteq> 0"
      by linarith

    then have "4 * c^2 + (-2) * c + (-1) = 0"
      using \<open>c + 1 = 0 \<or> 4 * c^2 - 2 * c - 1 = 0\<close>
      by simp
    moreover have "discrim 4 (-2) (-1) = 20"
      unfolding discrim_def by simp
    moreover have "sqrt 20 = 2 * sqrt 5"
      by (metis numeral_times_numeral real_sqrt_four real_sqrt_mult semiring_norm(12,14))
    ultimately have "(c = (2 + 2 * sqrt 5) / (2 * 4) \<or>
                      c = (2 - 2 * sqrt 5) / (2 * 4))"
      using discriminant_iff[of 4 c "-2" "-1"]
      by auto
    then have "c = 1/4 + 1/4 * sqrt 5 \<or> c = 1/4 - 1/4 * sqrt 5"
      by fastforce
    moreover have "c < 0"
      unfolding c_def t_def using cos_lt_zero_pi[of "3 * pi / 5"]
      by simp
    ultimately show "cos (3 * pi / 5) = 1 / 4 - 1 / 4 * sqrt 5"
      unfolding c_def t_def
      by (metis add_nonneg_nonneg less_le not_le real_rat5_le_sqrt_cases zero_less_divide_1_iff
          zero_less_numeral)
  qed
  then have arccos_3pi5: "arccos (rat5 (1/4) (-(1/4))) = 3 * pi / 5" unfolding rat5_def
    by (simp add: of_rat_divide of_rat_minus)
  have "rat5 6 (- 2) \<ge> 0"
    unfolding rat5_0_1(1)[symmetric] rat5_le
    by simp
  have "(v = v1 \<and> ((e1 = convex hull {v1, v2} \<and> e2 = convex hull {v1, v5}) \<or>
                   (e1 = convex hull {v1, v5} \<and> e2 = convex hull {v1, v2}))) \<or>
        (v = v2 \<and> ((e1 = convex hull {v2, v1} \<and> e2 = convex hull {v2, v4}) \<or>
                   (e1 = convex hull {v2, v4} \<and> e2 = convex hull {v2, v1}))) \<or>
        (v = v3 \<and> ((e1 = convex hull {v3, v4} \<and> e2 = convex hull {v3, v5}) \<or>
                   (e1 = convex hull {v3, v5} \<and> e2 = convex hull {v3, v4}))) \<or>
        (v = v4 \<and> ((e1 = convex hull {v4, v2} \<and> e2 = convex hull {v4, v3}) \<or>
                   (e1 = convex hull {v4, v3} \<and> e2 = convex hull {v4, v2}))) \<or>
        (v = v5 \<and> ((e1 = convex hull {v5, v1} \<and> e2 = convex hull {v5, v3}) \<or>
                   (e1 = convex hull {v5, v3} \<and> e2 = convex hull {v5, v1})))"
    using conjI[OF *(1,2)] conjI[OF *(3,4)] *(5-7) unfolding assms dodecahedron_facet1_edges
    by (smt (verit) divide_cancel_right divide_eq_0_iff extreme_point_of_convex_hull_2 insert_commute
        rat5_eq solids_vectors_to_rat5(10) vector3_neq)
  moreover have "vangle (v2 - v1) (v5 - v1) = 3 * pi / 5"
                "vangle (v1 - v2) (v4 - v2) = 3 * pi / 5"
                "vangle (v4 - v3) (v5 - v3) = 3 * pi / 5"
                "vangle (v2 - v4) (v3 - v4) = 3 * pi / 5"
                "vangle (v1 - v5) (v3 - v5) = 3 * pi / 5"
    unfolding assms vector3_sub norm_eq_sqrt_inner vector3_dot vangle_def rat5_sub rat5_mul
    by (simp_all add: \<open>rat5 6 (- 2) \<ge> 0\<close> arccos_3pi5 vector3_eq_0 rat5_sub rat5_mul
        rat5_add rat5_eq_0 rat5_div)
  ultimately show "(\<exists>a b. e1 = convex hull {v, a} \<and> e2 = convex hull {v, b} \<and>
                          vangle (a - v) (b - v) = 3 * pi / 5)"
    using vangle_commute
    by metis
qed

lemma dodecahedron_equiangular:
  assumes "f face_of std_dodecahedron \<and> aff_dim f = 2"
  shows "equiangular f (3 * pi / 5)"
proof -
  define f1 where "f1 = convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]}"
  have "f1 face_of std_dodecahedron \<and> aff_dim f1 = 2"
    using f1_def dodecahedron_facets by blast
  then have "f1 congruent f"
    using assms dodecahedron_congruent_faces by blast
  then show ?thesis
    using equiangular_congruent dodecahedron_facet1_equiangular f1_def
    by blast
qed

end
