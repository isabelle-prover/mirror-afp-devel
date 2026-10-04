section\<open>Icosahedron\<close>

theory Icosahedron
  imports
    Computation
begin

subsection\<open>Definition\<close>

definition std_icosahedron :: "(real, 3) vec set"
  where "std_icosahedron \<equiv> convex hull
    {vector [0, 1, \<phi>], vector [0, 1, -\<phi>],
     vector [0, -1, \<phi>], vector [0, -1, -\<phi>],
     vector [1, \<phi>, 0], vector [1, -\<phi>, 0],
     vector [-1, \<phi>, 0], vector [-1, -\<phi>, 0],
     vector [\<phi>, 0, 1], vector [-\<phi>, 0, 1],
     vector [\<phi>, 0, -1], vector [-\<phi>, 0, -1]}"

lemma std_icosahedron_eq:
  shows "std_icosahedron = convex hull
    { vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)],
      vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)],
      vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)],
      vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)],
      vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0],
      vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0],
      vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0],
      vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0],
      vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0],
      vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0],
      vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0],
      vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]}"
  unfolding std_icosahedron_def rat5_def
  by (simp add: add_divide_distrib of_rat_divide of_rat_minus)

lemma icosahedron_fulldim:
  shows "aff_dim std_icosahedron = 3"
  unfolding std_icosahedron_def
  apply (rule polytope_3D)
  by (simp add: vector3_sub vector3_cross vector3_dot vector3_eq_0,
      smt (verit, ccfv_threshold) real_sqrt_ge_0_iff)+

lemma icosahedron_polyhedron:
  shows "polyhedron std_icosahedron"
  by (simp add: std_icosahedron_def polytope_convex_hull polytope_imp_polyhedron)

subsection\<open>Facets, edges, and vertices\<close>

lemma icosahedron_facets:
  fixes f :: "(real^3) set"
  shows "f face_of std_icosahedron \<and> aff_dim f = 2 \<longleftrightarrow>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
         f = convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
         f = convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}"
  unfolding std_icosahedron_eq
  apply (simp only: compute_faces_2 finite_insert finite.emptyI)
  apply (simp only: compute_faces_2_step_1 bex_empty simp_thms(31))
  apply (simp only: compute_faces_2_step_2 bex_empty simp_thms(31))
  apply (simp only: empty_iff ball_insert bex_empty bex_simps(5) ball_simps(5) simp_thms(21,31))
  apply (simp only: vector3_sub vector3_cross vector3_eq_0 rat5_add rat5_sub rat5_mul rat5_eq)
  apply (simp add: vector3_eq_0 vector3_dot rat5_add rat5_sub rat5_mul rat5_le rat5_eq rat5_eq_0 Let_def) 
    \<comment> \<open>very slow, ca 60s\<close>
  apply (simp only: insert_commute)
  by linarith

lemma icosahedron_facet1_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "n \<equiv> vector[rat5 1 1, rat5 (-1) 1, rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet2_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "n \<equiv> vector[rat5 (-1) (-1), rat5 (-1) 1, rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet3_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 2 0, rat5 2 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet4_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 2 0, rat5 (-2) 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet5_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-1) 1, rat5 0 0, rat5 1 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet6_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 (-2) 0, rat5 2 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet7_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 (-2) 0, rat5 (-2) 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet8_edges:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 1 (-1), rat5 0 0, rat5 1 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet9_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "n \<equiv> vector[rat5 1 1, rat5 1 (-1), rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet10_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v3 \<equiv> vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "n \<equiv> vector[rat5 (-1) (-1), rat5 1 (-1), rat5 0 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet11_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 (-2) 0, rat5 (-2) 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet12_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 (-2) 0, rat5 2 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet13_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
      and "v2 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-1) 1, rat5 0 0, rat5 (-1) (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet14_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 (-2) 0, rat5 2 0, rat5 (-2) 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet15_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 2 0, rat5 2 0, rat5 2 0] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet16_edges:
  defines "v1 \<equiv> vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0] :: real^3"
      and "v2 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 1 (-1), rat5 0 0, rat5 (-1) (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet17_edges:
  defines "v1 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 1 1, rat5 (-1) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet18_edges:
  defines "v1 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 (-1) (-1), rat5 (-1) 1] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet19_edges:
  defines "v1 \<equiv> vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 1 1, rat5 1 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 3 1"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma icosahedron_facet20_edges:
  defines "v1 \<equiv> vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v2 \<equiv> vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0] :: real^3"
      and "v3 \<equiv> vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)] :: real^3"
      and "n \<equiv> vector[rat5 0 0, rat5 (-1) (-1), rat5 1 (-1)] :: real^3"
    shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
           (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0 rat5_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = rat5 (-3) (-1)"
    unfolding v1_def v2_def v3_def n_def
    by (auto simp add: vector3_dot rat5_mul rat5_add)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemmas icosahedron_facet_edges =
  icosahedron_facet1_edges icosahedron_facet2_edges icosahedron_facet3_edges
  icosahedron_facet4_edges icosahedron_facet5_edges icosahedron_facet6_edges
  icosahedron_facet7_edges icosahedron_facet8_edges icosahedron_facet9_edges
  icosahedron_facet10_edges icosahedron_facet11_edges icosahedron_facet12_edges
  icosahedron_facet13_edges icosahedron_facet14_edges icosahedron_facet15_edges
  icosahedron_facet16_edges icosahedron_facet17_edges icosahedron_facet18_edges
  icosahedron_facet19_edges icosahedron_facet20_edges

lemma icosahedron_edges_per_face:
  assumes "f face_of std_icosahedron"
      and "aff_dim f = 2"
    shows "card {e. e face_of std_icosahedron \<and> aff_dim e = 1 \<and> e \<subseteq> f} = 3"
  using conjI[OF assms] unfolding icosahedron_facets face_edge_set_eq[OF assms(1)]
  apply (elim disjE forw_subst)
  unfolding icosahedron_facet_edges set_cases card_3_iff2
    segment_convex_hull[symmetric] closed_segment_eq
  by (simp_all add: vector3_eq doubleton_eq_iff rat5_eq)

lemma icosahedron_edges:
  "e face_of std_icosahedron \<and> aff_dim e = 1 \<longleftrightarrow>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>    
   e = convex hull {vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
   e = convex hull {vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  then obtain f where f_facts: "f face_of std_icosahedron \<and> aff_dim f = 2" "e face_of f \<and> aff_dim e = 1"
    using icosahedron_polyhedron icosahedron_fulldim edge_belongs_to_face
    by blast
  show ?rhs
    using f_facts unfolding icosahedron_facets
    apply (elim disjE) apply (all \<open>hypsubst_thin\<close>)
    unfolding icosahedron_facet_edges
    by linarith+
next
  assume "?rhs"
  then show "?lhs"
    using icosahedron_facets icosahedron_facet_edges
    (* takes a minute *)
    by (smt (verit, ccfv_threshold) face_of_trans insertI1 insert_commute mem_Collect_eq)
qed

lemma icosahedron_vertices:
  shows "(v face_of std_icosahedron \<and> aff_dim v = 0) =
         (v = {vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} \<or>
          v = {vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} \<or>
          v = {vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
          v = {vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} \<or>
          v = {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0]} \<or>
          v = {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0]} \<or>
          v = {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0]} \<or>
          v = {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]})"
  (is "?lhs = ?rhs")
proof
  assume *: "?lhs"
  then obtain e where "e face_of std_icosahedron" "aff_dim e = 1" "v face_of e"
    using icosahedron_polyhedron icosahedron_fulldim vertex_belongs_to_edge
    by blast
  show "?rhs"
    using conjI[OF \<open>e face_of std_icosahedron\<close> \<open>aff_dim e = 1\<close>]
    unfolding icosahedron_edges
    using vertices_of_edge[OF _ \<open>v face_of e\<close>] *
    by metis+
next
  assume "?rhs"
  then show "?lhs"
    apply (elim disjE forw_subst)
    by (smt (z3) aff_dim_sing extreme_point_of_segment face_of_singleton face_of_trans
        segment_convex_hull icosahedron_edges)+
qed

lemma icosahedron_edges_per_vertex:
  assumes "v face_of std_icosahedron"
      and "aff_dim v = 0"
    shows "card {e. e face_of std_icosahedron \<and> aff_dim e = 1 \<and> v \<subseteq> e} = 5"
  unfolding vertex_edge_set_eq[OF assms(1)]
  using conjI[OF assms]
  unfolding icosahedron_vertices conj_assoc[symmetric] icosahedron_edges
  by (elim disjE forw_subst) edges_per_vertex+

subsection\<open>Regularity\<close>

lemma icosahedron_congruent_edges:
  assumes "e1 face_of std_icosahedron \<and> aff_dim e1 = 1"
      and "e2 face_of std_icosahedron \<and> aff_dim e2 = 1"
  shows "e1 congruent e2"
proof -
  let ?edges =
    "{convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},    
      convex hull {vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}}"
  have "e1 \<in> ?edges" "e2 \<in> ?edges"
    using assms unfolding icosahedron_edges
    by auto
  moreover have "\<forall>e\<in>?edges.
          convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0]} congruent e"
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

lemma icosahedron_congruent_faces:
  assumes "f1 face_of std_icosahedron \<and> aff_dim f1 = 2"
      and "f2 face_of std_icosahedron \<and> aff_dim f2 = 2"
    shows "f1 congruent f2"
proof -
  let ?faces =
    "{convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]},
      convex hull {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}}"
  have "f1 \<in> ?faces" "f2 \<in> ?faces"
    using assms icosahedron_facets
    by auto
  moreover have "\<forall>f\<in>?faces.
          convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} congruent f"
    apply (simp only: ball_simps(7) Set.ball_empty simp_thms(21))
    unfolding conj_assoc[symmetric]
    by (rule conjI)+ show_congruence+
  ultimately show ?thesis
    using congruent_set by meson
qed

lemma icosahedron_facet1_equiangular:
  defines "v1 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0] :: real^3"
  defines "v2 \<equiv> vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0] :: real^3"
  defines "v3 \<equiv> vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0] :: real^3"
  shows "equiangular (convex hull {v1, v2, v3}) (pi / 3)"
  unfolding equiangular_def
proof (clarify)
  fix e1 e2 v
  assume *: "e1 face_of convex hull {v1, v2, v3}" "aff_dim e1 = 1"
            "e2 face_of convex hull {v1, v2, v3}" "aff_dim e2 = 1"
            "e1 \<noteq> e2" "v extreme_point_of e1" "v extreme_point_of e2"
  have "rat5 4 0 \<ge> 0" "rat5 (1/2) 0 = 1/2"
    unfolding rat5_def
    by (simp_all add: of_rat_divide)
  have "(v = v1 \<and> ((e1 = convex hull {v1, v2} \<and> e2 = convex hull {v1, v3}) \<or>
                   (e1 = convex hull {v1, v3} \<and> e2 = convex hull {v1, v2}))) \<or>
        (v = v2 \<and> ((e1 = convex hull {v2, v1} \<and> e2 = convex hull {v2, v3}) \<or>
                   (e1 = convex hull {v2, v3} \<and> e2 = convex hull {v2, v1}))) \<or>
        (v = v3 \<and> ((e1 = convex hull {v3, v1} \<and> e2 = convex hull {v3, v2}) \<or>
                   (e1 = convex hull {v3, v2} \<and> e2 = convex hull {v3, v1})))"
    using conjI[OF *(1,2)] conjI[OF *(3,4)] *(5-7) unfolding assms icosahedron_facet1_edges
    by (smt (verit, best) extreme_point_of_convex_hull_2 insert_commute vector3_eq)
  moreover have "vangle (v2 - v1) (v3 - v1) = pi / 3"
                "vangle (v1 - v2) (v3 - v2) = pi / 3"
                "vangle (v1 - v3) (v2 - v3) = pi / 3"
    unfolding assms vector3_sub norm_eq_sqrt_inner vector3_dot vangle_def rat5_sub rat5_mul
    by (simp_all add: vector3_eq_0 rat5_sub rat5_mul rat5_add rat5_eq_0 rat5_div
        \<open>rat5 4 0 \<ge> 0\<close> \<open>rat5 (1/2) 0 = 1/2\<close>)
  ultimately show "(\<exists>a b. e1 = convex hull {v, a} \<and> e2 = convex hull {v, b} \<and>
                          vangle (a - v) (b - v) = pi / 3)"
    using vangle_commute
    by metis
qed

lemma icosahedron_equiangular:
  assumes "f face_of std_icosahedron \<and> aff_dim f = 2"
  shows "equiangular f (pi / 3)"
proof -
  define f1 where "f1 = convex hull {(vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0]::real^3), vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]}"
  have "f1 face_of std_icosahedron \<and> aff_dim f1 = 2"
    using f1_def icosahedron_facets by blast
  then have "f1 congruent f"
    using assms icosahedron_congruent_faces by blast
  then show ?thesis
    using equiangular_congruent icosahedron_facet1_equiangular f1_def
    by blast
qed

end
