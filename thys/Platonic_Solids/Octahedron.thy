section\<open>Octahedron\<close>

theory Octahedron
  imports Computation
begin

subsection\<open>Definition\<close>

definition std_octahedron :: "(real, 3) vec set"
  where "std_octahedron \<equiv> convex hull
    {vector [1, 0, 0], vector [-1, 0, 0],
     vector [0, 0, 1], vector [0, 0, -1],
     vector [0, 1, 0], vector [0, -1, 0]}"

lemma octahedron_fulldim:
  shows "aff_dim std_octahedron = 3"
  unfolding std_octahedron_def
  apply (rule polytope_3D)
  by (simp add: vector3_sub vector3_cross vector3_dot vector3_eq_0)+

lemma octahedron_polyhedron:
  shows "polyhedron std_octahedron"
  by (simp add: std_octahedron_def polytope_convex_hull polytope_imp_polyhedron)

subsection\<open>Facets, edges, and vertices\<close>

lemma octahedron_facets:
  fixes f :: "(real^3) set"
  shows "f face_of std_octahedron \<and> aff_dim f = 2 \<longleftrightarrow>
         f = convex hull {vector[- 1, 0, 0], vector[0, - 1, 0], vector[0, 0, - 1]} \<or>
         f = convex hull {vector[- 1, 0, 0], vector[0, - 1, 0], vector[0, 0, 1]} \<or>
         f = convex hull {vector[- 1, 0, 0], vector[0, 1, 0], vector[0, 0, - 1]} \<or>
         f = convex hull {vector[- 1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]} \<or>
         f = convex hull {vector[1, 0, 0], vector[0, - 1, 0], vector[0, 0, - 1]} \<or>
         f = convex hull {vector[1, 0, 0], vector[0, - 1, 0], vector[0, 0, 1]} \<or>
         f = convex hull {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, - 1]} \<or>
         f = convex hull {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]}"
  unfolding std_octahedron_def
  apply (simp only: compute_faces_2 finite_insert finite.emptyI)
  apply (simp only: compute_faces_2_step_1 bex_empty simp_thms(31))
  apply (simp only: compute_faces_2_step_2 bex_empty simp_thms(31))
  apply (simp only: empty_iff ball_insert bex_empty bex_simps(5) ball_simps(5) simp_thms(21,31))
  apply (simp add: vector3_sub vector3_cross vector3_eq_0 vector3_dot Let_def)
  apply (simp only: insert_commute)
  by linarith

lemma octahedron_facet1_edges:
  defines "v1 \<equiv> vector[-1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, -1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, -1] :: real^3"
    and "n \<equiv> vector[1, 1, 1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = -1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet2_edges:
  defines "v1 \<equiv> vector[-1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, -1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, 1] :: real^3"
    and "n \<equiv> vector[-1, -1, 1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = 1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet3_edges:
  defines "v1 \<equiv> vector[-1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, 1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, -1] :: real^3"
    and "n \<equiv> vector[-1, 1, -1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = 1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet4_edges:
  defines "v1 \<equiv> vector[-1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, 1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, 1] :: real^3"
    and "n \<equiv> vector[1, -1, -1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = -1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet5_edges:
  defines "v1 \<equiv> vector[1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, -1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, -1] :: real^3"
    and "n \<equiv> vector[1, -1, -1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = 1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet6_edges:
  defines "v1 \<equiv> vector[1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, -1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, 1] :: real^3"
    and "n \<equiv> vector[-1, 1, -1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = -1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet7_edges:
  defines "v1 \<equiv> vector[1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, 1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, -1] :: real^3"
    and "n \<equiv> vector[-1, -1, 1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = -1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemma octahedron_facet8_edges:
  defines "v1 \<equiv> vector[1, 0, 0] :: real^3"
    and "v2 \<equiv> vector[0, 1, 0] :: real^3"
    and "v3 \<equiv> vector[0, 0, 1] :: real^3"
    and "n \<equiv> vector[1, 1, 1] :: real^3"
  shows "(e face_of (convex hull {v1, v2, v3}) \<and> aff_dim e = 1) =
         (e = convex hull {v1, v2} \<or> e = convex hull {v1, v3} \<or> e = convex hull {v2, v3})"
proof -
  have n_nz: "n \<noteq> 0"
    unfolding n_def by (simp add: vector3_eq_0)
  have plane: "\<And>x. x \<in> {v1, v2, v3} \<Longrightarrow> n \<bullet> x = 1"
    by (auto simp add: assms vector3_dot)
  have finite: "finite {v1, v2, v3}"
    using assms by blast
  show ?thesis
    by (facet_edges plane: plane n_nz: n_nz defs: assms)
qed

lemmas octahedron_facet_edges =
  octahedron_facet1_edges octahedron_facet2_edges
  octahedron_facet3_edges octahedron_facet4_edges octahedron_facet5_edges
  octahedron_facet6_edges octahedron_facet7_edges octahedron_facet8_edges

lemma octahedron_edges_per_face:
  assumes "f face_of std_octahedron"
      and "aff_dim f = 2"
  shows "card {e. e face_of std_octahedron \<and> aff_dim e = 1 \<and> e \<subseteq> f} = 3"
  using conjI[OF assms] unfolding octahedron_facets face_edge_set_eq[OF assms(1)]
  apply (elim disjE forw_subst)
  unfolding octahedron_facet_edges set_cases card_3_iff2
    segment_convex_hull[symmetric] closed_segment_eq
  by (simp_all add: vector3_eq doubleton_eq_iff)

lemma octahedron_edges:
  "e face_of std_octahedron \<and> aff_dim e = 1 \<longleftrightarrow>
   e = convex hull {vector[- 1, 0, 0], vector[0, - 1, 0]} \<or>
   e = convex hull {vector[- 1, 0, 0], vector[0, 1, 0]} \<or>
   e = convex hull {vector[- 1, 0, 0], vector[0, 0, - 1]} \<or>
   e = convex hull {vector[- 1, 0, 0], vector[0, 0, 1]} \<or>
   e = convex hull {vector[1, 0, 0], vector[0, - 1, 0]} \<or>
   e = convex hull {vector[1, 0, 0], vector[0, 1, 0]} \<or>
   e = convex hull {vector[1, 0, 0], vector[0, 0, - 1]} \<or>
   e = convex hull {vector[1, 0, 0], vector[0, 0, 1]} \<or>
   e = convex hull {vector[0, - 1, 0], vector[0, 0, - 1]} \<or>
   e = convex hull {vector[0, - 1, 0], vector[0, 0, 1]} \<or>
   e = convex hull {vector[0, 1, 0], vector[0, 0, - 1]} \<or>
   e = convex hull {vector[0, 1, 0], vector[0, 0, 1]}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  then obtain f where f_facts: "f face_of std_octahedron \<and> aff_dim f = 2" "e face_of f \<and> aff_dim e = 1"
    using octahedron_polyhedron octahedron_fulldim edge_belongs_to_face
    by blast
  show ?rhs
    using f_facts unfolding octahedron_facets
    apply (elim disjE) apply (all \<open>hypsubst_thin\<close>)
    unfolding octahedron_facet_edges
    by linarith+
next
  assume "?rhs"
  then show "?lhs"
    using octahedron_facets octahedron_facet_edges
    by (smt (verit, ccfv_threshold) face_of_trans insertI1 insert_commute mem_Collect_eq)
qed

lemma octahedron_vertices:
  shows "(v face_of std_octahedron \<and> aff_dim v = 0) =
         (v = {vector [1, 0, 0]} \<or>
          v = {vector [-1, 0, 0]} \<or>
          v = {vector [0, 0, 1]} \<or>
          v = {vector [0, 0, -1]} \<or>
          v = {vector [0, 1, 0]} \<or>
          v = {vector [0, -1, 0]})"
  (is "?lhs = ?rhs")
proof
  assume *: "?lhs"
  then obtain e where e_facts: "e face_of std_octahedron \<and> aff_dim e = 1" "v face_of e"
    using octahedron_polyhedron octahedron_fulldim vertex_belongs_to_edge
    by blast
  show "?rhs"
    using e_facts(1)
    unfolding octahedron_edges
    apply (elim disjE)
    using vertices_of_edge[OF _ \<open>v face_of e\<close>] *
    by metis+
next
  assume "?rhs"
  then show "?lhs"
    apply (elim disjE)
    by (meson aff_dim_sing extreme_point_of_convex_hull_2 face_of_singleton
        face_of_trans octahedron_edges)+
qed

lemma octahedron_edges_per_vertex:
  assumes "v face_of std_octahedron"
      and "aff_dim v = 0"
  shows "card {e. e face_of std_octahedron \<and> aff_dim e = 1 \<and> v \<subseteq> e} = 4"
  unfolding vertex_edge_set_eq[OF assms(1)]
  using conjI[OF assms]
  unfolding octahedron_vertices conj_assoc[symmetric] octahedron_edges
  by (elim disjE forw_subst) edges_per_vertex+

subsection\<open>Regularity\<close>

lemma octahedron_congruent_edges:
  assumes "e1 face_of std_octahedron \<and> aff_dim e1 = 1"
      and "e2 face_of std_octahedron \<and> aff_dim e2 = 1"
  shows "e1 congruent e2"
proof -
  let ?edges =
    "{convex hull {(vector[- 1, 0, 0]::real^3), vector[0, - 1, 0]},
      convex hull {vector[- 1, 0, 0], vector[0, 1, 0]},
      convex hull {vector[- 1, 0, 0], vector[0, 0, - 1]},
      convex hull {vector[- 1, 0, 0], vector[0, 0, 1]},
      convex hull {vector[1, 0, 0], vector[0, - 1, 0]},
      convex hull {vector[1, 0, 0], vector[0, 1, 0]},
      convex hull {vector[1, 0, 0], vector[0, 0, - 1]},
      convex hull {vector[1, 0, 0], vector[0, 0, 1]},
      convex hull {vector[0, - 1, 0], vector[0, 0, - 1]},
      convex hull {vector[0, - 1, 0], vector[0, 0, 1]},
      convex hull {vector[0, 1, 0], vector[0, 0, - 1]},
      convex hull {vector[0, 1, 0], vector[0, 0, 1]}}"
  have "e1 \<in> ?edges" "e2 \<in> ?edges"
    using assms unfolding octahedron_edges
    by auto
  moreover have "\<forall>e\<in>?edges. convex hull {vector[- 1, 0, 0], vector[0, - 1, 0]} congruent e"
    apply (simp only: ball_simps(7) Set.ball_empty simp_thms(21))
    unfolding conj_assoc[symmetric] segment_convex_hull[symmetric]
    apply (rule conjI)+
    apply (all \<open>rule congruent_segments\<close>)
    unfolding dist_norm vector3_sub
    apply (simp_all add: norm_eq)
    unfolding vector3_dot
    by linarith+
  ultimately show ?thesis
    using congruent_set by meson
qed

lemma octahedron_congruent_faces:
  assumes "f1 face_of std_octahedron \<and> aff_dim f1 = 2"
      and "f2 face_of std_octahedron \<and> aff_dim f2 = 2"
    shows "f1 congruent f2"
proof -
  let ?faces =
    "{convex hull {(vector[- 1, 0, 0]::real^3), vector[0, - 1, 0], vector[0, 0, - 1]},
      convex hull {vector[- 1, 0, 0], vector[0, - 1, 0], vector[0, 0, 1]},
      convex hull {vector[- 1, 0, 0], vector[0, 1, 0], vector[0, 0, - 1]},
      convex hull {vector[- 1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]},
      convex hull {vector[1, 0, 0], vector[0, - 1, 0], vector[0, 0, - 1]},
      convex hull {vector[1, 0, 0], vector[0, - 1, 0], vector[0, 0, 1]},
      convex hull {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, - 1]},
      convex hull {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]}}"
  have "f1 \<in> ?faces" "f2 \<in> ?faces"
    using assms octahedron_facets
    by auto
  moreover have "\<forall>f\<in>?faces.
          convex hull {vector[- 1, 0, 0], vector[0, - 1, 0], vector[0, 0, - 1]} congruent f"
    apply (simp only: ball_simps(7) Set.ball_empty simp_thms(21))
    unfolding conj_assoc[symmetric]
    by (rule conjI)+ show_congruence+
  ultimately show ?thesis
    using congruent_set by meson
qed

lemma octahedron_facet1_equiangular:
  defines "v1 \<equiv> vector[-1, 0, 0] :: real^3"
  defines "v2 \<equiv> vector[0, -1, 0] :: real^3"
  defines "v3 \<equiv> vector[0, 0, -1] :: real^3"
  shows "equiangular (convex hull {v1, v2, v3}) (pi / 3)"
  unfolding equiangular_def
proof (clarify)
  fix e1 e2 v
  assume *: "e1 face_of convex hull {v1, v2, v3}" "aff_dim e1 = 1"
            "e2 face_of convex hull {v1, v2, v3}" "aff_dim e2 = 1"
            "e1 \<noteq> e2" "v extreme_point_of e1" "v extreme_point_of e2"
  have "(v = v1 \<and> ((e1 = convex hull {v1, v2} \<and> e2 = convex hull {v1, v3}) \<or>
                   (e1 = convex hull {v1, v3} \<and> e2 = convex hull {v1, v2}))) \<or>
        (v = v2 \<and> ((e1 = convex hull {v2, v1} \<and> e2 = convex hull {v2, v3}) \<or>
                   (e1 = convex hull {v2, v3} \<and> e2 = convex hull {v2, v1}))) \<or>
        (v = v3 \<and> ((e1 = convex hull {v3, v1} \<and> e2 = convex hull {v3, v2}) \<or>
                   (e1 = convex hull {v3, v2} \<and> e2 = convex hull {v3, v1})))"
    using conjI[OF *(1,2)] conjI[OF *(3,4)] *(5-7) unfolding assms octahedron_facet1_edges
    by (smt (verit, best) extreme_point_of_convex_hull_2 insert_commute vector3_eq)
  moreover have "vangle (v2 - v1) (v3 - v1) = pi / 3"
                "vangle (v1 - v2) (v3 - v2) = pi / 3"
                "vangle (v1 - v3) (v2 - v3) = pi / 3"
    unfolding assms vector3_sub norm_eq_sqrt_inner vector3_dot vangle_def
    by (simp_all add: vector3_eq_0)
  ultimately show "(\<exists>a b. e1 = convex hull {v, a} \<and> e2 = convex hull {v, b} \<and>
                          vangle (a - v) (b - v) = pi / 3)"
    using vangle_commute
    by metis
qed

lemma octahedron_equiangular:
  assumes "f face_of std_octahedron \<and> aff_dim f = 2"
  shows "equiangular f (pi / 3)"
proof -
  define f1 where "f1 = convex hull {vector[- 1, 0, 0]::real^3, vector[0, - 1, 0], vector[0, 0, - 1]}"
  have "f1 face_of std_octahedron \<and> aff_dim f1 = 2"
    using f1_def octahedron_facets by blast
  then have "f1 congruent f"
    using assms octahedron_congruent_faces by blast
  then show ?thesis
    using equiangular_congruent octahedron_facet1_equiangular f1_def
    by blast
qed

end
