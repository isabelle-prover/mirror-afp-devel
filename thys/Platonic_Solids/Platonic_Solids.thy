section \<open>Main result\<close>

theory Platonic_Solids
  imports
    Euler_Polyhedron_Formula.Euler_Formula
    Polytope_More
    Tetrahedron
    Cube
    Octahedron
    Dodecahedron
    Icosahedron
begin

subsection\<open>Possible Schläfli symbols\<close>

lemma platonic_solid_limits:
  fixes p :: "(real^3) set"
  assumes is_polytope: "polytope p"
      and aff_dim_p: "aff_dim p = 3"
      and edges_per_face: "\<forall>f. f face_of p \<and> aff_dim f = 2 \<longrightarrow>
                card {e. e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f} = m"
      and edges_per_vert: "\<forall>v. v face_of p \<and> aff_dim v = 0 \<longrightarrow>
                card {e. e face_of p \<and> aff_dim e = 1 \<and> v \<subseteq> e} = n"
  shows "(m = 3 \<and> n = 3) \<or>
         (m = 4 \<and> n = 3) \<or>
         (m = 3 \<and> n = 4) \<or>
         (m = 5 \<and> n = 3) \<or>
         (m = 3 \<and> n = 5)"
proof -
  let ?V = "card {v. v face_of p \<and> aff_dim v = 0}"
  let ?E = "card {e. e face_of p \<and> aff_dim e = 1}"
  let ?F = "card {f. f face_of p \<and> aff_dim f = 2}"
  have "?V + ?F - ?E = 2"
    using Euler_relation[OF is_polytope aff_dim_p] by fastforce
  then have "?V + ?F = ?E + 2"
    by linarith
  moreover have "?V \<ge> 4"
    using polytope_vertex_lower_bound[OF is_polytope] aff_dim_p
    by fastforce
  moreover have "?F \<ge> 4"
  proof -
    have "f facet_of p \<longleftrightarrow> f face_of p \<and> aff_dim f = 2" for f
      unfolding facet_of_def aff_dim_p by auto
    then show ?thesis
      using polytope_facet_lower_bound[OF is_polytope] aff_dim_p by presburger
  qed
  ultimately have "?E \<ge> 6"
    by linarith
  have "\<And>f. f face_of p \<Longrightarrow> aff_dim f = 2 \<Longrightarrow> card {e. e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f} \<ge> 3"
  proof -
    fix f
    assume *: "f face_of p" "aff_dim f = 2"
    then have f_polytope: "polytope f"
      using face_of_polytope_polytope is_polytope
      by blast
    have "e facet_of f \<longleftrightarrow> e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f" for e
      using face_of_face[OF *(1)] unfolding facet_of_def *(2)
      by auto
    then show "card {e. e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f} \<ge> 3"
      using polytope_facet_lower_bound[OF f_polytope] *(2)
      by presburger
  qed
  then have "m \<ge> 3"
    using edges_per_face
    by (metis (mono_tags, lifting) Collect_empty_eq One_nat_def 
        \<open>?F \<ge> 4\<close> add_Suc_shift card.empty linorder_not_le
        numeral_Bit0 one_add_one plus_nat.add_0 zero_less_Suc)

  have "m * ?F = 2 * ?E"
    using edges_per_face facet_ridge_relation[OF is_polytope] unfolding aff_dim_p
    by simp
  moreover have "n * ?V = 2 * ?E"
    using edge_vertex_relation[OF is_polytope edges_per_vert] .
  moreover have "m * (n * ?V) + n * (m * ?F) = m * n * (?E + 2)"
    using \<open>?V + ?F = ?E + 2\<close> by algebra
  ultimately have E_m_n_relation: "2 * ?E * (m + n) = m * n * (?E + 2)"
    by algebra

  have "n \<noteq> 0"
    using \<open>?E \<ge> 6\<close> E_m_n_relation \<open>3 \<le> m\<close> rel_simps(28)
    by fastforce
  moreover have "n \<noteq> 1"
    using \<open>?F \<ge> 4\<close> \<open>?V + ?F = ?E + 2\<close> \<open>n * ?V = 2 * ?E\<close> by force
  moreover have "n \<noteq> 2"
    using E_m_n_relation \<open>m * ?F = 2 * ?E\<close> \<open>?E \<ge> 6\<close> \<open>?F \<ge> 4\<close> by force
  ultimately have "n \<ge> 3"
    by auto

  have "?E * (m * n) < ?E * (2 * (m + n))"
    using \<open>3 \<le> m\<close> \<open>n \<noteq> 0\<close> E_m_n_relation
    by (simp add: algebra_simps)
  then have "m * n < 2 * (m + n)"
    by auto
  then have "int m * int n - 2 * int m - 2 * int n < 0"
    by (smt (verit, ccfv_SIG) diff_add_cancel diff_less_0_iff_less group_cancel.add2 mult_2
        of_nat_add of_nat_less_iff of_nat_mult)
  then have "int m * (int n - 2) - 2 * int n < 0"
    by (simp add: right_diff_distrib')
  then have "int m * (int n - 2) - 2 * (int n - 2) < 4"
    by simp
  then have int_m_n_ineq: "(int m - 2) * (int n - 2) < 4"
    using int_distrib(3) by presburger
  have "(m - 2) * (int n - 2) < 4"
    using int_m_n_ineq \<open>3 \<le> m\<close> by simp
  then have "int ((m - 2) * (n - 2)) < int 4"
    by (simp add: of_nat_diff_if)
  then have m_n_ineq: "(m - 2) * (n - 2) < 4"
    by linarith

  have "m - 2 \<ge> 1" "n - 2 \<ge> 1"
    using \<open>3 \<le> m\<close> \<open>3 \<le> n\<close> by auto

  have "m \<le> 5"
    proof (rule ccontr)
      assume "\<not>(m \<le> 5)"
      then have *: "m - 2 \<ge> 4" by simp
      have "(m - 2) * (n - 2) \<ge> 4"
        using mult_le_mono[OF * \<open>n - 2 \<ge> 1\<close>] by auto
      then show "False"
        using m_n_ineq by linarith
    qed
  have "n \<le> 5"
  proof (rule ccontr)
    assume "\<not>(n \<le> 5)"
    then have *: "n - 2 \<ge> 4" by simp
    have "(m - 2) * (n - 2) \<ge> 4"
      using mult_le_mono[OF \<open>m - 2 \<ge> 1\<close> *] by auto
    then show "False"
      using m_n_ineq by linarith
  qed

  have "m = 3 \<or> m = 4 \<or> m = 5"
    using \<open>3 \<le> m\<close> \<open>m \<le> 5\<close> by linarith
  moreover have "n = 3 \<or> n = 4 \<or> n = 5"
    using \<open>3 \<le> n\<close> \<open>n \<le> 5\<close> by linarith
  ultimately show ?thesis
    using m_n_ineq by presburger
qed

subsection\<open>Exactly five Platonic solids\<close>

theorem platonic_solids_full:
  shows "(\<exists>p::(real^3) set. polytope p \<and> aff_dim p = 3 \<and>
              (\<forall>f. f face_of p \<and> aff_dim f = 2 \<longrightarrow>
                   card {e. e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f} = m) \<and>
              (\<forall>v. v face_of p \<and> aff_dim v = 0 \<longrightarrow>
                   card {e. e face_of p \<and> aff_dim e = 1 \<and> v \<subseteq> e} = n) \<and>
              (\<forall>f1 f2. f1 face_of p \<and> aff_dim f1 = 2 \<and>
                       f2 face_of p \<and> aff_dim f2 = 2 \<longrightarrow> f1 congruent f2) \<and>
              (\<forall>e1 e2. e1 face_of p \<and> aff_dim e1 = 1 \<and>
                       e2 face_of p \<and> aff_dim e2 = 1 \<longrightarrow> e1 congruent e2) \<and>
              (\<exists>t. \<forall>f. f face_of p \<and> aff_dim f = 2 \<longrightarrow> equiangular f t)) =
         ((m = 3 \<and> n = 3) \<or>
          (m = 4 \<and> n = 3) \<or>
          (m = 3 \<and> n = 4) \<or>
          (m = 5 \<and> n = 3) \<or>
          (m = 3 \<and> n = 5))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using platonic_solid_limits by auto
next
  assume "?rhs"
  then consider
    (m3_n3) "m = 3 \<and> n = 3" |
    (m3_n4) "m = 3 \<and> n = 4" |
    (m3_n5) "m = 3 \<and> n = 5" |
    (m4_n3) "m = 4 \<and> n = 3" |
    (m5_n3) "m = 5 \<and> n = 3"
    by fast
  then show "?lhs"
  proof (cases)
    case m3_n3
    moreover have "polytope std_tetrahedron"
      by (simp add: polytope_convex_hull std_tetrahedron_def)
    ultimately show ?thesis
      using tetrahedron_fulldim tetrahedron_edges_per_face tetrahedron_edges_per_vertex
        tetrahedron_congruent_edges tetrahedron_congruent_faces tetrahedron_equiangular
      by blast
  next
    case m3_n4
    moreover have "polytope std_octahedron"
      by (simp add: polytope_convex_hull std_octahedron_def)
    ultimately show ?thesis
      using octahedron_fulldim octahedron_edges_per_face octahedron_edges_per_vertex
        octahedron_congruent_edges octahedron_congruent_faces octahedron_equiangular
      by blast
  next
    case m3_n5
    moreover have "polytope std_icosahedron"
      by (simp add: polytope_convex_hull std_icosahedron_def)
    ultimately show ?thesis
      using icosahedron_fulldim icosahedron_edges_per_face icosahedron_edges_per_vertex
        icosahedron_congruent_edges icosahedron_congruent_faces icosahedron_equiangular
      by blast
  next
    case m4_n3
    moreover have "polytope std_cube"
      by (simp add: polytope_convex_hull std_cube_def)
    ultimately show ?thesis
      using cube_fulldim cube_edges_per_face cube_edges_per_vertex
        cube_congruent_edges cube_congruent_faces cube_equiangular
      by blast
  next
    case m5_n3
    moreover have "polytope std_dodecahedron"
      by (simp add: polytope_convex_hull std_dodecahedron_def)
    ultimately show ?thesis
      using dodecahedron_fulldim dodecahedron_edges_per_face dodecahedron_edges_per_vertex
        dodecahedron_congruent_edges dodecahedron_congruent_faces dodecahedron_equiangular
      by blast
  qed
qed

text\<open>This is the original top-level statement of the HOL Light
     formalization, kept here for parity. It omits the regularity
     condition on @{term p}.\<close>

theorem platonic_solids:
  shows "(\<exists>p::(real^3) set. polytope p \<and> aff_dim p = 3 \<and>
              (\<forall>f. f face_of p \<and> aff_dim f = 2 \<longrightarrow>
                   card {e. e face_of p \<and> aff_dim e = 1 \<and> e \<subseteq> f} = m) \<and>
              (\<forall>v. v face_of p \<and> aff_dim v = 0 \<longrightarrow>
                   card {e. e face_of p \<and> aff_dim e = 1 \<and> v \<subseteq> e} = n)) =
         ((m = 3 \<and> n = 3) \<or>
          (m = 4 \<and> n = 3) \<or>
          (m = 3 \<and> n = 4) \<or>
          (m = 5 \<and> n = 3) \<or>
          (m = 3 \<and> n = 5))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using platonic_solid_limits by auto
next
  assume ?rhs
  then show ?lhs
    unfolding platonic_solids_full[symmetric]
    by meson
qed

end