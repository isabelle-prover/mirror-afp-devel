section \<open>Polytopes\<close>

theory Polytope_More
  imports
    Convex_Euclidean_Space_More
    "HOL-Analysis.Analysis"
begin

subsection \<open>Invariance under isometries\<close>

lemma facet_of_translation_eq:
    "((+) a ` T facet_of (+) a ` S) = (T facet_of S)"
  by (simp add: aff_dim_translation_eq facet_of_def)

(* This proof is basically a copy of faces_of_translation from the Polytope
   library, only using facet_of instead. *)
lemma facets_of_translation:
  shows "{F. F facet_of (+) a ` S} = (`) ((+) a) ` {F. F facet_of S}"
proof -
  have "\<And>F. F facet_of (+) a ` S \<Longrightarrow> \<exists>G. G facet_of S \<and> F = (+) a ` G"
    by (metis facet_of_imp_subset facet_of_translation_eq subset_imageE)
  then show ?thesis
    by (auto simp: image_iff facet_of_translation_eq)
qed

lemma polyhedron_translation_eq:
  shows "polyhedron S = polyhedron ((+) x ` S)"
proof -
  have translation: "\<And>S x. polyhedron S \<Longrightarrow> polyhedron ((+) x ` S)"
  proof -
    fix S::"'b set" and x::"'b"
    assume "polyhedron S"
    then obtain F where F_props:
      "finite F"
      "S = \<Inter>F"
      "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {y. a \<bullet> y \<le> b}"
      unfolding polyhedron_def by force
    let ?F' = "((`) ((+) x)) ` F"
    have "finite ?F'"
      using F_props(1) by blast
    moreover have "((+) x ` S) = \<Inter>?F'"
      by (metis (no_types, lifting) F_props(1,2) Inf_fin.hom_commute
          Inf_fin_Inf Inf_top_conv(2) calculation empty_iff empty_is_image
          surj_plus translation_Int)
    moreover have "\<And>h'. h' \<in> ?F' \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h' = {y. a \<bullet> y \<le> b}"
    proof -
      fix h'
      assume "h' \<in> ?F'"
      then obtain h a b where
        h'_eq: "h' = ((+) x) ` h" and
        h_props: "h \<in> F" "a \<noteq> 0" "h = {y. a \<bullet> y \<le> b}"
        using F_props(3) by blast
      have "h' = {y + x | y. a \<bullet> y \<le> b}"
        using h'_eq h_props(3) by auto
      also have "... = {y. a \<bullet> (y - x) \<le> b}"
        by force
      finally have "h' = {y. a \<bullet> y \<le> b + a \<bullet> x}"
        by (auto simp: inner_diff_right)
      then show "\<exists>a b. a \<noteq> 0 \<and> h' = {y. a \<bullet> y \<le> b}"
        using h_props(2) by blast
    qed
    ultimately show "polyhedron ((+) x ` S)"
      unfolding polyhedron_def by meson
  qed
  show ?thesis
    using translation[of S x] translation[of "((+) x ` S)" "-x"]
    by (metis translation_galois)
qed

lemma face_of_isometry_eq:
  assumes "orthogonal_transformation f"
  shows "((\<lambda>x. c + f x) ` T face_of (\<lambda>x. c + f x) ` S) \<longleftrightarrow> T face_of S"
  by (metis assms face_of_translation_eq face_of_linear_image image_image
      orthogonal_transformation_inj orthogonal_transformation_linear)

lemma extreme_point_of_isometry_eq:
  assumes "orthogonal_transformation f"
  shows "(c + f T extreme_point_of (\<lambda>x. c + f x) ` S) \<longleftrightarrow> T extreme_point_of S"
  using face_of_isometry_eq[OF assms, of c "{T}" S]
  by (simp add: face_of_singleton)

lemma aff_dim_isometry_eq:
  assumes "orthogonal_transformation f"
  shows "aff_dim S = aff_dim ((\<lambda>x. c + f x) ` S)"
  by (metis assms aff_dim_injective_linear_image aff_dim_translation_eq image_image
      orthogonal_transformation_def orthogonal_transformation_inj)

subsection \<open>Distinctness of facets\<close>

lemma facets_of_polyhedron_explicit_distinct:
  fixes S :: "'a :: euclidean_space set"
  assumes finite: "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and h1_in: "h1 \<in> F"
      and h2_in: "h2 \<in> F"
      and eq: "S \<inter> {x. a h1 \<bullet> x = b h1} = S \<inter> {x. a h2 \<bullet> x = b h2}"
    shows "h1 = h2"
proof (rule ccontr)
  assume *: "h1 \<noteq> h2"
  have "S \<noteq> {}"
    using h1_in psub by force
  have "polyhedron S"
    by (meson polyhedron_Int_affine[of S] seq faceq finite)
  have "rel_interior S \<noteq> {}"
    using rel_interior_polyhedron_explicit
    by (simp add: \<open>S \<noteq> {}\<close> \<open>polyhedron S\<close> polyhedron_imp_convex
        rel_interior_eq_empty)
  then obtain z where z_props: "z \<in> S" "\<And>h. h \<in> F \<Longrightarrow> a h \<bullet> z < b h"
    using rel_interior_polyhedron_explicit[OF finite seq] faceq psub
    by blast
  have "S \<subset> affine hull S \<inter> \<Inter>(F - {h2})"
    using h2_in psub[of "F - {h2}"]
    by blast
  then obtain x where x_props: "x \<in> affine hull S" "x \<in> \<Inter>(F - {h2})" "x \<notin> S"
    by auto
  then have "a h2 \<bullet> x > b h2"
    using Diff_iff empty_iff faceq insert_iff seq
    by fastforce
  have "\<And>h. h \<in> (F - {h2}) \<Longrightarrow> a h \<bullet> x \<le> b h"
    using x_props(2) faceq by auto
  have "closed_segment x z \<inter> rel_frontier S \<noteq> {}"
    by (metis Diff_iff Int_iff closed_segment_subset connected_Int_rel_frontier
        connected_segment convex_affine_hull empty_iff ends_in_segment(1,2) seq
        x_props(1,3) z_props(1))
  then have "closed_segment x z \<inter> (S - rel_interior S) \<noteq> {}"
    by (simp add: \<open>polyhedron S\<close> rel_boundary_of_polyhedron
        rel_frontier_of_polyhedron)
  then obtain y where y_props:
    "y \<in> closed_segment x z"
    "y \<in> S - rel_interior S"
    "y \<in> S"
    by blast
  have "S - rel_interior S = \<Union>{S \<inter> {x. a h \<bullet> x = b h} | h. h \<in> F}"
    using facet_of_polyhedron_explicit[OF finite seq faceq psub]
      rel_boundary_of_polyhedron[OF \<open>polyhedron S\<close>]
    by auto
  then obtain h where h_props: "h \<in> F" "a h \<bullet> y = b h"
    using y_props(2) by auto
  have "\<exists>k. k \<in> F \<and> k \<noteq> h2 \<and> a k \<bullet> y = b k"
  proof (cases "h = h2")
    case True
    then have "y \<in> S \<inter> {x. a h2 \<bullet> x = b h2}"
      using h_props(2) y_props(3) by blast
    then have "a h1 \<bullet> y = b h1"
      using eq by blast
    then show ?thesis
      using h1_in * by blast
  next
    case False
    then show ?thesis
      using h_props by blast 
  qed
  then obtain k where k_props: "k \<in> F" "k \<noteq> h2" "a k \<bullet> y = b k"
    by blast
  have "y \<in> open_segment x z"
    by (metis DiffI \<open>\<exists>k. k \<in> F \<and> k \<noteq> h2 \<and> a k \<bullet> y = b k\<close>
        all_not_in_conv insertE open_segment_def order_less_irrefl
        x_props(3) y_props(1,3) z_props(2))
  then obtain u where u_props: "y = (1 - u) *\<^sub>R x + u *\<^sub>R z" "0 < u" "u < 1"
    using in_segment(2)[of y x z] by blast
  have "(1 - u) * (a k \<bullet> x) + u * (a k \<bullet> z) = b k"
    using k_props(3) unfolding u_props(1)
    by (simp add: inner_right_distrib)
  moreover have "(1 - u) * (a k \<bullet> x) \<le> (1 - u) * b k"
    by (simp add: \<open>\<And>ha. ha \<in> F - {h2} \<Longrightarrow> a ha \<bullet> x \<le> b ha\<close> k_props(1,2)
        u_props(3))
  moreover have "u * (a k \<bullet> z) < u * b k"
    by (simp add: k_props(1) u_props(2) z_props(2))
  ultimately show "False"
    by argo
qed

subsection \<open>Ridges lie in two facets\<close>

lemma polyhedron_ridge_two_facets_0:
  fixes p :: "'a :: euclidean_space set"
  assumes "polyhedron p"
    and "r face_of p"
    and "0 \<in> r"
    and "aff_dim r = aff_dim p - 2"
  shows "\<exists>f1 f2. f1 face_of p \<and> aff_dim f1 = aff_dim p - 1 \<and>
                 f2 face_of p \<and> aff_dim f2 = aff_dim p - 1 \<and>
                 f1 \<noteq> f2 \<and> r \<subseteq> f1 \<and> r \<subseteq> f2 \<and> f1 \<inter> f2 = r \<and>
                 (\<forall>f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<and> r \<subseteq> f
                      \<longrightarrow> f = f1 \<or> f = f2)"
proof -
  let ?S = "{f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<and> r \<subseteq> f}"
  have "finite ?S"
    by (simp add: assms(1) finite_polyhedron_faces)
  have "r = \<Inter>{f. f facet_of p \<and> r \<subseteq> f}"
    using face_of_polyhedron[of p r] assms by fastforce
  then have r_eq: "r = \<Inter>?S"
    using assms(3) facet_of_def by blast
  have "0 \<in> p"
    using assms(2,3) face_of_imp_subset by auto

  have "card ?S = 0 \<or> card ?S = 1 \<or> card ?S = 2 \<or> card ?S \<ge> 3"
    by linarith
  then consider
    (card0) "card ?S = 0" |
    (card1) "card ?S = 1" |
    (card2) "card ?S = 2" |
    (card3) "card ?S \<ge> 3"
    by argo

  then show ?thesis
  proof (cases)
    case card0
    then show ?thesis
      by (smt (verit, best) Inf_empty \<open>finite ?S\<close> aff_dim_UNIV
          aff_dim_le_DIM assms(4) card_gt_0_iff nless_le r_eq)

  next
    case card1
    then obtain f1 where
      S_eq: "?S = {f1}" and
      aff_dim_f1: "aff_dim f1 = aff_dim p - 1"
      by (metis (mono_tags, lifting) all_not_in_conv card_1_singletonE
          insert_not_empty mem_Collect_eq singletonD)
    show ?thesis
      using r_eq aff_dim_f1 assms(4) unfolding S_eq
      by simp

  next
    case card2
    then obtain f1 f2 where
      S_eq: "?S = {f1, f2}" and
      "f1 face_of p" "aff_dim f1 = aff_dim p - 1" "r \<subseteq> f1" and
      "f2 face_of p" "aff_dim f2 = aff_dim p - 1" "r \<subseteq> f2" and
      "f1 \<noteq> f2"
      by (smt (verit) card_2_iff insert_iff mem_Collect_eq)
    moreover have "f1 \<inter> f2 = r"
      using S_eq r_eq by auto
    moreover have "(\<forall>f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<and> r \<subseteq> f
                      \<longrightarrow> f = f1 \<or> f = f2)"
      using S_eq by auto
    ultimately show ?thesis
      by blast

  next
    case card3
    then have "card ?S \<ge> Suc (Suc (Suc 0))"
      by presburger
    then obtain f1 f2 f3 S2 where
      S_eq: "?S = insert f3 (insert f2 (insert f1 S2))" and
      fs_neq: "f1 \<noteq> f2" "f1 \<noteq> f3" "f2 \<noteq> f3"
      by (smt (verit) card_le_Suc_iff insertCI)
    have f1_props: "f1 face_of p" "aff_dim f1 = aff_dim p - 1" "r \<subseteq> f1" and
         f2_props: "f2 face_of p" "aff_dim f2 = aff_dim p - 1" "r \<subseteq> f2" and
         f3_props: "f3 face_of p" "aff_dim f3 = aff_dim p - 1" "r \<subseteq> f3"
      using S_eq
      by auto

    obtain F a b where
      "finite F" and
      p_eq: "p = affine hull p \<inter> \<Inter>F" and
      halfspaces: "\<And>h. h\<in>F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h} \<and>
               (\<forall>x \<in> affine hull p. x + a h \<in> affine hull p)" and
      minimal: "\<And>F'. F' \<subset> F \<longrightarrow> p \<subset> affine hull p \<inter> \<Inter>F'"
      using polyhedron_Int_affine_parallel_minimal[of p] assms(1)
      by metis
    obtain h1 where "h1 \<in> F" "a h1 \<noteq> 0" and f1_eq: "f1 = p \<inter> {x. a h1 \<bullet> x = b h1}"
      using facet_of_polyhedron_explicit[OF \<open>finite F\<close> p_eq, of a b f1]
        halfspaces minimal f1_props unfolding facet_of_def
      using assms(3) by blast
    obtain h2 where "h2 \<in> F" "a h2 \<noteq> 0" and f2_eq: "f2 = p \<inter> {x. a h2 \<bullet> x = b h2}"
      using facet_of_polyhedron_explicit[OF \<open>finite F\<close> p_eq, of a b f2]
        halfspaces minimal f2_props unfolding facet_of_def
      using assms(3) by blast
    obtain h3 where "h3 \<in> F" "a h3 \<noteq> 0" and f3_eq: "f3 = p \<inter> {x. a h3 \<bullet> x = b h3}"
      using facet_of_polyhedron_explicit[OF \<open>finite F\<close> p_eq, of a b f3]
        halfspaces minimal f3_props unfolding facet_of_def
      using assms(3) by blast

    have all_x_in_r: "\<And>x. x \<in> r \<Longrightarrow> a h1 \<bullet> x = b h1 \<and> a h2 \<bullet> x = b h2 \<and> a h3 \<bullet> x = b h3"
      using f1_props(3) f2_props(3) f3_props(3) f1_eq f2_eq f3_eq
      by blast
    then have b_hs_eq_0: "b h1 = 0" "b h2 = 0" "b h3 = 0"
      using \<open>0 \<in> r\<close> by force+
    then have all_x_in_r_0: "\<And>x. x \<in> r \<Longrightarrow> a h1 \<bullet> x = 0 \<and> a h2 \<bullet> x = 0 \<and> a h3 \<bullet> x = 0"
      using all_x_in_r by auto
    have a_hs_neq: "a h1 \<noteq> a h2" "a h1 \<noteq> a h3" "a h2 \<noteq> a h3"
      using b_hs_eq_0 f1_eq f2_eq f3_eq fs_neq by force+
    have hs_neq: "h1 \<noteq> h2" "h1 \<noteq> h3" "h2 \<noteq> h3"
      using fs_neq f1_eq f2_eq f3_eq by auto

    have "aff_dim r = dim r"
      using aff_dim_zero[OF hull_inc[OF \<open>0 \<in> r\<close>]] .
    moreover have "aff_dim p = dim p"
      using aff_dim_zero[OF hull_inc[OF \<open>0 \<in> p\<close>]] .
    ultimately have "dim r = dim p - 2"
      using assms(4) by presburger

    have not_contained_xy_z:
      "\<not> ({x. a hx \<bullet> x \<le> 0} \<inter> {x. a hy \<bullet> x \<le> 0} \<subseteq> {x. a hz \<bullet> x \<le> 0})"
      if "hx \<in> F" "hy \<in> F" "hz \<in> F" "b hx = 0" "b hy = 0" "b hz = 0" "hx \<noteq> hz" "hy \<noteq> hz" for hx hy hz
    proof
      assume "{x. a hx \<bullet> x \<le> 0} \<inter> {x. a hy \<bullet> x \<le> 0} \<subseteq> {x. a hz \<bullet> x \<le> 0}"
      then have *: "hx \<inter> hy \<subseteq> hz"
        using that halfspaces
        by metis
      have "F - {hz} \<subset> F"
        using \<open>hz \<in> F\<close> \<open>finite F\<close> by blast
      then have p_psubset: "p \<subset> affine hull p \<inter> \<Inter>(F - {hz})"
        using minimal by presburger
      have "hx \<in> F - {hz}" "hy \<in> F - {hz}"
        using that by auto
      then show "False"
        using * p_eq p_psubset by blast
    qed
    have not_contained_12_3:
      "\<not> ({x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h2 \<bullet> x \<le> 0} \<subseteq> {x. a h3 \<bullet> x \<le> 0})"
      using not_contained_xy_z[OF \<open>h1 \<in> F\<close> \<open>h2 \<in> F\<close> \<open>h3 \<in> F\<close>] b_hs_eq_0 hs_neq
      by blast
    have not_contained_13_2:
      "\<not> ({x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h2 \<bullet> x \<le> 0})"
      using not_contained_xy_z[OF \<open>h1 \<in> F\<close> \<open>h3 \<in> F\<close> \<open>h2 \<in> F\<close>] b_hs_eq_0 hs_neq
      by blast
    have not_contained_23_1:
      "\<not> ({x. a h2 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h1 \<bullet> x \<le> 0})"
      using not_contained_xy_z[OF \<open>h2 \<in> F\<close> \<open>h3 \<in> F\<close> \<open>h1 \<in> F\<close>] b_hs_eq_0 hs_neq
      by blast

    obtain w where "w \<in> rel_interior p"
      using \<open>0 \<in> p\<close> polyhedron_imp_convex rel_interior_eq_empty assms(1)
      by auto
    moreover have "rel_interior p = {x \<in> p. \<forall>h\<in>F. a h \<bullet> x < b h}"
      using rel_interior_polyhedron_explicit[OF \<open>finite F\<close> p_eq, of a b]
        halfspaces minimal
      by blast
    ultimately have w_props: "a h1 \<bullet> w < 0" "a h2 \<bullet> w < 0" "a h3 \<bullet> w < 0"
      using b_hs_eq_0 \<open>h1 \<in> F\<close> \<open>h2 \<in> F\<close> \<open>h3 \<in> F\<close>
      by auto

    have "r \<subseteq> span p"
      using face_of_imp_subset[OF assms(2)] span_superset[of p]
      by blast
    have "a h1 \<in> span p" "a h2 \<in> span p" "a h3 \<in> span p"
      using halfspaces \<open>h1 \<in> F\<close> \<open>h2 \<in> F\<close> \<open>h3 \<in> F\<close> \<open>0 \<in> p\<close>
      by (metis add_0 affine_hull_span_0 hull_inc)+
    then have "span {a h1, a h2, a h3} \<subseteq> span p"
      using subspace_span[of p]
      by (simp add: span_minimal)
    then have "r \<union> span {a h1, a h2, a h3} \<subseteq> span p"
      using \<open>r \<subseteq> span p\<close> subspace_span[of p]
      by (simp add: subspace_sum_minimal)
    have "dim (span p) = dim p"
      by simp
    have "(\<And>x y. x \<in> r \<Longrightarrow> y \<in> span {a h1, a h2, a h3} \<Longrightarrow> x \<bullet> y = 0)"
    proof -
      fix x y
      assume x_in_r: "x \<in> r"
      assume "y \<in> span {a h1, a h2, a h3}"
      then show "x \<bullet> y = 0"
      proof (induct y rule: span_induct)
        case base
        then show ?case
          using subspace_hyperplane by blast
      next
        case (step y)
        then show ?case
          using all_x_in_r_0[OF x_in_r]
          by (metis inner_commute empty_iff insertE)
      qed
    qed
    then have "dim (r \<union> span {a h1, a h2, a h3}) = dim r + dim (span {a h1, a h2, a h3})"
      using dim_orthogonal_sum[of r "span {a h1, a h2, a h3}"]
      by blast
    moreover have "dim (r \<union> span {a h1, a h2, a h3}) \<le> dim p"
      using dim_subset[OF \<open>r \<union> span {a h1, a h2, a h3} \<subseteq> span p\<close>]
      by auto
    ultimately have "dim (span {a h1, a h2, a h3}) \<le> 2"
      using \<open>dim r = dim p - 2\<close>
      by linarith

    have "independent {a h1, a h2, a h3}"
    proof
      assume "dependent {a h1, a h2, a h3}"
      have "finite {a h1, a h2, a h3}" by simp
      obtain c where c_sum: "(\<Sum>v\<in>{a h1, a h2, a h3}. c v *\<^sub>R v) = 0" 
                 and nonzero: "\<exists>v\<in>{a h1, a h2, a h3}. c v \<noteq> 0"
        using \<open>dependent {a h1, a h2, a h3}\<close> dependent_finite[OF \<open>finite {a h1, a h2, a h3}\<close>] 
        by auto

      let ?c1 = "c (a h1)" and ?c2 = "c (a h2)" and ?c3 = "c (a h3)"
      have sum_0: "?c1 *\<^sub>R a h1 + ?c2 *\<^sub>R a h2 + ?c3 *\<^sub>R a h3 = 0"
        using c_sum a_hs_neq
        by (simp add: group_cancel.add1)
      have "?c1 \<noteq> 0"
      proof 
        assume "?c1 = 0"
        then have "?c2 *\<^sub>R a h2 + ?c3 *\<^sub>R a h3 = 0" using sum_0 by simp
        then have "?c2 \<noteq> 0" "?c3 \<noteq> 0" 
          using nonzero \<open>?c1 = 0\<close>
          using \<open>a h2 \<noteq> 0\<close> \<open>a h3 \<noteq> 0\<close> by auto

        define k where "k = - (?c3 / ?c2)"
        have "a h2 = k *\<^sub>R a h3"
          using \<open>?c2 *\<^sub>R a h2 + ?c3 *\<^sub>R a h3 = 0\<close> \<open>?c2 \<noteq> 0\<close> 
          unfolding k_def
          by (smt (verit, ccfv_SIG) eq_vector_fraction_iff neg_eq_iff_add_eq_0 scaleR_left.minus scaleR_minus_right) 

        show False
        proof (cases "k > 0")
          case True
          then have "{x. a h3 \<bullet> x \<le> 0} = {x. a h2 \<bullet> x \<le> 0}"
            unfolding \<open>a h2 = k *\<^sub>R a h3\<close> by (auto simp: mult_le_0_iff)
          then have "{x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h2 \<bullet> x \<le> 0} \<subseteq> {x. a h3 \<bullet> x \<le> 0}"
            by blast
          then show False using not_contained_12_3 by simp
        next
          case False
          then have "k < 0" 
            using \<open>a h2 = k *\<^sub>R a h3\<close> a_hs_neq(3) \<open>a h2 \<noteq> 0\<close> by fastforce
          have "a h2 \<bullet> w = k * (a h3 \<bullet> w)" using \<open>a h2 = k *\<^sub>R a h3\<close> \<open>a h2 \<noteq> 0\<close> by auto
          moreover have "a h2 \<bullet> w < 0" using w_props(2) by simp
          moreover have "k * (a h3 \<bullet> w) > 0" using \<open>k < 0\<close> w_props(3) mult_neg_neg by blast
          ultimately show False by simp
        qed
      qed

      define u where "u = -(?c2 / ?c1)"
      define v where "v = -(?c3 / ?c1)"
      have "?c1 *\<^sub>R a h1 = -?c2 *\<^sub>R a h2 - ?c3 *\<^sub>R a h3"
        by (metis (no_types, lifting) sum_0 add.left_commute add.right_neutral add_minus_cancel scaleR_left.minus
            uminus_add_conv_diff)
      then have "(1/?c1) *\<^sub>R (?c1 *\<^sub>R a h1) = (1/?c1) *\<^sub>R (-?c2 *\<^sub>R a h2 - ?c3 *\<^sub>R a h3)"
        by auto
      then have a1_eq: "a h1 = u *\<^sub>R a h2 + v *\<^sub>R a h3"
        using \<open>?c1 \<noteq> 0\<close> unfolding u_def v_def 
        by (simp add: scaleR_right_diff_distrib)

      have "u \<noteq> 0"
      proof
        assume "u = 0"
        then have "a h1 = v *\<^sub>R a h3"
          using a1_eq by simp
        show False
        proof (cases "v > 0")
          case True
          then have "{x. a h3 \<bullet> x \<le> 0} = {x. a h1 \<bullet> x \<le> 0}"
            unfolding \<open>a h1 = v *\<^sub>R a h3\<close>
            by (auto simp: mult_le_0_iff)
          then have "{x. a h2 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h1 \<bullet> x \<le> 0}"
            by blast
          then show False
            using not_contained_23_1
            by simp
        next
          case False
          then have "v < 0" 
            using \<open>a h1 = v *\<^sub>R a h3\<close> a_hs_neq(2) \<open>a h1 \<noteq> 0\<close>
            by auto
          have "a h1 \<bullet> w = v * (a h3 \<bullet> w)"
            using \<open>a h1 = v *\<^sub>R a h3\<close>
            by simp
          moreover have "a h1 \<bullet> w < 0"
            using w_props(1) by simp
          moreover have "v * (a h3 \<bullet> w) > 0"
            using \<open>v < 0\<close> w_props(3) mult_neg_neg
            by blast
          ultimately show False by simp
        qed
      qed

      have "v \<noteq> 0"
      proof
        assume "v = 0"
        then have "a h1 = u *\<^sub>R a h2"
          using a1_eq by simp
        show False
        proof (cases "u > 0")
          case True
          then have "{x. a h2 \<bullet> x \<le> 0} = {x. a h1 \<bullet> x \<le> 0}"
            unfolding \<open>a h1 = u *\<^sub>R a h2\<close>
            by (auto simp: mult_le_0_iff)
          then have "{x. a h2 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h1 \<bullet> x \<le> 0}"
            by blast
          then show False
            using not_contained_23_1
            by simp
        next
          case False
          then have "u < 0" 
            using \<open>a h1 = u *\<^sub>R a h2\<close> a_hs_neq(1) \<open>a h1 \<noteq> 0\<close>
            by auto
          have "a h1 \<bullet> w = u * (a h2 \<bullet> w)"
            using \<open>a h1 = u *\<^sub>R a h2\<close>
            by simp
          moreover have "a h1 \<bullet> w < 0"
            using w_props(1) by simp
          moreover have "u * (a h2 \<bullet> w) > 0"
            using \<open>u < 0\<close> w_props(2) mult_neg_neg
            by blast
          ultimately show False by simp
        qed
      qed

      consider (pos_pos) "u > 0" "v > 0" | 
               (pos_neg) "u > 0" "v < 0" | 
               (neg_pos) "u < 0" "v > 0" | 
               (neg_neg) "u < 0" "v < 0"
        using \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> by linarith
      then show "False"
      proof cases
        case pos_pos
        have "{x. a h2 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h1 \<bullet> x \<le> 0}"
        proof
          fix x
          assume x_in: "x \<in> {x. a h2 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0}"
          have "a h1 \<bullet> x = u * (a h2 \<bullet> x) + v * (a h3 \<bullet> x)"
            using a1_eq by (simp add: inner_add)
          also have "... \<le> 0"
            using x_in pos_pos
            by (simp add: add_decreasing2 split_mult_neg_le)
          finally show "x \<in> {x. a h1 \<bullet> x \<le> 0}"
            by blast
        qed
        then show False
          using not_contained_23_1 by simp
      next
        case pos_neg
        have "u *\<^sub>R a h2 = a h1 + (-v) *\<^sub>R a h3" 
          using a1_eq
          by (simp add: algebra_simps)
        have "{x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0} \<subseteq> {x. a h2 \<bullet> x \<le> 0}"
        proof
          fix x assume x_in: "x \<in> {x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h3 \<bullet> x \<le> 0}"
          have "u * (a h2 \<bullet> x) = (a h1 \<bullet> x) + (-v) * (a h3 \<bullet> x)"
            using \<open>u *\<^sub>R a h2 = a h1 + (-v) *\<^sub>R a h3\<close>
            by (metis inner_left_distrib inner_scaleR_left)
          also have "... \<le> 0"
            using x_in pos_neg
            by (smt (verit, best) IntE mem_Collect_eq mult_le_0_iff) 
          finally have "u * (a h2 \<bullet> x) \<le> 0" .
          then show "x \<in> {x. a h2 \<bullet> x \<le> 0}"
            using \<open>u > 0\<close>
            by (simp add: mult_le_0_iff)
        qed
        then show False
          using not_contained_13_2
          by simp
      next
        case neg_pos
        have "v *\<^sub>R a h3 = a h1 + (-u) *\<^sub>R a h2" 
          using a1_eq
          by (simp add: algebra_simps)
        have "{x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h2 \<bullet> x \<le> 0} \<subseteq> {x. a h3 \<bullet> x \<le> 0}"
        proof
          fix x
          assume x_in: "x \<in> {x. a h1 \<bullet> x \<le> 0} \<inter> {x. a h2 \<bullet> x \<le> 0}"
          have "v * (a h3 \<bullet> x) = (a h1 \<bullet> x) + (-u) * (a h2 \<bullet> x)"
            using \<open>v *\<^sub>R a h3 = a h1 + (-u) *\<^sub>R a h2\<close>
            by (metis inner_left_distrib inner_scaleR_left)
          also have "... \<le> 0"
            using x_in neg_pos
            by (smt (verit, best) IntE mem_Collect_eq mult_le_0_iff)
          finally show "x \<in> {x. a h3 \<bullet> x \<le> 0}"
            using \<open>v > 0\<close>
            by (simp add: mult_le_0_iff)
        qed
        then show False
          using not_contained_12_3
          by simp
      next
        case neg_neg
        have "a h1 \<bullet> w = u * (a h2 \<bullet> w) + v * (a h3 \<bullet> w)"
          using a1_eq
          by (simp add: inner_add)
        moreover have "u * (a h2 \<bullet> w) > 0" "v * (a h3 \<bullet> w) > 0"
          using neg_neg w_props(2,3) mult_neg_neg
          by blast+
        ultimately have "a h1 \<bullet> w > 0"
          by simp
        then show False
          using w_props(1) by simp
      qed
    qed

    then have "dim (span {a h1, a h2, a h3}) = 3"
      using a_hs_neq(1,2,3) dim_span_eq_card_independent
      by fastforce
    then show ?thesis
      using \<open>dim (span {a h1, a h2, a h3}) \<le> 2\<close>
      by linarith
  qed
qed

lemma polyhedron_ridge_two_facets:
  fixes p :: "'a :: euclidean_space set"
  assumes "polyhedron p"
    and "r face_of p"
    and "r \<noteq> {}"
    and "aff_dim r = aff_dim p - 2"
  shows "\<exists>f1 f2. f1 face_of p \<and> aff_dim f1 = aff_dim p - 1 \<and>
                 f2 face_of p \<and> aff_dim f2 = aff_dim p - 1 \<and>
                 f1 \<noteq> f2 \<and> r \<subseteq> f1 \<and> r \<subseteq> f2 \<and> r = f1 \<inter> f2 \<and>
                 (\<forall>f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<and> r \<subseteq> f
                      \<longrightarrow> f = f1 \<or> f = f2)"
proof -
  obtain z where "z \<in> r"
    using assms(3) by blast
  then have "z \<in> p"
    using assms(2) face_of_imp_subset by auto
  let ?r' = "((+) (-z)) ` r"
  let ?p' = "((+) (-z)) ` p"
  have origin_r': "0 \<in> ?r'"
    using \<open>z \<in> r\<close> by simp
  have origin_p': "0 \<in> ?p'"
    using \<open>z \<in> p\<close> by simp
  have polyhedron: "polyhedron ?p'"
    using assms(1) polyhedron_translation_eq[of p "-z"] by blast
  have face_of: "?r' face_of ?p'"
    using assms(2) face_of_translation_eq by blast
  have nonempty: "?r' \<noteq> {}"
    using assms(3) by blast
  have aff_dims: "aff_dim ?r' = aff_dim ?p' - 2"
    by (metis aff_dim_translation_eq assms(4))
  obtain f1 f2 where
    f1_face_of: "f1 face_of ?p'" and
    aff_dim_f1: "aff_dim f1 = aff_dim ?p' - 1" and
    f2_face_of: "f2 face_of ?p'" and
    aff_dim_f2: "aff_dim f2 = aff_dim ?p' - 1" and
    fs_neq: "f1 \<noteq> f2" and
    sub_f1: "?r' \<subseteq> f1" and
    sub_f2: "?r' \<subseteq> f2" and
    fs_inter_eq: "f1 \<inter> f2 = ?r'" and
    only_fs: "(\<forall>f. f face_of ?p' \<and>
                      aff_dim f = aff_dim ?p' - 1 \<and> ?r' \<subseteq> f \<longrightarrow>
                      f = f1 \<or> f = f2)"
    using polyhedron_ridge_two_facets_0[OF polyhedron face_of origin_r' aff_dims]
    by auto
  let ?f1' = "((+) z) ` f1"
  let ?f2' = "((+) z) ` f2"
  have "?f1' face_of p"
    by (metis f1_face_of face_of_translation_eq translation_galois)
  moreover have "aff_dim ?f1' = aff_dim p - 1"
    by (metis aff_dim_f1 aff_dim_translation_eq)
  moreover have "?f2' face_of p"
    by (metis f2_face_of face_of_translation_eq translation_galois)
  moreover have "aff_dim ?f2' = aff_dim p - 1"
    by (metis aff_dim_f2 aff_dim_translation_eq)
  moreover have "?f1' \<noteq> ?f2'"
    using fs_neq translation_invert
    by auto
  moreover have "r \<subseteq> ?f1'"
    by (metis sub_f1 subset_image_iff translation_galois)
  moreover have "r \<subseteq> ?f2'"
    by (metis sub_f2 subset_image_iff translation_galois)
  moreover have "?f1' \<inter> ?f2' = r"
    by (metis fs_inter_eq translation_Int translation_galois)
  moreover have "(\<forall>f. f face_of p \<and>
                      aff_dim f = aff_dim p - 1 \<and> r \<subseteq> f \<longrightarrow>
                      f = ?f1' \<or> f = ?f2')"
    by (smt (verit, best) aff_dim_translation_eq face_of_translation_eq image_mono
        only_fs translation_galois)
  ultimately show ?thesis
    by blast
qed

subsection \<open>Lower bounds on face counts\<close>

subsubsection \<open>Vertices\<close>

lemma polytope_vertex_lower_bound:
  assumes "polytope p"
  shows "aff_dim p + 1 \<le> card {v. v face_of p \<and> aff_dim v = 0}"
proof -
  let ?V = "{v. v extreme_point_of p}"
  have sets_eq: "{v. v face_of p \<and> aff_dim v = 0} = (\<lambda>v. {v}) ` ?V"
    using face_of_singleton aff_dim_sing aff_dim_eq_0
    by auto
  then have cards_eq: "card {v. v face_of p \<and> aff_dim v = 0} = card ?V"
    unfolding sets_eq using card_image inj_singleton
    by blast
  have "aff_dim p + 1 \<le> aff_dim (convex hull ?V) + 1"
    using Krein_Milman_Minkowski[OF polytope_imp_compact[OF assms] polytope_imp_convex[OF assms]]
    by simp
  moreover have "aff_dim (convex hull ?V) + 1 \<le> card ?V"
    using finite_polyhedron_extreme_points[OF polytope_imp_polyhedron[OF assms]]
      aff_dim_le_card[of ?V] aff_dim_convex_hull[of ?V]
    by simp
  ultimately show ?thesis
    unfolding cards_eq by auto
qed

subsubsection\<open>Facets\<close>

lemma polytope_facet_lower_bound_0:
  assumes "polytope p"
  assumes "aff_dim p \<noteq> 0"
  assumes origin_in_p: "0 \<in> p"
  shows "aff_dim p + 1 \<le> card {f. f facet_of p}"
proof -
  have aff_dim_eq_dim: "aff_dim p = dim p"
    using origin_in_p aff_dim_zero[of p]
    by (simp add: hull_inc)

  obtain H a b where
    "finite H" and
    p_eq: "p = affine hull p \<inter> \<Inter>H" and
    halfspaces: "\<And>h. h\<in>H \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h} \<and>
             (\<forall>x \<in> affine hull p. x + a h \<in> affine hull p)" and
    minimal: "\<And>F'. F' \<subset> H \<longrightarrow> p \<subset> affine hull p \<inter> \<Inter>F'"
    using polyhedron_Int_affine_parallel_minimal[of p]
      polytope_imp_polyhedron[OF assms(1)]
    by metis
  have p_eq_span: "p = span p \<inter> \<Inter>H"
    using p_eq \<open>0 \<in> p\<close> affine_hull_span_0
    by blast
  have "\<And>h. h\<in>H \<Longrightarrow> 0\<in>h"
    using \<open>0 \<in> p\<close> p_eq
    by blast
  then have b_nonneg: "\<And>h. h\<in>H \<Longrightarrow> 0 \<le> b h"
    by (metis halfspaces inner_zero_right mem_Collect_eq)

  have ineq1: "dim p + 1 \<le> card H"
  proof (rule ccontr)
    assume "\<not>(dim p + 1 \<le> card H)"
    then have *: "card H \<le> dim p"
      by auto
    have "H \<noteq> {}"
      by (smt (verit, ccfv_threshold) IntE Int_lower2 affine_affine_hull
          affine_bounded_eq_lowdim closure_Inter_convex_open
          convex_rel_interior_finite_Inter emptyE finite.intros(1) image_is_empty
          inf.orderE local.aff_dim_eq_dim of_nat_0_le_iff origin_in_p p_eq
          polytope_eq_bounded_polyhedron rel_interior_eq_closure subset_hull
          assms(1,2))
    then obtain h where "h\<in>H"
      by blast
    have "\<forall>h'\<in>H. a h' \<in> span p"
      by (metis add_0 affine_hull_span_0 halfspaces hull_inc origin_in_p)
    then have "span (a ` (H - {h})) \<subseteq> span p"
      using span_mono[of "a ` (H - {h})" "span p"] span_span[of p]
      by blast
    moreover have "span (a ` (H - {h})) \<noteq> span p"
    proof
      assume "span (a ` (H - {h})) = span p"
      then have "dim (span p) = dim (span (a ` (H - {h})))"
        by argo
      also have "... \<le> card (a ` (H - {h}))"
        by (simp add: \<open>finite H\<close> dim_le_card')
      finally show "False"
        by (metis (no_types, lifting) "*" \<open>finite H\<close> \<open>h \<in> H\<close> card_Diff1_less_iff
            card_image_le dim_span finite_Diff linorder_not_le order_trans)
    qed
    ultimately have span_psubset: "span (a ` (H - {h})) \<subset> span p"
      by blast
    obtain n where
      "n \<noteq> 0"
      "n \<in> span p" and
      orthogonal: "\<And>x. x \<in> span (a ` (H - {h})) \<Longrightarrow> orthogonal n x"
      using orthogonal_to_subspace_exists_gen[OF span_psubset]
      by blast
    obtain B where bounded: "\<And>x. x\<in>p \<Longrightarrow> norm x \<le> B"
      using polytope_imp_bounded[OF assms(1)] bounded_pos[of p]
      by blast
    {assume "a h \<bullet> n \<ge> 0"
      let ?x = "-((B + 1) / (norm n)) *\<^sub>R n"
      have "?x \<in> span p"
        using \<open>n \<in> span p\<close> span_mul
        by blast
      moreover have "\<And>k. k\<in>H \<Longrightarrow> (a k) \<bullet> ?x \<le> (b k)"
      proof -
        fix k
        assume "k\<in>H"
        {assume "k = h"
          have "a h \<bullet> ?x \<le> b h"
            using \<open>0 \<le> a h \<bullet> n\<close> \<open>h \<in> H\<close> b_nonneg bounded divide_nonneg_nonneg
              inner_simps(6) origin_in_p real_0_le_add_iff
            by fastforce
        } moreover {assume "k \<noteq> h"
          have "(a k) \<bullet> ?x \<le> (b k)"
            by (smt (verit, best) \<open>k \<in> H\<close> \<open>k \<noteq> h\<close> b_nonneg image_eqI inner_commute
                inner_simps(6) insert_Diff_single insert_absorb insert_iff mult_eq_0_iff
                orthogonal orthogonal_def span_superset subsetD)
        } ultimately show "a k \<bullet> ?x \<le> b k"
          by blast
      qed
      ultimately have "?x \<in> p"
        using p_eq_span halfspaces
        by blast
      have "norm ?x > B"
        by (simp add: \<open>n \<noteq> 0\<close>)
      then have "False"
        using bounded[OF \<open>?x \<in> p\<close>]
        by linarith
    } moreover {assume "a h \<bullet> n \<le> 0"
      let ?x = "((B + 1) / (norm n)) *\<^sub>R n"
      have "?x \<in> span p"
        using \<open>n \<in> span p\<close> span_mul
        by blast
      moreover have "\<And>k. k\<in>H \<Longrightarrow> a k \<bullet> ?x \<le> b k"
      proof -
        fix k
        assume "k\<in>H"
        {assume "k = h"
          have "a h \<bullet> ?x \<le> b h"
            by (smt (verit, best) \<open>a h \<bullet> n \<le> 0\<close> \<open>h \<in> H\<close> b_nonneg bounded inner_simps(6)
                norm_ge_zero norm_zero origin_in_p real_scaleR_def split_scaleR_neg_le
                zero_le_divide_iff zero_less_one_class.zero_le_one)
        } moreover {assume "k \<noteq> h"
          have "(a k) \<bullet> ?x \<le> (b k)"
            by (smt (verit, best) \<open>k \<in> H\<close> \<open>k \<noteq> h\<close> b_nonneg image_eqI inner_commute
                inner_simps(6) insert_Diff_single insert_absorb insert_iff mult_eq_0_iff
                orthogonal orthogonal_def span_superset subsetD)
        } ultimately show "a k \<bullet> ?x \<le> b k"
          by blast
      qed
      ultimately have "?x \<in> p"
        using p_eq_span halfspaces
        by blast
      have "norm ?x > B"
        by (simp add: \<open>n \<noteq> 0\<close>)
      then have "False"
        using bounded[OF \<open>?x \<in> p\<close>]
        by linarith
    } ultimately show "False"
      by linarith
  qed

  have ineq2: "card H = card {f. f facet_of p}"
  proof -
    let ?g = "\<lambda>h. p \<inter> {x. a h \<bullet> x = b h}"
    have halfspaces_simple: "\<And>h'. h' \<in> H \<Longrightarrow> a h' \<noteq> 0 \<and> h' = {x. a h' \<bullet> x \<le> b h'}"
      using halfspaces by blast
    have "{f. f facet_of p} = ?g ` H"
      using facet_of_polyhedron_explicit[OF \<open>finite H\<close> p_eq halfspaces_simple] minimal
      by auto
    moreover have "inj_on ?g H"
      using facets_of_polyhedron_explicit_distinct[OF \<open>finite H\<close> p_eq halfspaces_simple]
      by (auto simp: minimal inj_on_def)
    ultimately show ?thesis
      using card_image by fastforce
  qed

  show ?thesis
    unfolding aff_dim_eq_dim
    using ineq1 ineq2
    by linarith
qed

lemma polytope_facet_lower_bound:
  assumes "polytope p"
  assumes "aff_dim p \<noteq> 0"
  shows "aff_dim p + 1 \<le> card {f. f facet_of p}"
proof (cases "p = {}")
  case True
  then show ?thesis
    using aff_dim_empty[of p] facet_of_empty
    by simp
next
  case False
  then obtain z where "z \<in> p"
    by blast
  have has_origin: "0 \<in> ((+) (-z) ` p)"
    using \<open>z \<in> p\<close> by simp
  have is_polytope: "polytope ((+) (-z) ` p)"
    using polytope_translation_eq[of "-z" p] assms(1)
    by blast
  have nonzero_aff_dim: "aff_dim ((+) (-z) ` p) \<noteq> 0"
    using aff_dim_translation_eq[of "-z" p] assms(2)
    by argo
  have h1: "card {f. f facet_of (+) (- z) ` p} = card ((`) ((+) (- z)) ` {f. f facet_of p})"
    using facets_of_translation[of "-z" p]
    by argo
  moreover have "inj_on ((`) ((+) (- z))) {f. f facet_of p}"
      by (simp add: inj_on_image)
  ultimately have "card {f. f facet_of (+) (- z) ` p} = card {f. f facet_of p}"
    by (metis card_image)
  then show ?thesis
    using polytope_facet_lower_bound_0[OF is_polytope nonzero_aff_dim has_origin]
    unfolding aff_dim_translation_eq[of "-z" p]
    by argo
qed

subsection\<open>Double counting\<close>

lemma multiple_counting:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite s"
  assumes "finite t"
  assumes "\<And>x. x\<in>s \<Longrightarrow> card {y\<in>t. R x y} = m"
  assumes "\<And>y. y\<in>t \<Longrightarrow> card {x\<in>s. R x y} = n"
  shows "m * card s = n * card t"
proof -
  have lhs: "(\<Sum>x\<in>s. \<Sum>y\<in>{y\<in>t. R x y}. 1) = m * card s"
    using assms(1,3) by simp
  have rhs: "(\<Sum>y\<in>t. \<Sum>x\<in>{x\<in>s. R x y}. 1) = n * card t"
    using assms(2,4) by simp
  show ?thesis
    using sum.swap_restrict[OF assms(1) assms(2), of "\<lambda>x y. (1::nat)" R]
    unfolding lhs rhs .
qed

subsubsection\<open>$m F = 2 E$\<close>

text\<open>Let F be the number of facets and E be the number of ridges.
     If there are m ridges per facet, then m*F = 2*E.\<close>

lemma facet_ridge_relation:
  assumes "polytope p"
      and "aff_dim p \<ge> 2"
      and edges_per_face: "\<forall>f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<longrightarrow>
                card {e. e face_of p \<and> aff_dim e = aff_dim p - 2 \<and> e \<subseteq> f} = m"
  shows "m * card {f. f face_of p \<and> aff_dim f = aff_dim p - 1} =
         2 * card {e. e face_of p \<and> aff_dim e = aff_dim p - 2}"
proof -
  let ?faces_set = "{f. f face_of p \<and> aff_dim f = aff_dim p - 1}"
  let ?edges_set = "{e. e face_of p \<and> aff_dim e = aff_dim p - 2}"
  have finite_faces: "finite ?faces_set"
    using finite_polytope_faces[OF \<open>polytope p\<close>]
    by fast
  have finite_edges: "finite ?edges_set"
    using finite_polytope_faces[OF \<open>polytope p\<close>]
    by fast
  have lhs_m: "\<And>f. f\<in>?faces_set \<Longrightarrow> card {e\<in>?edges_set. e \<subseteq> f} = m"
    using edges_per_face by auto
  have rhs_2: "\<And>e. e\<in>?edges_set \<Longrightarrow> card {f\<in>?faces_set. e \<subseteq> f} = 2"
  proof -
    fix e
    assume *: "e\<in>?edges_set"
    have "e face_of p"
      using *
      by blast
    have aff_dim_e: "aff_dim e = aff_dim p - 2"
      using * by auto
    then have "e \<noteq> {}"
      using assms(2) by auto
    have "polyhedron p"
      using polytope_imp_polyhedron[OF \<open>polytope p\<close>] .
    obtain f1 f2 where 
      f1_props: "f1 face_of p" "aff_dim f1 = aff_dim p - 1" "e \<subseteq> f1" and
      f2_props: "f2 face_of p" "aff_dim f2 = aff_dim p - 1" "e \<subseteq> f2" and
      distinct: "f1 \<noteq> f2" and
      characterization: "\<forall>f. f face_of p \<and> aff_dim f = aff_dim p - 1 \<and> e \<subseteq> f \<longrightarrow> f = f1 \<or> f = f2"
      using polyhedron_ridge_two_facets[OF \<open>polyhedron p\<close> \<open>e face_of p\<close> \<open>e \<noteq> {}\<close> aff_dim_e]
      by auto
    have "{f\<in>?faces_set. e \<subseteq> f} = {f1, f2}"
      using characterization f1_props f2_props
      by auto
    then show "card {f\<in>?faces_set. e \<subseteq> f} = 2"
      using distinct
      by simp
  qed
  show ?thesis
    using multiple_counting[OF finite_faces finite_edges lhs_m rhs_2] .
qed

subsubsection\<open>$n V = 2 E$\<close>

text\<open>Let V be the number of vertices and E be the number of edges.
     If there are n edges per vertex, then n*V = 2*E.\<close>

lemma edge_vertex_relation:
  assumes "polytope p"
      and edges_per_vert: "\<forall>v. v face_of p \<and> aff_dim v = 0 \<longrightarrow>
                card {e. e face_of p \<and> aff_dim e = 1 \<and> v \<subseteq> e} = n"
  shows "n * card {v. v face_of p \<and> aff_dim v = 0} =
         2 * card {e. e face_of p \<and> aff_dim e = 1}"
proof -
  let ?vertices_set = "{v. v face_of p \<and> aff_dim v = 0}"
  let ?edges_set = "{e. e face_of p \<and> aff_dim e = 1}"
  have finite_vertices: "finite ?vertices_set"
    using finite_polytope_faces[OF \<open>polytope p\<close>]
    by fast
  have finite_edges: "finite ?edges_set"
    using finite_polytope_faces[OF \<open>polytope p\<close>]
    by fast
  have lhs_n: "\<And>v. v\<in>?vertices_set \<Longrightarrow> card {e\<in>?edges_set. v \<subseteq> e} = n"
    using edges_per_vert by auto
  have rhs_2: "\<And>e. e\<in>?edges_set \<Longrightarrow> card {v\<in>?vertices_set. v \<subseteq> e} = 2"
  proof -
    fix e
    assume *: "e\<in>?edges_set"
    have "aff_dim e = 1"
      using * by auto
    then have "e \<noteq> {}"
      by force
    have "compact e"
      using * face_of_polytope_polytope[OF \<open>polytope p\<close>] polytope_imp_compact[of e]
      by blast
    have "convex e"
      using * unfolding face_of_def
      by blast
    have "collinear e"
    proof -
      obtain B where
        aff_hull_B_e: "affine hull B = affine hull e" and
        "\<not> affine_dependent B" and
        "int (card B) = 2"
        using \<open>aff_dim e = 1\<close> aff_dim_basis_exists[of e] by auto
      then obtain x y where B_eq: "B = {x, y}" "x \<noteq> y"
        by (meson card_2_iff of_nat_eq_numeral_iff)
      have "e \<subseteq> affine hull B"
        by (simp add: aff_hull_B_e hull_subset) 
      then show ?thesis
        unfolding B_eq using collinear_affine_hull
        by fast
    qed
    then obtain a b where e_eq: "e = closed_segment a b"
      using compact_convex_collinear_segment[OF \<open>e \<noteq> {}\<close> \<open>compact e\<close> \<open>convex e\<close> \<open>collinear e\<close>]
      by blast
    then have "a \<noteq> b"
      using \<open>aff_dim e = 1\<close>
      by force

    have "{v. v extreme_point_of e} = {v. {v} face_of e \<and> aff_dim {v} = 0}"
      unfolding face_of_singleton[symmetric] using aff_dim_sing
      by blast
    then have "(\<lambda>x. {x}) ` {v. v extreme_point_of e} = {v. v face_of e \<and> aff_dim v = 0}"
      using aff_dim_eq_0 by auto
    then have "(\<lambda>x. {x}) ` {v. v extreme_point_of e} = {v. v face_of p \<and> aff_dim v = 0 \<and> v \<subseteq> e}"
      using face_of_face * by force
    then have "bij_betw (\<lambda>x. {x}) {v. v extreme_point_of e} {v\<in>?vertices_set. v \<subseteq> e}"
      by (simp add: bij_betw_imageI inj_on_def)
    then have "card {v\<in>?vertices_set. v \<subseteq> e} = card {v. v extreme_point_of e}"
      using bij_betw_same_card by force
    moreover have "{v. v extreme_point_of e} = {a, b}"
      unfolding e_eq using extreme_point_of_segment[of _ a b] \<open>a \<noteq> b\<close>
      by auto
    moreover have "card {a, b} = 2"
      using \<open>a \<noteq> b\<close> by simp
    ultimately show "card {v\<in>?vertices_set. v \<subseteq> e} = 2"
      by argo
  qed
  show ?thesis
    using multiple_counting[OF finite_vertices finite_edges lhs_n rhs_2] .
qed

(* Don't expose multiple_counting because it doesn't have anything to do with polytopes *)
hide_fact multiple_counting

subsection \<open>Face containment\<close>

lemma ridge_belongs_to_facet:
  assumes "e face_of p"
      and "aff_dim e = aff_dim p - 2"
      and "aff_dim p \<ge> 2"
      and "polyhedron p"
  obtains f where "f face_of p" "aff_dim f = aff_dim p - 1" "e face_of f"
proof -
  have "e \<noteq> {}"
    using assms(2,3) by auto
  moreover have "e \<noteq> p"
    using assms(2,3) by auto
  ultimately obtain f where "f facet_of p" "e \<subseteq> f"
    using assms(1,4) face_of_polyhedron_subset_facet
    by blast
  then have "f face_of p" "aff_dim f = aff_dim p - 1"
    unfolding facet_of_def by simp+
  moreover have "e face_of f"
    using \<open>f face_of p\<close> assms(1) \<open>e \<subseteq> f\<close> face_of_face
    by blast
  ultimately show "(\<And>f. f face_of p \<Longrightarrow> aff_dim f = aff_dim p - 1 \<Longrightarrow> e face_of f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed

lemma peak_belongs_to_ridge:
  assumes "v face_of p"
      and "aff_dim v = aff_dim p - 3"
      and "aff_dim p \<ge> 3"
      and "polyhedron p"
  obtains e where "e face_of p" "aff_dim e = aff_dim p - 2" "v face_of e"
proof -
  have "v \<noteq> {}"
    using assms(2,3) by auto
  moreover have "v \<noteq> p"
    using assms(2,3) by auto
  ultimately obtain f where "f facet_of p" "v \<subseteq> f"
    using assms(1,4) face_of_polyhedron_subset_facet
    by blast
  then have "f face_of p" "aff_dim f = aff_dim p - 1"
    unfolding facet_of_def assms(3)
    by simp+
  moreover have "v face_of f"
    using \<open>f face_of p\<close> assms(1) \<open>v \<subseteq> f\<close> face_of_face
    by blast
  obtain e where "e face_of f" "aff_dim e = aff_dim p - 2" "v face_of e"
    using ridge_belongs_to_facet[OF \<open>v face_of f\<close> _ _ 
          face_of_polyhedron_polyhedron[OF assms(4) \<open>f face_of p\<close>]]
      assms(2,3) \<open>aff_dim f = aff_dim p - 1\<close>
    by auto
  then show "(\<And>e. e face_of p \<Longrightarrow> aff_dim e = aff_dim p - 2 \<Longrightarrow> v face_of e \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using face_of_trans[OF \<open>e face_of f\<close> \<open>f face_of p\<close>]
    by blast
qed

end
