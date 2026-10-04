section\<open>Computational helpers\<close>

theory Computation
  imports
    Convex_More
    Determinants_More
    "HOL-Analysis.Cross3"
    "HOL-Analysis.Polytope"
    "HOL-Eisbach.Eisbach"
    Polytope_More
    "HOL-Examples.Sqrt"
begin

subsection\<open>Operations in $\mathbb{Q}(\sqrt{5})$\<close>

text\<open>Numbers of the form $a + b \sqrt{5}$, where $a, b \in \mathbb{Q}$\<close>

abbreviation \<phi> :: "real"
  where "\<phi> \<equiv> (1 + sqrt 5)/2"

lemma real_rat5_mul:
  "(a1 + b1 * sqrt 5) * (a2 + b2 * sqrt 5)
    = (a1 * a2 + 5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt 5"
  by (simp add: algebra_simps)

lemma real_rat5_inv:
  assumes "a^2 \<noteq> 5 * b^2"
  shows "inverse (a + b * sqrt 5) = a / (a^2 - 5 * b^2) + -b / (a^2 - 5 * b^2) * sqrt 5"
proof -
  have "(a + b * sqrt 5) * (a - b * sqrt 5) = a^2 - 5 * b^2"
    by (simp add: algebra_simps power2_eq_square)
  moreover have "a^2 - 5 * b^2 \<noteq> 0"
    using assms by simp
  ultimately have "inverse (a + b * sqrt 5) = (a - b * sqrt 5) / (a^2 - 5 * b^2)"
    by (metis divide_inverse mult_1 mult_eq_0_iff
        nonzero_divide_mult_cancel_right)
  then show ?thesis
    by argo
qed

lemma real_rat5_div:
  assumes "a2^2 \<noteq> 5 * b2^2"
  shows "(a1 + b1 * sqrt 5) / (a2 + b2 * sqrt 5) = 
         ((a1 * a2 - 5 * b1 * b2) / (a2^2 - 5 * b2^2)) + 
         ((a2 * b1 - a1 * b2) / (a2^2 - 5 * b2^2)) * sqrt 5"
  unfolding divide_inverse[of "(a1 + b1 * sqrt 5)" "(a2 + b2 * sqrt 5)"]
    real_rat5_inv[OF assms]
  using real_rat5_mul[of a1 b1 "a2 / (a2^2 - 5 * b2^2)" "-b2 / (a2^2 - 5 * b2^2)"]
  by argo

lemma real_rat5_le_sqrt_cases:
  "x \<le> y * sqrt 5 \<longleftrightarrow>
   (x \<le> 0 \<and> 0 \<le> y) \<or>
   (0 \<le> x \<and> 0 \<le> y \<and> x^2 \<le> 5 * y^2) \<or>  
   (x \<le> 0 \<and> y \<le> 0 \<and> 5 * y^2 \<le> x^2)"
proof -
  have sqrt5_pos: "sqrt 5 > 0" by simp
  have sqrt5_sq: "(sqrt 5)^2 = 5" by simp

  consider
    (x_ge0_y_ge0) "x \<ge> 0" "y \<ge> 0" |
    (x_ge0_y_le0) "x \<ge> 0" "y \<le> 0" |
    (x_le0_y_ge0) "x \<le> 0" "y \<ge> 0" |
    (x_le0_y_le0) "x \<le> 0" "y \<le> 0"
    by argo

  then show ?thesis
  proof (cases)
    case x_ge0_y_ge0
    then show ?thesis
      using power_mono_iff[of x "y * sqrt 5" 2]
      by (auto simp add: power_mult_distrib sqrt5_sq mult_ac)
  next
    case x_ge0_y_le0
    then show ?thesis
      by (smt (verit) mult.left_commute mult_le_0_iff mult_zero_left
          not_numeral_le_zero power2_eq_square power2_less_eq_zero_iff
          real_sqrt_le_0_iff zero_le_mult_iff)
  next
    case x_le0_y_ge0
    then show ?thesis
      by (smt (verit, del_insts) sqrt5_pos power_mult_distrib real_sqrt_mult
          real_sqrt_pow2_iff)
  next
    case x_le0_y_le0
    have "x \<le> y * sqrt 5 \<longleftrightarrow> -x \<ge> -y * sqrt 5"
      by linarith
    also have "... \<longleftrightarrow> (-x)^2 \<ge> (-y * sqrt 5)^2"
      by (smt (verit) x_le0_y_le0 sqrt5_pos mult_nonneg_nonneg pos2 power_mono_iff)
    also have "... \<longleftrightarrow> x^2 \<ge> 5 * y^2"
      by (simp add: power_mult_distrib sqrt5_sq mult_ac)
    finally show ?thesis using \<open>x \<le> 0\<close> \<open>y \<le> 0\<close> by auto
  qed
qed

lemma real_rat5_le_comparison:
  "(a1 + b1 * sqrt 5) \<le> (a2 + b2 * sqrt 5) \<longleftrightarrow>
   (a1 \<le> a2 \<and> b1 \<le> b2) \<or>
   (a2 \<le> a1 \<and> b1 \<le> b2 \<and> (a1 - a2)^2 \<le> 5 * (b2 - b1)^2) \<or>
   (a1 \<le> a2 \<and> b2 \<le> b1 \<and> 5 * (b2 - b1)^2 \<le> (a1 - a2)^2)"
  using real_rat5_le_sqrt_cases[of "a1 - a2" "b2 - b1"]
  by argo

text\<open>Wrapper definition to avoiding oversimplification when applying simp\<close>

definition rat5 :: "rat \<Rightarrow> rat \<Rightarrow> real"
  where "rat5 a b = real_of_rat a + real_of_rat b * sqrt 5"

lemma rat5_add: "rat5 a1 b1 + rat5 a2 b2 = rat5 (a1 + a2) (b1 + b2)"
  unfolding rat5_def
  by (simp add: algebra_simps of_rat_add)

lemma rat5_sub: "rat5 a1 b1 - rat5 a2 b2 = rat5 (a1 - a2) (b1 - b2)"
  unfolding rat5_def
  by (simp add: algebra_simps of_rat_diff)

lemma rat5_mul: "rat5 a1 b1 * rat5 a2 b2 = rat5 (a1 * a2 + 5 * b1 * b2) (a1 * b2 + b1 * a2)"
  unfolding rat5_def
  by (simp add: algebra_simps of_rat_mult of_rat_add)

lemma rat5_div:
  assumes "a2 \<noteq> 0 \<or> b2 \<noteq> 0"
  shows "rat5 a1 b1 / rat5 a2 b2 = 
         rat5 ((a1 * a2 - 5 * b1 * b2) / (a2^2 - 5 * b2^2)) 
           ((a2 * b1 - a1 * b2) / (a2^2 - 5 * b2^2))"
proof -
  have denom_nonzero: "(real_of_rat a2)^2 \<noteq> 5 * (real_of_rat b2)^2"
  proof
    assume *: "(real_of_rat a2)^2 = 5 * (real_of_rat b2)^2"
    show False
    proof (cases "b2 = 0")
      case True
      then show False
        using * assms by simp
    next
      case False
      have "5 = (real_of_rat a2 / real_of_rat b2)^2"
        using * False
        by (simp add: field_simps of_rat_divide)
      then have "sqrt 5 = abs (real_of_rat (a2 / b2))"
        by (metis of_rat_divide real_sqrt_abs)
      moreover have "sqrt 5 \<notin> \<rat>"
        using sqrt_prime_irrational[of 5] by auto
      moreover have "abs (real_of_rat (a2 / b2)) \<in> \<rat>"
        by simp
      ultimately show False
        by auto
    qed
  qed
  show ?thesis
    using rat5_def real_rat5_div[OF denom_nonzero]
    by (simp add: of_rat_diff of_rat_divide of_rat_mult of_rat_power)
qed

lemma rat5_le:
  "(rat5 a1 b1 \<le> rat5 a2 b2) =
   ((a1 \<le> a2 \<and> b1 \<le> b2) \<or>
   (a2 \<le> a1 \<and> b1 \<le> b2 \<and> (a1 - a2)^2 \<le> 5 * (b2 - b1)^2) \<or>
   (a1 \<le> a2 \<and> b2 \<le> b1 \<and> 5 * (b2 - b1)^2 \<le> (a1 - a2)^2))"
  unfolding rat5_def real_rat5_le_comparison
  by (metis (mono_tags, opaque_lifting) of_rat_diff of_rat_less_eq of_rat_mult of_rat_numeral_eq
      of_rat_power)

lemma rat5_eq: "rat5 a1 b1 = rat5 a2 b2 \<longleftrightarrow> a1 = a2 \<and> b1 = b2"
proof -
  {
    assume *: "rat5 a1 b1 = rat5 a2 b2" "b1 \<noteq> b2"
    have "real_of_rat (a1 - a2) = real_of_rat (b2 - b1) * sqrt 5"
      using * rat5_def
      by (simp add: left_diff_distrib of_rat_diff)
    moreover have "real_of_rat (b2 - b1) \<noteq> 0"
      using * by simp
    ultimately have "sqrt 5 = real_of_rat ((a1 - a2) / (b2 - b1))"
      by (simp add: of_rat_divide)
    then have False
      using sqrt_prime_irrational[of 5] by auto
  } then show ?thesis
    using rat5_def by force
qed

lemma rat5_0_1:
  shows "rat5 0 0 = 0" "rat5 1 0 = 1" unfolding rat5_def by auto

lemma rat5_eq_0:
  "rat5 a1 b1 = 0 \<longleftrightarrow> a1 = 0 \<and> b1 = 0"
  using rat5_eq[of a1 b1 0 0] unfolding rat5_def
  by simp

lemma rat5_eq_1:
  "rat5 a1 b1 = 1 \<longleftrightarrow> a1 = 1 \<and> b1 = 0"
  using rat5_eq[of a1 b1 1 0] unfolding rat5_def
  by simp

subsection\<open>Operations in $\mathbb{R}^3$\<close>

lemma vector3_add:          
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows "vector [x1, x2, x3] + vector [y1, y2, y3] = 
         vector [x1 + y1, x2 + y2, x3 + y3]"
  by (simp add: vec_eq_iff vector_def forall_3)

lemma vector3_sub:
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows "vector [x1, x2, x3] - vector [y1, y2, y3] = 
         vector [x1 - y1, x2 - y2, x3 - y3]"
  by (simp add: vec_eq_iff vector_def forall_3)

unbundle cross3_syntax

lemma vector3_cross:
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows "vector [x1, x2, x3] \<times> vector [y1, y2, y3] = 
         (vector [x2 * y3 - x3 * y2, x3 * y1 - x1 * y3, x1 * y2 - x2 * y1] :: real^3)"
  by (simp add: cross3_def)

lemma vector3_eq_0:
  fixes x1 x2 x3 :: real
  shows "(vector [x1, x2, x3] :: real^3) = 0 \<longleftrightarrow> x1 = 0 \<and> x2 = 0 \<and> x3 = 0"
  by (simp add: vec_eq_iff vector_def forall_3)

lemma vector3_eq:
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows "(vector [x1, x2, x3] :: real^3) = vector [y1, y2, y3] \<longleftrightarrow> x1 = y1 \<and> x2 = y2 \<and> x3 = y3"
  by (simp add: vec_eq_iff vector_def forall_3)

lemma vector3_neq:
  shows "((vector [x1, x2, x3]::real^3) \<noteq> vector [y1, y2, y3]) =
         (x1 \<noteq> y1 \<or> x2 \<noteq> y2 \<or> x3 \<noteq> y3)"
  by (simp add: vec_eq_iff forall_3)

lemma vector3_dot:
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows "(vector [x1, x2, x3] :: real^3) \<bullet> vector [y1, y2, y3] = 
         x1*y1 + x2*y2 + x3*y3"
  by (simp add: inner_vec_def sum_3 vector_def)

subsection\<open>Computation of faces\<close>

subsubsection\<open>2-faces\<close>

lemma compute_faces_2:
  fixes F S :: "(real^3) set"
  assumes "finite S"
  shows "(F face_of (convex hull S) \<and> aff_dim F = 2) =
         (\<exists>x\<in>S. \<exists>y\<in>S. \<exists>z\<in>S.
          let a = (z - x) \<times> (y - x) in
          a \<noteq> 0 \<and>
          (let b = a \<bullet> x in
           ((\<forall>w\<in>S. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>S. a \<bullet> w \<ge> b)) \<and>
           F = convex hull (S \<inter> {x. a \<bullet> x = b})))"
  (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then have *: "F face_of (convex hull S)" "aff_dim F = 2" by blast+
  then obtain T where T_facts: "T \<subseteq> S" "F = convex hull T"
    by (meson assms face_of_convex_hull_subset finite_imp_compact)
  then obtain U where U_facts: "U \<subseteq> T" "\<not> affine_dependent U" "affine hull T = affine hull U"
    using affine_basis_exists[of T] by blast
  then have "aff_dim U = 2"
    by (metis "*"(2) T_facts(2) aff_dim_affine_hull aff_dim_convex_hull)
  then have "card U = 3"
    using U_facts(2) aff_dim_affine_independent by fastforce
  then obtain x y z where
    U_eq: "U = {x, y, z}" and
    xyz_neq: "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    using card_3_iff[of U] by blast
  then have not_collinear: "\<not> collinear {x, y, z}"
    using U_facts(2) exposed_face_of_polyhedron
    by (simp add: collinear_3_eq_affine_dependent)
  have xyz_in_S: "x \<in> S" "y \<in> S" "z \<in> S"
    using U_eq U_facts(1) T_facts(1) by blast+

  let ?a = "(z - x) \<times> (y - x)"
  let ?b = "?a \<bullet> x"
  let ?H = "{w. ?a \<bullet> w = ?b}"
  have "?a \<noteq> 0"
    using not_collinear collinear_3 cross_eq_0[symmetric]
    by (metis (no_types, opaque_lifting) NO_MATCH_def insert_commute)
  have "?a \<bullet> y = ?b"
    by (metis (no_types, opaque_lifting) add.commute diff_0_right diff_add_cancel dot_cross_self(2) inner_commute
        inner_diff_left)
  have "?a \<bullet> z = ?b"
    by (metis Cross3.left_diff_distrib cross_refl cross_triple diff_left_imp_eq diff_self)

  have "F exposed_face_of (convex hull S)"
    using *(1) polyhedron_convex_hull[OF assms] exposed_face_of_polyhedron
    by blast
  then obtain a' b' where a'_b'_facts:
    "convex hull S \<subseteq> {w. a' \<bullet> w \<le> b'}"
    "convex hull T = convex hull S \<inter> {w. a' \<bullet> w = b'}"
    unfolding exposed_face_of_def T_facts(2) by blast
  let ?H' = "{w. a' \<bullet> w = b'}"

  have "{x, y, z} \<subseteq> ?H"
    using \<open>?a \<bullet> y = ?b\<close> \<open>?a \<bullet> z = ?b\<close> by simp
  then have "affine hull {x, y, z} \<subseteq> ?H"
    using affine_hyperplane hull_minimal by metis
  then have "affine hull T \<subseteq> ?H"
    using U_eq U_facts(3) by blast
  moreover have "affine hull T \<subseteq> ?H'"
    using a'_b'_facts(2)
    by (metis affine_hyperplane affine_imp_convex inf.cobounded2 subset_hull)
  ultimately have "affine hull T \<subseteq> ?H \<inter> ?H'"
    by blast
  moreover have "aff_dim (affine hull T) = 2"
    by (metis U_facts(3) \<open>aff_dim U = 2\<close> aff_dim_affine_hull)
  ultimately have "aff_dim (?H \<inter> ?H') \<ge> 2"
    using aff_dim_subset
    by metis

  show "?rhs"
  proof (cases "?H' = UNIV")
    case True
    have "S \<subseteq> affine hull T"
      using True a'_b'_facts(2) convex_hull_subset_affine_hull hull_subset
      by fast
    then have s_in_plane: "S \<subseteq> ?H"
      using \<open>affine hull T \<subseteq> ?H\<close> by blast
    then have one_side: "(\<forall>w\<in>S. ?a \<bullet> w \<le> ?b) \<or> (\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b)"
      by auto

    have "S \<inter> ?H = S"
      using s_in_plane by auto
    then have "F = convex hull (S \<inter> {w. ?a \<bullet> w = ?b})"
      using True a'_b'_facts(2) T_facts(2) by simp

    then show ?thesis
      using xyz_in_S \<open>?a \<noteq> 0\<close> one_side
      unfolding Let_def by blast
  next
    case False
    have planes_eq: "?H = ?H'"
    proof (rule ccontr)
      assume neq: "?H \<noteq> ?H'"
      have "aff_dim ?H = 2"
        using \<open>?a \<noteq> 0\<close> aff_dim_hyperplane[of ?a ?b] by simp
      then have "aff_dim (?H \<inter> ?H') < 2"
        using aff_dim_affine_Int_hyperplane[of "?H" a' b']
          neq False subset_hyperplanes[of ?a ?b a' b']
        by (simp add: affine_hyperplane)
      then show "False"
        using \<open>aff_dim (?H \<inter> ?H') \<ge> 2\<close>
        by simp
    qed

    then have F_eq: "F = convex hull (S \<inter> ?H)"
      by (smt (verit, ccfv_threshold) Int_commute T_facts(1,2) a'_b'_facts(2) convex_convex_hull
          hull_minimal hull_subset inf.orderE le_inf_iff subsetI)

    have "?H' \<subseteq> ?H"
      using planes_eq by auto
    moreover have "a' \<noteq> 0"
      by (metis \<open>?a \<noteq> 0\<close> hyperplane_eq_UNIV hyperplane_eq_empty planes_eq)
    ultimately obtain k where "?a = k *\<^sub>R a'" "?b = k * b'" "k \<noteq> 0"
      using \<open>?a \<noteq> 0\<close> hyperplane_subset_imp_scaled
      by blast
    then have "(\<forall>w\<in>S. ?a \<bullet> w \<le> ?b) \<or> (\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b)"
      using a'_b'_facts(1) hull_subset[of S]
      by (auto simp: mult_le_cancel_left)

    then show ?thesis
      using xyz_in_S \<open>?a \<noteq> 0\<close> F_eq unfolding Let_def
      by blast
  qed
next
  assume "?rhs"
  then obtain x y z where
    xyz_in_S: "x \<in> S" "y \<in> S" "z \<in> S" and
    a_neq_0: "(z - x) \<times> (y - x) \<noteq> 0" and
    one_side: "(\<forall>w\<in>S. (z - x) \<times> (y - x) \<bullet> w \<le> (z - x) \<times> (y - x) \<bullet> x) \<or>
               (\<forall>w\<in>S. (z - x) \<times> (y - x) \<bullet> w \<ge> (z - x) \<times> (y - x) \<bullet> x)" and
    F_eq: "F = convex hull (S \<inter> {w. (z - x) \<times> (y - x) \<bullet> w = (z - x) \<times> (y - x) \<bullet> x})"
    unfolding Let_def by blast
  let ?a = "(z - x) \<times> (y - x)"
  let ?b = "?a \<bullet> x"
  let ?H = "{w. ?a \<bullet> w = ?b}"
  have "convex hull (S \<inter> ?H) = convex hull S \<inter> ?H"
  proof
    show "convex hull (S \<inter> ?H) \<subseteq> convex hull S \<inter> ?H"
      using convex_hyperplane[of "?a" "?b"] hull_mono[of "S \<inter> ?H" S convex]
        subset_hull[of convex "?H" "S \<inter> ?H"]
      by blast
  next
    show "convex hull S \<inter> ?H \<subseteq> convex hull (S \<inter> ?H)"
    proof (cases "S \<subseteq> ?H")
      case True
      then show ?thesis by (simp add: Int_absorb2)
    next
      case False
      let ?S_on = "S \<inter> ?H"
      let ?S_off = "S - ?H"
      have "convex hull S \<inter> ?H = convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H"
        by (metis Int_Diff_Un hull_Un_left hull_Un_right)
      moreover have "convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H \<subseteq> convex hull (S \<inter> ?H)"
      proof
        fix w
        assume *: "w \<in> convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H"
        have convex: "convex (convex hull (?S_on))" "convex (convex hull (?S_off))"
          using convex_convex_hull by blast+
        have nonempty1: "convex hull ?S_on \<noteq> {}"
          using xyz_in_S(1) convex_hull_eq_empty by blast
        have nonempty2: "convex hull ?S_off \<noteq> {}"
          using False convex_hull_eq_empty by simp
        obtain u p q where
          w_facts: "w = (1 - u) *\<^sub>R p + u *\<^sub>R q" "?a \<bullet> w = ?b" and
          p_in: "p \<in> convex hull ?S_on" and
          q_in: "q \<in> convex hull ?S_off" and
          u_range: "0 \<le> u" "u \<le> 1"
          using * convex_hull_union_nonempty_explicit[OF convex(1) nonempty1 convex(2) nonempty2]
          by blast
        show "w \<in> convex hull (S \<inter> ?H)"
        proof (cases "u = 0")
          case True
          then show ?thesis
            using p_in w_facts(1) by simp
        next
          case u_nonzero: False
          have "p \<in> convex hull ?H"
            using p_in hull_mono[of "?S_on" "?H"] by blast
          then have "?a \<bullet> p = ?b"
            using convex_hyperplane hull_same
            by blast
          have "q \<notin> ?H"
          proof
            assume "q \<in> ?H"
            then have "?a \<bullet> q = ?b" by simp
            consider
              (leq) "\<forall>w\<in>S. ?a \<bullet> w \<le> ?b" |
              (geq) "\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b"
              using one_side by blast
            then show "False"
            proof cases
              case leq
              then have "?S_off \<subseteq> {w. ?a \<bullet> w < ?b}"
                by fastforce
              then have "convex hull ?S_off \<subseteq> {w. ?a \<bullet> w < ?b}"
                using convex_halfspace_lt hull_minimal by metis
              then show "False"
                using \<open>?a \<bullet> q = ?b\<close> \<open>q \<in> convex hull ?S_off\<close> by auto
            next
              case geq
              then have "?S_off \<subseteq> {w. ?a \<bullet> w > ?b}"
                by fastforce
              then have "convex hull ?S_off \<subseteq> {w. ?a \<bullet> w > ?b}"
                using convex_halfspace_gt hull_minimal by metis
              then show "False"
                using \<open>?a \<bullet> q = ?b\<close> \<open>q \<in> convex hull ?S_off\<close> by auto
            qed
          qed
          then have "?a \<bullet> q \<noteq> ?b" by simp
          moreover have "?a \<bullet> ((1 - u) *\<^sub>R p + u *\<^sub>R q) = (1 - u) * (?a \<bullet> p) + u * (?a \<bullet> q)"
            by (simp add: inner_add_right)
          ultimately show ?thesis
            using \<open>q \<in> convex hull ?S_off\<close>
            by (metis \<open>?a \<bullet> p = ?b\<close> real_scaleR_def segment_degen_0 u_nonzero w_facts)
        qed
      qed
      ultimately show ?thesis by argo
    qed
  qed
  then have F_as_inter: "F = convex hull S \<inter> ?H"
    using F_eq by simp
  consider (case_le) "\<forall>w\<in>S. ?a \<bullet> w \<le> ?b" | (case_ge) "\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b"
      using one_side by blast
  then have face_of: "F face_of (convex hull S)"
  proof cases
    case case_le
    then have subset: "S \<subseteq> {x. ?a \<bullet> x \<le> ?b}"
      by blast
    have "convex hull S \<subseteq> {x. ?a \<bullet> x \<le> ?b}"
      using convex_halfspace_le[of ?a ?b] hull_minimal[OF subset, of convex]
      by blast
    then have "\<And>w. w\<in>convex hull S \<Longrightarrow> ?a \<bullet> w \<le> ?b"
      by blast
    then have "convex hull S \<inter> ?H face_of convex hull S"
      using face_of_Int_supporting_hyperplane_le[OF convex_convex_hull[of S]]
      by blast
    then show ?thesis
      using F_as_inter by simp
  next
    case case_ge
    then have subset: "S \<subseteq> {x. ?a \<bullet> x \<ge> ?b}"
      by blast
    have "convex hull S \<subseteq> {x. ?a \<bullet> x \<ge> ?b}"
      using convex_halfspace_ge[of ?b ?a] hull_minimal[OF subset, of convex]
      by blast
    then have "\<And>w. w\<in>convex hull S \<Longrightarrow> ?a \<bullet> w \<ge> ?b"
      by blast
    then have "convex hull S \<inter> ?H face_of convex hull S"
      using face_of_Int_supporting_hyperplane_ge[OF convex_convex_hull[of S]]
      by blast
    then show ?thesis
      using F_as_inter by simp
  qed

  have "aff_dim ?H = 2"
    using aff_dim_hyperplane[OF a_neq_0, of ?b] by simp
  have "F \<subseteq> ?H"
    using F_as_inter by blast 
  then have upper: "aff_dim F \<le> 2"
    using aff_dim_subset[of F ?H] unfolding \<open>aff_dim ?H = 2\<close>
    by blast

  have "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    using a_neq_0 by force+
  then have "card {x, y, z} = 3"
    by auto
  have "\<not> collinear {x, y, z}"
    using collinear_3[of z x y] cross_eq_0 a_neq_0
    by (simp add: insert_commute)
  then have dim_xyz: "aff_dim {x, y, z} = 2"
    using collinear_3_eq_affine_dependent aff_dim_affine_independent
    unfolding \<open>card {x, y, z} = 3\<close>
    by fastforce
  have "?a \<bullet> y = ?b"
    by (metis (no_types, opaque_lifting) dot_cross_self(2) inner_commute inner_diff_left right_minus_eq)  
  then have y_in: "y \<in> S \<inter> ?H"
    using xyz_in_S(2) by blast
  have "?a \<bullet> z = ?b"
    by (metis (no_types, lifting) Cross3.right_diff_distrib add_0 add_uminus_conv_diff
        cross_refl cross_skew cross_triple diff_0_right)
  then have z_in: "z \<in> S \<inter> ?H"
    using xyz_in_S(3) by blast
  then have "{x, y, z} \<subseteq> convex hull (S \<inter> ?H)"
    using xyz_in_S(1) y_in hull_subset by fast
  then have xyz_in_F: "{x, y, z} \<subseteq> F"
    using F_eq by simp
  have lower: "2 \<le> aff_dim F"
    using aff_dim_subset[OF xyz_in_F] dim_xyz by simp

  show "?lhs"
    using face_of upper lower by simp
qed

lemma set_choice_decomposition_1:
  assumes sym_yz: "\<And>x y z. Q x y z \<Longrightarrow> Q x z y"
  and sym_xy: "\<And>x y z. Q x y z \<Longrightarrow> Q y x z"
  and degen: "\<And>x z. \<not> Q x x z"
  shows "(\<exists>x\<in>insert v S. \<exists>y\<in>insert v S. \<exists>z\<in>insert v S. Q x y z) \<longleftrightarrow>
         (\<exists>y\<in>S. \<exists>z\<in>S. Q v y z) \<or> (\<exists>x\<in>S. \<exists>y\<in>S. \<exists>z\<in>S. Q x y z)"
  by (metis degen insertCI insertE sym_xy sym_yz)

lemma compute_faces_2_step_1:
  fixes F S v and T :: "(real^3) set"
  defines "Q \<equiv> (\<lambda>x y z. let a = (z - x) \<times> (y - x) in
                   a \<noteq> 0 \<and>
                   (let b = a \<bullet> x in
                    ((\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)) \<and>
                    F = convex hull (T \<inter> {k. a \<bullet> k = b})))"
  shows "(\<exists>x\<in> (insert v S). \<exists>y \<in> (insert v S). \<exists>z \<in> (insert v S). Q x y z) =
         ((\<exists>y\<in>S. \<exists>z\<in>S. Q v y z) \<or> (\<exists>x\<in>S. \<exists>y\<in>S. \<exists>z\<in>S. Q x y z))"
  (is "?lhs = ?rhs")
proof -
  have Q_degen: "\<And>x z. \<not> Q x x z"
    unfolding Q_def Let_def
    by (simp add: cross3_simps)
  have Q_invariant: "Q x y z" if "Q x z y" for x y z
    using that cross_skew[of "y - x" "z - x"] unfolding Q_def Let_def
    by auto

  have sym_xy: "\<And>x y z. Q x y z \<Longrightarrow> Q y x z"
  proof -
    fix x y z
    assume "Q x y z"
    then obtain a b where
      a_def: "a = (z - x) \<times> (y - x)" and
      a_nonzero: "a \<noteq> 0" and
      b_def: "b = a \<bullet> x" and
      ineq: "(\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)" and
      plane: "F = convex hull (T \<inter> {w. a \<bullet> w = b})"
      unfolding Q_def Let_def
      by auto
    let ?a' = "(z - y) \<times> (x - y)"
    let ?b' = "?a' \<bullet> y"
    have "?a' = -a"
      by (smt (verit, del_insts) Cross3.right_diff_distrib a_def cross_refl
          cross_skew eq_iff_diff_eq_0)
    have a_orth: "a \<bullet> (y - x) = 0"
      unfolding a_def dot_cross_self(3)
      by blast
    then have "a \<bullet> y = b"
      unfolding b_def
      by (simp add: inner_diff_right)
    show "Q y x z"
      unfolding Q_def Let_def
      using \<open>a \<bullet> y = b\<close> \<open>?a' = -a\<close> a_nonzero ineq plane
      by auto
  qed

  show ?thesis
    using set_choice_decomposition_1[of Q v S] Q_invariant sym_xy Q_degen Q_def
    by blast
qed

lemma set_choice_decomposition_2:
  assumes sym: "\<And>x y. Q x y \<Longrightarrow> Q y x"
  and degen: "\<And>x. \<not> Q x x"
  shows "(\<exists>y\<in>insert u S. \<exists>z\<in>insert u S. Q y z) \<longleftrightarrow>
         (\<exists>z\<in>S. Q u z) \<or> (\<exists>y\<in>S. \<exists>z\<in>S. Q y z)"
  by (metis degen insertCI insertE sym)

lemma compute_faces_2_step_2:
  fixes F u v S and T :: "(real^3) set"
  defines "Q \<equiv> (\<lambda>y z. let a = (z - v) \<times> (y - v) in
                   a \<noteq> 0 \<and>
                   (let b = a \<bullet> v in
                    ((\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)) \<and>
                    F = convex hull (T \<inter> {k. a \<bullet> k = b})))"
  shows "(\<exists>y \<in> (insert u S). \<exists>z \<in> (insert u S). Q y z) =
         ((\<exists>z\<in>S. Q u z) \<or> (\<exists>y\<in>S. \<exists>z\<in>S. Q y z))"
  (is "?lhs = ?rhs")
proof -
  have Q_degen: "\<And>x. \<not> Q x x"
    unfolding Q_def Let_def
    by (simp add: cross3_simps)

  have Q_sym: "\<And>x y. Q x y \<Longrightarrow> Q y x"
  proof -
    fix x y
    assume "Q x y"
    then obtain a b where
      a_def: "a = (y - v) \<times> (x - v)" and
      a_nonzero: "a \<noteq> 0" and
      b_def: "b = a \<bullet> v" and
      ineq: "(\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)" and
      plane: "F = convex hull (T \<inter> {w. a \<bullet> w = b})"
      unfolding Q_def Let_def
      by auto
    let ?a' = "(x - v) \<times> (y - v)"
    let ?b' = "?a' \<bullet> v"
    have "?a' = -a"
      unfolding a_def using cross_skew
      by blast
    have "{w. ?a' \<bullet> w = ?b'} = {w. a \<bullet> w = b}"
      unfolding \<open>?a' = -a\<close> using b_def
      by auto
    then show "Q y x"
      unfolding Q_def Let_def
      using \<open>?a' = -a\<close> a_nonzero plane ineq
      by auto
  qed

  show ?thesis
    using set_choice_decomposition_2[of Q u S] Q_sym Q_degen Q_def
    by blast
qed

subsubsection\<open>1-faces\<close>

lemma compute_faces_1:
  fixes F n d and S :: "(real^3) set"
  assumes "\<And>x. x\<in>S \<Longrightarrow> n \<bullet> x = d"
      and "finite S"
      and "n \<noteq> 0"
    shows "(F face_of (convex hull S) \<and> aff_dim F = 1) =
           (\<exists>x\<in>S. \<exists>y\<in>S.
            let a = n \<times> (y - x) in
             a \<noteq> 0 \<and>
             (let b = a \<bullet> x in
              ((\<forall>w\<in>S. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>S. a \<bullet> w \<ge> b)) \<and>
              F = convex hull (S \<inter> {w. a \<bullet> w = b})))"
  (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then have *: "F face_of (convex hull S)" "aff_dim F = 1" by blast+
  then obtain T where T_facts: "T \<subseteq> S" "F = convex hull T"
    by (meson assms face_of_convex_hull_subset finite_imp_compact)
  then obtain U where U_facts: "U \<subseteq> T" "\<not> affine_dependent U" "affine hull T = affine hull U"
    using affine_basis_exists[of T] by blast
  then have "aff_dim U = 1"
    by (metis *(2) T_facts(2) aff_dim_affine_hull aff_dim_convex_hull)
  then have "card U = 2"
    using U_facts(2) aff_dim_affine_independent by fastforce
  then obtain x y where U_eq: "U = {x, y}" and xy_neq: "x \<noteq> y"
    using card_2_iff[of U] by blast
  have xy_in_S: "x \<in> S" "y \<in> S"
    using U_eq U_facts(1) T_facts(1) by blast+

  let ?a = "n \<times> (y - x)"
  let ?b = "?a \<bullet> x"
  let ?H = "{w. ?a \<bullet> w = ?b}"

  have "n \<bullet> (y - x) = 0"
    using assms(1)[OF xy_in_S(1)] assms(1)[OF xy_in_S(2)]
    by (simp add: inner_diff_right)
  then have "?a \<noteq> 0"
    using norm_and_cross_eq_0[of n "y - x"] assms(3) xy_neq
    by simp
  have "?a \<bullet> y = ?b"
    by (metis (no_types, opaque_lifting) add.commute diff_0_right diff_add_cancel dot_cross_self(2) inner_commute
        inner_diff_left)

  have "F exposed_face_of (convex hull S)"
    using *(1) polyhedron_convex_hull[OF assms(2)] exposed_face_of_polyhedron
    by blast
  then obtain a0 b0 where a0_b0_facts:
    "convex hull S \<subseteq> {w. a0 \<bullet> w \<le> b0}"
    "convex hull T = convex hull S \<inter> {w. a0 \<bullet> w = b0}"
    unfolding exposed_face_of_def T_facts(2) by blast
  define a' where "a' = a0 - ((a0 \<bullet> n) / (n \<bullet> n)) *\<^sub>R n"
  define b' where "b' = b0 - ((a0 \<bullet> n) / (n \<bullet> n)) * d"
  have "a' \<bullet> n = 0"
    unfolding a'_def
    by (simp add: inner_diff_left dot_square_norm power2_eq_square)
  have "S \<subseteq> {w. n \<bullet> w = d}"
    using assms(1) by blast
  have "\<And>w. w \<in> convex hull S \<Longrightarrow> (a' \<bullet> w = b') = (a0 \<bullet> w = b0)"
  proof -
    fix w assume "w \<in> convex hull S"
    then have "n \<bullet> w = d"
      using \<open>S \<subseteq> {w. n \<bullet> w = d}\<close>
      by (metis (mono_tags, lifting) assms(1) convex_hyperplane hull_induct)
    then show "(a' \<bullet> w = b') = (a0 \<bullet> w = b0)"
      unfolding a'_def b'_def by (simp add: inner_diff_left)
  qed
  moreover have "\<And>w. w \<in> convex hull S \<Longrightarrow> (a' \<bullet> w \<le> b') = (a0 \<bullet> w \<le> b0)"
  proof -
    fix w assume "w \<in> convex hull S"
    then have "n \<bullet> w = d"
      using \<open>S \<subseteq> {w. n \<bullet> w = d}\<close>
      by (metis (mono_tags, lifting) assms(1) convex_hyperplane hull_induct)
    then show "(a' \<bullet> w \<le> b') = (a0 \<bullet> w \<le> b0)"
      unfolding a'_def b'_def by (simp add: inner_diff_left)
  qed
  ultimately have a'_b'_facts:
    "convex hull S \<subseteq> {w. a' \<bullet> w \<le> b'}"
    "convex hull T = convex hull S \<inter> {w. a' \<bullet> w = b'}"
    using a0_b0_facts by auto
  let ?H' = "{w. a' \<bullet> w = b'}"

  have "aff_dim (affine hull T) = 1"
    by (metis U_facts(3) \<open>aff_dim U = 1\<close> aff_dim_affine_hull)
  have "{x, y} \<subseteq> ?H"
    using \<open>?a \<bullet> y = ?b\<close> by simp
  then have "affine hull {x, y} \<subseteq> ?H"
    using affine_hyperplane hull_minimal by metis
  then have "affine hull T \<subseteq> ?H"
    using U_eq U_facts(3) by blast
  moreover have "affine hull T \<subseteq> ?H'"
    using a'_b'_facts(2)
    by (metis affine_hyperplane affine_imp_convex inf.cobounded2 subset_hull)
  ultimately have "affine hull T \<subseteq> ?H \<inter> ?H'"
    by blast
  then have "aff_dim (?H \<inter> ?H') \<ge> 1"
    using aff_dim_subset \<open>aff_dim (affine hull T) = 1\<close>
    by metis

  show "?rhs"
  proof (cases "convex hull T = convex hull S")
    case True
    then have "affine hull T = affine hull S"
      using affine_hull_convex_hull by metis
    then have "S \<subseteq> affine hull T"
      using T_facts(1)
      by (simp add: hull_subset)
    then have "S \<subseteq> ?H"
      using \<open>affine hull T \<subseteq> ?H\<close> by blast
    then show ?thesis
      using xy_in_S \<open>?a \<noteq> 0\<close> True T_facts(2) unfolding Let_def
      by (metis (mono_tags, lifting) Int_Collect dual_order.refl inf.orderE)

  next
    case False
    have "affine hull T \<subseteq> ?H'"
      using a'_b'_facts(2) T_facts(2)
      by (metis affine_hyperplane affine_imp_convex inf.cobounded2 subset_hull)
    
    have "affine hull T \<subseteq> ?H \<inter> ?H'"
      using \<open>affine hull T \<subseteq> ?H\<close> \<open>affine hull T \<subseteq> ?H'\<close> by blast

    have "aff_dim ?H = 2"
      using \<open>?a \<noteq> 0\<close> aff_dim_hyperplane by simp
    have "a' \<noteq> 0"
      using *(2) False Int_commute T_facts(2) a'_b'_facts(2)
      by auto
    then have "aff_dim ?H' = 2"
      using aff_dim_hyperplane by simp

    have "?H \<subseteq> ?H'"
    proof (rule ccontr)
      assume "\<not>(?H \<subseteq> ?H')"
      then have "aff_dim (?H \<inter> ?H') = 1"
        using aff_dim_affine_Int_hyperplane[of ?H a' b']
            \<open>aff_dim ?H = 2\<close> \<open>aff_dim ?H' = 2\<close> \<open>aff_dim (?H \<inter> ?H') \<ge> 1\<close>
        by (metis (no_types, lifting) ext affine_hyperplane diff_add_cancel diff_minus_eq_add
            diff_numeral_special(11) not_numeral_le_neg_one numeral_eq_one_iff)
      have "x + n \<in> ?H"
        by (simp add: dot_cross_self(4) inner_right_distrib)
      have "x \<in> ?H'"
        using U_eq U_facts(1) a'_b'_facts(2) hull_inc by fastforce
      have "n \<bullet> (x + n) \<noteq> d"
        by (simp add: assms(1,3) inner_right_distrib xy_in_S(1))
      have "affine hull S \<subseteq> {w. n \<bullet> w = d}"
        by (simp add: \<open>S \<subseteq> {w. n \<bullet> w = d}\<close> affine_hyperplane subset_hull)
      then have "convex hull T \<subseteq> {w. n \<bullet> w = d}"
        using a'_b'_facts(2) convex_hull_subset_affine_hull by auto
      have "x + n \<in> ?H'"
        using \<open>a' \<bullet> n = 0\<close>
        by (metis \<open>x \<in> ?H'\<close> add.commute add_0 inner_right_distrib mem_Collect_eq)
      have "?H \<inter> ?H' \<subseteq> {w. n \<bullet> w = d}"
        by (metis (mono_tags, lifting) \<open>aff_dim (affine hull T) = 1\<close> \<open>aff_dim (?H \<inter> ?H') = 1\<close>
            \<open>affine hull T \<subseteq> ?H \<inter> ?H'\<close> \<open>convex hull T \<subseteq> {w. n \<bullet> w = d}\<close> aff_dim_eq_full_gen
            affine_hull_convex_hull affine_hyperplane subset_hull)
      then show "False"
        using \<open>x + n \<in> ?H\<close> \<open>x + n \<in> ?H'\<close> \<open>n \<bullet> (x + n) \<noteq> d\<close>
        by blast
    qed
    then have "?H = ?H'"
      using subset_hyperplanes
      by (metis \<open>a' \<noteq> 0\<close> \<open>{x, y} \<subseteq> ?H\<close> empty_iff hyperplane_eq_UNIV insert_subset)

    then have "F = convex hull (S \<inter> ?H)"
      by (smt (verit, ccfv_threshold) Int_commute T_facts(1,2) a'_b'_facts(2) convex_convex_hull
          hull_minimal hull_subset inf.orderE le_inf_iff subsetI)

    moreover have "(\<forall>w\<in>S. ?a \<bullet> w \<le> ?b) \<or> (\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b)"
    proof -
      have "?H' \<subseteq> ?H"
        using \<open>?H = ?H'\<close> by auto
      then obtain k where k_facts: "?a = k *\<^sub>R a'" "?b = k * b'" "k \<noteq> 0"
        using \<open>?a \<noteq> 0\<close> \<open>a' \<noteq> 0\<close> hyperplane_subset_imp_scaled by blast
      show ?thesis
      proof (cases "k > 0")
        case True
        then have "\<And>w. ?a \<bullet> w \<le> ?b \<longleftrightarrow> a' \<bullet> w \<le> b'"
          using k_facts by (auto simp: mult_le_cancel_left)
        then show ?thesis
          using a'_b'_facts(1) hull_subset[of S] by auto
      next
        case False
        then have "k < 0"
          using k_facts by simp
        then have "\<And>w. ?a \<bullet> w \<ge> ?b \<longleftrightarrow> a' \<bullet> w \<le> b'"
          using k_facts by (auto simp: mult_le_cancel_left)
        then show ?thesis
          using a'_b'_facts(1) hull_subset[of S] by auto
      qed
    qed
    
    ultimately show ?thesis
      using xy_in_S \<open>?a \<noteq> 0\<close> unfolding Let_def
      by blast
  qed
next
  assume "?rhs"
  then obtain x y where
    xy_in_S: "x \<in> S" "y \<in> S" and
    a_neq_0: "n \<times> (y - x) \<noteq> 0" and
    one_side: "(\<forall>w\<in>S. n \<times> (y - x) \<bullet> w \<le> n \<times> (y - x) \<bullet> x) \<or>
               (\<forall>w\<in>S. n \<times> (y - x) \<bullet> w \<ge> n \<times> (y - x) \<bullet> x)" and
    F_eq: "F = convex hull (S \<inter> {w. n \<times> (y - x) \<bullet> w = n \<times> (y - x) \<bullet> x})"
    unfolding Let_def by blast
  let ?a = "n \<times> (y - x)"
  let ?b = "?a \<bullet> x"
  let ?H = "{w. ?a \<bullet> w = ?b}"
  have "convex hull (S \<inter> ?H) = convex hull S \<inter> ?H"
  proof
    show "convex hull (S \<inter> ?H) \<subseteq> convex hull S \<inter> ?H"
      using convex_hyperplane[of "?a" "?b"] hull_mono[of "S \<inter> ?H" S convex]
        subset_hull[of convex "?H" "S \<inter> ?H"]
      by blast
  next
    show "convex hull S \<inter> ?H \<subseteq> convex hull (S \<inter> ?H)"
    proof (cases "S \<subseteq> ?H")
      case True
      then show ?thesis by (simp add: Int_absorb2)
    next
      case False
      let ?S_on = "S \<inter> ?H"
      let ?S_off = "S - ?H"
      have "convex hull S \<inter> ?H = convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H"
        by (metis Int_Diff_Un hull_Un_left hull_Un_right)
      moreover have "convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H \<subseteq> convex hull (S \<inter> ?H)"
      proof
        fix w
        assume *: "w \<in> convex hull (convex hull (?S_on) \<union> convex hull (?S_off)) \<inter> ?H"
        have convex: "convex (convex hull (?S_on))" "convex (convex hull (?S_off))"
          using convex_convex_hull by blast+
        have nonempty1: "convex hull ?S_on \<noteq> {}"
          using xy_in_S(1) convex_hull_eq_empty by blast
        have nonempty2: "convex hull ?S_off \<noteq> {}"
          using False convex_hull_eq_empty by simp
        obtain u p q where
          w_facts: "w = (1 - u) *\<^sub>R p + u *\<^sub>R q" "?a \<bullet> w = ?b" and
          p_in: "p \<in> convex hull ?S_on" and
          q_in: "q \<in> convex hull ?S_off" and
          u_range: "0 \<le> u" "u \<le> 1"
          using * convex_hull_union_nonempty_explicit[OF convex(1) nonempty1 convex(2) nonempty2]
          by blast
        show "w \<in> convex hull (S \<inter> ?H)"
        proof (cases "u = 0")
          case True
          then show ?thesis
            using p_in w_facts(1) by simp
        next
          case u_nonzero: False
          have "p \<in> convex hull ?H"
            using p_in hull_mono[of "?S_on" "?H"] by blast
          then have "?a \<bullet> p = ?b"
            using convex_hyperplane hull_same
            by blast
          have "q \<in> convex hull ?S_off"
            using q_in by simp

          have "q \<notin> ?H"
          proof
            assume "q \<in> ?H"
            then have "?a \<bullet> q = ?b" by simp
            consider
              (leq) "\<forall>w\<in>S. ?a \<bullet> w \<le> ?b" |
              (geq) "\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b"
              using one_side by blast
            then show "False"
            proof cases
              case leq
              then have "?S_off \<subseteq> {w. ?a \<bullet> w < ?b}"
                by fastforce
              then have "convex hull ?S_off \<subseteq> {w. ?a \<bullet> w < ?b}"
                using convex_halfspace_lt hull_minimal by metis
              then show "False"
                using \<open>?a \<bullet> q = ?b\<close> \<open>q \<in> convex hull ?S_off\<close> by auto
            next
              case geq
              then have "?S_off \<subseteq> {w. ?a \<bullet> w > ?b}"
                by fastforce
              then have "convex hull ?S_off \<subseteq> {w. ?a \<bullet> w > ?b}"
                using convex_halfspace_gt hull_minimal by metis
              then show "False"
                using \<open>?a \<bullet> q = ?b\<close> \<open>q \<in> convex hull ?S_off\<close> by auto
            qed
          qed
          then have q_not_in_H: "?a \<bullet> q \<noteq> ?b" by simp

          have "?a \<bullet> ((1 - u) *\<^sub>R p + u *\<^sub>R q) = (1 - u) * (?a \<bullet> p) + u * (?a \<bullet> q)"
            by (simp add: inner_add_right)
          then show ?thesis
            using q_not_in_H \<open>q \<in> convex hull ?S_off\<close>
            by (metis \<open>?a \<bullet> p = ?b\<close> real_scaleR_def segment_degen_0 u_nonzero w_facts)
        qed
      qed
      ultimately show ?thesis by argo
    qed
  qed
  then have F_as_inter: "F = convex hull S \<inter> ?H"
    using F_eq by simp
  consider (case_le) "\<forall>w\<in>S. ?a \<bullet> w \<le> ?b" | (case_ge) "\<forall>w\<in>S. ?a \<bullet> w \<ge> ?b"
      using one_side by blast
  then have face_of: "F face_of (convex hull S)"
  proof cases
    case case_le
    then have subset: "S \<subseteq> {x. ?a \<bullet> x \<le> ?b}"
      by blast
    have "convex hull S \<subseteq> {x. ?a \<bullet> x \<le> ?b}"
      using convex_halfspace_le[of ?a ?b] hull_minimal[OF subset, of convex]
      by blast
    then have "\<And>w. w\<in>convex hull S \<Longrightarrow> ?a \<bullet> w \<le> ?b"
      by blast
    then have "convex hull S \<inter> ?H face_of convex hull S"
      using face_of_Int_supporting_hyperplane_le[OF convex_convex_hull[of S]]
      by blast
    then show ?thesis
      using F_as_inter by simp
  next
    case case_ge
    then have subset: "S \<subseteq> {x. ?a \<bullet> x \<ge> ?b}"
      by blast
    have "convex hull S \<subseteq> {x. ?a \<bullet> x \<ge> ?b}"
      using convex_halfspace_ge[of ?b ?a] hull_minimal[OF subset, of convex]
      by blast
    then have "\<And>w. w\<in>convex hull S \<Longrightarrow> ?a \<bullet> w \<ge> ?b"
      by blast
    then have "convex hull S \<inter> ?H face_of convex hull S"
      using face_of_Int_supporting_hyperplane_ge[OF convex_convex_hull[of S]]
      by blast
    then show ?thesis
      using F_as_inter by simp
  qed

  have "S \<subseteq> {x. n \<bullet> x = d}"
    using assms(1) by blast
  have "aff_dim ?H = 2"
    using aff_dim_hyperplane[OF a_neq_0, of ?b] by simp
  have "\<not>(?H \<subseteq> {v. n \<bullet> v = d})"
  proof -
    have "\<exists>v. n \<bullet> v \<noteq> d \<and> n \<times> (y - x) \<bullet> v = x \<bullet> n \<times> (y - x)"
      by (metis (no_types) assms(3) diff_0_right diff_add_cancel dot_cross_self(1) inner_commute
          inner_diff_left inner_eq_zero_iff minus_diff_eq)
    then show ?thesis
      by (smt (z3) Collect_mono_iff inner_commute)
  qed
  then have "aff_dim (?H \<inter> {x. n \<bullet> x = d}) \<le> 1"
    using aff_dim_affine_Int_hyperplane[of ?H n d] unfolding \<open>aff_dim ?H = 2\<close>
    by (simp add: affine_hyperplane)
  moreover have "F \<subseteq> (?H \<inter> {x. n \<bullet> x = d})"
    using F_as_inter assms(1) \<open>S \<subseteq> {x. n \<bullet> x = d}\<close>
      convex_hyperplane[of n d] subset_hull[of convex "{x. n \<bullet> x = d}" S]
    by blast
  ultimately have upper: "aff_dim F \<le> 1"
    using aff_dim_subset[of F "?H \<inter> {x. n \<bullet> x = d}"] unfolding \<open>aff_dim ?H = 2\<close>
    by linarith
  have "x \<noteq> y"
    using a_neq_0 by auto
  moreover have "?a \<bullet> y = ?b"
    by (metis (no_types, opaque_lifting) dot_cross_self(2) inner_commute inner_diff_left right_minus_eq)
  moreover have "{x, y} \<subseteq> F"
    using xy_in_S
    by (simp add: F_as_inter calculation(2) hull_inc)
  moreover have "aff_dim {x, y} = 1"
    by (simp add: calculation(1))
  ultimately have lower: "aff_dim F \<ge> 1"
    using aff_dim_subset by metis

  show "?lhs"
    using face_of upper lower by simp
qed

lemma compute_faces_1_step:
  fixes F n u S and T :: "(real^3) set"
  defines "Q \<equiv> (\<lambda>x y. let a = n \<times> (y - x) in
                   a \<noteq> 0 \<and>
                   (let b = a \<bullet> x in
                    ((\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)) \<and>
                    F = convex hull (T \<inter> {k. a \<bullet> k = b})))"
  shows "(\<exists>y \<in> (insert u S). \<exists>z \<in> (insert u S). Q y z) =
         ((\<exists>z\<in>S. Q u z) \<or> (\<exists>y\<in>S. \<exists>z\<in>S. Q y z))"
  (is "?lhs = ?rhs")
proof -
  have Q_degen: "\<And>x. \<not> Q x x"
    unfolding Q_def Let_def
    by (simp add: cross3_simps)

  have Q_sym: "\<And>x y. Q x y \<Longrightarrow> Q y x"
  proof -
    fix x y
    assume "Q x y"
    then obtain a b where
      a_def: "a = n \<times> (y - x)" and
      a_nonzero: "a \<noteq> 0" and
      b_def: "b = a \<bullet> x" and
      ineq: "(\<forall>w\<in>T. a \<bullet> w \<le> b) \<or> (\<forall>w\<in>T. a \<bullet> w \<ge> b)" and
      plane: "F = convex hull (T \<inter> {w. a \<bullet> w = b})"
      unfolding Q_def Let_def
      by auto
    let ?a' = "n \<times> (x - y)"
    let ?b' = "?a' \<bullet> y"
    have "?a' = -a"
      unfolding a_def Cross3.right_diff_distrib
      by auto
    have "a \<bullet> y - a \<bullet> x = 0"
      by (metis a_def dot_cross_self(3) inner_diff_right)
    then have "{w. ?a' \<bullet> w = ?b'} = {w. a \<bullet> w = b}"
      unfolding \<open>?a' = -a\<close> b_def
      by auto
    then show "Q y x"
      unfolding Q_def Let_def
      using \<open>?a' = -a\<close> a_nonzero plane ineq
      by auto
  qed

  show ?thesis
    using set_choice_decomposition_2[of Q u S] Q_sym Q_degen Q_def
    by blast
qed

method facet_edges uses plane n_nz defs =
  (simp only: compute_faces_1[OF plane _ n_nz] finite_insert finite.emptyI,
   simp only: compute_faces_1_step bex_empty simp_thms(31),
   simp only: empty_iff ball_insert bex_empty bex_simps(5) ball_simps(5) simp_thms(21,31),
   simp add: defs vector3_sub vector3_cross vector3_dot vector3_eq_0 Let_def
             rat5_mul rat5_add rat5_sub rat5_eq rat5_eq_0 rat5_le)

subsection\<open>Full-dimensionality\<close>

lemma polytope_3D:
  fixes S :: "(real^3) set"
  assumes "(z - x) \<times> (y - x) \<noteq> 0"
      and "\<exists>w\<in>S. ((z - x) \<times> (y - x)) \<bullet> w \<noteq> ((z - x) \<times> (y - x)) \<bullet> x"
  shows "aff_dim (convex hull (insert x (insert y (insert z S)))) = 3"
  (is "aff_dim ?hull = 3")
proof -
  have "aff_dim ?hull \<le> int (DIM(real^3))"
    by (rule aff_dim_le_DIM)
  then have upper: "aff_dim ?hull \<le> 3"
    by auto
  let ?a = "(z - x) \<times> (y - x)"
  obtain w where w_facts: "w \<in> S" "?a \<bullet> w \<noteq> ?a \<bullet> x"
    using assms(2) by blast
  have "{w, x, y, z} \<subseteq> ?hull"
    using hull_subset w_facts(1) by fastforce
  have "aff_dim {w, x, y, z} \<ge> 3"
  proof (cases "w \<in> affine hull {x, y, z}")
    case True
    have "?a \<bullet> y = ?a \<bullet> x" "?a \<bullet> z = ?a \<bullet> x"
      by (metis (no_types, lifting) Cross3.left_diff_distrib cross_refl cross_skew cross_triple
          diff_0 diff_0_right)+
    then have "{x,y,z} \<subseteq> {v. ?a \<bullet> v = ?a \<bullet> x}"
      by blast
    then have "w \<in> {v. ?a \<bullet> v = ?a \<bullet> x}"
      using True affine_hyperplane[of "?a" "?a \<bullet> x"]
        subset_hull[of affine "{v. ?a \<bullet> v = ?a \<bullet> x}" "{x, y, z}"]
      by blast
    then show ?thesis
      using w_facts(2) by blast
  next
    case False
    have "\<not> collinear {x, y, z}"
      by (metis (no_types, opaque_lifting) assms(1) NO_MATCH_def collinear_3 cross_eq_0
          insert_commute)
    then show ?thesis 
      using False aff_dim_insert
      by (smt (verit, ccfv_threshold) collinear_aff_dim)
  qed
  then have "aff_dim ?hull \<ge> 3"
    by (meson \<open>{w, x, y, z} \<subseteq> ?hull\<close> aff_dim_subset order_trans)
  then show ?thesis
    using upper by simp
qed

subsection\<open>Relations between faces of different dimensions\<close>

text\<open>These lemmas are used when formalizing the number of
     edges per face and number of edges per vertex.\<close>

corollary edge_belongs_to_face:
  assumes "e face_of p"
      and "aff_dim e = 1"
      and "aff_dim p = 3"
      and "polyhedron p"
  obtains f where "f face_of p" "aff_dim f = 2" "e face_of f"
  using assms(2,3) ridge_belongs_to_facet[OF assms(1) _ _ assms(4)]
  by auto

corollary vertex_belongs_to_edge:
  assumes "v face_of p"
      and "aff_dim v = 0"
      and "aff_dim p = 3"
      and "polyhedron p"
  obtains e where "e face_of p" "aff_dim e = 1" "v face_of e"
  using assms(2,3) peak_belongs_to_ridge[OF assms(1) _ _ assms(4)]
  by auto

lemma vertices_of_edge:
  assumes "e = convex hull {a, b}"
      and "v face_of e"
      and "aff_dim v = 0"
  shows "v = {a} \<or> v = {b}"
  by (metis assms aff_dim_eq_0 extreme_point_of_convex_hull_2 face_of_singleton)

lemma vertex_edge_set_eq:
  assumes "v face_of S"
  shows "card {e. e face_of S \<and> aff_dim e = 1 \<and> v \<subseteq> e} =
         card {e. e face_of S \<and> aff_dim e = 1 \<and> v face_of e}"
  by (meson assms face_of_face)

lemma face_edge_set_eq:
  assumes "f face_of S"
  shows "card {e. e face_of S \<and> aff_dim e = 1 \<and> e \<subseteq> f} =
         card {e. e face_of f \<and> aff_dim e = 1}"
  using face_of_face[OF assms(1)]
  by meson

lemma set_disj_union_distr:
  shows "{e. (P e \<or> Q e) \<and> R e} = {e. P e \<and> R e} \<union> {e. Q e \<and> R e}"
  by blast

lemma v_sing_face_of_e:
  shows "(e = a \<and> {x} face_of e) = (e = a \<and> x extreme_point_of a)"
  using face_of_singleton by blast

lemma card_3_iff2:
  shows "(card {x, y, z} = 3) = (x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
  by (simp add: card_insert_if)

lemma card_4_iff2:
  shows "(card {w, x, y, z} = 4) = (w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and> x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
  by (simp add: card_insert_if)

lemma card_5_iff:
  shows "card {u,w,x,y,z} = 5 \<longleftrightarrow> (u \<noteq> w \<and> u \<noteq> x \<and> u \<noteq> y \<and> u \<noteq> z \<and> w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and> x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z)"
  by (simp add: card_insert_if)

method edges_per_vertex =
  (unfold set_disj_union_distr segment_convex_hull[symmetric] v_sing_face_of_e;
   simp_all add: extreme_point_of_segment vector3_eq rat5_eq;
   unfold card_3_iff2 card_4_iff2 card_5_iff closed_segment_eq;
   simp_all add: vector3_eq rat5_eq doubleton_eq_iff)

lemma set_cases:
  shows "{x. x = a} = {a}" "{x. x = a \<or> P x} = insert a {x. P x}"
  by auto

subsection\<open>Congruence\<close>

definition congruent :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool" (infixr \<open>(congruent)\<close> 50)
  where "S congruent T \<longleftrightarrow> (\<exists>c f. orthogonal_transformation f \<and> T = (\<lambda>x. c + f x) ` S)"

lemma congruent_refl:
  shows "S congruent S"
  unfolding congruent_def
  using orthogonal_transformation_id image_add_0
  by blast

lemma congruent_sym:
  shows "S congruent T \<longleftrightarrow> T congruent S"
proof -
  have forward: "\<And>S T. S congruent T \<Longrightarrow> T congruent S"
  proof -
    fix S T :: "'b set"
    assume "S congruent T"
    then obtain c f where orthog: "orthogonal_transformation f" and T: "T = (\<lambda>x. c + f x) ` S"
      unfolding congruent_def by blast
    then have orthog_inv: "orthogonal_transformation (inv f)"
      using orthogonal_transformation_inv by blast
    have "bounded_linear (inv f)"
      using orthogonal_transformation_linear[OF orthog_inv]
      by (simp add: linear_conv_bounded_linear)

    have "(\<lambda>y. - inv f c + inv f y) ` T = (\<lambda>x. -inv f c + inv f (c + f x)) ` S"
      using T by blast
    also have "... = (\<lambda>x. -inv f c + inv f c + inv f (f x)) ` S"
      using \<open>bounded_linear (inv f)\<close>
      by (simp add: linear_simps)
    also have "... = (\<lambda>x. inv f (f x)) ` S"
      by simp
    finally have "S = (\<lambda>y. - inv f c + inv f y) ` T"
      by (simp add: orthog bijection.intro bijection.inv_left orthogonal_transformation_bij)
    then show "T congruent S"
      unfolding congruent_def using orthog_inv
      by blast
  qed
  then show ?thesis
    by blast
qed

lemma congruent_trans:
  assumes "R congruent S"
  assumes "S congruent T"
  shows "R congruent T"
proof -
  obtain f c where orthog_f: "orthogonal_transformation f" and S: "S = (\<lambda>x. c + f x) ` R"
    using assms(1) unfolding congruent_def by blast
  obtain g d where orthog_g: "orthogonal_transformation g" and T: "T = (\<lambda>x. d + g x) ` S"
    using assms(2) unfolding congruent_def by blast
  then have "T = (\<lambda>x. d + g (c + f x)) ` R"
    unfolding S by blast
  then have "T = (\<lambda>x. d + g c + g (f x)) ` R"
    using orthogonal_transformation_linear[OF orthog_g] linear_conv_bounded_linear[of g]
      linear_simps(1)
    by fastforce
  moreover have "orthogonal_transformation (g o f)"
    using orthog_f orthog_g orthogonal_transformation_compose
    by blast
  ultimately show ?thesis
    unfolding congruent_def
    by fastforce
qed

lemma congruent_set:
  assumes "\<forall>t\<in>(insert s S). s congruent t"
  assumes "x \<in> (insert s S)"
  assumes "y \<in> (insert s S)"
  shows "x congruent y"
  using assms congruent_sym congruent_trans
  by metis

subsubsection\<open>Congruence of segments\<close>

lemma congruent_segments:
  fixes a b c d :: "real^'n"
  assumes "dist a b = dist c d"
  shows "(closed_segment a b) congruent (closed_segment c d)"
proof -
  have "norm (b - a) = norm (d - c)"
    using assms
    by (simp add: dist_norm norm_minus_commute)
  then obtain f where f_facts: "orthogonal_transformation f" "f (b - a) = d - c"
    using orthogonal_transformation_exists
    by blast
  have "linear f"
    using orthogonal_transformation_linear[OF f_facts(1)] .
  have "d = (c - f a) + f b"
    using linear_diff[OF \<open>linear f\<close>, of b a] unfolding f_facts(2)
    by (metis add.left_commute diff_add_cancel)
  moreover have "(\<lambda>x. (c - f a) + f x) = (\<lambda>x. (c - f a) + x) o f"
    by auto
  ultimately have "(\<lambda>x. (c - f a) + f x) ` closed_segment a b =
                    ((\<lambda>x. (c - f a) + x) \<circ> f) ` (convex hull {a, b})"
    unfolding segment_convex_hull[of a b]
    by argo
  also have "... = (\<lambda>x. (c - f a) + x) ` (convex hull (f ` {a, b}))"
    using image_comp convex_hull_linear_image[OF \<open>linear f\<close>]
    by metis
  also have "... = convex hull {(c - f a) + f a, (c - f a) + f b}"
    by (metis (no_types, opaque_lifting) convex_hull_translation
        image_empty image_insert)
  also have "... = convex hull {c, d}"
    unfolding \<open>d = (c - f a) + f b\<close> by auto
  finally show ?thesis
    unfolding congruent_def segment_convex_hull[of c d]
    using f_facts(1)
    by blast
qed

subsubsection\<open>Congruence of 2-faces\<close>

lemma congruent_simple:
  assumes "\<exists>A::real^3^3. orthogonal_matrix A \<and> (\<lambda>x. A *v x) ` S = T"
  shows "(convex hull S) congruent (convex hull T)"
proof -
  obtain A where A_facts: "orthogonal_matrix A" "(\<lambda>x. A *v x) ` S = T"
    using assms by blast
  then have "convex hull T  = (\<lambda>x. A *v x) ` (convex hull S)"
    using convex_hull_linear_image by blast
  moreover have "orthogonal_transformation (\<lambda>x. A *v x)"
    using A_facts(1) orthogonal_transformation_matrix
    by fastforce
  ultimately show ?thesis
    unfolding congruent_def
    by (metis image_add_0[of "convex hull T"]
        image_image[of "(+) 0" "(*v) A" "convex hull S"])
qed

lemma matrix_vector_mul_3:
  shows "(vector [vector[a11, a12, a13],
                  vector[a21, a22, a23],
                  vector[a31, a32, a33]]::real^3^3) *v vector [x1, x2, x3] =
         vector [a11 * x1 + a12 * x2 + a13 * x3,
                 a21 * x1 + a22 * x2 + a23 * x3,
                 a31 * x1 + a32 * x2 + a33 * x3]"
  by (simp add: vec_eq_iff matrix_vector_mult_def forall_3 sum_3)

lemma matrix_lemma:
  fixes A :: "real^3^3"
  shows "(A *v x1 = x2 \<and> A *v y1 = y2 \<and> A *v z1 = z2) =
         ((vector [x1, y1, z1]::real^3^3) *v (row 1 A) = vector[x2$1, y2$1, z2$1] \<and>
          (vector [x1, y1, z1]::real^3^3) *v (row 2 A) = vector[x2$2, y2$2, z2$2] \<and>
          (vector [x1, y1, z1]::real^3^3) *v (row 3 A) = vector[x2$3, y2$3, z2$3])"
  by (simp add: vec_eq_iff matrix_vector_mult_def row_def forall_3 sum_3 mult.commute conj_comms)

lemma matrix_by_cramer_lemma:
  fixes A :: "real^3^3"
  assumes "det (vector[x1, y1, z1]::real^3^3) \<noteq> 0"
  shows "(A *v x1 = x2 \<and> A *v y1 = y2 \<and> A *v z1 = z2) =
         (A = (\<chi> m k. det ((\<chi> i j.
                           if j = k
                           then (vector [x2$m, y2$m, z2$m]::real^3)$i
                           else (vector [x1, y1, z1]::real^3^3)$i$j)
                          ::real^3^3) /
                    det (vector [x1, y1, z1]::real^3^3)))"
  unfolding matrix_lemma cramer[OF assms(1)]
  by (simp add: vec_eq_iff row_def forall_3)

definition mk_matrix33 :: "(real^3) \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow> real^3^3"
  where "mk_matrix33 x1 y1 z1 x2 y2 z2 = (let d = det (vector[x1, y1, z1]::real^3^3) in vector [vector [
          (x2$1 * y1$2 * z1$3 +
           x1$2 * y1$3 * z2$1 +
           x1$3 * y2$1 * z1$2 -
           x2$1 * y1$3 * z1$2 -
           x1$2 * y2$1 * z1$3 -
           x1$3 * y1$2 * z2$1) / d,
          (x1$1 * y2$1 * z1$3 +
           x2$1 * y1$3 * z1$1 +
           x1$3 * y1$1 * z2$1 -
           x1$1 * y1$3 * z2$1 -
           x2$1 * y1$1 * z1$3 -
           x1$3 * y2$1 * z1$1) / d,
          (x1$1 * y1$2 * z2$1 +
           x1$2 * y2$1 * z1$1 +
           x2$1 * y1$1 * z1$2 -
           x1$1 * y2$1 * z1$2 -
           x1$2 * y1$1 * z2$1 -
           x2$1 * y1$2 * z1$1) / d], vector [
          (x2$2 * y1$2 * z1$3 +
           x1$2 * y1$3 * z2$2 +
           x1$3 * y2$2 * z1$2 -
           x2$2 * y1$3 * z1$2 -
           x1$2 * y2$2 * z1$3 -
           x1$3 * y1$2 * z2$2) / d,
          (x1$1 * y2$2 * z1$3 +
           x2$2 * y1$3 * z1$1 +
           x1$3 * y1$1 * z2$2 -
           x1$1 * y1$3 * z2$2 -
           x2$2 * y1$1 * z1$3 -
           x1$3 * y2$2 * z1$1) / d,
          (x1$1 * y1$2 * z2$2 +
           x1$2 * y2$2 * z1$1 +
           x2$2 * y1$1 * z1$2 -
           x1$1 * y2$2 * z1$2 -
           x1$2 * y1$1 * z2$2 -
           x2$2 * y1$2 * z1$1) / d], vector [
          (x2$3 * y1$2 * z1$3 +
           x1$2 * y1$3 * z2$3 +
           x1$3 * y2$3 * z1$2 -
           x2$3 * y1$3 * z1$2 -
           x1$2 * y2$3 * z1$3 -
           x1$3 * y1$2 * z2$3) / d,
          (x1$1 * y2$3 * z1$3 +
           x2$3 * y1$3 * z1$1 +
           x1$3 * y1$1 * z2$3 -
           x1$1 * y1$3 * z2$3 -
           x2$3 * y1$1 * z1$3 -
           x1$3 * y2$3 * z1$1) / d,
          (x1$1 * y1$2 * z2$3 +
           x1$2 * y2$3 * z1$1 +
           x2$3 * y1$1 * z1$2 -
           x1$1 * y2$3 * z1$2 -
           x1$2 * y1$1 * z2$3 -
           x2$3 * y1$2 * z1$1) / d]])"

lemma set3_neqI:
  assumes "a \<notin> {x, y, z} \<or> b \<notin> {x, y, z} \<or> c \<notin> {x, y, z}"
  shows "{a, b, c} \<noteq> {x, y, z}"
  using assms by auto

lemma set4_neqI:
  assumes "a \<notin> {w, x, y, z} \<or> b \<notin> {w, x, y, z} \<or> c \<notin> {w, x, y, z} \<or> d \<notin> {w, x, y, z}"
  shows "{a, b, c, d} \<noteq> {w, x, y, z}"
  using assms by auto

lemma orthogonal_matrix33:
  fixes Q :: "real^3^3"
  shows "(orthogonal_matrix Q) =
         (Q$1$1 * Q$1$1 + Q$2$1 * Q$2$1 + Q$3$1 * Q$3$1 = 1 \<and>
          Q$1$1 * Q$1$2 + Q$2$1 * Q$2$2 + Q$3$1 * Q$3$2 = 0 \<and>
          Q$1$1 * Q$1$3 + Q$2$1 * Q$2$3 + Q$3$1 * Q$3$3 = 0 \<and>
          Q$1$2 * Q$1$1 + Q$2$2 * Q$2$1 + Q$3$2 * Q$3$1 = 0 \<and>
          Q$1$2 * Q$1$2 + Q$2$2 * Q$2$2 + Q$3$2 * Q$3$2 = 1 \<and>
          Q$1$2 * Q$1$3 + Q$2$2 * Q$2$3 + Q$3$2 * Q$3$3 = 0 \<and>
          Q$1$3 * Q$1$1 + Q$2$3 * Q$2$1 + Q$3$3 * Q$3$1 = 0 \<and>
          Q$1$3 * Q$1$2 + Q$2$3 * Q$2$2 + Q$3$3 * Q$3$2 = 0 \<and>
          Q$1$3 * Q$1$3 + Q$2$3 * Q$2$3 + Q$3$3 * Q$3$3 = 1)"
  by (simp add: orthogonal_matrix transpose_def matrix_matrix_mult_def sum_3 mat_def
      vec_eq_iff forall_3)

lemma matrix_by_cramer:
  fixes A :: "real^3^3"
  assumes "A = mk_matrix33 x1 y1 z1 x2 y2 z2"
  assumes "det (vector [x1, y1, z1]::real^3^3) \<noteq> 0"
  shows "A *v x1 = x2" "A *v y1 = y2" "A *v z1 = z2"
  using assms(1) matrix_by_cramer_lemma[OF assms(2)]
  unfolding mk_matrix33_def Let_def
  by (auto simp add: det_3 vec_eq_iff forall_3)

(* Adding orthogonal condition makes it easier to `apply rule` the matrix_by_cramer 
   part when it's used in the Eisbach methods for the solids *)
lemma matrix_by_cramer_orthog:
  fixes x1 y1 z1 x2 y2 z2 :: "real^3"
  assumes "orthogonal_matrix (mk_matrix33 x1 y1 z1 x2 y2 z2)"
  assumes "det (vector [x1, y1, z1]::real^3^3) \<noteq> 0"
  shows "orthogonal_matrix (mk_matrix33 x1 y1 z1 x2 y2 z2) \<and>
         (*v) (mk_matrix33 x1 y1 z1 x2 y2 z2) ` {x1, y1, z1} = {x2, y2, z2}"
  using assms(1) matrix_by_cramer[OF _ assms(2)] by auto

text\<open>Lookup table mapping a face to three vertices on that face that are adjacent
     (vertices that define a pair of intersecting edges)\<close>

definition adjacency_table :: "((real, 3) vec set \<times> ((real, 3) vec \<times> (real, 3) vec \<times> (real, 3) vec)) list" where
  "adjacency_table = [
     ({vector[-1, -1, 1], vector[-1, 1, -1], vector[1, -1, -1]},  (vector [-1, -1, 1], vector [-1, 1, -1], vector [1, -1, -1])),
     ({vector[-1, -1, 1], vector[-1, 1, -1], vector[1, 1, 1]}, (vector[-1, -1, 1], vector[-1, 1, - 1], vector[1, 1, 1])),
     ({vector[-1, -1, 1], vector[1, - 1, - 1], vector[1, 1, 1]}, (vector[-1, -1, 1], vector[1, - 1, - 1], vector[1, 1, 1])),
     ({vector[-1, 1, -1], vector[1, - 1, - 1], vector[1, 1, 1]}, (vector[-1, 1, -1], vector[1, - 1, - 1], vector[1, 1, 1])),

     ({vector[-1, -1, -1], vector[-1, -1, 1], vector[-1, 1, -1], vector[-1, 1, 1]}, (vector[-1, -1, -1], vector[-1, -1, 1], vector[-1, 1, 1])),
     ({vector[-1, -1, -1], vector[-1, -1, 1], vector[1, -1, -1], vector[1, -1, 1]}, (vector[-1, -1, -1], vector[-1, -1, 1], vector[1, -1, 1])),
     ({vector[-1, -1, -1], vector[-1, 1, -1], vector[1, -1, -1], vector[1, 1, -1]}, (vector[-1, -1, -1], vector[-1, 1, -1], vector[1, 1, -1])),
     ({vector[-1, -1, 1], vector[-1, 1, 1], vector[1, -1, 1], vector[1, 1, 1]}, (vector[-1, -1, 1], vector[-1, 1, 1], vector[1, 1, 1])),
     ({vector[-1, 1, -1], vector[-1, 1, 1], vector[1, 1, -1], vector[1, 1, 1]}, (vector[-1, 1, -1], vector[-1, 1, 1], vector[1, 1, 1])),
     ({vector[1, -1, -1], vector[1, -1, 1], vector[1, 1, -1], vector[1, 1, 1]}, (vector[1, -1, -1], vector[1, -1, 1], vector[1, 1, 1])),

     ({vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, -1]}, (vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, -1])),
     ({vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, 1]}, (vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, 1])),
     ({vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, -1]}, (vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, -1])),
     ({vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]}, (vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, 1])),
     ({vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, -1]}, (vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, -1])),
     ({vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, 1]}, (vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, 1])),
     ({vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, -1]}, (vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, -1])),
     ({vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]}, (vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1])),

     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]}, (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])),
     ({vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]}, (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0])),

     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}, (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}, (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]}, (vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])),
     ({vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]}, (vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])),
     ({vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]}, (vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]))
   ]"

definition adjacent_points :: "(real, 3) vec set \<Rightarrow> (real, 3) vec \<times> (real, 3) vec \<times> (real, 3) vec" where
  "adjacent_points S = (
     case map_of adjacency_table S of
       Some res \<Rightarrow> res
     | None \<Rightarrow> undefined
   )"

lemma set43_neqI:
  assumes "a \<notin> {x, y, z} \<or> b \<notin> {x, y, z} \<or> c \<notin> {x, y, z} \<or> d \<notin> {x, y, z}"
  shows "{a, b, c, d} \<noteq> {x, y, z}"
        "{x, y, z} \<noteq> {a, b, c, d}"
  using assms by auto

lemma solids_vectors_to_rat5:
  shows "vector[1, 1, 1] = vector[rat5 (1) 0, rat5 (1) 0, rat5 (1) 0]"
        "vector[1, 1, -1] = vector[rat5 (1) 0, rat5 (1) 0, rat5 (-1) 0]"
        "vector[1, -1, 1] = vector[rat5 (1) 0, rat5 (-1) 0, rat5 (1) 0]"
        "vector[1, -1, -1] = vector[rat5 (1) 0, rat5 (-1) 0, rat5 (-1) 0]"
        "vector[-1, 1, 1] = vector[rat5 (-1) 0, rat5 (1) 0, rat5 (1) 0]"
        "vector[-1, 1, -1] = vector[rat5 (-1) 0, rat5 (1) 0, rat5 (-1) 0]"
        "vector[-1, -1, 1] = vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (1) 0]"
        "vector[-1, -1, -1] = vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0]"
        "vector[1, 0, 0] = vector[rat5 (1) 0, rat5 (0) 0, rat5 (0) 0]"
        "vector[-1, 0, 0] = vector[rat5 (-1) 0, rat5 (0) 0, rat5 (0) 0]"
        "vector[0, 0, 1] = vector[rat5 (0) 0, rat5 (0) 0, rat5 (1) 0]"
        "vector[0, 0, -1] = vector[rat5 (0) 0, rat5 (0) 0, rat5 (-1) 0]"
        "vector[0, 1, 0] = vector[rat5 (0) 0, rat5 (1) 0, rat5 (0) 0]"
        "vector[0, -1, 0] = vector[rat5 (0) 0, rat5 (-1) 0, rat5 (0) 0]"
  unfolding rat5_def
  by auto

lemma set53_neqI:
  assumes "a \<notin> {x, y, z} \<or> b \<notin> {x, y, z} \<or> c \<notin> {x, y, z} \<or> d \<notin> {x, y, z} \<or> e \<notin> {x, y, z}"
  shows "{a, b, c, d,e } \<noteq> {x, y, z}"
        "{x, y, z} \<noteq> {a, b, c, d, e}"
  using assms by auto

lemma set54_neqI:
  assumes "a \<notin> {w, x, y, z} \<or> b \<notin> {w, x, y, z} \<or> c \<notin> {w, x, y, z} \<or> d \<notin> {w, x, y, z} \<or> e \<notin> {w, x, y, z}"
  shows "{a, b, c, d,e } \<noteq> {w, x, y, z}"
        "{w, x, y, z} \<noteq> {a, b, c, d, e}"
  using assms by auto

lemma set5_neqI:
  assumes "a \<notin> {v, w, x, y, z} \<or> b \<notin> {v, w, x, y, z} \<or> c \<notin> {v, w, x, y, z} \<or> d \<notin> {v, w, x, y, z} \<or> e \<notin> {v, w, x, y, z}"
  shows "{a, b, c, d,e } \<noteq> {v, w, x, y, z}"
  using assms by auto

lemma set3_eq_iff:
  shows "({a, b, c} = {d, e, f}) =
         (a \<in> {d, e, f} \<and> b \<in> {d, e, f} \<and> c \<in> {d, e, f} \<and>
          d \<in> {a, b, c} \<and> e \<in> {a, b, c} \<and> f \<in> {a, b, c})"
  by auto

lemma set3_vector_neq:
  assumes "(a1 \<noteq> d1 \<and> a1 \<noteq> d2 \<and> a1 \<noteq> d3)"
  shows "{(vector [a1, b1, c1]::real^3), vector [a2, b2, c2], vector [a3, b3, c3]} \<noteq>
         {vector [d1, e1, f1], vector [d2, e2, f2], vector [d3, e3, f3]}"
  by (auto simp add: set3_neqI assms vector3_neq)

lemma adjacent_points:
  shows "adjacent_points {vector[-1, -1, 1], vector[- 1, 1, - 1], vector[1, - 1, - 1]} = (vector [-1, -1, 1], vector [-1, 1, -1], vector [1, -1, -1])"
        "adjacent_points {vector[-1, -1, 1], vector[-1, 1, -1], vector[1, 1, 1]} = (vector[-1, -1, 1], vector[-1, 1, - 1], vector[1, 1, 1])"
        "adjacent_points {vector[-1, -1, 1], vector[1, - 1, - 1], vector[1, 1, 1]} = (vector[-1, -1, 1], vector[1, - 1, - 1], vector[1, 1, 1])"
        "adjacent_points {vector[-1, 1, -1], vector[1, - 1, - 1], vector[1, 1, 1]} = (vector[-1, 1, -1], vector[1, - 1, - 1], vector[1, 1, 1])"

        "adjacent_points {vector[-1, -1, -1], vector[-1, -1, 1], vector[-1, 1, -1], vector[-1, 1, 1]} = (vector[-1, -1, -1], vector[-1, -1, 1], vector[-1, 1, 1])"
        "adjacent_points {vector[-1, -1, -1], vector[-1, -1, 1], vector[1, -1, -1], vector[1, -1, 1]} = (vector[-1, -1, -1], vector[-1, -1, 1], vector[1, -1, 1])"
        "adjacent_points {vector[-1, -1, -1], vector[-1, 1, -1], vector[1, -1, -1], vector[1, 1, -1]} = (vector[-1, -1, -1], vector[-1, 1, -1], vector[1, 1, -1])"
        "adjacent_points {vector[-1, -1, 1], vector[-1, 1, 1], vector[1, -1, 1], vector[1, 1, 1]} = (vector[-1, -1, 1], vector[-1, 1, 1], vector[1, 1, 1])"
        "adjacent_points {vector[-1, 1, -1], vector[-1, 1, 1], vector[1, 1, -1], vector[1, 1, 1]} = (vector[-1, 1, -1], vector[-1, 1, 1], vector[1, 1, 1])"
        "adjacent_points {vector[1, -1, -1], vector[1, -1, 1], vector[1, 1, -1], vector[1, 1, 1]} = (vector[1, -1, -1], vector[1, -1, 1], vector[1, 1, 1])"

        "adjacent_points {vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, -1]} = (vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, -1])"
        "adjacent_points {vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, 1]} = (vector[-1, 0, 0], vector[0, -1, 0], vector[0, 0, 1])"
        "adjacent_points {vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, -1]} = (vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, -1])"
        "adjacent_points {vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]} = (vector[-1, 0, 0], vector[0, 1, 0], vector[0, 0, 1])"
        "adjacent_points {vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, -1]} = (vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, -1])"
        "adjacent_points {vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, 1]} = (vector[1, 0, 0], vector[0, -1, 0], vector[0, 0, 1])"
        "adjacent_points {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, -1]} = (vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, -1])"
        "adjacent_points {vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1]} = (vector[1, 0, 0], vector[0, 1, 0], vector[0, 0, 1])"

        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0]} = (vector[rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (-1) 0, rat5 1 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (-1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0]} = (vector[rat5 (-1/2) (1/2), rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (1/2) (1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1/2) (1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 1 0], vector[rat5 1 0, rat5 1 0, rat5 1 0])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1/2) (1/2), rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 (1/2) (-1/2), rat5 (-1/2) (-1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (1/2) (-1/2)], vector[rat5 1 0, rat5 (-1) 0, rat5 (-1) 0], vector[rat5 1 0, rat5 1 0, rat5 (-1) 0])"

        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} = (vector[rat5 (-1/2) (-1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 (-1) 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} = (vector[rat5 (1/2) (1/2), rat5 0 0, rat5 1 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)]} = (vector[rat5 (-1) 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 1 0, rat5 (-1/2) (-1/2), rat5 0 0], vector[rat5 0 0, rat5 (-1) 0, rat5 (1/2) (1/2)])"
        "adjacent_points {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)]} = (vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (-1/2) (-1/2)])"
        "adjacent_points {vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)]} = (vector[rat5 (-1) 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 1 0, rat5 (1/2) (1/2), rat5 0 0], vector[rat5 0 0, rat5 1 0, rat5 (1/2) (1/2)])"
  apply (simp_all add: adjacent_points_def adjacency_table_def set3_neqI set4_neqI set43_neqI
      set53_neqI set54_neqI set5_neqI vector3_neq)[18]
  by (simp_all add: rat5_eq adjacent_points_def adjacency_table_def set3_neqI set4_neqI set43_neqI
      set53_neqI set54_neqI set5_neqI vector3_neq set3_vector_neq solids_vectors_to_rat5)

definition mk_matrix33_ap :: "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> real^3^3" where
  "mk_matrix33_ap f1 f2 = (let vs = adjacent_points f1; us = adjacent_points f2 in
                           mk_matrix33 (fst vs) (fst (snd vs)) (snd (snd vs))
                                       (fst us) (fst (snd us)) (snd (snd us)))"

method show_congruence =
  (((erule forw_subst)+)?;
   (match conclusion in "convex hull (s::(real^3) set) congruent convex hull (t::(real^3) set)" for s t \<Rightarrow>
      \<open>(rule congruent_simple), (rule exI[where x="mk_matrix33_ap s t"])\<close>);
   (simp only: mk_matrix33_ap_def Let_def fst_conv snd_conv adjacent_points);
   (rule matrix_by_cramer_orthog | simp add: matrix_by_cramer det_3 rat5_eq_0 rat5_add rat5_mul rat5_sub);
   (simp only: mk_matrix33_def vector_3 det_3 rat5_add rat5_mul rat5_sub rat5_eq);
   (simp add: matrix_vector_mul_3 orthogonal_matrix33 rat5_add rat5_mul rat5_sub rat5_div rat5_eq
    rat5_eq_0 rat5_eq_1 Let_def; fast))

subsection\<open>Equiangularity\<close>

text\<open>vangle is from Manuel Eberl's AFP entry on triangles
     (see https://www.isa-afp.org/thys/Triangle/Angles.html)\<close>

definition vangle :: "'a::real_inner \<Rightarrow> 'a \<Rightarrow> real" where
  "vangle x y = (if x = 0 \<or> y = 0 then pi / 2 else arccos (x \<bullet> y / (norm x * norm y)))"

lemma vangle_commute:
  shows "vangle x y = vangle y x"
  unfolding vangle_def inner_commute[of y x]
  by argo

lemma isometry_maintains_angles_forw:
  fixes c
  assumes "orthogonal_transformation h"
  defines "g \<equiv> (\<lambda>x. c + h x)"
  shows "((e1 face_of f1 \<and> aff_dim e1 = 1) \<and>
          (e2 face_of f1 \<and> aff_dim e2 = 1) \<and>
          e1 = convex hull {v, a} \<and> e2 = convex hull {v, b} \<and>
          vangle (a - v) (b - v) = t) \<Longrightarrow>
         ((g ` e1 face_of g ` f1 \<and> aff_dim (g ` e1) = 1) \<and>
          (g ` e2 face_of g ` f1 \<and> aff_dim (g ` e2) = 1) \<and>
          g ` e1 = convex hull {g v, g a} \<and> g ` e2 = convex hull {g v, g b} \<and>
          vangle (g a - g v) (g b - g v) = t)"
  (is "?lhs \<Longrightarrow> ?rhs")
proof -
  assume *: ?lhs
  then have "g ` e1 face_of g ` f1 \<and> aff_dim (g ` e1) = 1"
            "g ` e2 face_of g ` f1 \<and> aff_dim (g ` e2) = 1"
    using face_of_isometry_eq[OF assms(1)] aff_dim_isometry_eq[OF assms(1)] g_def
    by auto
  moreover have "g ` e1 = convex hull {g v, g a}"
                "g ` e2 = convex hull {g v, g b}"
    using * convex_hull_isometry[OF assms(1), of c] g_def
    by simp_all
  moreover have "vangle (g a - g v) (g b - g v) = t"
  proof -
    have "a - v \<noteq> 0" "b - v \<noteq> 0"
      using * by auto
    have "vangle (g a - g v) (g b - g v) =
               arccos ((g a - g v) \<bullet> (g b - g v) / (norm (g a - g v) * norm (g b - g v)))"
      unfolding vangle_def by simp
    also have "... = arccos ((h a - h v) \<bullet> (h b - h v) / (norm (h a - h v) * norm (h b - h v)))"
      unfolding g_def by simp
    also have "... = arccos (h (a - v) \<bullet> h (b - v) / (norm (h (a - v)) * norm (h (b - v))))"
      using orthogonal_transformation_linear[OF assms(1)]
      by (simp add: linear_diff)
    also have "... = arccos ((a - v) \<bullet> (b - v) / (norm (a - v) * norm (b - v)))"
      unfolding orthogonal_transformation_norm[OF assms(1)]
      by (metis (mono_tags, opaque_lifting) assms(1) orthogonal_transformation_def)
    finally show ?thesis
      using * vangle_def \<open>a - v \<noteq> 0\<close> \<open>b - v \<noteq> 0\<close>
      by metis
  qed
  ultimately show ?rhs
    by blast
qed

definition equiangular :: "'a::euclidean_space set \<Rightarrow> real \<Rightarrow> bool"
  where "equiangular f t \<longleftrightarrow>
         (\<forall>e1 e2 v. (e1 face_of f \<and> aff_dim e1 = 1) \<and> (e2 face_of f \<and> aff_dim e2 = 1) \<and>
                    e1 \<noteq> e2 \<and> v extreme_point_of e1 \<and> v extreme_point_of e2 \<longrightarrow>
                    (\<exists>a b. e1 = convex hull {v, a} \<and> e2 = convex hull {v, b} \<and>
                           vangle (a - v) (b - v) = t))"

lemma equiangular_congruent_forw:
  assumes "f1 congruent f2"
  assumes "equiangular f1 t"
  shows "equiangular f2 t"
proof -
  {
    fix e1' e2' v'
    assume *: "(e1' face_of f2 \<and> aff_dim e1' = 1) \<and>
               (e2' face_of f2 \<and> aff_dim e2' = 1) \<and>
               e1' \<noteq> e2' \<and> v' extreme_point_of e1' \<and> v' extreme_point_of e2'"
    obtain c h where orthog:"orthogonal_transformation h" and f2: "f2 = (\<lambda>x. c + h x) ` f1"
      using assms unfolding congruent_def by blast
    then have orthog_inv: "orthogonal_transformation (inv h)"
      using orthogonal_transformation_inv by blast
    have "bounded_linear (inv h)"
      using orthogonal_transformation_linear[OF orthog_inv]
      by (simp add: linear_conv_bounded_linear)
    have "(\<lambda>y. - inv h c + inv h y) ` f2 = (\<lambda>x. -inv h c + inv h (c + h x)) ` f1"
      using f2 by blast
    also have "... = (\<lambda>x. -inv h c + inv h c + inv h (h x)) ` f1"
      using \<open>bounded_linear (inv h)\<close>
      by (simp add: linear_simps)
    also have "... = (\<lambda>x. inv h (h x)) ` f1"
      by simp
    finally have f1: "f1 = (\<lambda>y. - inv h c + inv h y) ` f2"
      by (simp add: orthog bijection.intro bijection.inv_left orthogonal_transformation_bij)
  
    define g where "g = (\<lambda>x. c + h x)"
    define g_inv where "g_inv = (\<lambda>x. - inv h c + inv h x)"
    have g_inv_g: "g_inv (g y) = y" for y
      using g_def g_inv_def
      by (simp add: \<open>bounded_linear (inv h)\<close> linear_simps(1) orthog orthogonal_transformation_inj)
    then have g_g_inv: "g (g_inv x) = x" for x
      using g_def g_inv_def
      by (metis add_minus_cancel bijection.intro
          bijection.inv_right orthog orthogonal_transformation_bij)
  
    define e1 where "e1 = g_inv ` e1'"
    define e2 where "e2 = g_inv ` e2'"
    define v where "v = g_inv v'"
  
    have e1_e2: "e1 face_of f1 \<and> aff_dim e1 = 1" "e2 face_of f1 \<and> aff_dim e2 = 1"
      using * e1_def e2_def f1 face_of_isometry_eq[OF orthog_inv]
        aff_dim_isometry_eq[OF orthog_inv]
      unfolding g_def g_inv_def
      by presburger+
    moreover have "e1 \<noteq> e2"
      using e1_def e2_def * g_inv_g g_g_inv
      by (metis (no_types) image_f_inv_f surj_def surj_imp_inv_eq)
    moreover have "v extreme_point_of e1" "v extreme_point_of e2"
      unfolding e1_def e2_def v_def using * extreme_point_of_isometry_eq[OF orthog_inv] g_inv_def
      by blast+
    ultimately obtain a b where ab: "e1 = convex hull {v, a}" "e2 = convex hull {v, b}"
                     "vangle (a - v) (b - v) = t"
      using assms(2) unfolding equiangular_def
      by meson
  
    then have "g ` e1 = convex hull {g v, g a} \<and> g ` e2 = convex hull {g v, g b} \<and>
            vangle (g a - g v) (g b - g v) = t"
      using isometry_maintains_angles_forw[OF orthog, of e1 f1 e2 v] g_def e1_e2
      by presburger
    then have "\<exists>a b. e1' = convex hull {v', a} \<and> e2' = convex hull {v', b} \<and>
                     vangle (a - v') (b - v') = t"
      using * unfolding e1_def e2_def v_def
      by (metis (mono_tags, lifting) image_f_inv_f g_inv_g g_g_inv surj_def surj_imp_inv_eq)
  } then show ?thesis
    unfolding equiangular_def
    by blast
qed

lemma equiangular_congruent:
  assumes "f1 congruent f2"
  shows "equiangular f1 t \<longleftrightarrow> equiangular f2 t"
  using equiangular_congruent_forw assms congruent_sym
  by blast

end