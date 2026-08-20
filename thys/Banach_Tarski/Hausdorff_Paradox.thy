(*  Title:       Hausdorff_Paradox.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    The Hausdorff paradox.

    Statement: there is a countable subset \<open>D\<close> of the unit sphere
    \<open>S\<^sup>2\<close> such that the action of the free \<open>F\<^sub>2 \<le> SO(3)\<close>
    on \<open>S\<^sup>2 \<setminus> D\<close> is free, and consequently the
    paradoxical decomposition of \<open>F\<^sub>2\<close> transports to a
    paradoxical decomposition of \<open>S\<^sup>2 \<setminus> D\<close> under
    rotations.

    The "bad set" \<open>D\<close> consists of the fixed points (axes
    intersected with \<open>S\<^sup>2\<close>) of all non-trivial rotations
    \<open>sigma w\<close> for \<open>w \<in> F\<^sub>2 \<setminus> {[]}\<close>; each such
    rotation has at most two fixed points on \<open>S\<^sup>2\<close>, so
    \<open>D\<close> is at most countable.

    The paradoxical decomposition of F-2 is transported to
    \<open>S\<^sup>2 \<setminus> D\<close> using representatives of free-action orbits.
*)

theory Hausdorff_Paradox
  imports Free_Rotations_SO3
begin

section \<open>The bad set of fixed points\<close>

definition fixed_point_set :: "(real^3 \<Rightarrow> real^3) \<Rightarrow> (real^3) set" where
  "fixed_point_set f = {x \<in> sphere2. f x = x}"

definition bad_set_D :: "(real^3) set" where
  "bad_set_D = (\<Union>w \<in> carrier F2 - {[]}. fixed_point_set (sigma w))"

lemma carrier_F2_countable: "countable (carrier F2)"
proof (rule countable_subset)
  show "carrier F2 \<subseteq> (UNIV :: ((bool \<times> gen2) list) set)"
    by simp
  show "countable (UNIV :: ((bool \<times> gen2) list) set)"
  proof -
    have gen2_finite: "finite (UNIV :: gen2 set)"
      using Gen2_finite Gen2_UNIV by simp
    have alphabet_finite: "finite ((UNIV :: bool set) \<times> (UNIV :: gen2 set))"
      by (rule finite_cartesian_product) (simp_all add: gen2_finite)
    have alphabet_countable: "countable (UNIV :: (bool \<times> gen2) set)"
      by (rule countable_finite) (use alphabet_finite in \<open>simp only: UNIV_Times_UNIV\<close>)
    have "countable (lists (UNIV :: (bool \<times> gen2) set))"
      by (rule countable_lists) (rule alphabet_countable)
    then show ?thesis by simp
  qed
qed

lemma bad_set_D_index_countable: "countable (carrier F2 - {[]})"
  using carrier_F2_countable by simp

lemma fixed_point_set_subset_sphere2: "fixed_point_set f \<subseteq> sphere2"
  by (simp add: fixed_point_set_def)

lemma SO3_fixed_cross:
  assumes "f \<in> SO3" and "f x = x" and "f y = y"
  shows "f (cross3 x y) = cross3 x y"
proof -
  have f_orth: "orthogonal_transformation f"
    using assms(1) unfolding SO3_def rotation_def by auto
  have f_det: "matrix_det (matrix f) = 1"
    using assms(1) unfolding SO3_def rotation_def by auto
  have "cross3 (f x) (f y) = matrix_det (matrix f) *\<^sub>R f (cross3 x y)"
    using cross_orthogonal_transformation[OF f_orth, of x y] .
  with assms(2,3) f_det show ?thesis
    by simp
qed

lemma SO3_fixed_cross_nonzero_imp_id:
  assumes "f \<in> SO3" and "f x = x" and "f y = y" and "cross3 x y \<noteq> 0"
  shows "f = id"
proof -
  let ?n = "cross3 x y"
  let ?u = "y - ((x \<bullet> y) / (x \<bullet> x)) *\<^sub>R x"
  let ?S = "{x, ?u, ?n}"
  have f_orth: "orthogonal_transformation f"
    using assms(1) unfolding SO3_def rotation_def by auto
  have f_lin: "linear f"
    by (rule orthogonal_transformation_linear[OF f_orth])
  have x_ne: "x \<noteq> 0"
    using assms(4) by auto
  have xx_ne: "x \<bullet> x \<noteq> 0"
    using x_ne by simp
  have n_fix: "f ?n = ?n"
    by (rule SO3_fixed_cross[OF assms(1,2,3)])
  have u_fix: "f ?u = ?u"
    using assms(2,3) f_lin
    by (simp add: linear_diff linear_scale)
  have cross_x_u: "cross3 x ?u = ?n"
    by (simp add: Cross3.right_diff_distrib cross_mult_right)
  have u_ne: "?u \<noteq> 0"
  proof
    assume "?u = 0"
    hence "cross3 x ?u = 0"
      by simp
    with cross_x_u assms(4) show False
      by simp
  qed
  have x_u_orth: "orthogonal x ?u"
    using xx_ne by (simp add: orthogonal_def inner_diff_right inner_commute)
  have n_x_orth: "orthogonal ?n x"
    by (rule orthogonal_cross)
  have n_y_orth: "orthogonal ?n y"
    by (rule orthogonal_cross)
  have n_u_orth: "orthogonal ?n ?u"
    using n_x_orth n_y_orth
    by (simp add: orthogonal_def inner_diff_right)
  have pairwise_S: "pairwise orthogonal ?S"
    using x_u_orth n_x_orth n_u_orth
    by (auto simp: pairwise_def orthogonal_commute)
  have zero_notin_S: "0 \<notin> ?S"
    using assms(4) x_ne u_ne by auto
  have ind_S: "independent ?S"
    by (rule pairwise_orthogonal_independent[OF pairwise_S zero_notin_S])
  have x_neq_u: "x \<noteq> ?u"
  proof
    assume "x = ?u"
    hence "orthogonal x x"
      using x_u_orth by simp
    with x_ne show False
      by (simp add: orthogonal_def)
  qed
  have x_neq_n: "x \<noteq> ?n"
  proof
    assume "x = ?n"
    hence "orthogonal x x"
      using n_x_orth by (simp add: orthogonal_commute)
    with x_ne show False
      by (simp add: orthogonal_def)
  qed
  have u_neq_n: "?u \<noteq> ?n"
  proof
    assume "?u = ?n"
    hence "orthogonal ?u ?u"
      using n_u_orth by (simp add: orthogonal_commute)
    with u_ne show False
      by (simp add: orthogonal_def)
  qed
  have card_S: "card ?S = CARD(3)"
    using x_neq_u x_neq_n u_neq_n by simp
  have dim_S: "dim ?S = CARD(3)"
    using ind_S card_S by (simp add: dim_eq_card_independent)
  have span_S: "span ?S = UNIV"
  proof (rule iffD1[OF dim_eq_full])
    show "dim ?S = DIM(real^3)"
      using dim_S by simp
  qed
  have fixed_on_S: "\<And>z. z \<in> ?S \<Longrightarrow> f z = id z"
    using assms(2) u_fix n_fix by auto
  have fixed_on_span: "\<And>z. z \<in> span ?S \<Longrightarrow> f z = id z"
    by (rule linear_eq_on_span[OF f_lin linear_id fixed_on_S])
  show ?thesis
  proof
    fix z
    have "z \<in> span ?S"
      using span_S by simp
    thus "f z = id z"
      by (rule fixed_on_span)
  qed
qed

lemma nonidentity_SO3_fixed_points_cross_zero:
  assumes "f \<in> SO3" and "f \<noteq> id" and "x \<in> fixed_point_set f" and "y \<in> fixed_point_set f"
  shows "cross3 x y = 0"
proof (rule ccontr)
  assume cross_ne: "cross3 x y \<noteq> 0"
  have fx: "f x = x" and fy: "f y = y"
    using assms(3,4) by (simp_all add: fixed_point_set_def)
  have "f = id"
    by (rule SO3_fixed_cross_nonzero_imp_id[OF assms(1) fx fy cross_ne])
  with assms(2) show False
    by simp
qed

lemma collinear_sphere2_two_points:
  assumes "a \<in> sphere2" and "y \<in> sphere2" and "cross3 a y = 0"
  shows "y = a \<or> y = - a"
proof -
  have cross_col: "cross3 a y = 0 \<longleftrightarrow> collinear {0, a, y}"
    by (rule cross_eq_0)
  have norm_a: "norm a = 1"
    using assms(1) by (simp add: sphere2_def)
  have norm_y: "norm y = 1"
    using assms(2) by (simp add: sphere2_def)
  have a_ne: "a \<noteq> 0"
  proof
    assume "a = 0"
    with norm_a show False
      by simp
  qed
  have y_ne: "y \<noteq> 0"
  proof
    assume "y = 0"
    with norm_y show False
      by simp
  qed
  have col: "collinear {0, a, y}"
    using assms(3) cross_col by blast
  have cases: "a = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R a)"
    using iffD1[OF collinear_lemma[of a y] col] .
  then obtain c where y_eq: "y = c *\<^sub>R a"
    using a_ne y_ne by blast
  have "\<bar>c\<bar> = 1"
    using norm_y by (simp add: y_eq norm_a)
  hence c_cases: "c = 1 \<or> c = -1"
  proof (cases "c \<ge> 0")
    case True
    with \<open>\<bar>c\<bar> = 1\<close> have "c = 1"
      by simp
    thus ?thesis ..
  next
    case False
    with \<open>\<bar>c\<bar> = 1\<close> have "c = -1"
      by simp
    thus ?thesis ..
  qed
  show ?thesis
    using c_cases y_eq by auto
qed

lemma bad_set_D_countable_if_fixed_point_sets_countable:
  assumes "\<And>w. w \<in> carrier F2 - {[]} \<Longrightarrow> countable (fixed_point_set (sigma w))"
  shows "countable bad_set_D"
proof -
  have "countable (\<Union>w \<in> carrier F2 - {[]}. fixed_point_set (sigma w))"
    by (rule countable_UN) (use bad_set_D_index_countable assms in auto)
  thus ?thesis
    by (simp add: bad_set_D_def)
qed

lemma nonidentity_SO3_fixed_point_set_countable:
  assumes "f \<in> SO3" and "f \<noteq> id"
  shows "countable (fixed_point_set f)"
proof (cases "fixed_point_set f = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where a: "a \<in> fixed_point_set f"
    by auto
  hence a_sphere: "a \<in> sphere2"
    by (simp add: fixed_point_set_def)
  have subset_two: "fixed_point_set f \<subseteq> {a, - a}"
  proof
    fix y
    assume y: "y \<in> fixed_point_set f"
    hence y_sphere: "y \<in> sphere2"
      by (simp add: fixed_point_set_def)
    have cross_zero: "cross3 a y = 0"
      by (rule nonidentity_SO3_fixed_points_cross_zero[OF assms a y])
    have "y = a \<or> y = - a"
      by (rule collinear_sphere2_two_points[OF a_sphere y_sphere cross_zero])
    thus "y \<in> {a, - a}"
      by simp
  qed
  have "finite (fixed_point_set f)"
    by (rule finite_subset[OF subset_two]) simp
  thus ?thesis
    by (rule countable_finite)
qed

lemma sigma_fixed_point_set_countable:
  assumes "w \<in> carrier F2 - {[]}"
  shows "countable (fixed_point_set (sigma w))"
proof -
  have "sigma w \<in> SO3"
    using assms sigma_image_in_SO3 by auto
  moreover have "sigma w \<noteq> id"
    using assms sigma_nontrivial_word_not_id by auto
  ultimately show ?thesis
    by (rule nonidentity_SO3_fixed_point_set_countable)
qed

lemma bad_set_D_countable: "countable bad_set_D"
  by (rule bad_set_D_countable_if_fixed_point_sets_countable)
    (rule sigma_fixed_point_set_countable)

lemma bad_set_D_subset: "bad_set_D \<subseteq> sphere2"
  unfolding bad_set_D_def fixed_point_set_def by auto

lemma sphere2_minus_bad_subset: "sphere2 - bad_set_D \<subseteq> sphere2"
  by auto

interpretation sigma_sphere_action:
  group_action "carrier F2" "[]" "(\<lambda>w1 w2. w1 \<otimes>\<^bsub>F2\<^esub> w2)" "\<lambda>w x. sigma w x" sphere2
proof
  show "[] \<in> carrier F2"
    by simp
  show "\<And>g h. g \<in> carrier F2 \<Longrightarrow> h \<in> carrier F2 \<Longrightarrow> g \<otimes>\<^bsub>F2\<^esub> h \<in> carrier F2"
    using group.subgroup_self group_def monoid.m_closed free_group_is_group by blast
  show "\<And>g x. g \<in> carrier F2 \<Longrightarrow> x \<in> sphere2 \<Longrightarrow> sigma g x \<in> sphere2"
    using sigma_preserves_sphere2 by blast
  show "\<And>x. x \<in> sphere2 \<Longrightarrow> sigma [] x = x"
    by simp
  show "\<And>g h x. g \<in> carrier F2 \<Longrightarrow> h \<in> carrier F2 \<Longrightarrow> x \<in> sphere2 \<Longrightarrow>
      sigma (g \<otimes>\<^bsub>F2\<^esub> h) x = sigma g (sigma h x)"
    using sigma_homomorphism by (simp add: o_def)
qed

lemma F2_conjugate_nontrivial:
  assumes "w \<in> carrier F2" "v \<in> carrier F2" "v \<noteq> []"
  shows "(inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w \<noteq> []"
proof
  interpret G: group F2
    by (rule free_group_is_group)
  assume conj_eq: "(inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w = []"
  have inv_closed: "inv\<^bsub>F2\<^esub> w \<in> carrier F2"
    using assms(1) by (rule G.inv_closed)
  have vw_closed: "v \<otimes>\<^bsub>F2\<^esub> w \<in> carrier F2"
    by (rule G.m_closed) (use assms in simp_all)
  have assoc_eq:
    "inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> (v \<otimes>\<^bsub>F2\<^esub> w) =
      (inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w"
    using inv_closed assms by (simp add: G.m_assoc)
  have eq1: "inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> (v \<otimes>\<^bsub>F2\<^esub> w) = []"
    using conj_eq assoc_eq by simp
  have "v \<otimes>\<^bsub>F2\<^esub> w = w \<otimes>\<^bsub>F2\<^esub> []"
    using G.inv_solve_left'[OF G.one_closed assms(1) vw_closed] eq1 by simp
  hence "v \<otimes>\<^bsub>F2\<^esub> w = w"
    using assms by simp
  hence "v = []"
    using assms by simp
  with assms(3) show False by simp
qed

lemma sigma_inverse_left:
  assumes "w \<in> carrier F2"
  shows "sigma (inv\<^bsub>F2\<^esub> w) (sigma w x) = x"
proof -
  interpret G: group F2
    by (rule free_group_is_group)
  have inv_closed: "inv\<^bsub>F2\<^esub> w \<in> carrier F2"
    using assms by (rule G.inv_closed)
  have "sigma (inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> w) x = sigma (inv\<^bsub>F2\<^esub> w) (sigma w x)"
    using sigma_homomorphism[OF inv_closed assms]
    by (simp add: o_def)
  moreover have "inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> w = []"
    using G.l_inv[OF assms] by simp
  ultimately show ?thesis
    by simp
qed

lemma sigma_conjugate_fixed_pullback:
  assumes "w \<in> carrier F2"
    and "v \<in> carrier F2"
    and "sigma v (sigma w x) = sigma w x"
  shows "sigma ((inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w) x = x"
proof -
  interpret G: group F2
    by (rule free_group_is_group)
  have inv_closed: "inv\<^bsub>F2\<^esub> w \<in> carrier F2"
    using assms(1) by (rule G.inv_closed)
  have iv_closed: "inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v \<in> carrier F2"
    using inv_closed assms(2) by (rule G.m_closed)
  have "sigma ((inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w) x =
      sigma (inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) (sigma w x)"
    using sigma_homomorphism[OF iv_closed assms(1)] by (simp add: o_def)
  also have "\<dots> = sigma (inv\<^bsub>F2\<^esub> w) (sigma v (sigma w x))"
    using sigma_homomorphism[OF inv_closed assms(2)] by (simp add: o_def)
  also have "\<dots> = sigma (inv\<^bsub>F2\<^esub> w) (sigma w x)"
    using assms(3) by simp
  also have "\<dots> = x"
    using sigma_inverse_left[OF assms(1)] by simp
  finally show ?thesis .
qed

lemma sigma_preimage_bad_set:
  assumes "w \<in> carrier F2"
    and "x \<in> sphere2"
    and "sigma w x \<in> bad_set_D"
  shows "x \<in> bad_set_D"
proof -
  from assms(3) obtain v where v_carrier: "v \<in> carrier F2"
    and v_ne: "v \<noteq> []"
    and fixed: "sigma v (sigma w x) = sigma w x"
    unfolding bad_set_D_def fixed_point_set_def by auto
  define u where "u = (inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v) \<otimes>\<^bsub>F2\<^esub> w"
  have u_carrier: "u \<in> carrier F2"
  proof -
    interpret G: group F2
      by (rule free_group_is_group)
    have inv_closed: "inv\<^bsub>F2\<^esub> w \<in> carrier F2"
      using assms(1) by (rule G.inv_closed)
    have "inv\<^bsub>F2\<^esub> w \<otimes>\<^bsub>F2\<^esub> v \<in> carrier F2"
      using inv_closed v_carrier by (rule G.m_closed)
    thus ?thesis
      unfolding u_def using assms(1) by (rule G.m_closed)
  qed
  have u_ne: "u \<noteq> []"
    using F2_conjugate_nontrivial[OF assms(1) v_carrier v_ne] by (simp add: u_def)
  have "sigma u x = x"
    using sigma_conjugate_fixed_pullback[OF assms(1) v_carrier fixed] by (simp add: u_def)
  hence "x \<in> fixed_point_set (sigma u)"
    using assms(2) by (simp add: fixed_point_set_def)
  with u_carrier u_ne show ?thesis
    unfolding bad_set_D_def by blast
qed

lemma sigma_preserves_sphere2_minus_bad_set:
  assumes "w \<in> carrier F2"
    and "x \<in> sphere2 - bad_set_D"
  shows "sigma w x \<in> sphere2 - bad_set_D"
proof
  show "sigma w x \<in> sphere2"
    using assms sigma_preserves_sphere2 by blast
  show "sigma w x \<notin> bad_set_D"
  proof
    assume "sigma w x \<in> bad_set_D"
    hence "x \<in> bad_set_D"
      using assms sigma_preimage_bad_set by auto
    with assms(2) show False by simp
  qed
qed

interpretation sigma_sphere_minus_bad_action:
  group_action "carrier F2" "[]" "(\<lambda>w1 w2. w1 \<otimes>\<^bsub>F2\<^esub> w2)" "\<lambda>w x. sigma w x"
    "sphere2 - bad_set_D"
proof
  show "[] \<in> carrier F2"
    by simp
  show "\<And>g h. g \<in> carrier F2 \<Longrightarrow> h \<in> carrier F2 \<Longrightarrow> g \<otimes>\<^bsub>F2\<^esub> h \<in> carrier F2"
    using group.subgroup_self group_def monoid.m_closed free_group_is_group by blast
  show "\<And>g x. g \<in> carrier F2 \<Longrightarrow> x \<in> sphere2 - bad_set_D \<Longrightarrow>
      sigma g x \<in> sphere2 - bad_set_D"
    by (rule sigma_preserves_sphere2_minus_bad_set)
  show "\<And>x. x \<in> sphere2 - bad_set_D \<Longrightarrow> sigma [] x = x"
    by simp
  show "\<And>g h x. g \<in> carrier F2 \<Longrightarrow> h \<in> carrier F2 \<Longrightarrow> x \<in> sphere2 - bad_set_D \<Longrightarrow>
      sigma (g \<otimes>\<^bsub>F2\<^esub> h) x = sigma g (sigma h x)"
    using sigma_homomorphism by (simp add: o_def)
qed


section \<open>Free action of \<open>F\<^sub>2\<close> on \<open>S\<^sup>2 \<setminus> D\<close>\<close>

text \<open>
  By construction, every point of \<open>S\<^sup>2 \<setminus> D\<close> avoids the
  fixed-point set of every non-trivial group element, hence is moved by
  every non-trivial \<open>sigma w\<close>.
\<close>

text \<open>The action is free away from the fixed-point bad set.\<close>
lemma sigma_action_free_off_D:
  assumes "x \<in> sphere2 - bad_set_D"
    and "w \<in> carrier F2"
    and "sigma w x = x"
  shows "w = []"
proof (rule ccontr)
  assume w_ne: "w \<noteq> []"
  from assms(1) have x_sphere: "x \<in> sphere2" and x_notbad: "x \<notin> bad_set_D"
    by auto
  from x_sphere assms(3) have "x \<in> fixed_point_set (sigma w)"
    by (simp add: fixed_point_set_def)
  with assms(2) w_ne have "x \<in> bad_set_D"
    unfolding bad_set_D_def by blast
  with x_notbad show False ..
qed

lemma sigma_sphere_minus_bad_action_free:
  "sigma_sphere_minus_bad_action.free_on (sphere2 - bad_set_D)"
  unfolding sigma_sphere_minus_bad_action.free_on_def
  using sigma_action_free_off_D by auto

lemma sigma_orbit_eqI:
  assumes x: "x \<in> sphere2 - bad_set_D"
    and y: "y \<in> sphere2 - bad_set_D"
    and g: "g \<in> carrier F2"
    and y_eq: "y = sigma g x"
  shows "sigma_sphere_minus_bad_action.orbit y =
    sigma_sphere_minus_bad_action.orbit x"
proof
  interpret G: group F2
    by (rule free_group_is_group)
  show "sigma_sphere_minus_bad_action.orbit y \<subseteq>
      sigma_sphere_minus_bad_action.orbit x"
  proof
    fix z
    assume "z \<in> sigma_sphere_minus_bad_action.orbit y"
    then obtain h where h: "h \<in> carrier F2" and z: "z = sigma h y"
      unfolding sigma_sphere_minus_bad_action.orbit_def by blast
    have hg: "h \<otimes>\<^bsub>F2\<^esub> g \<in> carrier F2"
      by (rule G.m_closed[OF h g])
    have "z = sigma (h \<otimes>\<^bsub>F2\<^esub> g) x"
      using z y_eq sigma_homomorphism[OF h g] by (simp add: o_def)
    thus "z \<in> sigma_sphere_minus_bad_action.orbit x"
      unfolding sigma_sphere_minus_bad_action.orbit_def using hg by blast
  qed
  show "sigma_sphere_minus_bad_action.orbit x \<subseteq>
      sigma_sphere_minus_bad_action.orbit y"
  proof
    fix z
    assume "z \<in> sigma_sphere_minus_bad_action.orbit x"
    then obtain h where h: "h \<in> carrier F2" and z: "z = sigma h x"
      unfolding sigma_sphere_minus_bad_action.orbit_def by blast
    have invg: "inv\<^bsub>F2\<^esub> g \<in> carrier F2"
      by (rule G.inv_closed[OF g])
    have h_invg: "h \<otimes>\<^bsub>F2\<^esub> inv\<^bsub>F2\<^esub> g \<in> carrier F2"
      by (rule G.m_closed[OF h invg])
    have x_eq: "x = sigma (inv\<^bsub>F2\<^esub> g) y"
      using y_eq sigma_inverse_left[OF g] by simp
    have "z = sigma (h \<otimes>\<^bsub>F2\<^esub> inv\<^bsub>F2\<^esub> g) y"
      using z x_eq sigma_homomorphism[OF h invg] by (simp add: o_def)
    thus "z \<in> sigma_sphere_minus_bad_action.orbit y"
      unfolding sigma_sphere_minus_bad_action.orbit_def using h_invg by blast
  qed
qed

lemma sigma_orbit_eq_if_common_point:
  assumes x: "x \<in> sphere2 - bad_set_D"
    and y: "y \<in> sphere2 - bad_set_D"
    and z: "z \<in> sigma_sphere_minus_bad_action.orbit x"
    and z': "z \<in> sigma_sphere_minus_bad_action.orbit y"
  shows "sigma_sphere_minus_bad_action.orbit x =
    sigma_sphere_minus_bad_action.orbit y"
proof -
  from z obtain g where g: "g \<in> carrier F2" and z_eq: "z = sigma g x"
    unfolding sigma_sphere_minus_bad_action.orbit_def by blast
  have zX: "z \<in> sphere2 - bad_set_D"
    using sigma_preserves_sphere2_minus_bad_set[OF g x] z_eq by simp
  have orbit_z_x: "sigma_sphere_minus_bad_action.orbit z =
      sigma_sphere_minus_bad_action.orbit x"
    using sigma_orbit_eqI[OF x zX g z_eq] .
  from z' obtain h where h: "h \<in> carrier F2" and z_eq_y: "z = sigma h y"
    unfolding sigma_sphere_minus_bad_action.orbit_def by blast
  have orbit_z_y: "sigma_sphere_minus_bad_action.orbit z =
      sigma_sphere_minus_bad_action.orbit y"
    using sigma_orbit_eqI[OF y zX h z_eq_y] .
  show ?thesis
    using orbit_z_x orbit_z_y by simp
qed


section \<open>Transporting the free-group paradox to \<open>S\<^sup>2 \<setminus> D\<close>\<close>

definition hausdorff_rep :: "real^3 \<Rightarrow> real^3" where
  "hausdorff_rep x = (SOME y. y \<in> sigma_sphere_minus_bad_action.orbit x)"

definition hausdorff_lift :: "((bool \<times> gen2) list) set \<Rightarrow> (real^3) set" where
  "hausdorff_lift u =
    {sigma g (hausdorff_rep x) | g x. g \<in> u \<and> x \<in> sphere2 - bad_set_D}"

definition hausdorff_sigma_image_set ::
    "(bool \<times> gen2) list \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set" where
  "hausdorff_sigma_image_set g u = sigma g ` u"

lemma map2_hausdorff_sigma_image_set_eq:
  "map2 sigma_sphere_minus_bad_action.image_set gs As =
    map2 hausdorff_sigma_image_set gs As"
  by (induction gs arbitrary: As)
     (auto simp: hausdorff_sigma_image_set_def sigma_sphere_minus_bad_action.image_set_def
       split: list.splits)

lemma hausdorff_rep_in_orbit:
  assumes "x \<in> sphere2 - bad_set_D"
  shows "hausdorff_rep x \<in> sigma_sphere_minus_bad_action.orbit x"
  unfolding hausdorff_rep_def
  by (rule someI_ex) (use sigma_sphere_minus_bad_action.orbit_self[OF assms] in blast)

lemma hausdorff_rep_in_X:
  assumes "x \<in> sphere2 - bad_set_D"
  shows "hausdorff_rep x \<in> sphere2 - bad_set_D"
proof -
  from hausdorff_rep_in_orbit[OF assms] obtain g
    where g: "g \<in> carrier F2" and rep_eq: "hausdorff_rep x = sigma g x"
    unfolding sigma_sphere_minus_bad_action.orbit_def by blast
  show ?thesis
    using sigma_preserves_sphere2_minus_bad_set[OF g assms] rep_eq by simp
qed

lemma hausdorff_rep_eq_if_orbit_eq:
  assumes "sigma_sphere_minus_bad_action.orbit x =
    sigma_sphere_minus_bad_action.orbit y"
  shows "hausdorff_rep x = hausdorff_rep y"
  using assms by (simp add: hausdorff_rep_def)

lemma hausdorff_rep_idem:
  assumes x: "x \<in> sphere2 - bad_set_D"
  shows "hausdorff_rep (hausdorff_rep x) = hausdorff_rep x"
proof -
  let ?r = "hausdorff_rep x"
  have rX: "?r \<in> sphere2 - bad_set_D"
    by (rule hausdorff_rep_in_X[OF x])
  have r_orbit_x: "?r \<in> sigma_sphere_minus_bad_action.orbit x"
    by (rule hausdorff_rep_in_orbit[OF x])
  have r_orbit_r: "?r \<in> sigma_sphere_minus_bad_action.orbit ?r"
    by (rule sigma_sphere_minus_bad_action.orbit_self[OF rX])
  have "sigma_sphere_minus_bad_action.orbit ?r =
      sigma_sphere_minus_bad_action.orbit x"
    by (rule sigma_orbit_eq_if_common_point[OF rX x r_orbit_r r_orbit_x])
  hence "hausdorff_rep ?r = hausdorff_rep x"
    by (rule hausdorff_rep_eq_if_orbit_eq)
  thus ?thesis
    by simp
qed

lemma hausdorff_lift_subset_X:
  assumes "u \<subseteq> carrier F2"
  shows "hausdorff_lift u \<subseteq> sphere2 - bad_set_D"
proof
  fix y
  assume "y \<in> hausdorff_lift u"
  then obtain g x where gu: "g \<in> u" and x: "x \<in> sphere2 - bad_set_D"
    and y_eq: "y = sigma g (hausdorff_rep x)"
    unfolding hausdorff_lift_def by blast
  have g: "g \<in> carrier F2"
    using assms gu by auto
  have repX: "hausdorff_rep x \<in> sphere2 - bad_set_D"
    by (rule hausdorff_rep_in_X[OF x])
  show "y \<in> sphere2 - bad_set_D"
    using sigma_preserves_sphere2_minus_bad_set[OF g repX] y_eq by simp
qed

lemma F2_act_image_set_subset_carrier:
  assumes "g \<in> carrier F2" and "u \<subseteq> carrier F2"
  shows "F2_act.image_set g u \<subseteq> carrier F2"
  unfolding F2_act.image_set_def
  using assms by auto

lemma sigma_free_same_point_eq:
  assumes x: "x \<in> sphere2 - bad_set_D"
    and p: "p \<in> carrier F2"
    and q: "q \<in> carrier F2"
    and eq: "sigma p x = sigma q x"
  shows "p = q"
proof -
  interpret G: group F2
    by (rule free_group_is_group)
  have invp: "inv\<^bsub>F2\<^esub> p \<in> carrier F2"
    by (rule G.inv_closed[OF p])
  have invpq: "inv\<^bsub>F2\<^esub> p \<otimes>\<^bsub>F2\<^esub> q \<in> carrier F2"
    by (rule G.m_closed[OF invp q])
  have fixed: "sigma (inv\<^bsub>F2\<^esub> p \<otimes>\<^bsub>F2\<^esub> q) x = x"
  proof -
    have "sigma (inv\<^bsub>F2\<^esub> p \<otimes>\<^bsub>F2\<^esub> q) x =
        sigma (inv\<^bsub>F2\<^esub> p) (sigma q x)"
      using sigma_homomorphism[OF invp q] by (simp add: o_def)
    also have "\<dots> = sigma (inv\<^bsub>F2\<^esub> p) (sigma p x)"
      using eq by simp
    also have "\<dots> = x"
      using sigma_inverse_left[OF p] by simp
    finally show ?thesis .
  qed
  have invpq_unit: "inv\<^bsub>F2\<^esub> p \<otimes>\<^bsub>F2\<^esub> q = []"
    by (rule sigma_action_free_off_D[OF x invpq fixed])
  have "q = p \<otimes>\<^bsub>F2\<^esub> []"
    using G.inv_solve_left'[OF G.one_closed p q] invpq_unit by simp
  thus ?thesis
    using p by simp
qed

lemma hausdorff_lift_disjoint:
  assumes disj: "u \<inter> v = {}"
    and u: "u \<subseteq> carrier F2"
    and v: "v \<subseteq> carrier F2"
  shows "hausdorff_lift u \<inter> hausdorff_lift v = {}"
proof
  show "hausdorff_lift u \<inter> hausdorff_lift v \<subseteq> {}"
  proof
    fix z
    assume z: "z \<in> hausdorff_lift u \<inter> hausdorff_lift v"
    then obtain p x where pu: "p \<in> u" and x: "x \<in> sphere2 - bad_set_D"
      and z_p: "z = sigma p (hausdorff_rep x)"
      unfolding hausdorff_lift_def by blast
    from z obtain q y where qv: "q \<in> v" and y: "y \<in> sphere2 - bad_set_D"
      and z_q: "z = sigma q (hausdorff_rep y)"
      unfolding hausdorff_lift_def by blast
    let ?rx = "hausdorff_rep x"
    let ?ry = "hausdorff_rep y"
    have p: "p \<in> carrier F2"
      using u pu by auto
    have q: "q \<in> carrier F2"
      using v qv by auto
    have rxX: "?rx \<in> sphere2 - bad_set_D"
      by (rule hausdorff_rep_in_X[OF x])
    have ryX: "?ry \<in> sphere2 - bad_set_D"
      by (rule hausdorff_rep_in_X[OF y])
    have z_orbit_rx: "z \<in> sigma_sphere_minus_bad_action.orbit ?rx"
      unfolding sigma_sphere_minus_bad_action.orbit_def
      using p z_p by blast
    have z_orbit_ry: "z \<in> sigma_sphere_minus_bad_action.orbit ?ry"
      unfolding sigma_sphere_minus_bad_action.orbit_def
      using q z_q by blast
    have orbit_eq: "sigma_sphere_minus_bad_action.orbit ?rx =
        sigma_sphere_minus_bad_action.orbit ?ry"
      by (rule sigma_orbit_eq_if_common_point[OF rxX ryX z_orbit_rx z_orbit_ry])
    have rep_rx: "hausdorff_rep ?rx = ?rx"
      by (rule hausdorff_rep_idem[OF x])
    have rep_ry: "hausdorff_rep ?ry = ?ry"
      by (rule hausdorff_rep_idem[OF y])
    have rx_eq_ry: "?rx = ?ry"
      using hausdorff_rep_eq_if_orbit_eq[OF orbit_eq] rep_rx rep_ry by simp
    have p_eq_q: "p = q"
      by (rule sigma_free_same_point_eq[OF rxX p q]) (use z_p z_q rx_eq_ry in simp)
    have "p \<in> u \<inter> v"
      using pu qv p_eq_q by auto
    with disj show "z \<in> {}"
      by simp
  qed
qed simp

lemma hausdorff_lift_pairwise_disjoint:
  assumes disj: "pairwise_disjoint As"
    and sub: "\<forall>u \<in> set As. u \<subseteq> carrier F2"
  shows "pairwise_disjoint (map hausdorff_lift As)"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (map hausdorff_lift As)"
    and j: "j < length (map hausdorff_lift As)"
    and ij: "i \<noteq> j"
  have iA: "i < length As"
    using i by simp
  have jA: "j < length As"
    using j by simp
  have Ai: "As ! i \<subseteq> carrier F2"
    using sub iA by simp
  have Aj: "As ! j \<subseteq> carrier F2"
    using sub jA by simp
  have "As ! i \<inter> As ! j = {}"
    using disj iA jA ij by (simp add: pairwise_disjoint_def)
  hence "hausdorff_lift (As ! i) \<inter> hausdorff_lift (As ! j) = {}"
    by (rule hausdorff_lift_disjoint[OF _ Ai Aj])
  thus "(map hausdorff_lift As) ! i \<inter> (map hausdorff_lift As) ! j = {}"
    using iA jA by simp
qed

lemma hausdorff_sigma_image_lift:
  assumes g: "g \<in> carrier F2"
    and u: "u \<subseteq> carrier F2"
  shows "hausdorff_sigma_image_set g (hausdorff_lift u) =
    hausdorff_lift (F2_act.image_set g u)"
proof
  show "hausdorff_sigma_image_set g (hausdorff_lift u) \<subseteq>
      hausdorff_lift (F2_act.image_set g u)"
  proof
    fix z
    assume "z \<in> hausdorff_sigma_image_set g (hausdorff_lift u)"
    then obtain y where y: "y \<in> hausdorff_lift u" and z_eq: "z = sigma g y"
      unfolding hausdorff_sigma_image_set_def by blast
    from y obtain a x where au: "a \<in> u" and x: "x \<in> sphere2 - bad_set_D"
      and y_eq: "y = sigma a (hausdorff_rep x)"
      unfolding hausdorff_lift_def by blast
    have a: "a \<in> carrier F2"
      using u au by auto
    have ga_image: "g \<otimes>\<^bsub>F2\<^esub> a \<in> F2_act.image_set g u"
      unfolding F2_act.image_set_def using au by auto
    have "z = sigma (g \<otimes>\<^bsub>F2\<^esub> a) (hausdorff_rep x)"
      using sigma_homomorphism[OF g a] z_eq y_eq by (simp add: o_def)
    thus "z \<in> hausdorff_lift (F2_act.image_set g u)"
      unfolding hausdorff_lift_def using ga_image x by blast
  qed
  show "hausdorff_lift (F2_act.image_set g u) \<subseteq>
      hausdorff_sigma_image_set g (hausdorff_lift u)"
  proof
    fix z
    assume "z \<in> hausdorff_lift (F2_act.image_set g u)"
    then obtain h x where h: "h \<in> F2_act.image_set g u"
      and x: "x \<in> sphere2 - bad_set_D"
      and z_eq: "z = sigma h (hausdorff_rep x)"
      unfolding hausdorff_lift_def by blast
    from h obtain a where au: "a \<in> u" and h_eq: "h = g \<otimes>\<^bsub>F2\<^esub> a"
      unfolding F2_act.image_set_def by auto
    have a: "a \<in> carrier F2"
      using u au by auto
    have y_lift: "sigma a (hausdorff_rep x) \<in> hausdorff_lift u"
      unfolding hausdorff_lift_def using au x by blast
    have "z = sigma g (sigma a (hausdorff_rep x))"
      using sigma_homomorphism[OF g a] z_eq h_eq by (simp add: o_def)
    thus "z \<in> hausdorff_sigma_image_set g (hausdorff_lift u)"
      unfolding hausdorff_sigma_image_set_def using y_lift by blast
  qed
qed

lemma hausdorff_translated_lift_pairwise_disjoint:
  assumes len: "length As = length gs"
    and gs: "set gs \<subseteq> carrier F2"
    and sub: "\<forall>u \<in> set As. u \<subseteq> carrier F2"
    and disj: "pairwise_disjoint (map2 F2_act.image_set gs As)"
  shows "pairwise_disjoint (map2 hausdorff_sigma_image_set gs (map hausdorff_lift As))"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (map2 hausdorff_sigma_image_set gs (map hausdorff_lift As))"
    and j: "j < length (map2 hausdorff_sigma_image_set gs (map hausdorff_lift As))"
    and ij: "i \<noteq> j"
  have iA: "i < length As"
    using i len by simp
  have jA: "j < length As"
    using j len by simp
  have ig: "gs ! i \<in> carrier F2"
  proof -
    have "i < length gs"
      using iA len by simp
    thus ?thesis
      using gs nth_mem by blast
  qed
  have jg: "gs ! j \<in> carrier F2"
  proof -
    have "j < length gs"
      using jA len by simp
    thus ?thesis
      using gs nth_mem by blast
  qed
  have Ai: "As ! i \<subseteq> carrier F2"
    using sub iA by simp
  have Aj: "As ! j \<subseteq> carrier F2"
    using sub jA by simp
  have img_i: "F2_act.image_set (gs ! i) (As ! i) \<subseteq> carrier F2"
    by (rule F2_act_image_set_subset_carrier[OF ig Ai])
  have img_j: "F2_act.image_set (gs ! j) (As ! j) \<subseteq> carrier F2"
    by (rule F2_act_image_set_subset_carrier[OF jg Aj])
  have img_disj: "F2_act.image_set (gs ! i) (As ! i) \<inter>
      F2_act.image_set (gs ! j) (As ! j) = {}"
    using disj iA jA ij len by (simp add: pairwise_disjoint_def)
  have lift_disj: "hausdorff_lift (F2_act.image_set (gs ! i) (As ! i)) \<inter>
      hausdorff_lift (F2_act.image_set (gs ! j) (As ! j)) = {}"
    by (rule hausdorff_lift_disjoint[OF img_disj img_i img_j])
  have trans_i: "hausdorff_sigma_image_set (gs ! i) (hausdorff_lift (As ! i)) =
      hausdorff_lift (F2_act.image_set (gs ! i) (As ! i))"
    by (rule hausdorff_sigma_image_lift[OF ig Ai])
  have trans_j: "hausdorff_sigma_image_set (gs ! j) (hausdorff_lift (As ! j)) =
      hausdorff_lift (F2_act.image_set (gs ! j) (As ! j))"
    by (rule hausdorff_sigma_image_lift[OF jg Aj])
  show "(map2 hausdorff_sigma_image_set gs (map hausdorff_lift As)) ! i \<inter>
      (map2 hausdorff_sigma_image_set gs (map hausdorff_lift As)) ! j = {}"
    using lift_disj trans_i trans_j iA jA len by simp
qed

lemma hausdorff_lift_cover:
  assumes len: "length As = length gs"
    and gs: "set gs \<subseteq> carrier F2"
    and sub: "\<forall>u \<in> set As. u \<subseteq> carrier F2"
    and cover: "carrier F2 =
      (\<Union>i<length As. F2_act.image_set (gs ! i) (As ! i))"
  shows "sphere2 - bad_set_D =
    (\<Union>i<length As. hausdorff_sigma_image_set (gs ! i) (hausdorff_lift (As ! i)))"
proof -
  let ?X = "sphere2 - bad_set_D"
  let ?U = "(\<Union>i<length As. hausdorff_sigma_image_set (gs ! i) (hausdorff_lift (As ! i)))"
  show "?X = ?U"
  proof (rule subset_antisym)
    show "?X \<subseteq> ?U"
    proof
      fix x
      assume x: "x \<in> ?X"
      interpret G: group F2
        by (rule free_group_is_group)
      from hausdorff_rep_in_orbit[OF x] obtain r
        where r: "r \<in> carrier F2" and rep_eq: "hausdorff_rep x = sigma r x"
        unfolding sigma_sphere_minus_bad_action.orbit_def by blast
      define h where "h = inv\<^bsub>F2\<^esub> r"
      have h: "h \<in> carrier F2"
        unfolding h_def by (rule G.inv_closed[OF r])
      have x_eq: "x = sigma h (hausdorff_rep x)"
        unfolding h_def using rep_eq sigma_inverse_left[OF r] by simp
      from cover h obtain i where i: "i < length As"
        and h_img: "h \<in> F2_act.image_set (gs ! i) (As ! i)"
        by blast
      from h_img obtain a where aA: "a \<in> As ! i" and h_eq: "h = gs ! i \<otimes>\<^bsub>F2\<^esub> a"
        unfolding F2_act.image_set_def by auto
      have gi: "gs ! i \<in> carrier F2"
      proof -
        have "i < length gs"
          using i len by simp
        thus ?thesis
          using gs nth_mem by blast
      qed
      have Ai: "As ! i \<subseteq> carrier F2"
        using sub i by simp
      have a: "a \<in> carrier F2"
        using Ai aA by auto
      have y_lift: "sigma a (hausdorff_rep x) \<in> hausdorff_lift (As ! i)"
        unfolding hausdorff_lift_def using aA x by blast
      have "sigma (gs ! i) (sigma a (hausdorff_rep x)) = sigma h (hausdorff_rep x)"
        using sigma_homomorphism[OF gi a] h_eq by (simp add: o_def)
      hence "x = sigma (gs ! i) (sigma a (hausdorff_rep x))"
        using x_eq by simp
      hence "x \<in> hausdorff_sigma_image_set (gs ! i) (hausdorff_lift (As ! i))"
        unfolding hausdorff_sigma_image_set_def using y_lift by blast
      thus "x \<in> ?U"
        using i by blast
    qed
    show "?U \<subseteq> ?X"
    proof
      fix y
      assume "y \<in> ?U"
      then obtain i where i: "i < length As"
        and y_img: "y \<in> hausdorff_sigma_image_set (gs ! i) (hausdorff_lift (As ! i))"
        by blast
      from y_img obtain z where z_lift: "z \<in> hausdorff_lift (As ! i)"
        and y_eq: "y = sigma (gs ! i) z"
        unfolding hausdorff_sigma_image_set_def by blast
      have gi: "gs ! i \<in> carrier F2"
      proof -
        have "i < length gs"
          using i len by simp
        thus ?thesis
          using gs nth_mem by blast
      qed
      have Ai: "As ! i \<subseteq> carrier F2"
        using sub i by simp
      have zX: "z \<in> ?X"
        using hausdorff_lift_subset_X[OF Ai] z_lift by auto
      show "y \<in> ?X"
        using sigma_preserves_sphere2_minus_bad_set[OF gi zX] y_eq by simp
    qed
  qed
qed


section \<open>The Hausdorff paradox\<close>

text \<open>
  Define the rotation-action of \<open>F\<^sub>2\<close> on the sphere by
  evaluation: \<open>sigma w \<cdot> x = sigma w x\<close>. Off the bad set, this
  is a free action, and the paradoxical decomposition of \<open>F\<^sub>2\<close>
  transports along orbits.
\<close>

text \<open>
  Hausdorff's theorem: \<open>S\<^sup>2 \<setminus> D\<close> is paradoxical
  under the action of SO(3).
\<close>

theorem hausdorff_paradox_strong:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((bool \<times> gen2) list) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> carrier F2 \<and> set gQ \<subseteq> carrier F2 \<and>
       set (map sigma gP) \<subseteq> SO3 \<and> set (map sigma gQ) \<subseteq> SO3 \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 hausdorff_sigma_image_set gP P) \<and>
       pairwise_disjoint (map2 hausdorff_sigma_image_set gQ Q) \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length P. hausdorff_sigma_image_set (gP ! i) (P ! i)) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length Q. hausdorff_sigma_image_set (gQ ! i) (Q ! i))"
proof -
  from F2_paradoxical_partition obtain P0 Q0 :: "((bool \<times> gen2) list) set list"
    and gP gQ :: "((bool \<times> gen2) list) list"
    where lenP: "length P0 = length gP"
      and lenQ: "length Q0 = length gQ"
      and gP: "set gP \<subseteq> carrier F2"
      and gQ: "set gQ \<subseteq> carrier F2"
      and disj_all: "pairwise_disjoint (P0 @ Q0)"
      and disj_imP: "pairwise_disjoint (map2 F2_act.image_set gP P0)"
      and disj_imQ: "pairwise_disjoint (map2 F2_act.image_set gQ Q0)"
      and source_cover0: "carrier F2 =
        (\<Union>i<length P0. P0 ! i) \<union> (\<Union>i<length Q0. Q0 ! i)"
      and coverP: "carrier F2 = (\<Union>i<length P0. F2_act.image_set (gP ! i) (P0 ! i))"
      and coverQ: "carrier F2 = (\<Union>i<length Q0. F2_act.image_set (gQ ! i) (Q0 ! i))"
    by auto
  let ?P = "map hausdorff_lift P0"
  let ?Q = "map hausdorff_lift Q0"
  have P0_sub: "\<forall>u \<in> set P0. u \<subseteq> carrier F2"
  proof
    fix u
    assume "u \<in> set P0"
    then obtain i where i: "i < length P0" and u_eq: "u = P0 ! i"
      by (auto simp: in_set_conv_nth)
    show "u \<subseteq> carrier F2"
      using source_cover0 i u_eq by auto
  qed
  have Q0_sub: "\<forall>u \<in> set Q0. u \<subseteq> carrier F2"
  proof
    fix u
    assume "u \<in> set Q0"
    then obtain i where i: "i < length Q0" and u_eq: "u = Q0 ! i"
      by (auto simp: in_set_conv_nth)
    show "u \<subseteq> carrier F2"
      using source_cover0 i u_eq by auto
  qed
  have all_sub: "\<forall>u \<in> set (P0 @ Q0). u \<subseteq> carrier F2"
    using P0_sub Q0_sub by auto
  have lenP': "length ?P = length gP"
    using lenP by simp
  have lenQ': "length ?Q = length gQ"
    using lenQ by simp
  have gP_SO3: "set (map sigma gP) \<subseteq> SO3"
    using gP sigma_image_in_SO3 by auto
  have gQ_SO3: "set (map sigma gQ) \<subseteq> SO3"
    using gQ sigma_image_in_SO3 by auto
  have source_disj: "pairwise_disjoint (?P @ ?Q)"
    using hausdorff_lift_pairwise_disjoint[OF disj_all all_sub] by simp
  have trans_disjP: "pairwise_disjoint (map2 hausdorff_sigma_image_set gP ?P)"
    by (rule hausdorff_translated_lift_pairwise_disjoint[OF lenP gP P0_sub disj_imP])
  have trans_disjQ: "pairwise_disjoint (map2 hausdorff_sigma_image_set gQ ?Q)"
    by (rule hausdorff_translated_lift_pairwise_disjoint[OF lenQ gQ Q0_sub disj_imQ])
  have P_sub_X: "\<forall>i < length ?P. ?P ! i \<subseteq> sphere2 - bad_set_D"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?P"
    have "P0 ! i \<subseteq> carrier F2"
      using P0_sub i by simp
    thus "?P ! i \<subseteq> sphere2 - bad_set_D"
      using i hausdorff_lift_subset_X by simp
  qed
  have Q_sub_X: "\<forall>i < length ?Q. ?Q ! i \<subseteq> sphere2 - bad_set_D"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?Q"
    have "Q0 ! i \<subseteq> carrier F2"
      using Q0_sub i by simp
    thus "?Q ! i \<subseteq> sphere2 - bad_set_D"
      using i hausdorff_lift_subset_X by simp
  qed
  have source_cover': "sphere2 - bad_set_D =
      (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
  proof (rule subset_antisym)
    show "sphere2 - bad_set_D \<subseteq>
        (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
    proof
      fix x
      assume x: "x \<in> sphere2 - bad_set_D"
      interpret G: group F2
        by (rule free_group_is_group)
      from hausdorff_rep_in_orbit[OF x] obtain r
        where r: "r \<in> carrier F2" and rep_eq: "hausdorff_rep x = sigma r x"
        unfolding sigma_sphere_minus_bad_action.orbit_def by blast
      define h where "h = inv\<^bsub>F2\<^esub> r"
      have h: "h \<in> carrier F2"
        unfolding h_def by (rule G.inv_closed[OF r])
      have x_eq: "x = sigma h (hausdorff_rep x)"
        unfolding h_def using rep_eq sigma_inverse_left[OF r] by simp
      from source_cover0 h have h_cases:
        "h \<in> (\<Union>i<length P0. P0 ! i) \<or> h \<in> (\<Union>i<length Q0. Q0 ! i)"
        by blast
      thus "x \<in> (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
      proof
        assume "h \<in> (\<Union>i<length P0. P0 ! i)"
        then obtain i where i: "i < length P0" and hP: "h \<in> P0 ! i"
          by blast
        have "x \<in> hausdorff_lift (P0 ! i)"
          unfolding hausdorff_lift_def using hP x x_eq by blast
        hence "x \<in> ?P ! i"
          using i by simp
        hence "x \<in> (\<Union>i<length ?P. ?P ! i)"
          using i by auto
        thus ?thesis
          by blast
      next
        assume "h \<in> (\<Union>i<length Q0. Q0 ! i)"
        then obtain i where i: "i < length Q0" and hQ: "h \<in> Q0 ! i"
          by blast
        have "x \<in> hausdorff_lift (Q0 ! i)"
          unfolding hausdorff_lift_def using hQ x x_eq by blast
        hence "x \<in> ?Q ! i"
          using i by simp
        hence "x \<in> (\<Union>i<length ?Q. ?Q ! i)"
          using i by auto
        thus ?thesis
          by blast
      qed
    qed
    show "(\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)
        \<subseteq> sphere2 - bad_set_D"
      using P_sub_X Q_sub_X by auto
  qed
  have coverP': "sphere2 - bad_set_D =
      (\<Union>i<length ?P. hausdorff_sigma_image_set (gP ! i) (?P ! i))"
    using hausdorff_lift_cover[OF lenP gP P0_sub coverP] by simp
  have coverQ': "sphere2 - bad_set_D =
      (\<Union>i<length ?Q. hausdorff_sigma_image_set (gQ ! i) (?Q ! i))"
    using hausdorff_lift_cover[OF lenQ gQ Q0_sub coverQ] by simp
  show ?thesis
    apply (rule exI[of _ ?P])
    apply (rule exI[of _ ?Q])
    apply (rule exI[of _ gP])
    apply (rule exI[of _ gQ])
    using lenP' lenQ' gP gQ gP_SO3 gQ_SO3 source_disj trans_disjP trans_disjQ
      P_sub_X Q_sub_X source_cover' coverP' coverQ'
    by blast
qed

theorem hausdorff_paradoxical:
  "sigma_sphere_minus_bad_action.paradoxical (sphere2 - bad_set_D)"
proof -
  from hausdorff_paradox_strong obtain P Q :: "(real^3) set list"
    and gP gQ :: "((bool \<times> gen2) list) list"
    where "length P = length gP" and "length Q = length gQ"
      and "set gP \<subseteq> carrier F2" and "set gQ \<subseteq> carrier F2"
      and "pairwise_disjoint (P @ Q)"
      and "pairwise_disjoint (map2 hausdorff_sigma_image_set gP P)"
      and "pairwise_disjoint (map2 hausdorff_sigma_image_set gQ Q)"
      and P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D"
      and Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D"
      and coverP: "sphere2 - bad_set_D =
        (\<Union>i<length P. hausdorff_sigma_image_set (gP ! i) (P ! i))"
      and coverQ: "sphere2 - bad_set_D =
        (\<Union>i<length Q. hausdorff_sigma_image_set (gQ ! i) (Q ! i))"
    by auto
  have pieces_sub: "(\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)
      \<subseteq> sphere2 - bad_set_D"
    using P_sub Q_sub by auto
  have imageP_eq: "map2 sigma_sphere_minus_bad_action.image_set gP P =
      map2 hausdorff_sigma_image_set gP P"
    by (rule map2_hausdorff_sigma_image_set_eq)
  have imageQ_eq: "map2 sigma_sphere_minus_bad_action.image_set gQ Q =
      map2 hausdorff_sigma_image_set gQ Q"
    by (rule map2_hausdorff_sigma_image_set_eq)
  have coverP_action: "sphere2 - bad_set_D =
      (\<Union>i<length P. sigma_sphere_minus_bad_action.image_set (gP ! i) (P ! i))"
    using coverP
    by (simp add: hausdorff_sigma_image_set_def sigma_sphere_minus_bad_action.image_set_def)
  have coverQ_action: "sphere2 - bad_set_D =
      (\<Union>i<length Q. sigma_sphere_minus_bad_action.image_set (gQ ! i) (Q ! i))"
    using coverQ
    by (simp add: hausdorff_sigma_image_set_def sigma_sphere_minus_bad_action.image_set_def)
  have imageP_disj_action: "pairwise_disjoint (map2 sigma_sphere_minus_bad_action.image_set gP P)"
    using \<open>pairwise_disjoint (map2 hausdorff_sigma_image_set gP P)\<close> imageP_eq
    by metis
  have imageQ_disj_action: "pairwise_disjoint (map2 sigma_sphere_minus_bad_action.image_set gQ Q)"
    using \<open>pairwise_disjoint (map2 hausdorff_sigma_image_set gQ Q)\<close> imageQ_eq
    by metis
  show ?thesis
    unfolding sigma_sphere_minus_bad_action.paradoxical_def
    apply (rule exI[of _ P])
    apply (rule exI[of _ Q])
    apply (rule exI[of _ gP])
    apply (rule exI[of _ gQ])
    using \<open>length P = length gP\<close> \<open>length Q = length gQ\<close>
      \<open>set gP \<subseteq> carrier F2\<close> \<open>set gQ \<subseteq> carrier F2\<close>
      \<open>pairwise_disjoint (P @ Q)\<close>
      imageP_disj_action imageQ_disj_action pieces_sub coverP_action coverQ_action
    by blast
qed

theorem hausdorff_paradox_rot_strong:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q) \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
        (sphere2 - bad_set_D) =
          (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  from hausdorff_paradox_strong obtain P Q :: "(real^3) set list"
    and wP wQ :: "((bool \<times> gen2) list) list"
    where lenP: "length P = length wP"
      and lenQ: "length Q = length wQ"
      and wP_SO3: "set (map sigma wP) \<subseteq> SO3"
      and wQ_SO3: "set (map sigma wQ) \<subseteq> SO3"
      and disj: "pairwise_disjoint (P @ Q)"
      and disjP: "pairwise_disjoint (map2 hausdorff_sigma_image_set wP P)"
      and disjQ: "pairwise_disjoint (map2 hausdorff_sigma_image_set wQ Q)"
      and P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D"
      and Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D"
      and source_cover: "sphere2 - bad_set_D =
        (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      and coverP: "sphere2 - bad_set_D =
        (\<Union>i<length P. hausdorff_sigma_image_set (wP ! i) (P ! i))"
      and coverQ: "sphere2 - bad_set_D =
        (\<Union>i<length Q. hausdorff_sigma_image_set (wQ ! i) (Q ! i))"
    by auto
  let ?gP = "map sigma wP"
  let ?gQ = "map sigma wQ"
  have map2P_eq:
    "map2 (\<lambda>g A. g ` A) ?gP P = map2 hausdorff_sigma_image_set wP P"
    using lenP
  proof (induction wP arbitrary: P)
    case Nil
    then show ?case by simp
  next
    case (Cons w ws)
    then obtain A Ps where P: "P = A # Ps"
      by (cases P) auto
    with Cons show ?case
      by (simp add: hausdorff_sigma_image_set_def)
  qed
  have map2Q_eq:
    "map2 (\<lambda>g A. g ` A) ?gQ Q = map2 hausdorff_sigma_image_set wQ Q"
    using lenQ
  proof (induction wQ arbitrary: Q)
    case Nil
    then show ?case by simp
  next
    case (Cons w ws)
    then obtain A Qs where Q: "Q = A # Qs"
      by (cases Q) auto
    with Cons show ?case
      by (simp add: hausdorff_sigma_image_set_def)
  qed
  have disjP_rot: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) ?gP P)"
    using disjP map2P_eq by simp
  have disjQ_rot: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) ?gQ Q)"
    using disjQ map2Q_eq by simp
  have coverP_rot: "sphere2 - bad_set_D =
      (\<Union>i<length P. (?gP ! i) ` (P ! i))"
    using coverP lenP by (simp add: hausdorff_sigma_image_set_def)
  have coverQ_rot: "sphere2 - bad_set_D =
      (\<Union>i<length Q. (?gQ ! i) ` (Q ! i))"
    using coverQ lenQ by (simp add: hausdorff_sigma_image_set_def)
  show ?thesis
    apply (rule exI[of _ P])
    apply (rule exI[of _ Q])
    apply (rule exI[of _ ?gP])
    apply (rule exI[of _ ?gQ])
    using lenP lenQ wP_SO3 wQ_SO3 disj disjP_rot disjQ_rot
      P_sub Q_sub source_cover coverP_rot coverQ_rot
    by simp
qed

theorem hausdorff_paradox:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (sphere2 - bad_set_D) =
         (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
        (sphere2 - bad_set_D) =
          (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  from hausdorff_paradox_strong obtain P Q :: "(real^3) set list"
    and wP wQ :: "((bool \<times> gen2) list) list"
    where lenP: "length P = length wP"
      and lenQ: "length Q = length wQ"
      and wP_SO3: "set (map sigma wP) \<subseteq> SO3"
      and wQ_SO3: "set (map sigma wQ) \<subseteq> SO3"
      and P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D"
      and Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D"
      and coverP: "sphere2 - bad_set_D =
        (\<Union>i<length P. hausdorff_sigma_image_set (wP ! i) (P ! i))"
      and coverQ: "sphere2 - bad_set_D =
        (\<Union>i<length Q. hausdorff_sigma_image_set (wQ ! i) (Q ! i))"
    by auto
  let ?gP = "map sigma wP"
  let ?gQ = "map sigma wQ"
  have coverP_rot: "sphere2 - bad_set_D =
      (\<Union>i<length P. (?gP ! i) ` (P ! i))"
    using coverP lenP by (simp add: hausdorff_sigma_image_set_def)
  have coverQ_rot: "sphere2 - bad_set_D =
      (\<Union>i<length Q. (?gQ ! i) ` (Q ! i))"
    using coverQ lenQ by (simp add: hausdorff_sigma_image_set_def)
  show ?thesis
    apply (rule exI[of _ P])
    apply (rule exI[of _ Q])
    apply (rule exI[of _ ?gP])
    apply (rule exI[of _ ?gQ])
    using lenP lenQ wP_SO3 wQ_SO3 P_sub Q_sub coverP_rot coverQ_rot
    by simp
qed

end
