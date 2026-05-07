(*  Title:       Sphere_Decomposition.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    Paradoxical decomposition of the entire two-sphere
    \<open>S\<^sup>2\<close>, by absorbing the "bad set" of fixed points via a
    standard translation argument.

    Sketch (the classical absorption argument):
      pick a rotation \<open>R \<in> SO(3)\<close> of infinite order whose axis
      avoids the bad set and such that \<open>D\<close>, \<open>R D\<close>,
      \<open>R\<^sup>2 D\<close>, \<dots> are pairwise disjoint;
      let \<open>E = D \<union> R D \<union> R\<^sup>2 D \<union> \<dots>\<close>;
      then \<open>S\<^sup>2 \<setminus> D\<close> and \<open>S\<^sup>2\<close> are
      equidecomposable via \<open>E \<mapsto> R E\<close>.

    The absorbing rotation is constructed by avoiding countably many
    forbidden collision angles.
*)

theory Sphere_Decomposition
  imports Hausdorff_Paradox
begin

text \<open>
  Equidecomposability of \<open>S\<^sup>2 \<setminus> D\<close> and \<open>S\<^sup>2\<close>.
\<close>

definition Rz_angle_mat :: "real \<Rightarrow> real^3^3" where
  "Rz_angle_mat t = vector [
     vector [cos t, - sin t, 0],
     vector [sin t, cos t, 0],
     vector [0, 0, 1]]"

definition Rz_angle :: "real \<Rightarrow> real^3 \<Rightarrow> real^3" where
  "Rz_angle t v = Rz_angle_mat t *v v"

definition e1_3 :: "real^3" where
  "e1_3 = vector [1, 0, 0]"

definition e3_3 :: "real^3" where
  "e3_3 = vector [0, 0, 1]"

lemma Rz_angle_mat_orthogonal: "orthogonal_matrix (Rz_angle_mat t)"
  unfolding orthogonal_matrix Rz_angle_mat_def
  by (simp add: matrix_matrix_mult_def transpose_def mat_def vec_eq_iff vector_def sum_3 forall_3
      power2_eq_square algebra_simps)

lemma det_Rz_angle_mat [simp]: "det (Rz_angle_mat t) = 1"
  unfolding Rz_angle_mat_def
  by (simp add: det_3 vector_def power2_eq_square algebra_simps)

lemma Rz_angle_in_SO3: "Rz_angle t \<in> SO3"
  unfolding SO3_def rotation_def Rz_angle_def
  by (simp add: orthogonal_transformation_matrix Rz_angle_mat_orthogonal matrix_vector_mul_linear)

lemma Rz_angle_mat_add:
  "Rz_angle_mat a ** Rz_angle_mat b = Rz_angle_mat (a + b)"
  unfolding Rz_angle_mat_def
  by (simp add: matrix_matrix_mult_def vec_eq_iff vector_def sum_3 forall_3
      cos_add sin_add algebra_simps)

lemma Rz_angle_compose:
  "Rz_angle a \<circ> Rz_angle b = Rz_angle (a + b)"
  by (rule ext) (simp add: Rz_angle_def matrix_vector_mul_assoc Rz_angle_mat_add)

lemma Rz_angle_funpow:
  "(Rz_angle t ^^ n) = Rz_angle (real n * t)"
proof (induction n)
  case 0
  show ?case
    by (rule ext) (simp add: Rz_angle_def Rz_angle_mat_def mat_def matrix_vector_mult_def
        vec_eq_iff vector_def forall_3 sum_3)
next
  case (Suc n)
  have "(Rz_angle t ^^ Suc n) = Rz_angle t \<circ> Rz_angle (real n * t)"
    using Suc.IH by simp
  also have "\<dots> = Rz_angle (t + real n * t)"
    by (rule Rz_angle_compose)
  also have "t + real n * t = real (Suc n) * t"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma Rz_angle_components [simp]:
  "(Rz_angle t x) $ 1 = cos t * x $ 1 - sin t * x $ 2"
  "(Rz_angle t x) $ 2 = sin t * x $ 1 + cos t * x $ 2"
  "(Rz_angle t x) $ 3 = x $ 3"
  by (simp_all add: Rz_angle_def Rz_angle_mat_def matrix_vector_mult_def
      vector_def sum_3)

lemma Rz_angle_eq_non_axis_sin_cos:
  assumes "Rz_angle a x = Rz_angle b x" and "x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0"
  shows "sin a = sin b \<and> cos a = cos b"
proof -
  let ?X = "x $ 1"
  let ?Y = "x $ 2"
  let ?C = "cos a - cos b"
  let ?S = "sin a - sin b"
  have comp1: "(Rz_angle a x) $ 1 = (Rz_angle b x) $ 1"
    using arg_cong[OF assms(1), of "\<lambda>v. v $ 1"] .
  have comp2: "(Rz_angle a x) $ 2 = (Rz_angle b x) $ 2"
    using arg_cong[OF assms(1), of "\<lambda>v. v $ 2"] .
  have eq1: "?C * ?X - ?S * ?Y = 0"
    using comp1 by (simp add: algebra_simps)
  have eq2: "?S * ?X + ?C * ?Y = 0"
    using comp2 by (simp add: algebra_simps)
  have nonzero: "?X\<^sup>2 + ?Y\<^sup>2 \<noteq> 0"
    using assms(2) by (simp add: power2_eq_square sum_squares_eq_zero_iff)
  have C_eq: "?C * (?X\<^sup>2 + ?Y\<^sup>2) =
      (?C * ?X - ?S * ?Y) * ?X + (?S * ?X + ?C * ?Y) * ?Y"
    by (simp add: power2_eq_square algebra_simps)
  have Cprod0: "?C * (?X\<^sup>2 + ?Y\<^sup>2) = 0"
    using C_eq eq1 eq2 by simp
  hence C_or: "?C = 0 \<or> ?X\<^sup>2 + ?Y\<^sup>2 = 0"
    by (simp add: mult_eq_0_iff)
  have C0: "?C = 0"
    using C_or nonzero by blast
  have S_eq: "?S * (?X\<^sup>2 + ?Y\<^sup>2) =
      (?S * ?X + ?C * ?Y) * ?X - (?C * ?X - ?S * ?Y) * ?Y"
    by (simp add: power2_eq_square algebra_simps)
  have Sprod0: "?S * (?X\<^sup>2 + ?Y\<^sup>2) = 0"
    using S_eq eq1 eq2 by simp
  hence S_or: "?S = 0 \<or> ?X\<^sup>2 + ?Y\<^sup>2 = 0"
    by (simp add: mult_eq_0_iff)
  have S0: "?S = 0"
    using S_or nonzero by blast
  from S0 C0 show ?thesis
    by simp
qed

lemma Rz_angle_collision_angles_countable:
  assumes nonaxis: "x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0"
  shows "countable {t. Rz_angle t x = y}"
proof (cases "{t. Rz_angle t x = y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where a: "Rz_angle a x = y"
    by auto
  have subset: "{t. Rz_angle t x = y} \<subseteq> (\<lambda>n::int. a + 2 * pi * n) ` UNIV"
  proof
    fix t
    assume t: "t \<in> {t. Rz_angle t x = y}"
    hence eq: "Rz_angle t x = Rz_angle a x"
      using a by simp
    have trig: "sin t = sin a \<and> cos t = cos a"
      by (rule Rz_angle_eq_non_axis_sin_cos[OF eq nonaxis])
    have "\<exists>n::int. t = a + 2 * pi * n"
      using iffD1[OF sin_cos_eq_iff[of t a] trig] .
    then obtain n :: int where n: "t = a + 2 * pi * n"
      by blast
    show "t \<in> (\<lambda>n::int. a + 2 * pi * n) ` UNIV"
      using n by simp
  qed
  have "countable ((\<lambda>n::int. a + 2 * pi * n) ` UNIV)"
    by simp
  thus ?thesis
    by (rule countable_subset[OF subset])
qed

lemma Rz_angle_scaled_collision_angles_countable:
  assumes "k > 0" and nonaxis: "x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0"
  shows "countable {t. Rz_angle (real k * t) x = y}"
proof -
  let ?f = "\<lambda>t::real. real k * t"
  let ?A = "{u. Rz_angle u x = y}"
  have count_A: "countable ?A"
    by (rule Rz_angle_collision_angles_countable[OF nonaxis])
  have inj_f: "inj_on ?f UNIV"
    using assms(1) by (auto simp: inj_on_def)
  have count_pre: "countable {t \<in> UNIV. ?f t \<in> ?A}"
    by (rule countable_image_inj_gen[OF inj_f count_A])
  thus ?thesis
    by simp
qed

lemma e1_3_in_sphere2: "e1_3 \<in> sphere2"
  by (simp add: e1_3_def sphere2_def norm_eq_1 inner_vec_def sum_3 vector_def)

lemma e1_3_nonaxis: "e1_3 $ 1 \<noteq> 0 \<or> e1_3 $ 2 \<noteq> 0"
  by (simp add: e1_3_def)

lemma e3_3_in_sphere2: "e3_3 \<in> sphere2"
  by (simp add: e3_3_def sphere2_def norm_eq_1 inner_vec_def sum_3 vector_def)

lemma z_axis_sphere2_cases:
  assumes "x \<in> sphere2" and "x $ 1 = 0" and "x $ 2 = 0"
  shows "x = e3_3 \<or> x = - e3_3"
proof -
  have x3_sq: "(x $ 3)\<^sup>2 = 1"
    using assms unfolding sphere2_def
    by (simp add: norm_eq_1 inner_vec_def sum_3 power2_eq_square)
  hence "x $ 3 = 1 \<or> x $ 3 = -1"
    by (simp add: power2_eq_1_iff)
  thus ?thesis
    using assms(2,3)
    by (auto simp: e3_3_def vec_eq_iff vector_def forall_3)
qed

lemma SO3_funpow:
  assumes "R \<in> SO3"
  shows "(R ^^ n) \<in> SO3"
proof (induction n)
  case 0
  show ?case
    using id_in_SO3 by (simp add: id_def)
next
  case (Suc n)
  have "R \<circ> (R ^^ n) \<in> SO3"
    by (rule SO3_closed_compose[OF assms Suc.IH])
  thus ?case
    by (simp add: o_def)
qed

lemma SO3_inj:
  assumes "f \<in> SO3"
  shows "inj f"
proof -
  have "orthogonal_transformation f"
    using assms unfolding SO3_def rotation_def by auto
  thus ?thesis
    by (rule orthogonal_transformation_inj)
qed

lemma SO3_surj:
  assumes "f \<in> SO3"
  shows "surj f"
proof -
  have "orthogonal_transformation f"
    using assms unfolding SO3_def rotation_def by auto
  thus ?thesis
    by (rule orthogonal_transformation_surj)
qed

lemma SO3_linear:
  assumes "f \<in> SO3"
  shows "linear f"
proof -
  have "orthogonal_transformation f"
    using assms unfolding SO3_def rotation_def by auto
  thus ?thesis
    by (rule orthogonal_transformation_linear)
qed

lemma SO3_inverse:
  assumes "f \<in> SO3"
  shows "Hilbert_Choice.inv f \<in> SO3"
proof -
  have f_orth: "orthogonal_transformation f"
    and f_det: "det (matrix f) = 1"
    using assms unfolding SO3_def rotation_def by auto
  have inv_orth: "orthogonal_transformation (Hilbert_Choice.inv f)"
    by (rule orthogonal_transformation_inv[OF f_orth])
  have f_lin: "linear f"
    by (rule orthogonal_transformation_linear[OF f_orth])
  have inv_lin: "linear (Hilbert_Choice.inv f)"
    by (rule orthogonal_transformation_linear[OF inv_orth])
  have surj_f: "surj f"
    by (rule orthogonal_transformation_surj[OF f_orth])
  have comp_id: "f \<circ> Hilbert_Choice.inv f = id"
    using surj_f by (auto simp: fun_eq_iff surj_f_inv_f)
  have "det (matrix (f \<circ> Hilbert_Choice.inv f)) =
      det (matrix f) * det (matrix (Hilbert_Choice.inv f))"
    using matrix_compose[OF inv_lin f_lin] by (simp add: det_mul)
  also have "\<dots> = det (matrix (Hilbert_Choice.inv f))"
    using f_det by simp
  finally have "det (matrix (Hilbert_Choice.inv f)) = 1"
    using comp_id by simp
  with inv_orth show ?thesis
    unfolding SO3_def rotation_def by simp
qed

lemma conjugate_funpow:
  assumes bijS: "bij S"
  shows "((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ n) =
    S \<circ> (R ^^ n) \<circ> Hilbert_Choice.inv S"
proof (induction n)
  case 0
  show ?case
    using bijS by (auto simp: fun_eq_iff bij_is_surj surj_f_inv_f)
next
  case (Suc n)
  have injS: "inj S"
    using bijS by (simp add: bij_is_inj)
  show ?case
  proof (rule ext)
    fix x
    have n_eq: "((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ n) x =
        S ((R ^^ n) (Hilbert_Choice.inv S x))"
      using fun_cong[OF Suc.IH, of x] by (simp add: o_def)
    have "((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ Suc n) x =
        S (R (Hilbert_Choice.inv S (((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ n) x)))"
      by simp
    also have "\<dots> = S (R (Hilbert_Choice.inv S
        (S ((R ^^ n) (Hilbert_Choice.inv S x)))))"
      using n_eq by simp
    also have "\<dots> = S ((R ^^ Suc n) (Hilbert_Choice.inv S x))"
      using injS by (simp add: inv_f_f)
    finally show "((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ Suc n) x =
        (S \<circ> (R ^^ Suc n) \<circ> Hilbert_Choice.inv S) x"
      by simp
  qed
qed

lemma conjugate_funpow_image:
  assumes bijS: "bij S"
  shows "((S \<circ> R \<circ> Hilbert_Choice.inv S) ^^ n) ` D =
    S ` ((R ^^ n) ` (Hilbert_Choice.inv S ` D))"
  using conjugate_funpow[OF bijS, of n R]
  by auto

lemma exists_antipodal_axis_avoiding_countable:
  assumes count_D: "countable D"
  shows "\<exists>a \<in> sphere2. a \<notin> D \<and> - a \<notin> D"
proof -
  let ?A = "D \<union> uminus ` D"
  have count_A: "countable ?A"
    using count_D by simp
  let ?bad = "(\<Union>y \<in> ?A. {t. Rz_angle t e1_3 = y})"
  have count_bad: "countable ?bad"
  proof (intro countable_UN count_A)
    fix y
    assume "y \<in> ?A"
    show "countable {t. Rz_angle t e1_3 = y}"
      by (rule Rz_angle_collision_angles_countable[OF e1_3_nonaxis])
  qed
  obtain t where t_not_bad: "t \<notin> ?bad"
    using real_interval_avoid_countable_set[OF zero_less_one count_bad] by blast
  define a where "a = Rz_angle t e1_3"
  have a_sphere: "a \<in> sphere2"
    unfolding a_def
    by (rule rotation_preserves_sphere2[OF Rz_angle_in_SO3 e1_3_in_sphere2])
  have a_not_A: "a \<notin> ?A"
    using t_not_bad unfolding a_def by blast
  hence a_not_D: "a \<notin> D"
    by simp
  have neg_a_not_D: "- a \<notin> D"
  proof
    assume "- a \<in> D"
    hence "uminus (- a) \<in> uminus ` D"
      by blast
    hence "a \<in> uminus ` D"
      by simp
    with a_not_A show False
      by simp
  qed
  from a_sphere a_not_D neg_a_not_D show ?thesis
    by blast
qed

lemma exists_Rz_angle_absorbing:
  assumes count_D: "countable D"
    and nonaxis: "\<And>x. x \<in> D \<Longrightarrow> x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0"
  shows "\<exists>t. \<forall>n m. n \<noteq> m \<longrightarrow> ((Rz_angle t ^^ n) ` D) \<inter> ((Rz_angle t ^^ m) ` D) = {}"
proof -
  let ?bad = "(\<Union>k \<in> {k::nat. k > 0}. \<Union>x \<in> D. \<Union>y \<in> D.
    {t. Rz_angle (real k * t) x = y})"
  have count_bad: "countable ?bad"
  proof (intro countable_UN countable_Collect countableI_type count_D)
    fix k x y
    assume "k \<in> {k::nat. 0 < k}" and "x \<in> D" and "y \<in> D"
    thus "countable {t. Rz_angle (real k * t) x = y}"
      by (intro Rz_angle_scaled_collision_angles_countable nonaxis) auto
  qed
  obtain t where t_not_bad: "t \<notin> ?bad"
    using real_interval_avoid_countable_set[OF zero_less_one count_bad] by blast
  have disj: "((Rz_angle t ^^ n) ` D) \<inter> ((Rz_angle t ^^ m) ` D) = {}" if "n \<noteq> m" for n m
  proof (rule ccontr)
    assume "((Rz_angle t ^^ n) ` D) \<inter> ((Rz_angle t ^^ m) ` D) \<noteq> {}"
    then obtain x y z where x: "x \<in> D" and y: "y \<in> D"
      and z: "z = (Rz_angle t ^^ n) x" "z = (Rz_angle t ^^ m) y"
      by blast
    have False if nm: "n < m"
    proof -
      let ?k = "m - n"
      have k_pos: "?k > 0"
        using nm by simp
      have m_eq: "m = n + ?k"
        using nm by simp
      have eq: "(Rz_angle t ^^ n) x = (Rz_angle t ^^ m) y"
        using z by simp
      have tail: "(Rz_angle t ^^ m) y =
          (Rz_angle t ^^ n) ((Rz_angle t ^^ ?k) y)"
        using m_eq by (metis comp_apply funpow_add)
      have "(Rz_angle t ^^ n) x = (Rz_angle t ^^ n) ((Rz_angle t ^^ ?k) y)"
        using eq tail by simp
      moreover have "inj (Rz_angle t ^^ n)"
        by (rule SO3_inj[OF SO3_funpow[OF Rz_angle_in_SO3]])
      ultimately have x_eq: "x = (Rz_angle t ^^ ?k) y"
        by (meson injD)
      have "Rz_angle (real ?k * t) y = x"
        using x_eq Rz_angle_funpow[of ?k t] by (simp add: fun_eq_iff)
      hence "t \<in> {u. Rz_angle (real ?k * u) y = x}"
        by simp
      hence "t \<in> ?bad"
        using k_pos x y by blast
      with t_not_bad show False
        by contradiction
    qed
    moreover have False if mn: "m < n"
    proof -
      let ?k = "n - m"
      have k_pos: "?k > 0"
        using mn by simp
      have n_eq: "n = m + ?k"
        using mn by simp
      have eq: "(Rz_angle t ^^ m) y = (Rz_angle t ^^ n) x"
        using z by simp
      have tail: "(Rz_angle t ^^ n) x =
          (Rz_angle t ^^ m) ((Rz_angle t ^^ ?k) x)"
        using n_eq by (metis comp_apply funpow_add)
      have "(Rz_angle t ^^ m) y = (Rz_angle t ^^ m) ((Rz_angle t ^^ ?k) x)"
        using eq tail by simp
      moreover have "inj (Rz_angle t ^^ m)"
        by (rule SO3_inj[OF SO3_funpow[OF Rz_angle_in_SO3]])
      ultimately have y_eq: "y = (Rz_angle t ^^ ?k) x"
        by (meson injD)
      have "Rz_angle (real ?k * t) x = y"
        using y_eq Rz_angle_funpow[of ?k t] by (simp add: fun_eq_iff)
      hence "t \<in> {u. Rz_angle (real ?k * u) x = y}"
        by simp
      hence "t \<in> ?bad"
        using k_pos x y by blast
      with t_not_bad show False
        by contradiction
    qed
    ultimately show False
      using that by linarith
  qed
  show ?thesis
    using disj by blast
qed

lemma exists_absorbing_rotation:
  "\<exists>R \<in> SO3. \<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` bad_set_D) \<inter> ((R^^m) ` bad_set_D) = {}"
proof -
  obtain a where a_sphere: "a \<in> sphere2" and a_not_D: "a \<notin> bad_set_D"
    and neg_a_not_D: "- a \<notin> bad_set_D"
    using exists_antipodal_axis_avoiding_countable[OF bad_set_D_countable] by blast
  have norm_eq: "norm e3_3 = norm a"
    using e3_3_in_sphere2 a_sphere unfolding sphere2_def by simp
  have card3: "2 \<le> CARD(3)"
    by simp
  obtain S where S_orth: "orthogonal_transformation S"
    and S_det: "det (matrix S) = 1"
    and S_e3: "S e3_3 = a"
    using rotation_exists[OF card3 norm_eq] by blast
  have S_SO3: "S \<in> SO3"
    using S_orth S_det unfolding SO3_def rotation_def by simp
  have invS_SO3: "Hilbert_Choice.inv S \<in> SO3"
    by (rule SO3_inverse[OF S_SO3])
  have S_bij: "bij S"
    by (rule orthogonal_transformation_bij[OF S_orth])
  have S_inj: "inj S"
    using S_bij by (simp add: bij_is_inj)
  have S_surj: "surj S"
    using S_bij by (simp add: bij_is_surj)
  have S_lin: "linear S"
    by (rule orthogonal_transformation_linear[OF S_orth])
  let ?D' = "Hilbert_Choice.inv S ` bad_set_D"
  have count_D': "countable ?D'"
    using bad_set_D_countable by simp
  have nonaxis_D': "x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0" if xD: "x \<in> ?D'" for x
  proof (rule ccontr)
    assume "\<not> (x $ 1 \<noteq> 0 \<or> x $ 2 \<noteq> 0)"
    hence x1: "x $ 1 = 0" and x2: "x $ 2 = 0"
      by auto
    from xD obtain d where dD: "d \<in> bad_set_D" and x_def: "x = Hilbert_Choice.inv S d"
      by auto
    have d_sphere: "d \<in> sphere2"
      using dD bad_set_D_subset by auto
    have x_sphere: "x \<in> sphere2"
      unfolding x_def
      by (rule rotation_preserves_sphere2[OF invS_SO3 d_sphere])
    have axis_cases: "x = e3_3 \<or> x = - e3_3"
      by (rule z_axis_sphere2_cases[OF x_sphere x1 x2])
    have Sx_d: "S x = d"
      using x_def S_surj by (simp add: surj_f_inv_f)
    from axis_cases show False
    proof
      assume "x = e3_3"
      hence "d = a"
        using Sx_d S_e3 by simp
      with dD a_not_D show False
        by simp
    next
      assume "x = - e3_3"
      hence "S x = - a"
        using S_lin S_e3 by (simp add: linear_neg)
      hence "d = - a"
        using Sx_d by simp
      with dD neg_a_not_D show False
        by simp
    qed
  qed
  obtain t where t_disj:
    "\<forall>n m. n \<noteq> m \<longrightarrow>
      ((Rz_angle t ^^ n) ` ?D') \<inter> ((Rz_angle t ^^ m) ` ?D') = {}"
    using exists_Rz_angle_absorbing[OF count_D' nonaxis_D'] by blast
  let ?R = "S \<circ> Rz_angle t \<circ> Hilbert_Choice.inv S"
  have inner_SO3: "Rz_angle t \<circ> Hilbert_Choice.inv S \<in> SO3"
    by (rule SO3_closed_compose[OF Rz_angle_in_SO3 invS_SO3])
  have R_SO3: "?R \<in> SO3"
  proof -
    have "S \<circ> (Rz_angle t \<circ> Hilbert_Choice.inv S) \<in> SO3"
      by (rule SO3_closed_compose[OF S_SO3 inner_SO3])
    thus ?thesis
      by (simp add: o_assoc)
  qed
  have R_disj: "((?R ^^ n) ` bad_set_D) \<inter> ((?R ^^ m) ` bad_set_D) = {}"
    if nm: "n \<noteq> m" for n m
  proof -
    have n_img: "((?R ^^ n) ` bad_set_D) =
        S ` ((Rz_angle t ^^ n) ` ?D')"
      by (rule conjugate_funpow_image[OF S_bij])
    have m_img: "((?R ^^ m) ` bad_set_D) =
        S ` ((Rz_angle t ^^ m) ` ?D')"
      by (rule conjugate_funpow_image[OF S_bij])
    have z_disj: "((Rz_angle t ^^ n) ` ?D') \<inter> ((Rz_angle t ^^ m) ` ?D') = {}"
      using t_disj nm by blast
    show ?thesis
      unfolding n_img m_img
      using z_disj S_inj by (auto dest: injD)
  qed
  from R_SO3 R_disj show ?thesis
    by blast
qed

lemma SO3_funpow_preserves_sphere2:
  assumes "R \<in> SO3" and "x \<in> sphere2"
  shows "(R ^^ n) x \<in> sphere2"
  by (rule rotation_preserves_sphere2[OF SO3_funpow[OF assms(1)] assms(2)])

lemma funpow_Suc_image:
  "((R ^^ Suc n) ` S) = R ` ((R ^^ n) ` S)"
  by auto

lemma absorbing_rotation_shift:
  assumes disj: "\<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` D) \<inter> ((R^^m) ` D) = {}"
  defines "E \<equiv> (\<Union>n. (R^^n) ` D)"
  shows "R ` E = E - D"
proof
  show "R ` E \<subseteq> E - D"
  proof
    fix y
    assume "y \<in> R ` E"
    then obtain x n d where x: "x = (R ^^ n) d" and d: "d \<in> D" and y: "y = R x"
      unfolding E_def by blast
    have y_pow: "y \<in> (R ^^ Suc n) ` D"
      using x d y by auto
    hence "y \<in> E"
      unfolding E_def by blast
    moreover have "y \<notin> D"
    proof
      assume "y \<in> D"
      hence "y \<in> (R ^^ 0) ` D"
        by simp
      with y_pow have "((R ^^ Suc n) ` D) \<inter> ((R ^^ 0) ` D) \<noteq> {}"
        by blast
      moreover have "Suc n \<noteq> 0"
        by simp
      ultimately show False
        using disj by blast
    qed
    ultimately show "y \<in> E - D"
      by simp
  qed
next
  show "E - D \<subseteq> R ` E"
  proof
    fix y
    assume y: "y \<in> E - D"
    then obtain n d where y_pow: "y = (R ^^ n) d" and d: "d \<in> D"
      unfolding E_def by blast
    from y have y_not_D: "y \<notin> D"
      by simp
    show "y \<in> R ` E"
    proof (cases n)
      case 0
      with y_pow d y_not_D show ?thesis
        by simp
    next
      case (Suc k)
      have "(R ^^ k) d \<in> E"
        unfolding E_def using d by blast
      moreover have "y = R ((R ^^ k) d)"
        using y_pow Suc by simp
      ultimately show ?thesis
        by blast
    qed
  qed
qed

lemma sphere2_absorb_bad_set:
  "\<exists>P Q :: (real^3) set list. \<exists>gs :: ((real^3) \<Rightarrow> (real^3)) list.
      length P = length Q \<and> length P = length gs \<and>
      set gs \<subseteq> SO3 \<and>
      sphere2 = (\<Union>i<length P. P ! i) \<and>
      (sphere2 - bad_set_D) = (\<Union>i<length Q. Q ! i) \<and>
      (\<forall>i < length P. Q ! i = (gs ! i) ` (P ! i))"
proof -
  obtain R where R_SO3: "R \<in> SO3"
    and disj: "\<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` bad_set_D) \<inter> ((R^^m) ` bad_set_D) = {}"
    using exists_absorbing_rotation by auto
  define E where "E = (\<Union>n. (R^^n) ` bad_set_D)"
  have R_E: "R ` E = E - bad_set_D"
    unfolding E_def by (rule absorbing_rotation_shift[OF disj])
  have D_subset_E: "bad_set_D \<subseteq> E"
  proof
    fix x
    assume x: "x \<in> bad_set_D"
    have "x \<in> (R ^^ 0) ` bad_set_D"
      using x by (auto simp add: image_def)
    thus "x \<in> E"
      unfolding E_def by blast
  qed
  have E_subset_sphere2: "E \<subseteq> sphere2"
  proof
    fix x
    assume "x \<in> E"
    then obtain n d where x: "x = (R ^^ n) d" and d: "d \<in> bad_set_D"
      unfolding E_def by blast
    from d have "d \<in> sphere2"
      using bad_set_D_subset by blast
    with R_SO3 x show "x \<in> sphere2"
      using SO3_funpow_preserves_sphere2 by blast
  qed
  let ?P = "[E, sphere2 - E]"
  let ?Q = "[R ` E, sphere2 - E]"
  let ?gs = "[R, id]"
  have P_union: "sphere2 = (\<Union>i<length ?P. ?P ! i)"
  proof
    show "sphere2 \<subseteq> (\<Union>i<length ?P. ?P ! i)"
    proof
      fix x
      assume x: "x \<in> sphere2"
      show "x \<in> (\<Union>i<length ?P. ?P ! i)"
      proof (cases "x \<in> E")
        case True
        then show ?thesis
          by force
      next
        case False
        with x show ?thesis
          by force
      qed
    qed
  next
    show "(\<Union>i<length ?P. ?P ! i) \<subseteq> sphere2"
    proof
      fix x
      assume x: "x \<in> (\<Union>i<length ?P. ?P ! i)"
      then obtain i where i: "i < length ?P" and xi: "x \<in> ?P ! i"
        by blast
      have "i = 0 \<or> i = 1"
        using i by auto
      thus "x \<in> sphere2"
      proof
        assume "i = 0"
        with xi E_subset_sphere2 show ?thesis
          by auto
      next
        assume "i = 1"
        with xi show ?thesis
          by auto
      qed
    qed
  qed
  have Q_union: "sphere2 - bad_set_D = (\<Union>i<length ?Q. ?Q ! i)"
  proof
    show "sphere2 - bad_set_D \<subseteq> (\<Union>i<length ?Q. ?Q ! i)"
    proof
      fix x
      assume x: "x \<in> sphere2 - bad_set_D"
      show "x \<in> (\<Union>i<length ?Q. ?Q ! i)"
      proof (cases "x \<in> E")
        case True
        with x R_E show ?thesis
          by force
      next
        case False
        with x show ?thesis
          by force
      qed
    qed
  next
    show "(\<Union>i<length ?Q. ?Q ! i) \<subseteq> sphere2 - bad_set_D"
    proof
      fix x
      assume x: "x \<in> (\<Union>i<length ?Q. ?Q ! i)"
      then obtain i where i: "i < length ?Q" and xi: "x \<in> ?Q ! i"
        by blast
      have "i = 0 \<or> i = 1"
        using i by auto
      thus "x \<in> sphere2 - bad_set_D"
      proof
        assume "i = 0"
        with xi R_E E_subset_sphere2 show ?thesis
          by auto
      next
        assume "i = 1"
        with xi D_subset_E show ?thesis
          by auto
      qed
    qed
  qed
  have image_eq: "\<forall>i < length ?P. ?Q ! i = (?gs ! i) ` (?P ! i)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?P"
    have "i = 0 \<or> i = 1"
      using i by auto
    thus "?Q ! i = (?gs ! i) ` (?P ! i)"
      by auto
  qed
  show ?thesis
    apply (rule exI[of _ ?P])
    apply (rule exI[of _ ?Q])
    apply (rule exI[of _ ?gs])
    using R_SO3 id_in_SO3 P_union Q_union image_eq
    by auto
qed

text \<open>
  Combining the Hausdorff paradox with the absorption argument yields
  the paradoxical decomposition of the full sphere.
\<close>

lemma sphere_indexed_union_append_singleton:
  fixes P :: "'a set list" and S :: "'a set"
  shows "(\<Union>i<length (P @ [S]). (P @ [S]) ! i) =
    (\<Union>i<length P. P ! i) \<union> S"
proof -
  have "(\<Union>i<length (P @ [S]). (P @ [S]) ! i) =
      (\<Union>i<Suc (length P). (P @ [S]) ! i)"
    by simp
  also have "\<dots> =
      (\<Union>i<length P. (P @ [S]) ! i) \<union> (P @ [S]) ! length P"
    by (simp add: lessThan_Suc Un_commute)
  also have "\<dots> = (\<Union>i<length P. P ! i) \<union> S"
  proof -
    have "(\<Union>i<length P. (P @ [S]) ! i) = (\<Union>i<length P. P ! i)"
      by (rule SUP_cong) (simp_all add: nth_append)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma sphere_indexed_image_union_append_singleton:
  fixes P :: "'a set list" and G :: "('a \<Rightarrow> 'b) list" and S :: "'a set"
    and g :: "'a \<Rightarrow> 'b"
  assumes "length P = length G"
  shows "(\<Union>i<length (P @ [S]). (G @ [g]) ! i ` ((P @ [S]) ! i)) =
    (\<Union>i<length P. G ! i ` (P ! i)) \<union> g ` S"
proof -
  have "(\<Union>i<length (P @ [S]). (G @ [g]) ! i ` ((P @ [S]) ! i)) =
      (\<Union>i<Suc (length P). (G @ [g]) ! i ` ((P @ [S]) ! i))"
    by simp
  also have "\<dots> =
      (\<Union>i<length P. (G @ [g]) ! i ` ((P @ [S]) ! i)) \<union>
      (G @ [g]) ! length P ` ((P @ [S]) ! length P)"
    by (simp add: lessThan_Suc Un_commute)
  also have "\<dots> = (\<Union>i<length P. G ! i ` (P ! i)) \<union> g ` S"
    using assms by (simp add: nth_append)
  finally show ?thesis .
qed

lemma sphere2_absorb_cover:
  assumes R_SO3: "R \<in> SO3"
    and disj: "\<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` bad_set_D) \<inter> ((R^^m) ` bad_set_D) = {}"
    and len: "length P = length g"
    and g_SO3: "set g \<subseteq> SO3"
    and P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D"
    and X_cover: "sphere2 - bad_set_D = (\<Union>i<length P. (g ! i) ` (P ! i))"
  shows "\<exists>P' :: (real^3) set list. \<exists>g' :: ((real^3) \<Rightarrow> (real^3)) list.
      length P' = length g' \<and>
      set g' \<subseteq> SO3 \<and>
      (\<forall>i < length P'. P' ! i \<subseteq> sphere2) \<and>
      sphere2 = (\<Union>i<length P'. P' ! i) \<and>
      sphere2 = (\<Union>i<length P'. (g' ! i) ` (P' ! i))"
proof -
  define E where "E = (\<Union>n. (R^^n) ` bad_set_D)"
  have R_E: "R ` E = E - bad_set_D"
    unfolding E_def by (rule absorbing_rotation_shift[OF disj])
  have D_subset_E: "bad_set_D \<subseteq> E"
  proof
    fix x
    assume x: "x \<in> bad_set_D"
    have "x \<in> (R ^^ 0) ` bad_set_D"
      using x by (auto simp add: image_def)
    thus "x \<in> E"
      unfolding E_def by blast
  qed
  have E_subset_sphere2: "E \<subseteq> sphere2"
  proof
    fix x
    assume "x \<in> E"
    then obtain n d where x: "x = (R ^^ n) d" and d: "d \<in> bad_set_D"
      unfolding E_def by blast
    from d have "d \<in> sphere2"
      using bad_set_D_subset by blast
    with R_SO3 x show "x \<in> sphere2"
      using SO3_funpow_preserves_sphere2 by blast
  qed
  have invR_SO3: "Hilbert_Choice.inv R \<in> SO3"
    by (rule SO3_inverse[OF R_SO3])
  have R_inj: "inj R"
    by (rule SO3_inj[OF R_SO3])
  define P0 where "P0 = P @ P"
  define g0 where "g0 = map (\<lambda>h. Hilbert_Choice.inv R \<circ> h) g @ g"
  define Rest where "Rest = sphere2 - (\<Union>i<length P0. P0 ! i)"
  define P' where "P' = P0 @ [Rest]"
  define g' where "g' = g0 @ [id]"
  have len0: "length P0 = length g0"
    using len by (simp add: P0_def g0_def)
  have len': "length P' = length g'"
    using len0 by (simp add: P'_def g'_def)
  have g0_SO3: "set g0 \<subseteq> SO3"
  proof
    fix h
    assume "h \<in> set g0"
    hence "h \<in> (\<lambda>k. Hilbert_Choice.inv R \<circ> k) ` set g \<or> h \<in> set g"
      by (auto simp: g0_def)
    thus "h \<in> SO3"
    proof
      assume "h \<in> (\<lambda>k. Hilbert_Choice.inv R \<circ> k) ` set g"
      then obtain k where k: "k \<in> set g" and h: "h = Hilbert_Choice.inv R \<circ> k"
        by blast
      have k_SO3: "k \<in> SO3"
        using g_SO3 k by auto
      show ?thesis
        unfolding h by (rule SO3_closed_compose[OF invR_SO3 k_SO3])
    next
      assume "h \<in> set g"
      thus ?thesis
        using g_SO3 by auto
    qed
  qed
  have g'_SO3: "set g' \<subseteq> SO3"
    using g0_SO3 id_in_SO3 by (auto simp: g'_def)
  have P0_sub: "\<forall>i < length P0. P0 ! i \<subseteq> sphere2"
  proof (intro allI impI)
    fix i
    assume i: "i < length P0"
    show "P0 ! i \<subseteq> sphere2"
    proof (cases "i < length P")
      case True
      have P0_i: "P0 ! i = P ! i"
        using True by (simp add: P0_def nth_append)
      have "P ! i \<subseteq> sphere2"
        using P_sub True by blast
      thus ?thesis
        by (simp add: P0_i)
    next
      case False
      hence i2: "i - length P < length P"
        using i by (simp add: P0_def)
      have "P0 ! i = P ! (i - length P)"
        using False i by (simp add: P0_def nth_append)
      with P_sub i2 show ?thesis
        by auto
    qed
  qed
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> sphere2"
  proof (intro allI impI)
    fix i
    assume i: "i < length P'"
    show "P' ! i \<subseteq> sphere2"
    proof (cases "i < length P0")
      case True
      have P'_i: "P' ! i = P0 ! i"
        using True by (simp add: P'_def nth_append)
      have "P0 ! i \<subseteq> sphere2"
        using P0_sub True by blast
      thus ?thesis
        by (simp add: P'_i)
    next
      case False
      with i have "i = length P0"
        by (simp add: P'_def)
      thus ?thesis
        by (auto simp: P'_def Rest_def)
    qed
  qed
  have P'_cover: "sphere2 = (\<Union>i<length P'. P' ! i)"
  proof -
    have "(\<Union>i<length P'. P' ! i) =
        (\<Union>i<length P0. P0 ! i) \<union> Rest"
      unfolding P'_def by (rule sphere_indexed_union_append_singleton)
    also have "\<dots> = sphere2"
    proof
      show "(\<Union>i<length P0. P0 ! i) \<union> Rest \<subseteq> sphere2"
        using P0_sub by (auto simp: Rest_def)
      show "sphere2 \<subseteq> (\<Union>i<length P0. P0 ! i) \<union> Rest"
        by (auto simp: Rest_def)
    qed
    finally show ?thesis
      by simp
  qed
  have image0_cover: "sphere2 \<subseteq> (\<Union>i<length P0. (g0 ! i) ` (P0 ! i))"
  proof
    fix y
    assume y_sphere: "y \<in> sphere2"
    show "y \<in> (\<Union>i<length P0. (g0 ! i) ` (P0 ! i))"
    proof (cases "y \<in> E")
      case True
      hence Ry_in_RE: "R y \<in> R ` E"
        by blast
      have Ry_E_minus_D: "R y \<in> E - bad_set_D"
        using Ry_in_RE R_E by simp
      have Ry_X: "R y \<in> sphere2 - bad_set_D"
      proof
        show "R y \<in> sphere2"
          using Ry_E_minus_D E_subset_sphere2 by blast
        show "R y \<notin> bad_set_D"
          using Ry_E_minus_D by simp
      qed
      then obtain i x where i: "i < length P" and x: "x \<in> P ! i"
        and Ry: "R y = (g ! i) x"
        using X_cover by blast
      have i0: "i < length P0"
        using i by (simp add: P0_def)
      have g0_i: "g0 ! i = Hilbert_Choice.inv R \<circ> (g ! i)"
        using i len by (simp add: g0_def nth_append)
      have P0_i: "P0 ! i = P ! i"
        using i by (simp add: P0_def nth_append)
      have "(g0 ! i) x = y"
      proof -
        have inv_Ry: "Hilbert_Choice.inv R (R y) = y"
          by (rule inv_f_f[OF R_inj])
        have "(g0 ! i) x = Hilbert_Choice.inv R ((g ! i) x)"
          by (simp add: g0_i)
        also have "\<dots> = Hilbert_Choice.inv R (R y)"
          using Ry by simp
        also have "\<dots> = y"
          by (rule inv_Ry)
        finally show ?thesis .
      qed
      moreover have "(g0 ! i) x \<in> (g0 ! i) ` (P0 ! i)"
        using x P0_i by blast
      ultimately show ?thesis
        using i0 by blast
    next
      case False
      have y_X: "y \<in> sphere2 - bad_set_D"
      proof
        show "y \<in> sphere2"
          by (rule y_sphere)
        show "y \<notin> bad_set_D"
          using False D_subset_E by auto
      qed
      then obtain i x where i: "i < length P" and x: "x \<in> P ! i"
        and y_eq: "y = (g ! i) x"
        using X_cover by blast
      let ?j = "length P + i"
      have j0: "?j < length P0"
        using i by (simp add: P0_def)
      have g0_j: "g0 ! ?j = g ! i"
        using i len by (simp add: g0_def nth_append)
      have P0_j: "P0 ! ?j = P ! i"
        using i by (simp add: P0_def nth_append)
      show ?thesis
      proof -
        have "(g0 ! ?j) x \<in> (g0 ! ?j) ` (P0 ! ?j)"
          using x P0_j by blast
        moreover have "(g0 ! ?j) x = y"
          using y_eq g0_j by simp
        ultimately show ?thesis
          using j0 by blast
      qed
    qed
  qed
  have image0_subset: "(\<Union>i<length P0. (g0 ! i) ` (P0 ! i)) \<subseteq> sphere2"
  proof
    fix y
    assume "y \<in> (\<Union>i<length P0. (g0 ! i) ` (P0 ! i))"
    then obtain i x where i: "i < length P0" and x: "x \<in> P0 ! i"
      and y: "y = (g0 ! i) x"
      by blast
    have g0_i: "g0 ! i \<in> SO3"
    proof -
      have "g0 ! i \<in> set g0"
        using i len0 by (simp add: nth_mem)
      thus ?thesis
        using g0_SO3 by blast
    qed
    have x_sphere: "x \<in> sphere2"
      using P0_sub i x by auto
    show "y \<in> sphere2"
      using rotation_preserves_sphere2[OF g0_i x_sphere] y by simp
  qed
  have image0_eq: "sphere2 = (\<Union>i<length P0. (g0 ! i) ` (P0 ! i))"
  proof
    show "sphere2 \<subseteq> (\<Union>i<length P0. (g0 ! i) ` (P0 ! i))"
      by (rule image0_cover)
    show "(\<Union>i<length P0. (g0 ! i) ` (P0 ! i)) \<subseteq> sphere2"
      by (rule image0_subset)
  qed
  have image_cover: "sphere2 = (\<Union>i<length P'. (g' ! i) ` (P' ! i))"
  proof -
    have "(\<Union>i<length P'. (g' ! i) ` (P' ! i)) =
        (\<Union>i<length P0. (g0 ! i) ` (P0 ! i)) \<union> id ` Rest"
      unfolding P'_def g'_def
      by (rule sphere_indexed_image_union_append_singleton[OF len0])
    also have "\<dots> = sphere2"
    proof -
      have "id ` Rest \<subseteq> sphere2"
        by (auto simp: Rest_def)
      with image0_eq show ?thesis
        by blast
    qed
    finally show ?thesis
      by simp
  qed
  show ?thesis
  proof (intro exI conjI)
    show "length P' = length g'"
      by (rule len')
    show "set g' \<subseteq> SO3"
      by (rule g'_SO3)
    show "\<forall>i<length P'. P' ! i \<subseteq> sphere2"
      by (rule P'_sub)
    show "sphere2 = (\<Union>i<length P'. P' ! i)"
      by (rule P'_cover)
    show "sphere2 = (\<Union>i<length P'. (g' ! i) ` (P' ! i))"
      by (rule image_cover)
  qed
qed

theorem sphere2_paradoxical_strong:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q) \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2) \<and>
       sphere2 = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       sphere2 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       sphere2 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  obtain R where R_SO3: "R \<in> SO3"
    and disj: "\<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` bad_set_D) \<inter> ((R^^m) ` bad_set_D) = {}"
    using exists_absorbing_rotation by blast
  define E where "E = (\<Union>n. (R^^n) ` bad_set_D)"
  have R_E: "R ` E = E - bad_set_D"
    unfolding E_def by (rule absorbing_rotation_shift[OF disj])
  have D_subset_E: "bad_set_D \<subseteq> E"
  proof
    fix x
    assume x: "x \<in> bad_set_D"
    have "x \<in> (R ^^ 0) ` bad_set_D"
      using x by (auto simp add: image_def)
    thus "x \<in> E"
      unfolding E_def by blast
  qed
  have E_subset_sphere2: "E \<subseteq> sphere2"
  proof
    fix x
    assume "x \<in> E"
    then obtain n d where x: "x = (R ^^ n) d" and d: "d \<in> bad_set_D"
      unfolding E_def by blast
    from d have "d \<in> sphere2"
      using bad_set_D_subset by blast
    with R_SO3 x show "x \<in> sphere2"
      using SO3_funpow_preserves_sphere2 by blast
  qed
  have invR_SO3: "Hilbert_Choice.inv R \<in> SO3"
    by (rule SO3_inverse[OF R_SO3])
  have R_inj: "inj R"
    by (rule SO3_inj[OF R_SO3])
  let ?X = "sphere2 - bad_set_D"
  let ?Y = "sphere2"
  let ?A = "[E, sphere2 - E]"
  let ?B = "[R ` E, sphere2 - E]"
  let ?e = "[R, id]"
  let ?t = "[Hilbert_Choice.inv R, id]"
  have A_cover: "?Y = (\<Union>k<length ?A. ?A ! k)"
    using E_subset_sphere2 by (auto simp: lessThan_Suc)
  have A_disj: "pairwise_disjoint ?A"
    unfolding pairwise_disjoint_def
  proof (intro allI impI)
    fix i j
    assume i: "i < length ?A" and j: "j < length ?A" and ij: "i \<noteq> j"
    have "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)"
      using i j ij by auto
    thus "?A ! i \<inter> ?A ! j = {}"
      by auto
  qed
  have B_cover: "?X = (\<Union>k<length ?B. ?B ! k)"
  proof
    show "?X \<subseteq> (\<Union>k<length ?B. ?B ! k)"
    proof
      fix x
      assume x: "x \<in> ?X"
      show "x \<in> (\<Union>k<length ?B. ?B ! k)"
      proof (cases "x \<in> E")
        case True
        with x R_E show ?thesis
          by force
      next
        case False
        with x show ?thesis
          by force
      qed
    qed
    show "(\<Union>k<length ?B. ?B ! k) \<subseteq> ?X"
    proof
      fix x
      assume x: "x \<in> (\<Union>k<length ?B. ?B ! k)"
      then obtain k where k: "k < length ?B" and xk: "x \<in> ?B ! k"
        by blast
      have "k = 0 \<or> k = 1"
        using k by auto
      thus "x \<in> ?X"
      proof
        assume "k = 0"
        with xk R_E E_subset_sphere2 show ?thesis
          by auto
      next
        assume "k = 1"
        with xk D_subset_E show ?thesis
          by auto
      qed
    qed
  qed
  have B_disj: "pairwise_disjoint ?B"
    unfolding pairwise_disjoint_def
  proof (intro allI impI)
    fix i j
    assume i: "i < length ?B" and j: "j < length ?B" and ij: "i \<noteq> j"
    have "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)"
      using i j ij by auto
    thus "?B ! i \<inter> ?B ! j = {}"
      using R_E by auto
  qed
  have e_left: "\<And>k x. \<lbrakk>k < length ?A; x \<in> ?A ! k\<rbrakk>
      \<Longrightarrow> (?e ! k) x \<in> ?B ! k \<and> (?t ! k) ((?e ! k) x) = x"
  proof -
    fix k x
    assume k: "k < length ?A" and x: "x \<in> ?A ! k"
    have "k = 0 \<or> k = 1"
      using k by auto
    thus "(?e ! k) x \<in> ?B ! k \<and> (?t ! k) ((?e ! k) x) = x"
    proof
      assume "k = 0"
      with x show ?thesis
        using inv_f_f[OF R_inj, of x] by auto
    next
      assume "k = 1"
      with x show ?thesis
        by auto
    qed
  qed
  have t_left: "\<And>k y. \<lbrakk>k < length ?B; y \<in> ?B ! k\<rbrakk>
      \<Longrightarrow> (?t ! k) y \<in> ?A ! k \<and> (?e ! k) ((?t ! k) y) = y"
  proof -
    fix k y
    assume k: "k < length ?B" and y: "y \<in> ?B ! k"
    have "k = 0 \<or> k = 1"
      using k by auto
    thus "(?t ! k) y \<in> ?A ! k \<and> (?e ! k) ((?t ! k) y) = y"
    proof
      assume "k = 0"
      then obtain x where x: "x \<in> E" and y_eq: "y = R x"
        using y by auto
      have inv_eq: "Hilbert_Choice.inv R y = x"
        using y_eq inv_f_f[OF R_inj, of x] by simp
      with x y_eq \<open>k = 0\<close> show ?thesis
        by simp
    next
      assume "k = 1"
      with y show ?thesis
        by auto
    qed
  qed

  from hausdorff_paradox_rot_strong obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3) \<Rightarrow> (real^3)) list"
    where lenP: "length P = length gP"
      and lenQ: "length Q = length gQ"
      and gP_SO3: "set gP \<subseteq> SO3"
      and gQ_SO3: "set gQ \<subseteq> SO3"
      and source_disj: "pairwise_disjoint (P @ Q)"
      and imageP_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P)"
      and imageQ_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q)"
      and P_sub: "\<forall>i < length P. P ! i \<subseteq> ?X"
      and Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> ?X"
      and source_cover: "?X = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      and imageP_cover: "?X = (\<Union>i<length P. (gP ! i) ` (P ! i))"
      and imageQ_cover: "?X = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by auto
  have gP_inj: "\<And>i. i < length P \<Longrightarrow> inj (gP ! i)"
  proof -
    fix i assume i: "i < length P"
    have "gP ! i \<in> SO3"
    proof -
      have "i < length gP"
        using lenP i by simp
      hence "gP ! i \<in> set gP"
        by (rule nth_mem)
      thus ?thesis
        using gP_SO3 by blast
    qed
    thus "inj (gP ! i)"
      by (rule SO3_inj)
  qed
  have gQ_inj: "\<And>i. i < length Q \<Longrightarrow> inj (gQ ! i)"
  proof -
    fix i assume i: "i < length Q"
    have "gQ ! i \<in> SO3"
    proof -
      have "i < length gQ"
        using lenQ i by simp
      hence "gQ ! i \<in> set gQ"
        by (rule nth_mem)
      thus ?thesis
        using gQ_SO3 by blast
    qed
    thus "inj (gQ ! i)"
      by (rule SO3_inj)
  qed
  have mapsP: "\<And>k i l. \<lbrakk>k < length ?A; i < length P; l < length ?B\<rbrakk>
      \<Longrightarrow> transfer_map ?t gP ?e k i l \<in> SO3"
  proof -
    fix k i l
    assume k: "k < length ?A" and i: "i < length P" and l: "l < length ?B"
    have gi: "gP ! i \<in> SO3"
    proof -
      have "i < length gP"
        using lenP i by simp
      hence "gP ! i \<in> set gP"
        by (rule nth_mem)
      thus ?thesis
        using gP_SO3 by blast
    qed
    have ek: "?e ! k \<in> SO3"
    proof -
      have "k = 0 \<or> k = 1"
        using k by auto
      thus ?thesis
        using R_SO3 id_in_SO3 by auto
    qed
    have tl: "?t ! l \<in> SO3"
    proof -
      have "l = 0 \<or> l = 1"
        using l by auto
      thus ?thesis
        using invR_SO3 id_in_SO3 by auto
    qed
    have left: "(?t ! l) \<circ> (gP ! i) \<in> SO3"
      by (rule SO3_closed_compose[OF tl gi])
    show "transfer_map ?t gP ?e k i l \<in> SO3"
      unfolding transfer_map_def
      by (rule SO3_closed_compose[OF left ek])
  qed
  have mapsQ: "\<And>k i l. \<lbrakk>k < length ?A; i < length Q; l < length ?B\<rbrakk>
      \<Longrightarrow> transfer_map ?t gQ ?e k i l \<in> SO3"
  proof -
    fix k i l
    assume k: "k < length ?A" and i: "i < length Q" and l: "l < length ?B"
    have gi: "gQ ! i \<in> SO3"
    proof -
      have "i < length gQ"
        using lenQ i by simp
      hence "gQ ! i \<in> set gQ"
        by (rule nth_mem)
      thus ?thesis
        using gQ_SO3 by blast
    qed
    have ek: "?e ! k \<in> SO3"
    proof -
      have "k = 0 \<or> k = 1"
        using k by auto
      thus ?thesis
        using R_SO3 id_in_SO3 by auto
    qed
    have tl: "?t ! l \<in> SO3"
    proof -
      have "l = 0 \<or> l = 1"
        using l by auto
      thus ?thesis
        using invR_SO3 id_in_SO3 by auto
    qed
    have left: "(?t ! l) \<circ> (gQ ! i) \<in> SO3"
      by (rule SO3_closed_compose[OF tl gi])
    show "transfer_map ?t gQ ?e k i l \<in> SO3"
      unfolding transfer_map_def
      by (rule SO3_closed_compose[OF left ek])
  qed
  have lenAB: "length ?A = length ?B"
    by simp
  from transfer_partitioned_paradox[
      OF lenAB A_cover A_disj B_cover B_disj e_left t_left lenP lenQ source_disj
        source_cover imageP_disj imageQ_disj imageP_cover imageQ_cover gP_inj gQ_inj
        mapsP mapsQ]
  obtain P' Q' :: "(real^3) set list" and hP hQ :: "((real^3) \<Rightarrow> (real^3)) list"
    where lenP': "length P' = length hP"
      and lenQ': "length Q' = length hQ"
      and hP_SO3: "set hP \<subseteq> SO3"
      and hQ_SO3: "set hQ \<subseteq> SO3"
      and source_disj': "pairwise_disjoint (P' @ Q')"
      and imageP_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hP P')"
      and imageQ_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hQ Q')"
      and source_cover': "?Y = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
      and imageP_cover': "?Y = (\<Union>i<length P'. (hP ! i) ` (P' ! i))"
      and imageQ_cover': "?Y = (\<Union>i<length Q'. (hQ ! i) ` (Q' ! i))"
    by auto
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> sphere2"
    using source_cover' by blast
  have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> sphere2"
    using source_cover' by blast
  show ?thesis
  proof (intro exI conjI)
    show "length P' = length hP"
      by (rule lenP')
    show "length Q' = length hQ"
      by (rule lenQ')
    show "set hP \<subseteq> SO3"
      by (rule hP_SO3)
    show "set hQ \<subseteq> SO3"
      by (rule hQ_SO3)
    show "pairwise_disjoint (P' @ Q')"
      by (rule source_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hP P')"
      by (rule imageP_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hQ Q')"
      by (rule imageQ_disj')
    show "\<forall>i<length P'. P' ! i \<subseteq> sphere2"
      by (rule P'_sub)
    show "\<forall>i<length Q'. Q' ! i \<subseteq> sphere2"
      by (rule Q'_sub)
    show "sphere2 = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
      by (rule source_cover')
    show "sphere2 = (\<Union>i<length P'. (hP ! i) ` (P' ! i))"
      by (rule imageP_cover')
    show "sphere2 = (\<Union>i<length Q'. (hQ ! i) ` (Q' ! i))"
      by (rule imageQ_cover')
  qed
qed

theorem sphere2_paradoxical:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2) \<and>
       sphere2 = (\<Union>i<length P. P ! i) \<and>
       sphere2 = (\<Union>i<length Q. Q ! i) \<and>
       sphere2 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       sphere2 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  obtain R where R_SO3: "R \<in> SO3"
    and disj: "\<forall>n m. n \<noteq> m \<longrightarrow> ((R^^n) ` bad_set_D) \<inter> ((R^^m) ` bad_set_D) = {}"
    using exists_absorbing_rotation by blast
  from hausdorff_paradox obtain P Q :: "(real^3) set list"
    and hP hQ :: "((real^3) \<Rightarrow> (real^3)) list"
    where hd:
      "length P = length hP \<and> length Q = length hQ \<and>
       set hP \<subseteq> SO3 \<and> set hQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D) \<and>
       sphere2 - bad_set_D = (\<Union>i<length P. (hP ! i) ` (P ! i)) \<and>
       sphere2 - bad_set_D = (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
    by (elim exE)
  from hd have lenP: "length P = length hP"
    by (elim conjE)
  from hd have lenQ: "length Q = length hQ"
    by (elim conjE)
  from hd have hP_SO3: "set hP \<subseteq> SO3"
    by (elim conjE)
  from hd have hQ_SO3: "set hQ \<subseteq> SO3"
    by (elim conjE)
  from hd have P_sub: "\<forall>i < length P. P ! i \<subseteq> sphere2 - bad_set_D"
    by (elim conjE)
  from hd have Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> sphere2 - bad_set_D"
    by (elim conjE)
  from hd have coverP: "sphere2 - bad_set_D = (\<Union>i<length P. (hP ! i) ` (P ! i))"
    by (elim conjE)
  from hd have coverQ: "sphere2 - bad_set_D = (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
    by (elim conjE)
  from sphere2_absorb_cover[OF R_SO3 disj lenP hP_SO3 P_sub coverP]
  obtain P' hP' where P'_all:
      "length P' = length hP' \<and>
      set hP' \<subseteq> SO3 \<and>
      (\<forall>i < length P'. P' ! i \<subseteq> sphere2) \<and>
      sphere2 = (\<Union>i<length P'. P' ! i) \<and>
      sphere2 = (\<Union>i<length P'. (hP' ! i) ` (P' ! i))"
    by (elim exE)
  from P'_all have P'_len: "length P' = length hP'"
    by (elim conjE)
  from P'_all have P'_SO3: "set hP' \<subseteq> SO3"
    by (elim conjE)
  from P'_all have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> sphere2"
    by (elim conjE)
  from P'_all have P'_src: "sphere2 = (\<Union>i<length P'. P' ! i)"
    by (elim conjE)
  from P'_all have P'_img: "sphere2 = (\<Union>i<length P'. (hP' ! i) ` (P' ! i))"
    by (elim conjE)
  from sphere2_absorb_cover[OF R_SO3 disj lenQ hQ_SO3 Q_sub coverQ]
  obtain Q' hQ' where Q'_all:
      "length Q' = length hQ' \<and>
      set hQ' \<subseteq> SO3 \<and>
      (\<forall>i < length Q'. Q' ! i \<subseteq> sphere2) \<and>
      sphere2 = (\<Union>i<length Q'. Q' ! i) \<and>
      sphere2 = (\<Union>i<length Q'. (hQ' ! i) ` (Q' ! i))"
    by (elim exE)
  from Q'_all have Q'_len: "length Q' = length hQ'"
    by (elim conjE)
  from Q'_all have Q'_SO3: "set hQ' \<subseteq> SO3"
    by (elim conjE)
  from Q'_all have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> sphere2"
    by (elim conjE)
  from Q'_all have Q'_src: "sphere2 = (\<Union>i<length Q'. Q' ! i)"
    by (elim conjE)
  from Q'_all have Q'_img: "sphere2 = (\<Union>i<length Q'. (hQ' ! i) ` (Q' ! i))"
    by (elim conjE)
  show ?thesis
  proof (intro exI conjI)
    show "length P' = length hP'"
      by (rule P'_len)
    show "length Q' = length hQ'"
      by (rule Q'_len)
    show "set hP' \<subseteq> SO3"
      by (rule P'_SO3)
    show "set hQ' \<subseteq> SO3"
      by (rule Q'_SO3)
    show "\<forall>i<length P'. P' ! i \<subseteq> sphere2"
      by (rule P'_sub)
    show "\<forall>i<length Q'. Q' ! i \<subseteq> sphere2"
      by (rule Q'_sub)
    show "sphere2 = (\<Union>i<length P'. P' ! i)"
      by (rule P'_src)
    show "sphere2 = (\<Union>i<length Q'. Q' ! i)"
      by (rule Q'_src)
    show "sphere2 = (\<Union>i<length P'. (hP' ! i) ` (P' ! i))"
      by (rule P'_img)
    show "sphere2 = (\<Union>i<length Q'. (hQ' ! i) ` (Q' ! i))"
      by (rule Q'_img)
  qed
qed

end
