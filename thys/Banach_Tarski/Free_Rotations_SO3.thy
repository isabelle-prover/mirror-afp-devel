(*  Title:       Free_Rotations_SO3.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    SO(3) contains a free subgroup isomorphic to F\<^sub>2.

    The classical witnesses are the rotations R\<^sub>x and R\<^sub>z by
    arccos(1/3) about orthogonal axes (e.g. the x- and z-axes). Showing
    that they generate a free F\<^sub>2 is a substantial undertaking
    (see Wagon, "The Banach-Tarski Paradox", Theorem 2.1; de Rauglaudre,
    JFR 2017). It uses the AFP Free-Groups entry's PingPongLemma; the
    geometric content is to provide disjoint subsets of the sphere that
    R\<^sub>x and R\<^sub>z "ping-pong" between.

    This theory proves the concrete arithmetic freeness result used to
    embed the free group F\<^sub>2 into SO(3).
*)

theory Free_Rotations_SO3
  imports
    "Banach_Tarski.F2_Paradox"
    "Banach_Tarski.Free_Action_Paradox"
    "HOL-Computational_Algebra.Primes"
    "Free-Groups.PingPongLemma"
begin

section \<open>Rotations of three-space\<close>

text \<open>
  A rotation is an orthogonal transformation of determinant 1.
\<close>

definition rotation :: "(real^3 \<Rightarrow> real^3) \<Rightarrow> bool" where
  "rotation f \<longleftrightarrow> orthogonal_transformation f \<and> det (matrix f) = 1"

definition SO3 :: "(real^3 \<Rightarrow> real^3) set" where
  "SO3 = {f. rotation f}"

text \<open>SO(3) contains the identity and is closed under composition.\<close>

lemma id_in_SO3: "id \<in> SO3"
proof -
  have "orthogonal_transformation (id::real^3 \<Rightarrow> real^3)"
    using orthogonal_transformation_id by (simp add: id_def)
  moreover have "det (matrix (id::real^3 \<Rightarrow> real^3)) = 1"
    by simp
  ultimately show ?thesis
    unfolding SO3_def rotation_def by simp
qed

lemma SO3_closed_compose:
  assumes "f \<in> SO3" and "g \<in> SO3"
  shows "f \<circ> g \<in> SO3"
proof -
  from assms have f_orth: "orthogonal_transformation f"
    and g_orth: "orthogonal_transformation g"
    and f_det: "det (matrix f) = 1"
    and g_det: "det (matrix g) = 1"
    unfolding SO3_def rotation_def by auto
  have f_lin: "linear f" using f_orth by (rule orthogonal_transformation_linear)
  have g_lin: "linear g" using g_orth by (rule orthogonal_transformation_linear)

  have orth_comp: "orthogonal_transformation (f \<circ> g)"
    using f_orth g_orth by (rule orthogonal_transformation_compose)

  have "matrix (f \<circ> g) = matrix f ** matrix g"
    using g_lin f_lin by (rule matrix_compose)
  hence "det (matrix (f \<circ> g)) = det (matrix f) * det (matrix g)"
    by (simp add: det_mul)
  also have "\<dots> = 1" using f_det g_det by simp
  finally have "det (matrix (f \<circ> g)) = 1" .

  with orth_comp show ?thesis
    unfolding SO3_def rotation_def by simp
qed

text \<open>SO(3) elements preserve the unit sphere.\<close>

lemma rotation_preserves_sphere2:
  assumes "f \<in> SO3" and "x \<in> sphere2"
  shows "f x \<in> sphere2"
proof -
  from assms(1) have "orthogonal_transformation f"
    unfolding SO3_def rotation_def by auto
  hence "norm (f x) = norm x"
    by (rule orthogonal_transformation_norm)
  with assms(2) show ?thesis
    by (simp add: sphere2_def)
qed

lemma SO3_bij:
  assumes "f \<in> SO3"
  shows "bij f"
  using assms orthogonal_transformation_bij
  unfolding SO3_def rotation_def by auto


section \<open>Two distinguished rotations\<close>

text \<open>
  We use the rotations \<open>R\<^sub>x\<close> (about the x-axis) and
  \<open>R\<^sub>z\<close> (about the z-axis) by the same angle \<open>\<theta>\<close>
  with \<open>cos \<theta> = 1/3\<close>. The exact-form witnesses are unimportant
  for the paradoxical decomposition; what matters is the abstract
  conclusion that these generate a free \<open>F\<^sub>2\<close> inside SO(3).
\<close>

definition rot_c :: real where
  "rot_c = 1 / 3"

definition rot_s :: real where
  "rot_s = sqrt 8 / 3"

lemma rot_c_sq_plus_rot_s_sq: "rot_c\<^sup>2 + rot_s\<^sup>2 = 1"
  unfolding rot_c_def rot_s_def
  by (simp add: power_divide)

lemma rot_c_mul_plus_rot_s_mul [simp]: "rot_c * rot_c + rot_s * rot_s = 1"
  using rot_c_sq_plus_rot_s_sq by (simp add: power2_eq_square)

definition Rx_mat :: "real^3^3" where
  "Rx_mat = vector [
     vector [1, 0, 0],
     vector [0, rot_c, - rot_s],
     vector [0, rot_s, rot_c]]"

definition Rz_mat :: "real^3^3" where
  "Rz_mat = vector [
     vector [rot_c, - rot_s, 0],
     vector [rot_s, rot_c, 0],
     vector [0, 0, 1]]"

definition Rx_inv_mat :: "real^3^3" where
  "Rx_inv_mat = vector [
     vector [1, 0, 0],
     vector [0, rot_c, rot_s],
     vector [0, - rot_s, rot_c]]"

definition Rz_inv_mat :: "real^3^3" where
  "Rz_inv_mat = vector [
     vector [rot_c, rot_s, 0],
     vector [- rot_s, rot_c, 0],
     vector [0, 0, 1]]"

definition Rx :: "real^3 \<Rightarrow> real^3" where
  "Rx v = Rx_mat *v v"

definition Rz :: "real^3 \<Rightarrow> real^3" where
  "Rz v = Rz_mat *v v"

definition Rx_inv :: "real^3 \<Rightarrow> real^3" where
  "Rx_inv v = Rx_inv_mat *v v"

definition Rz_inv :: "real^3 \<Rightarrow> real^3" where
  "Rz_inv v = Rz_inv_mat *v v"

lemma Rx_mat_orthogonal: "orthogonal_matrix Rx_mat"
  unfolding orthogonal_matrix Rx_mat_def
  by (simp add: matrix_matrix_mult_def transpose_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rz_mat_orthogonal: "orthogonal_matrix Rz_mat"
  unfolding orthogonal_matrix Rz_mat_def
  by (simp add: matrix_matrix_mult_def transpose_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rx_inv_mat_orthogonal: "orthogonal_matrix Rx_inv_mat"
  unfolding orthogonal_matrix Rx_inv_mat_def
  by (simp add: matrix_matrix_mult_def transpose_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rz_inv_mat_orthogonal: "orthogonal_matrix Rz_inv_mat"
  unfolding orthogonal_matrix Rz_inv_mat_def
  by (simp add: matrix_matrix_mult_def transpose_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma det_Rx_mat [simp]: "det Rx_mat = 1"
  unfolding Rx_mat_def
  by (simp add: det_3 vector_def rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma det_Rz_mat [simp]: "det Rz_mat = 1"
  unfolding Rz_mat_def
  by (simp add: det_3 vector_def rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma det_Rx_inv_mat [simp]: "det Rx_inv_mat = 1"
  unfolding Rx_inv_mat_def
  by (simp add: det_3 vector_def rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma det_Rz_inv_mat [simp]: "det Rz_inv_mat = 1"
  unfolding Rz_inv_mat_def
  by (simp add: det_3 vector_def rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rx_mat_inverse_left: "Rx_inv_mat ** Rx_mat = mat 1"
  unfolding Rx_inv_mat_def Rx_mat_def
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rx_mat_inverse_right: "Rx_mat ** Rx_inv_mat = mat 1"
  unfolding Rx_inv_mat_def Rx_mat_def
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rz_mat_inverse_left: "Rz_inv_mat ** Rz_mat = mat 1"
  unfolding Rz_inv_mat_def Rz_mat_def
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

lemma Rz_mat_inverse_right: "Rz_mat ** Rz_inv_mat = mat 1"
  unfolding Rz_inv_mat_def Rz_mat_def
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff vector_def sum_3 forall_3
      rot_c_sq_plus_rot_s_sq power2_eq_square algebra_simps)

text \<open>The concrete generators and their inverses lie in \<open>SO(3)\<close>.\<close>
lemma Rx_in_SO3: "Rx \<in> SO3"
  unfolding SO3_def rotation_def Rx_def
  by (simp add: orthogonal_transformation_matrix Rx_mat_orthogonal matrix_vector_mul_linear)

lemma Rz_in_SO3: "Rz \<in> SO3"
  unfolding SO3_def rotation_def Rz_def
  by (simp add: orthogonal_transformation_matrix Rz_mat_orthogonal matrix_vector_mul_linear)

lemma Rx_inv_in_SO3: "Rx_inv \<in> SO3"
  unfolding SO3_def rotation_def Rx_inv_def
  by (simp add: orthogonal_transformation_matrix Rx_inv_mat_orthogonal matrix_vector_mul_linear)

lemma Rz_inv_in_SO3: "Rz_inv \<in> SO3"
  unfolding SO3_def rotation_def Rz_inv_def
  by (simp add: orthogonal_transformation_matrix Rz_inv_mat_orthogonal matrix_vector_mul_linear)

text \<open>The named inverse rotations are two-sided inverses of the generators.\<close>
lemma Rx_inv_left: "Rx_inv \<circ> Rx = id"
  by (rule ext) (simp add: Rx_inv_def Rx_def matrix_vector_mul_assoc Rx_mat_inverse_left)

lemma Rz_inv_left: "Rz_inv \<circ> Rz = id"
  by (rule ext) (simp add: Rz_inv_def Rz_def matrix_vector_mul_assoc Rz_mat_inverse_left)

lemma Rx_inv_right: "Rx \<circ> Rx_inv = id"
  by (rule ext) (simp add: Rx_inv_def Rx_def matrix_vector_mul_assoc Rx_mat_inverse_right)

lemma Rz_inv_right: "Rz \<circ> Rz_inv = id"
  by (rule ext) (simp add: Rz_inv_def Rz_def matrix_vector_mul_assoc Rz_mat_inverse_right)


section \<open>The rotations as bijections of the sphere\<close>

definition sphere_perm :: "(real^3 \<Rightarrow> real^3) \<Rightarrow> (real^3 \<Rightarrow> real^3)" where
  "sphere_perm f = restrict f sphere2"

lemma SO3_bij_betw_sphere2:
  assumes "f \<in> SO3"
  shows "bij_betw f sphere2 sphere2"
proof -
  have "f ` sphere2 \<subseteq> sphere2"
    using rotation_preserves_sphere2[OF assms] by auto
  moreover have "sphere2 \<subseteq> f ` sphere2"
  proof
    fix y assume y: "y \<in> sphere2"
    from SO3_bij[OF assms] obtain x where x: "y = f x"
      by (meson bij_pointE)
    have "x \<in> sphere2"
    proof -
      from assms have orth: "orthogonal_transformation f"
        unfolding SO3_def rotation_def by auto
      from x y have "norm (f x) = 1"
        by (simp add: sphere2_def)
      moreover from orth have "norm (f x) = norm x"
        by (rule orthogonal_transformation_norm)
      ultimately show ?thesis
        by (simp add: sphere2_def)
    qed
    with x show "y \<in> f ` sphere2"
      by blast
  qed
  moreover have "inj_on f sphere2"
  proof -
    have "inj f"
      using SO3_bij[OF assms] by (rule bij_is_inj)
    thus ?thesis
      by (rule inj_on_subset) simp
  qed
  ultimately show ?thesis
    unfolding bij_betw_def by auto
qed

lemma sphere_perm_in_Bij:
  assumes "f \<in> SO3"
  shows "sphere_perm f \<in> Bij sphere2"
  using SO3_bij_betw_sphere2[OF assms]
  by (simp add: sphere_perm_def Bij_def)

lemma sphere_perm_mult:
  assumes "sphere_perm f \<in> Bij sphere2" "sphere_perm g \<in> Bij sphere2"
  shows "sphere_perm f \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm g = sphere_perm (f \<circ> g)"
proof (rule ext)
  fix x
  show "(sphere_perm f \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm g) x = sphere_perm (f \<circ> g) x"
  proof (cases "x \<in> sphere2")
    case True
    from assms True have "sphere_perm g x \<in> sphere2"
      by (auto simp: Bij_def bij_betw_def)
    with assms True show ?thesis
      by (simp add: sphere_perm_def BijGroup_def compose_def restrict_def)
  next
    case False
    with assms show ?thesis
      by (simp add: sphere_perm_def BijGroup_def compose_def restrict_def)
  qed
qed

lemma sphere_perm_id: "sphere_perm id = \<one>\<^bsub>BijGroup sphere2\<^esub>"
  by (simp add: sphere_perm_def BijGroup_def id_def)

lemma sphere_perm_Rx [simp]: "sphere_perm Rx \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule Rx_in_SO3)

lemma sphere_perm_Rx_inv [simp]: "sphere_perm Rx_inv \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule Rx_inv_in_SO3)

lemma sphere_perm_Rz [simp]: "sphere_perm Rz \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule Rz_in_SO3)

lemma sphere_perm_Rz_inv [simp]: "sphere_perm Rz_inv \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule Rz_inv_in_SO3)

lemma sphere_perm_Rx_inv_left:
  "sphere_perm Rx_inv \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rx = \<one>\<^bsub>BijGroup sphere2\<^esub>"
  by (simp add: sphere_perm_mult Rx_inv_left sphere_perm_id)

lemma sphere_perm_Rx_inv_right:
  "sphere_perm Rx \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rx_inv = \<one>\<^bsub>BijGroup sphere2\<^esub>"
  by (simp add: sphere_perm_mult Rx_inv_right sphere_perm_id)

lemma sphere_perm_Rz_inv_left:
  "sphere_perm Rz_inv \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rz = \<one>\<^bsub>BijGroup sphere2\<^esub>"
  by (simp add: sphere_perm_mult Rz_inv_left sphere_perm_id)

lemma sphere_perm_Rz_inv_right:
  "sphere_perm Rz \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rz_inv = \<one>\<^bsub>BijGroup sphere2\<^esub>"
  by (simp add: sphere_perm_mult Rz_inv_right sphere_perm_id)

lemma inv_sphere_perm_Rx:
  "inv\<^bsub>BijGroup sphere2\<^esub> (sphere_perm Rx) = sphere_perm Rx_inv"
proof -
  interpret B: group "BijGroup sphere2"
    by (rule group_BijGroup)
  show ?thesis
  proof (rule B.inv_equality)
    show "sphere_perm Rx_inv \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rx = \<one>\<^bsub>BijGroup sphere2\<^esub>"
      by (rule sphere_perm_Rx_inv_left)
    show "sphere_perm Rx \<in> carrier (BijGroup sphere2)"
      by (simp add: BijGroup_def)
    show "sphere_perm Rx_inv \<in> carrier (BijGroup sphere2)"
      by (simp add: BijGroup_def)
  qed
qed

lemma inv_sphere_perm_Rz:
  "inv\<^bsub>BijGroup sphere2\<^esub> (sphere_perm Rz) = sphere_perm Rz_inv"
proof -
  interpret B: group "BijGroup sphere2"
    by (rule group_BijGroup)
  show ?thesis
  proof (rule B.inv_equality)
    show "sphere_perm Rz_inv \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm Rz = \<one>\<^bsub>BijGroup sphere2\<^esub>"
      by (rule sphere_perm_Rz_inv_left)
    show "sphere_perm Rz \<in> carrier (BijGroup sphere2)"
      by (simp add: BijGroup_def)
    show "sphere_perm Rz_inv \<in> carrier (BijGroup sphere2)"
      by (simp add: BijGroup_def)
  qed
qed

interpretation sphere_Bij: group "BijGroup sphere2"
  by (rule group_BijGroup)


section \<open>The map sigma: \<open>F\<^sub>2\<close> to SO(3)\<close>

text \<open>
  The map \<open>sigma\<close> sends each reduced word in \<open>F\<^sub>2\<close> to the
  corresponding composition of \<open>R\<^sub>x\<close>, \<open>R\<^sub>z\<close>, and
  their inverses.
\<close>

definition letter_to_rot :: "bool \<times> gen2 \<Rightarrow> (real^3 \<Rightarrow> real^3)" where
  "letter_to_rot p = (case p of
       (False, A) \<Rightarrow> Rx
     | (True,  A) \<Rightarrow> Rx_inv
     | (False, B) \<Rightarrow> Rz
     | (True,  B) \<Rightarrow> Rz_inv)"

definition rho :: "gen2 \<Rightarrow> (real^3 \<Rightarrow> real^3)" where
  "rho x = (case x of A \<Rightarrow> sphere_perm Rx | B \<Rightarrow> sphere_perm Rz)"

lemma rho_in_BijGroup:
  "rho \<in> Gen2 \<rightarrow> carrier (BijGroup sphere2)"
  by (auto simp: rho_def BijGroup_def)

lemma rho_image_subset_BijGroup:
  "rho ` Gen2 \<subseteq> carrier (BijGroup sphere2)"
  using rho_in_BijGroup by auto

definition sphere_rot_group :: "(real^3 \<Rightarrow> real^3) monoid" where
  "sphere_rot_group =
    (BijGroup sphere2)\<lparr>carrier := \<langle>rho ` Gen2\<rangle>\<^bsub>BijGroup sphere2\<^esub>\<rparr>"

lemma sphere_rot_subgroup:
  "subgroup (carrier sphere_rot_group) (BijGroup sphere2)"
  unfolding sphere_rot_group_def
  apply simp
  by (rule sphere_Bij.gen_subgroup_is_subgroup) (auto simp: rho_def BijGroup_def)

lemma sphere_rot_group_is_group: "group sphere_rot_group"
  unfolding sphere_rot_group_def
  by (rule sphere_Bij.subgroup_imp_group)
    (rule sphere_Bij.gen_subgroup_is_subgroup, rule rho_image_subset_BijGroup)

interpretation sphere_rot: group sphere_rot_group
  by (rule sphere_rot_group_is_group)

lemma rho_in_sphere_rot_group:
  "rho \<in> Gen2 \<rightarrow> carrier sphere_rot_group"
  by (auto simp: sphere_rot_group_def intro: gen_span.gen_gens)

lemma sphere_rot_inclusion_hom:
  "id \<in> hom sphere_rot_group (BijGroup sphere2)"
  using sphere_Bij.gen_span_closed[OF rho_image_subset_BijGroup]
  by (auto simp: hom_def sphere_rot_group_def)

lemma sphere_rot_generated:
  "\<langle>rho ` Gen2\<rangle>\<^bsub>sphere_rot_group\<^esub> = carrier sphere_rot_group"
proof -
  let ?H = "\<langle>rho ` Gen2\<rangle>\<^bsub>BijGroup sphere2\<^esub>"
  let ?G = "(BijGroup sphere2)\<lparr>carrier := ?H\<rparr>"
  have sub: "subgroup ?H (BijGroup sphere2)"
    by (rule sphere_Bij.gen_subgroup_is_subgroup) (rule rho_image_subset_BijGroup)
  have left: "\<langle>rho ` Gen2\<rangle>\<^bsub>sphere_rot_group\<^esub> \<subseteq> carrier sphere_rot_group"
    by (rule sphere_rot.gen_span_closed) (use rho_in_sphere_rot_group in auto)
  have right: "?H \<subseteq> \<langle>rho ` Gen2\<rangle>\<^bsub>?G\<^esub>"
  proof
    fix x
    assume "x \<in> ?H"
    thus "x \<in> \<langle>rho ` Gen2\<rangle>\<^bsub>?G\<^esub>"
    proof (induct rule: gen_span.induct)
      case gen_one
      have "\<one>\<^bsub>?G\<^esub> \<in> \<langle>rho ` Gen2\<rangle>\<^bsub>?G\<^esub>"
        by (rule gen_span.gen_one)
      thus ?case by simp
    next
      case (gen_gens x)
      thus ?case
        by (rule gen_span.gen_gens)
    next
      case (gen_inv x)
      have inv_eq: "inv\<^bsub>?G\<^esub> x = inv\<^bsub>BijGroup sphere2\<^esub> x"
        using sphere_Bij.m_inv_consistent[OF sub gen_inv.hyps(1)] .
      have "inv\<^bsub>?G\<^esub> x \<in> \<langle>rho ` Gen2\<rangle>\<^bsub>?G\<^esub>"
        by (rule gen_span.gen_inv) (rule gen_inv.hyps(2))
      thus ?case
        using inv_eq by metis
    next
      case (gen_mult x y)
      have "x \<otimes>\<^bsub>?G\<^esub> y \<in> \<langle>rho ` Gen2\<rangle>\<^bsub>?G\<^esub>"
        by (rule gen_span.gen_mult) (use gen_mult.hyps in auto)
      thus ?case by simp
    qed
  qed
  show ?thesis
    using left right by (auto simp: sphere_rot_group_def)
qed

lemma sphere_Bij_lift_gi_rho:
  assumes "snd p \<in> Gen2"
  shows "sphere_Bij.lift_gi rho p = sphere_perm (letter_to_rot p)"
  using assms
  by (cases p)
    (auto simp: rho_def letter_to_rot_def sphere_Bij.lift_gi_def
      inv_sphere_perm_Rx inv_sphere_perm_Rz split: bool.splits gen2.splits)

lemma sphere_rot_inv_rho_eq_sphere_Bij:
  assumes "i \<in> Gen2"
  shows "inv\<^bsub>sphere_rot_group\<^esub> (rho i) = inv\<^bsub>BijGroup sphere2\<^esub> (rho i)"
proof -
  have rho_i: "rho i \<in> carrier sphere_rot_group"
    using rho_in_sphere_rot_group assms by auto
  have "inv\<^bsub>(BijGroup sphere2)\<lparr>carrier := carrier sphere_rot_group\<rparr>\<^esub> (rho i) =
      inv\<^bsub>BijGroup sphere2\<^esub> (rho i)"
    using sphere_Bij.m_inv_consistent[OF sphere_rot_subgroup rho_i] .
  thus ?thesis
    by (simp add: sphere_rot_group_def)
qed

lemma sphere_rot_lift_gi_rho_eq_sphere_Bij:
  assumes "snd p \<in> Gen2"
  shows "sphere_rot.lift_gi rho p = sphere_Bij.lift_gi rho p"
  using assms
  by (cases p)
    (auto simp: sphere_rot.lift_gi_def sphere_Bij.lift_gi_def
      sphere_rot_inv_rho_eq_sphere_Bij)

lemma sphere_rot_lift_rho_eq_sphere_Bij:
  assumes "w \<in> lists (UNIV \<times> Gen2)"
  shows "sphere_rot.lift rho w = sphere_Bij.lift rho w"
  using assms
proof (induct w)
  case Nil
  show ?case
  proof -
    have "sphere_rot.lift rho [] = \<one>\<^bsub>sphere_rot_group\<^esub>"
      by simp
    also have "\<dots> = \<one>\<^bsub>BijGroup sphere2\<^esub>"
      by (simp add: sphere_rot_group_def)
    also have "\<dots> = sphere_Bij.lift rho []"
      by simp
    finally show ?case .
  qed
next
  case (Cons p w)
  have p_gen: "snd p \<in> Gen2"
    by (simp add: Gen2_UNIV)
  have w_lists: "w \<in> lists (UNIV \<times> Gen2)"
    using Cons.prems by (auto simp: Gen2_UNIV)
  have IH: "sphere_rot.lift rho w = sphere_Bij.lift rho w"
    using Cons.hyps w_lists by simp
  have gi_rot_closed: "sphere_rot.lift_gi rho p \<in> carrier sphere_rot_group"
    using rho_in_sphere_rot_group p_gen by (rule sphere_rot.lift_gi_closed)
  have tail_rot_closed: "sphere_rot.lift rho w \<in> carrier sphere_rot_group"
    using rho_in_sphere_rot_group w_lists by (rule sphere_rot.lift_closed)
  have gi_Bij_closed: "sphere_Bij.lift_gi rho p \<in> carrier (BijGroup sphere2)"
    using rho_in_BijGroup p_gen by (rule sphere_Bij.lift_gi_closed)
  have tail_Bij_closed: "sphere_Bij.lift rho w \<in> carrier (BijGroup sphere2)"
    using rho_in_BijGroup w_lists by (rule sphere_Bij.lift_closed)
  have "sphere_rot.lift rho (p # w) =
      sphere_rot.lift_gi rho p \<otimes>\<^bsub>sphere_rot_group\<^esub> sphere_rot.lift rho w"
    using gi_rot_closed tail_rot_closed
    by (simp add: sphere_rot.lift_def)
  also have "\<dots> =
      sphere_Bij.lift_gi rho p \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_Bij.lift rho w"
    using IH sphere_rot_lift_gi_rho_eq_sphere_Bij[OF p_gen]
    by (simp add: sphere_rot_group_def)
  also have "\<dots> = sphere_Bij.lift rho (p # w)"
    using gi_Bij_closed tail_Bij_closed
    by (simp add: sphere_Bij.lift_def)
  finally show ?case .
qed

lemma sphere_Bij_lift_rho_injective_if_ping_pong:
  fixes Xin Xout :: "gen2 \<Rightarrow> (real^3) set"
  assumes sub_out: "\<forall>i\<in>Gen2. Xout i \<subseteq> sphere2"
    and sub_in: "\<forall>i\<in>Gen2. Xin i \<subseteq> sphere2"
    and disj_out: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xout i \<inter> Xout j = {}"
    and disj_in: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xin i \<inter> Xin j = {}"
    and disj_cross: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. Xin i \<inter> Xout j = {}"
    and x_sphere: "x \<in> sphere2"
    and ping: "\<forall>i\<in>Gen2. rho i ` (sphere2 - Xout i) \<subseteq> Xin i"
    and pong: "\<forall>i\<in>Gen2. (inv\<^bsub>sphere_rot_group\<^esub> (rho i)) ` (sphere2 - Xin i) \<subseteq> Xout i"
  shows "inj_on (sphere_Bij.lift rho) (carrier F2)"
proof -
  have iso: "sphere_rot.lift rho \<in> iso F2 sphere_rot_group"
  proof (rule ping_pong_lemma[
      where X = sphere2 and I = Gen2 and act = id and g = rho
        and Xout = Xout and Xin = Xin and x = x])
    show "group sphere_rot_group"
      by (rule sphere_rot_group_is_group)
    show "id \<in> hom sphere_rot_group (BijGroup sphere2)"
      by (rule sphere_rot_inclusion_hom)
    show "rho \<in> Gen2 \<rightarrow> carrier sphere_rot_group"
      by (rule rho_in_sphere_rot_group)
    show "\<langle>rho ` Gen2\<rangle>\<^bsub>sphere_rot_group\<^esub> = carrier sphere_rot_group"
      by (rule sphere_rot_generated)
    show "\<forall>i\<in>Gen2. Xout i \<subseteq> sphere2"
      by (rule sub_out)
    show "\<forall>i\<in>Gen2. Xin i \<subseteq> sphere2"
      by (rule sub_in)
    show "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xout i \<inter> Xout j = {}"
      by (rule disj_out)
    show "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xin i \<inter> Xin j = {}"
      by (rule disj_in)
    show "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. Xin i \<inter> Xout j = {}"
      by (rule disj_cross)
    show "x \<in> sphere2"
      by (rule x_sphere)
    show "\<forall>i. Gen2 = {i} \<longrightarrow> x \<notin> Xout i \<and> x \<notin> Xin i"
      by auto
    show "\<forall>i\<in>Gen2. id (rho i) ` (sphere2 - Xout i) \<subseteq> Xin i"
      using ping by simp
    show "\<forall>i\<in>Gen2. id (inv\<^bsub>sphere_rot_group\<^esub> (rho i)) ` (sphere2 - Xin i) \<subseteq> Xout i"
      using pong by simp
  qed
  have inj_rot: "inj_on (sphere_rot.lift rho) (carrier F2)"
    using iso by (auto simp: iso_def bij_betw_def)
  show ?thesis
  proof (rule inj_onI)
    fix w v
    assume w: "w \<in> carrier F2" and v: "v \<in> carrier F2"
      and eq: "sphere_Bij.lift rho w = sphere_Bij.lift rho v"
    have w_lists: "w \<in> lists (UNIV \<times> Gen2)"
      using w by (simp add: F2_carrier_iff)
    have v_lists: "v \<in> lists (UNIV \<times> Gen2)"
      using v by (simp add: F2_carrier_iff)
    have "sphere_rot.lift rho w = sphere_Bij.lift rho w"
      using w_lists by (rule sphere_rot_lift_rho_eq_sphere_Bij)
    also have "\<dots> = sphere_Bij.lift rho v"
      by (rule eq)
    also have "\<dots> = sphere_rot.lift rho v"
      using v_lists by (rule sphere_rot_lift_rho_eq_sphere_Bij[symmetric])
    finally have "sphere_rot.lift rho w = sphere_rot.lift rho v" .
    with inj_rot w v show "w = v"
      by (auto simp: inj_on_def)
  qed
qed

definition sigma :: "(bool \<times> gen2) list \<Rightarrow> (real^3 \<Rightarrow> real^3)" where
  "sigma w = foldr (\<lambda>p f. letter_to_rot p \<circ> f) w id"

lemma letter_to_rot_cancel_left [simp]:
  "letter_to_rot (True, A) \<circ> letter_to_rot (False, A) = id"
  "letter_to_rot (False, A) \<circ> letter_to_rot (True, A) = id"
  "letter_to_rot (True, B) \<circ> letter_to_rot (False, B) = id"
  "letter_to_rot (False, B) \<circ> letter_to_rot (True, B) = id"
  by (simp_all add: letter_to_rot_def Rx_inv_left Rx_inv_right Rz_inv_left Rz_inv_right)

lemma letter_to_rot_canceling:
  assumes "canceling p q"
  shows "letter_to_rot p \<circ> letter_to_rot q = id"
  using assms
  by (cases p; cases q)
    (auto split: bool.splits gen2.splits
      simp: canceling_def letter_to_rot_def Rx_inv_left Rx_inv_right Rz_inv_left Rz_inv_right)

lemma sigma_Nil [simp]: "sigma [] = id"
  by (simp add: sigma_def)

lemma sigma_Cons [simp]: "sigma (p # w) = letter_to_rot p \<circ> sigma w"
  by (simp add: sigma_def)

lemma sigma_append [simp]: "sigma (u @ v) = sigma u \<circ> sigma v"
  by (induct u) (simp_all add: o_assoc)

lemma sigma_singleton [simp]: "sigma [p] = letter_to_rot p"
  by (simp add: fun_eq_iff)

lemma sigma_doubleton_canceling:
  assumes "canceling p q"
  shows "sigma [p, q] = id"
  using letter_to_rot_canceling[OF assms]
  by (simp add: o_def fun_eq_iff)

lemma sigma_cancels_to_1:
  assumes "cancels_to_1 x y"
  shows "sigma x = sigma y"
proof -
  from assms obtain xs1 x1 x2 xs2
    where x_eq: "x = xs1 @ x1 # x2 # xs2"
      and y_eq: "y = xs1 @ xs2"
      and cancel: "canceling x1 x2"
    by (rule cancels_to_1_unfold)
  have "sigma x = sigma xs1 \<circ> sigma [x1, x2] \<circ> sigma xs2"
    by (simp add: x_eq o_assoc)
  also have "\<dots> = sigma xs1 \<circ> sigma xs2"
    using letter_to_rot_canceling[OF cancel]
    by (auto simp: fun_eq_iff o_def)
  also have "\<dots> = sigma y"
    by (simp add: y_eq)
  finally show ?thesis .
qed

lemma sigma_cancels_to:
  assumes "cancels_to x y"
  shows "sigma x = sigma y"
  using assms unfolding cancels_to_def
proof (induct rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  then show ?case
    using sigma_cancels_to_1 by simp
qed

lemma sigma_normalize [simp]: "sigma (normalize w) = sigma w"
  using sigma_cancels_to[OF normalized_cancels_to] by simp

lemma letter_to_rot_in_SO3: "letter_to_rot p \<in> SO3"
  by (cases p)
    (auto split: bool.splits gen2.splits
      simp: letter_to_rot_def Rx_in_SO3 Rz_in_SO3 Rx_inv_in_SO3 Rz_inv_in_SO3)

lemma sphere_perm_letter_to_rot_in_Bij [simp]:
  "sphere_perm (letter_to_rot p) \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule letter_to_rot_in_SO3)

lemma sigma_in_SO3: "sigma w \<in> SO3"
proof (induct w)
  case Nil
  show ?case
    using id_in_SO3 by (simp add: id_def)
next
  case (Cons p w)
  have "letter_to_rot p \<circ> sigma w \<in> SO3"
    using letter_to_rot_in_SO3 Cons.hyps by (rule SO3_closed_compose)
  then show ?case by (simp add: o_def)
qed

lemma sigma_preserves_sphere2:
  assumes "x \<in> sphere2"
  shows "sigma w x \<in> sphere2"
  using rotation_preserves_sphere2[OF sigma_in_SO3 assms] .

lemma sigma_bij: "bij (sigma w)"
  using SO3_bij sigma_in_SO3 by blast

lemma sphere_perm_sigma_in_Bij [simp]:
  "sphere_perm (sigma w) \<in> Bij sphere2"
  by (rule sphere_perm_in_Bij) (rule sigma_in_SO3)

lemma sphere_Bij_lift_rho_eq_sigma:
  assumes "w \<in> lists (UNIV \<times> Gen2)"
  shows "sphere_Bij.lift rho w = sphere_perm (sigma w)"
  using assms
proof (induct w)
  case Nil
  show ?case
    by (simp add: sphere_perm_id[symmetric] id_def)
next
  case (Cons p w)
  have p_gen: "snd p \<in> Gen2"
    by (simp add: Gen2_UNIV)
  have w_lists: "w \<in> lists (UNIV \<times> Gen2)"
    using Cons.prems by (auto simp: Gen2_UNIV)
  have IH: "sphere_Bij.lift rho w = sphere_perm (sigma w)"
    using Cons.hyps w_lists by simp
  have singleton_lists: "[p] \<in> lists (UNIV \<times> Gen2)"
    by (simp add: Gen2_UNIV)
  have "sphere_Bij.lift rho (p # w) = sphere_Bij.lift rho ([p] @ w)"
    by simp
  also have "\<dots> = sphere_Bij.lift rho [p] \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_Bij.lift rho w"
    using sphere_Bij.lift_append[OF rho_in_BijGroup singleton_lists w_lists] .
  also have "sphere_Bij.lift rho [p] = sphere_perm (letter_to_rot p)"
  proof -
    have gi_closed: "sphere_Bij.lift_gi rho p \<in> carrier (BijGroup sphere2)"
      using rho_in_BijGroup p_gen by (rule sphere_Bij.lift_gi_closed)
    have "sphere_Bij.lift rho [p] = sphere_Bij.lift_gi rho p"
      using rho_in_BijGroup p_gen
      by (simp add: sphere_Bij.lift_def gi_closed)
    also have "\<dots> = sphere_perm (letter_to_rot p)"
      using p_gen by (rule sphere_Bij_lift_gi_rho)
    finally show ?thesis .
  qed
  also have "sphere_perm (letter_to_rot p) \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_Bij.lift rho w =
      sphere_perm (letter_to_rot p) \<otimes>\<^bsub>BijGroup sphere2\<^esub> sphere_perm (sigma w)"
    using IH by simp
  also have "\<dots> = sphere_perm (letter_to_rot p \<circ> sigma w)"
    by (rule sphere_perm_mult) simp_all
  also have "\<dots> = sphere_perm (sigma (p # w))"
    by simp
  finally show ?case .
qed

lemma sigma_injective_if_sphere_lift_injective:
  assumes "inj_on (sphere_Bij.lift rho) (carrier F2)"
  shows "inj_on sigma (carrier F2)"
proof (rule inj_onI)
  fix w v
  assume w: "w \<in> carrier F2" and v: "v \<in> carrier F2" and eq: "sigma w = sigma v"
  have w_lists: "w \<in> lists (UNIV \<times> Gen2)"
    using w by (simp add: F2_carrier_iff)
  have v_lists: "v \<in> lists (UNIV \<times> Gen2)"
    using v by (simp add: F2_carrier_iff)
  have "sphere_Bij.lift rho w = sphere_perm (sigma w)"
    using w_lists by (rule sphere_Bij_lift_rho_eq_sigma)
  also have "\<dots> = sphere_perm (sigma v)"
    using eq by simp
  also have "\<dots> = sphere_Bij.lift rho v"
    using v_lists by (rule sphere_Bij_lift_rho_eq_sigma[symmetric])
  finally have lift_eq: "sphere_Bij.lift rho w = sphere_Bij.lift rho v" .
  show "w = v"
    using assms w v lift_eq by (auto simp: inj_on_def)
qed

lemma sigma_injective_if_ping_pong:
  fixes Xin Xout :: "gen2 \<Rightarrow> (real^3) set"
  assumes sub_out: "\<forall>i\<in>Gen2. Xout i \<subseteq> sphere2"
    and sub_in: "\<forall>i\<in>Gen2. Xin i \<subseteq> sphere2"
    and disj_out: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xout i \<inter> Xout j = {}"
    and disj_in: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. i \<noteq> j \<longrightarrow> Xin i \<inter> Xin j = {}"
    and disj_cross: "\<forall>i\<in>Gen2. \<forall>j\<in>Gen2. Xin i \<inter> Xout j = {}"
    and x_sphere: "x \<in> sphere2"
    and ping: "\<forall>i\<in>Gen2. rho i ` (sphere2 - Xout i) \<subseteq> Xin i"
    and pong: "\<forall>i\<in>Gen2. (inv\<^bsub>sphere_rot_group\<^esub> (rho i)) ` (sphere2 - Xin i) \<subseteq> Xout i"
  shows "inj_on sigma (carrier F2)"
  by (rule sigma_injective_if_sphere_lift_injective)
    (rule sphere_Bij_lift_rho_injective_if_ping_pong[
      OF sub_out sub_in disj_out disj_in disj_cross x_sphere ping pong])

text \<open>The ping-pong criterion gives a reusable injectivity criterion for \<open>sigma\<close>.\<close>

section \<open>Arithmetic freeness invariant\<close>

text \<open>
  The classical proof that the above rotations generate a free subgroup
  is arithmetic rather than geometric: scale each letter by \<open>3\<close>, so
  every word has entries in the integer quadratic ring generated by
  @{term "sqrt 2"}.  A nonempty reduced word
  leaves a coefficient nonzero modulo \<open>3\<close> after applying it to a
  suitable basis vector, whereas the identity matrix would have all
  scaled off-axis coefficients divisible by \<open>3\<close>.

  The following definitions make that invariant explicit.  They are
  deliberately separated from real-vector semantics so that the finite
  modulo-\<open>3\<close> induction can be discharged by simplification and case
  analysis before being connected back to \<open>sigma\<close>.
\<close>

type_synonym zsqrt2 = "int \<times> int"
type_synonym zvec3 = "zsqrt2 \<times> zsqrt2 \<times> zsqrt2"

definition zsqrt2_val :: "zsqrt2 \<Rightarrow> real" where
  "zsqrt2_val q = of_int (fst q) + of_int (snd q) * sqrt 2"

definition zsqrt2_add :: "zsqrt2 \<Rightarrow> zsqrt2 \<Rightarrow> zsqrt2" where
  "zsqrt2_add p q = (fst p + fst q, snd p + snd q)"

definition zsqrt2_neg :: "zsqrt2 \<Rightarrow> zsqrt2" where
  "zsqrt2_neg p = (- fst p, - snd p)"

definition zsqrt2_sub :: "zsqrt2 \<Rightarrow> zsqrt2 \<Rightarrow> zsqrt2" where
  "zsqrt2_sub p q = zsqrt2_add p (zsqrt2_neg q)"

definition zsqrt2_scale :: "int \<Rightarrow> zsqrt2 \<Rightarrow> zsqrt2" where
  "zsqrt2_scale n p = (n * fst p, n * snd p)"

definition zsqrt2_mul_sqrt2 :: "zsqrt2 \<Rightarrow> zsqrt2" where
  "zsqrt2_mul_sqrt2 p = (2 * snd p, fst p)"

definition zsqrt2_div3 :: "zsqrt2 \<Rightarrow> bool" where
  "zsqrt2_div3 p \<longleftrightarrow> 3 dvd fst p \<and> 3 dvd snd p"

definition zvec3_div3 :: "zvec3 \<Rightarrow> bool" where
  "zvec3_div3 v \<longleftrightarrow>
    (case v of (x, y, z) \<Rightarrow> zsqrt2_div3 x \<and> zsqrt2_div3 y \<and> zsqrt2_div3 z)"

definition zvec3_scale :: "int \<Rightarrow> zvec3 \<Rightarrow> zvec3" where
  "zvec3_scale n v = (case v of (x, y, z) \<Rightarrow>
     (zsqrt2_scale n x, zsqrt2_scale n y, zsqrt2_scale n z))"

definition zvec3_val :: "zvec3 \<Rightarrow> real^3" where
  "zvec3_val v = (case v of (x, y, z) \<Rightarrow>
     vector [zsqrt2_val x, zsqrt2_val y, zsqrt2_val z])"

definition ze_x :: zvec3 where
  "ze_x = ((1, 0), (0, 0), (0, 0))"

definition ze_y :: zvec3 where
  "ze_y = ((0, 0), (1, 0), (0, 0))"

definition ze_z :: zvec3 where
  "ze_z = ((0, 0), (0, 0), (1, 0))"

definition zRx_step :: "zvec3 \<Rightarrow> zvec3" where
  "zRx_step v = (case v of (x, y, z) \<Rightarrow>
     (zsqrt2_scale 3 x,
      zsqrt2_sub y (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 z)),
      zsqrt2_add (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 y)) z))"

definition zRx_inv_step :: "zvec3 \<Rightarrow> zvec3" where
  "zRx_inv_step v = (case v of (x, y, z) \<Rightarrow>
     (zsqrt2_scale 3 x,
      zsqrt2_add y (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 z)),
      zsqrt2_sub z (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 y))))"

definition zRz_step :: "zvec3 \<Rightarrow> zvec3" where
  "zRz_step v = (case v of (x, y, z) \<Rightarrow>
     (zsqrt2_sub x (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 y)),
      zsqrt2_add (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 x)) y,
      zsqrt2_scale 3 z))"

definition zRz_inv_step :: "zvec3 \<Rightarrow> zvec3" where
  "zRz_inv_step v = (case v of (x, y, z) \<Rightarrow>
     (zsqrt2_add x (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 y)),
      zsqrt2_sub y (zsqrt2_scale 2 (zsqrt2_mul_sqrt2 x)),
      zsqrt2_scale 3 z))"

definition zletter_step :: "bool \<times> gen2 \<Rightarrow> zvec3 \<Rightarrow> zvec3" where
  "zletter_step p = (case p of
       (False, A) \<Rightarrow> zRx_step
     | (True,  A) \<Rightarrow> zRx_inv_step
     | (False, B) \<Rightarrow> zRz_step
     | (True,  B) \<Rightarrow> zRz_inv_step)"

definition zword_step :: "(bool \<times> gen2) list \<Rightarrow> zvec3 \<Rightarrow> zvec3" where
  "zword_step w v = foldr (\<lambda>p f. zletter_step p \<circ> f) w id v"

definition zword_witness :: "(bool \<times> gen2) list \<Rightarrow> zvec3" where
  "zword_witness w = (case snd (last w) of A \<Rightarrow> ze_y | B \<Rightarrow> ze_x)"

datatype r3 = R0 | R1 | R2

type_synonym rcoef = "r3 \<times> r3"
type_synonym rvec3 = "rcoef \<times> rcoef \<times> rcoef"

fun r3_add :: "r3 \<Rightarrow> r3 \<Rightarrow> r3" where
  "r3_add R0 x = x"
| "r3_add x R0 = x"
| "r3_add R1 R1 = R2"
| "r3_add R1 R2 = R0"
| "r3_add R2 R1 = R0"
| "r3_add R2 R2 = R1"

fun r3_neg :: "r3 \<Rightarrow> r3" where
  "r3_neg R0 = R0"
| "r3_neg R1 = R2"
| "r3_neg R2 = R1"

definition r3_sub :: "r3 \<Rightarrow> r3 \<Rightarrow> r3" where
  "r3_sub x y = r3_add x (r3_neg y)"

fun r3_double :: "r3 \<Rightarrow> r3" where
  "r3_double R0 = R0"
| "r3_double R1 = R2"
| "r3_double R2 = R1"

definition rcoef_add :: "rcoef \<Rightarrow> rcoef \<Rightarrow> rcoef" where
  "rcoef_add p q = (r3_add (fst p) (fst q), r3_add (snd p) (snd q))"

definition rcoef_neg :: "rcoef \<Rightarrow> rcoef" where
  "rcoef_neg p = (r3_neg (fst p), r3_neg (snd p))"

definition rcoef_sub :: "rcoef \<Rightarrow> rcoef \<Rightarrow> rcoef" where
  "rcoef_sub p q = rcoef_add p (rcoef_neg q)"

definition rcoef_double :: "rcoef \<Rightarrow> rcoef" where
  "rcoef_double p = (r3_double (fst p), r3_double (snd p))"

definition rcoef_mul_sqrt2 :: "rcoef \<Rightarrow> rcoef" where
  "rcoef_mul_sqrt2 p = (r3_double (snd p), fst p)"

definition rRx_step :: "rvec3 \<Rightarrow> rvec3" where
  "rRx_step v = (case v of (x, y, z) \<Rightarrow>
     ((R0, R0),
      rcoef_sub y (rcoef_double (rcoef_mul_sqrt2 z)),
      rcoef_add (rcoef_double (rcoef_mul_sqrt2 y)) z))"

definition rRx_inv_step :: "rvec3 \<Rightarrow> rvec3" where
  "rRx_inv_step v = (case v of (x, y, z) \<Rightarrow>
     ((R0, R0),
      rcoef_add y (rcoef_double (rcoef_mul_sqrt2 z)),
      rcoef_sub z (rcoef_double (rcoef_mul_sqrt2 y))))"

definition rRz_step :: "rvec3 \<Rightarrow> rvec3" where
  "rRz_step v = (case v of (x, y, z) \<Rightarrow>
     (rcoef_sub x (rcoef_double (rcoef_mul_sqrt2 y)),
      rcoef_add (rcoef_double (rcoef_mul_sqrt2 x)) y,
      (R0, R0)))"

definition rRz_inv_step :: "rvec3 \<Rightarrow> rvec3" where
  "rRz_inv_step v = (case v of (x, y, z) \<Rightarrow>
     (rcoef_add x (rcoef_double (rcoef_mul_sqrt2 y)),
      rcoef_sub y (rcoef_double (rcoef_mul_sqrt2 x)),
      (R0, R0)))"

definition rletter_step :: "bool \<times> gen2 \<Rightarrow> rvec3 \<Rightarrow> rvec3" where
  "rletter_step p = (case p of
       (False, A) \<Rightarrow> rRx_step
     | (True,  A) \<Rightarrow> rRx_inv_step
     | (False, B) \<Rightarrow> rRz_step
     | (True,  B) \<Rightarrow> rRz_inv_step)"

definition rword_step :: "(bool \<times> gen2) list \<Rightarrow> rvec3 \<Rightarrow> rvec3" where
  "rword_step w v = foldr (\<lambda>p f. rletter_step p \<circ> f) w id v"

definition re_x :: rvec3 where
  "re_x = ((R1, R0), (R0, R0), (R0, R0))"

definition re_y :: rvec3 where
  "re_y = ((R0, R0), (R1, R0), (R0, R0))"

definition rword_witness :: "(bool \<times> gen2) list \<Rightarrow> rvec3" where
  "rword_witness w = (case snd (last w) of A \<Rightarrow> re_y | B \<Rightarrow> re_x)"

definition rzero_vec :: rvec3 where
  "rzero_vec = ((R0, R0), (R0, R0), (R0, R0))"

definition rstate :: "bool \<times> gen2 \<Rightarrow> rvec3 \<Rightarrow> bool" where
  "rstate p v \<longleftrightarrow>
    v \<in> (case p of
       (False, A) \<Rightarrow> {
          ((R0, R0), (R0, R1), (R1, R0)),
          ((R0, R0), (R0, R2), (R2, R0)),
          ((R0, R0), (R1, R0), (R0, R2)),
          ((R0, R0), (R2, R0), (R0, R1))}
     | (True, A) \<Rightarrow> {
          ((R0, R0), (R0, R1), (R2, R0)),
          ((R0, R0), (R0, R2), (R1, R0)),
          ((R0, R0), (R1, R0), (R0, R1)),
          ((R0, R0), (R2, R0), (R0, R2))}
     | (False, B) \<Rightarrow> {
          ((R0, R1), (R1, R0), (R0, R0)),
          ((R0, R2), (R2, R0), (R0, R0)),
          ((R1, R0), (R0, R2), (R0, R0)),
          ((R2, R0), (R0, R1), (R0, R0))}
     | (True, B) \<Rightarrow> {
          ((R0, R1), (R2, R0), (R0, R0)),
          ((R0, R2), (R1, R0), (R0, R0)),
          ((R1, R0), (R0, R1), (R0, R0)),
          ((R2, R0), (R0, R2), (R0, R0))})"

lemma rstate_single:
  "rstate p (rletter_step p (case snd p of A \<Rightarrow> re_y | B \<Rightarrow> re_x))"
  by (cases p)
    (auto split: bool.splits gen2.splits
      simp: rstate_def rletter_step_def rRx_step_def rRx_inv_step_def
        rRz_step_def rRz_inv_step_def re_x_def re_y_def rcoef_add_def
        rcoef_sub_def rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def)

lemma rstate_step_FA_FA:
  "rstate (False, A) v \<Longrightarrow> rstate (False, A) (rletter_step (False, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_FA_FB:
  "rstate (False, B) v \<Longrightarrow> rstate (False, A) (rletter_step (False, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_FA_TB:
  "rstate (True, B) v \<Longrightarrow> rstate (False, A) (rletter_step (False, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TA_TA:
  "rstate (True, A) v \<Longrightarrow> rstate (True, A) (rletter_step (True, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TA_FB:
  "rstate (False, B) v \<Longrightarrow> rstate (True, A) (rletter_step (True, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TA_TB:
  "rstate (True, B) v \<Longrightarrow> rstate (True, A) (rletter_step (True, A) v)"
  by (simp add: rstate_def rletter_step_def rRx_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_FB_FB:
  "rstate (False, B) v \<Longrightarrow> rstate (False, B) (rletter_step (False, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_FB_FA:
  "rstate (False, A) v \<Longrightarrow> rstate (False, B) (rletter_step (False, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_FB_TA:
  "rstate (True, A) v \<Longrightarrow> rstate (False, B) (rletter_step (False, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TB_TB:
  "rstate (True, B) v \<Longrightarrow> rstate (True, B) (rletter_step (True, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TB_FA:
  "rstate (False, A) v \<Longrightarrow> rstate (True, B) (rletter_step (True, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemma rstate_step_TB_TA:
  "rstate (True, A) v \<Longrightarrow> rstate (True, B) (rletter_step (True, B) v)"
  by (simp add: rstate_def rletter_step_def rRz_inv_step_def rcoef_add_def rcoef_sub_def
      rcoef_neg_def rcoef_double_def rcoef_mul_sqrt2_def r3_sub_def; elim disjE; simp)

lemmas rstate_step_cases =
  rstate_step_FA_FA rstate_step_FA_FB rstate_step_FA_TB
  rstate_step_TA_TA rstate_step_TA_FB rstate_step_TA_TB
  rstate_step_FB_FB rstate_step_FB_FA rstate_step_FB_TA
  rstate_step_TB_TB rstate_step_TB_FA rstate_step_TB_TA

lemma rstate_step:
  assumes "rstate q v" and "\<not> canceling p q"
  shows "rstate p (rletter_step p v)"
  using assms
  by (cases p; cases q; cases "fst p"; cases "snd p"; cases "fst q"; cases "snd q")
    (auto simp: canceling_def rstate_step_cases)

lemma rstate_nonzero:
  assumes "rstate p v"
  shows "v \<noteq> rzero_vec"
  using assms
  by (cases p)
    (auto split: bool.splits gen2.splits simp: rstate_def rzero_vec_def)

lemma rword_step_Cons [simp]:
  "rword_step (p # w) v = rletter_step p (rword_step w v)"
  by (simp add: rword_step_def)

lemma zword_step_Cons [simp]:
  "zword_step (p # w) v = zletter_step p (zword_step w v)"
  by (simp add: zword_step_def)

lemma rword_witness_Cons_nonempty [simp]:
  assumes "w \<noteq> []"
  shows "rword_witness (p # w) = rword_witness w"
  using assms by (cases w) (simp_all add: rword_witness_def)

lemma rword_step_witness_state:
  assumes "w \<in> carrier F2" and "w \<noteq> []"
  shows "rstate (hd w) (rword_step w (rword_witness w))"
  using assms
proof (induct w)
  case Nil
  then show ?case
    by simp
next
  case (Cons p w)
  have tail: "w \<in> carrier F2" and ncan_tail: "w = [] \<or> \<not> canceling p (hd w)"
    using Cons.prems(1) by (auto dest: F2_ConsD)
  show ?case
  proof (cases w)
    case Nil
    then show ?thesis
      using rstate_single[of p] by (simp add: rword_step_def rword_witness_def)
  next
    case (Cons q ws)
    have "rstate q (rword_step (q # ws) (rword_witness (q # ws)))"
      using Cons.hyps[OF tail] Cons by simp
    moreover have "\<not> canceling p q"
      using ncan_tail Cons by simp
    ultimately have "rstate p (rletter_step p (rword_step (q # ws) (rword_witness (q # ws))))"
      by (rule rstate_step)
    then show ?thesis
      using Cons by simp
  qed
qed

definition r3_of_int :: "int \<Rightarrow> r3" where
  "r3_of_int n = (if n mod 3 = 0 then R0 else if n mod 3 = 1 then R1 else R2)"

definition rcoef_of_z :: "zsqrt2 \<Rightarrow> rcoef" where
  "rcoef_of_z p = (r3_of_int (fst p), r3_of_int (snd p))"

definition rvec3_of_z :: "zvec3 \<Rightarrow> rvec3" where
  "rvec3_of_z v = (case v of (x, y, z) \<Rightarrow> (rcoef_of_z x, rcoef_of_z y, rcoef_of_z z))"

lemma r3_of_int_add:
  "r3_of_int (a + b) = r3_add (r3_of_int a) (r3_of_int b)"
  by (auto simp: r3_of_int_def split: if_splits; presburger)

lemma r3_of_int_neg:
  "r3_of_int (- a) = r3_neg (r3_of_int a)"
  by (auto simp: r3_of_int_def split: if_splits; presburger)

lemma r3_of_int_sub:
  "r3_of_int (a - b) = r3_add (r3_of_int a) (r3_neg (r3_of_int b))"
  by (auto simp: r3_of_int_def split: if_splits; presburger)

lemma r3_of_int_double:
  "r3_of_int (2 * a) = r3_double (r3_of_int a)"
  by (auto simp: r3_of_int_def split: if_splits; presburger)

lemma r3_of_int_triple:
  "r3_of_int (3 * a) = R0"
  by (simp add: r3_of_int_def)

lemma rcoef_of_z_simps [simp]:
  "rcoef_of_z (zsqrt2_add p q) = rcoef_add (rcoef_of_z p) (rcoef_of_z q)"
  "rcoef_of_z (zsqrt2_neg p) = rcoef_neg (rcoef_of_z p)"
  "rcoef_of_z (zsqrt2_sub p q) = rcoef_sub (rcoef_of_z p) (rcoef_of_z q)"
  "rcoef_of_z (zsqrt2_scale 2 p) = rcoef_double (rcoef_of_z p)"
  "rcoef_of_z (zsqrt2_scale 3 p) = (R0, R0)"
  "rcoef_of_z (zsqrt2_mul_sqrt2 p) = rcoef_mul_sqrt2 (rcoef_of_z p)"
  by (simp_all add: rcoef_of_z_def zsqrt2_add_def zsqrt2_neg_def zsqrt2_sub_def
      zsqrt2_scale_def zsqrt2_mul_sqrt2_def rcoef_add_def rcoef_neg_def rcoef_sub_def
      rcoef_double_def rcoef_mul_sqrt2_def r3_of_int_add r3_of_int_neg
      r3_of_int_sub r3_of_int_double r3_of_int_triple)

lemma rvec3_of_z_basis [simp]:
  "rvec3_of_z ze_x = re_x"
  "rvec3_of_z ze_y = re_y"
  by (simp_all add: rvec3_of_z_def rcoef_of_z_def ze_x_def ze_y_def re_x_def re_y_def r3_of_int_def)

lemma rstep_of_z_simps [simp]:
  "rvec3_of_z (zRx_step v) = rRx_step (rvec3_of_z v)"
  "rvec3_of_z (zRx_inv_step v) = rRx_inv_step (rvec3_of_z v)"
  "rvec3_of_z (zRz_step v) = rRz_step (rvec3_of_z v)"
  "rvec3_of_z (zRz_inv_step v) = rRz_inv_step (rvec3_of_z v)"
  by (cases v; simp add: rvec3_of_z_def zRx_step_def zRx_inv_step_def zRz_step_def
        zRz_inv_step_def rRx_step_def rRx_inv_step_def rRz_step_def rRz_inv_step_def)+

lemma rletter_step_of_z [simp]:
  "rvec3_of_z (zletter_step p v) = rletter_step p (rvec3_of_z v)"
  by (cases p)
    (auto split: bool.splits gen2.splits simp: zletter_step_def rletter_step_def)

lemma rword_step_of_z [simp]:
  "rvec3_of_z (zword_step w v) = rword_step w (rvec3_of_z v)"
proof (induct w arbitrary: v)
  case Nil
  then show ?case
    by (simp add: zword_step_def rword_step_def)
next
  case (Cons p w)
  then show ?case
    by simp
qed

lemma rword_witness_of_z [simp]:
  "rvec3_of_z (zword_witness w) = rword_witness w"
  by (cases "snd (last w)")
    (simp_all add: zword_witness_def rword_witness_def)

lemma r3_of_int_eq_R0_iff:
  "r3_of_int n = R0 \<longleftrightarrow> 3 dvd n"
  by (simp add: r3_of_int_def dvd_eq_mod_eq_0)

lemma rcoef_of_z_zero_iff:
  "rcoef_of_z p = (R0, R0) \<longleftrightarrow> zsqrt2_div3 p"
  by (cases p) (simp add: rcoef_of_z_def zsqrt2_div3_def r3_of_int_eq_R0_iff)

lemma rvec3_of_z_zero_iff:
  "rvec3_of_z v = rzero_vec \<longleftrightarrow> zvec3_div3 v"
  by (cases v) (simp add: rvec3_of_z_def rzero_vec_def zvec3_div3_def rcoef_of_z_zero_iff)

lemma zsqrt2_val_simps [simp]:
  "zsqrt2_val (zsqrt2_add p q) = zsqrt2_val p + zsqrt2_val q"
  "zsqrt2_val (zsqrt2_neg p) = - zsqrt2_val p"
  "zsqrt2_val (zsqrt2_sub p q) = zsqrt2_val p - zsqrt2_val q"
  "zsqrt2_val (zsqrt2_scale n p) = of_int n * zsqrt2_val p"
  unfolding zsqrt2_val_def zsqrt2_add_def zsqrt2_neg_def zsqrt2_sub_def zsqrt2_scale_def
  by (simp_all add: algebra_simps)

lemma zsqrt2_mul_sqrt2_val [simp]:
  "zsqrt2_val (zsqrt2_mul_sqrt2 p) = sqrt 2 * zsqrt2_val p"
  unfolding zsqrt2_val_def zsqrt2_mul_sqrt2_def
  by (simp add: algebra_simps)

lemma sqrt_prime_irrational_dev:
  fixes p :: nat
  assumes "prime p"
  shows "sqrt p \<notin> \<rat>"
proof
  from assms have p: "p > 1"
    by (rule prime_gt_1_nat)
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat
    where n: "n \<noteq> 0"
      and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
      and "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  have eq: "m\<^sup>2 = p * n\<^sup>2"
  proof -
    from n sqrt_rat have "m = \<bar>sqrt p\<bar> * n"
      by simp
    then have "m\<^sup>2 = (sqrt p)\<^sup>2 * n\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "(sqrt p)\<^sup>2 = p"
      by simp
    also have "\<dots> * n\<^sup>2 = p * n\<^sup>2"
      by simp
    finally show ?thesis
      by linarith
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<^sup>2" ..
    with assms show "p dvd m"
      by (rule prime_dvd_power)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2"
      by algebra
    with p have "n\<^sup>2 = p * k\<^sup>2"
      by (simp add: power2_eq_square)
    then have "p dvd n\<^sup>2" ..
    with assms show "p dvd n"
      by (rule prime_dvd_power)
  qed
  then have "p dvd gcd m n"
    by simp
  with \<open>coprime m n\<close> have "p = 1"
    by simp
  with p show False
    by simp
qed

lemma sqrt_2_not_rat_dev: "sqrt 2 \<notin> \<rat>"
  using sqrt_prime_irrational_dev[of 2] by simp

lemma zsqrt2_val_eq_iff:
  "zsqrt2_val p = zsqrt2_val q \<longleftrightarrow> p = q"
proof
  assume eq: "zsqrt2_val p = zsqrt2_val q"
  obtain a b c d where defs: "p = (a, b)" "q = (c, d)"
    by (cases p; cases q) auto
  let ?A = "a - c"
  let ?B = "b - d"
  from eq defs have eq0: "of_int ?A + of_int ?B * sqrt 2 = (0::real)"
    by (simp add: zsqrt2_val_def algebra_simps)
  have "?B = 0"
  proof (rule ccontr)
    assume "?B \<noteq> 0"
    hence "sqrt 2 = - of_int ?A / of_int ?B"
      using eq0 by (simp add: field_simps)
    moreover have "- of_int ?A / of_int ?B \<in> \<rat>"
      by simp
    ultimately have "sqrt 2 \<in> \<rat>"
      by simp
    with sqrt_2_not_rat_dev show False
      by simp
  qed
  moreover with eq0 have "?A = 0"
    by simp
  ultimately show "p = q"
    using defs by simp
qed simp

lemma zvec3_val_eq_iff:
  "zvec3_val u = zvec3_val v \<longleftrightarrow> u = v"
  by (cases u; cases v)
    (auto simp: zvec3_val_def vector_def vec_eq_iff forall_3 zsqrt2_val_eq_iff)

lemma zvec3_scale_val [simp]:
  "zvec3_val (zvec3_scale n v) = scaleR (of_int n) (zvec3_val v)"
  by (cases v)
    (simp add: zvec3_scale_def zvec3_val_def vector_def vec_eq_iff forall_3)

lemma sqrt8_eq_2_sqrt2: "sqrt 8 = 2 * sqrt 2"
  proof -
  have "sqrt (8::real) = sqrt ((4::real) * 2)"
    by simp
  also have "\<dots> = sqrt (4::real) * sqrt 2"
    by (subst real_sqrt_mult) simp
  also have "\<dots> = 2 * sqrt 2"
    by simp
  finally show ?thesis .
qed

lemma zletter_step_single_mod3:
  "\<not> zvec3_div3 (zletter_step (False, A) ze_y)"
  "\<not> zvec3_div3 (zletter_step (True, A) ze_y)"
  "\<not> zvec3_div3 (zletter_step (False, B) ze_x)"
  "\<not> zvec3_div3 (zletter_step (True, B) ze_x)"
  by (simp_all add: zletter_step_def zRx_step_def zRx_inv_step_def zRz_step_def zRz_inv_step_def
      ze_x_def ze_y_def zvec3_div3_def zsqrt2_div3_def zsqrt2_add_def zsqrt2_sub_def
      zsqrt2_neg_def zsqrt2_scale_def zsqrt2_mul_sqrt2_def)

lemma zRx_step_val:
  "zvec3_val (zRx_step v) = scaleR 3 (Rx (zvec3_val v))"
  by (cases v)
    (simp add: zvec3_val_def zRx_step_def Rx_def Rx_mat_def rot_c_def rot_s_def
      sqrt8_eq_2_sqrt2 matrix_vector_mult_def vector_def vec_eq_iff sum_3 forall_3 algebra_simps)

lemma zRx_inv_step_val:
  "zvec3_val (zRx_inv_step v) = scaleR 3 (Rx_inv (zvec3_val v))"
  by (cases v)
    (simp add: zvec3_val_def zRx_inv_step_def Rx_inv_def Rx_inv_mat_def rot_c_def rot_s_def
      sqrt8_eq_2_sqrt2 matrix_vector_mult_def vector_def vec_eq_iff sum_3 forall_3 algebra_simps)

lemma zRz_step_val:
  "zvec3_val (zRz_step v) = scaleR 3 (Rz (zvec3_val v))"
  by (cases v)
    (simp add: zvec3_val_def zRz_step_def Rz_def Rz_mat_def rot_c_def rot_s_def
      sqrt8_eq_2_sqrt2 matrix_vector_mult_def vector_def vec_eq_iff sum_3 forall_3 algebra_simps)

lemma zRz_inv_step_val:
  "zvec3_val (zRz_inv_step v) = scaleR 3 (Rz_inv (zvec3_val v))"
  by (cases v)
    (simp add: zvec3_val_def zRz_inv_step_def Rz_inv_def Rz_inv_mat_def rot_c_def rot_s_def
      sqrt8_eq_2_sqrt2 matrix_vector_mult_def vector_def vec_eq_iff sum_3 forall_3 algebra_simps)

lemma zletter_step_val:
  "zvec3_val (zletter_step p v) = scaleR 3 (letter_to_rot p (zvec3_val v))"
  by (cases p)
    (auto split: bool.splits gen2.splits
      simp: zletter_step_def letter_to_rot_def zRx_step_val zRx_inv_step_val
        zRz_step_val zRz_inv_step_val)

lemma letter_to_rot_linear: "linear (letter_to_rot p)"
  unfolding letter_to_rot_def Rx_def Rx_inv_def Rz_def Rz_inv_def
  by (cases p)
    (simp split: bool.splits gen2.splits add: matrix_vector_mul_linear)

lemma zword_step_val:
  "zvec3_val (zword_step w v) =
    scaleR ((3::real) ^ length w) (sigma w (zvec3_val v))"
proof (induct w arbitrary: v)
  case Nil
  show ?case
    by (simp add: zword_step_def)
next
  case (Cons p w)
  have lin: "linear (letter_to_rot p)"
    by (rule letter_to_rot_linear)
  have "zvec3_val (zword_step (p # w) v) =
      zvec3_val (zletter_step p (zword_step w v))"
    by (simp add: zword_step_def)
  also have "\<dots> = scaleR 3 (letter_to_rot p (zvec3_val (zword_step w v)))"
    by (rule zletter_step_val)
  also have "\<dots> =
      scaleR 3 (letter_to_rot p
        (scaleR ((3::real) ^ length w) (sigma w (zvec3_val v))))"
    using Cons.hyps by simp
  also have "\<dots> =
      scaleR ((3::real) ^ Suc (length w)) ((letter_to_rot p \<circ> sigma w) (zvec3_val v))"
    using linear.scaleR[OF lin, of "((3::real) ^ length w)" "sigma w (zvec3_val v)"]
    by (simp add: scaleR_scaleR mult_ac)
  also have "\<dots> = scaleR ((3::real) ^ length (p # w)) (sigma (p # w) (zvec3_val v))"
    by simp
  finally show ?case .
qed

lemma zvec3_scale_power3_div3:
  assumes "n > 0"
  shows "zvec3_div3 (zvec3_scale ((3::int) ^ n) v)"
  using assms
  by (cases v)
    (auto simp: zvec3_div3_def zsqrt2_div3_def zvec3_scale_def zsqrt2_scale_def
      intro!: dvd_mult2)

lemma zword_step_identity_div3:
  assumes "w \<noteq> []" and "sigma w = id"
  shows "zvec3_div3 (zword_step w (zword_witness w))"
proof -
  have len_pos: "length w > 0"
    using assms(1) by (cases w) auto
  have "zvec3_val (zword_step w (zword_witness w)) =
      scaleR ((3::real) ^ length w) (zvec3_val (zword_witness w))"
    using zword_step_val[of w "zword_witness w"] assms(2) by simp
  also have "\<dots> = zvec3_val (zvec3_scale ((3::int) ^ length w) (zword_witness w))"
    by simp
  finally have "zword_step w (zword_witness w) =
      zvec3_scale ((3::int) ^ length w) (zword_witness w)"
    using zvec3_val_eq_iff by blast
  thus ?thesis
    using zvec3_scale_power3_div3[OF len_pos, of "zword_witness w"] by simp
qed

lemma zword_step_witness_not_div3_if_nonempty_F2:
  assumes "w \<in> carrier F2" and "w \<noteq> []"
  shows "\<not> zvec3_div3 (zword_step w (zword_witness w))"
proof
  assume div3: "zvec3_div3 (zword_step w (zword_witness w))"
  have "rstate (hd w) (rword_step w (rword_witness w))"
    using assms by (rule rword_step_witness_state)
  hence "rword_step w (rword_witness w) \<noteq> rzero_vec"
    by (rule rstate_nonzero)
  moreover from div3 have "rword_step w (rword_witness w) = rzero_vec"
    by (simp add: rvec3_of_z_zero_iff[symmetric])
  ultimately show False
    by contradiction
qed

text \<open>The word interpretation is an injective homomorphism into \<open>SO(3)\<close>.\<close>
theorem sigma_homomorphism:
  assumes "w1 \<in> carrier F2" "w2 \<in> carrier F2"
  shows "sigma (w1 \<otimes>\<^bsub>F2\<^esub> w2) = sigma w1 \<circ> sigma w2"
  by (simp add: F2_mult)

theorem sigma_nontrivial_word_not_id:
  assumes "w \<in> carrier F2" and "w \<noteq> []"
  shows "sigma w \<noteq> id"
proof
  assume "sigma w = id"
  hence "zvec3_div3 (zword_step w (zword_witness w))"
    using assms(2) by (intro zword_step_identity_div3)
  moreover have "\<not> zvec3_div3 (zword_step w (zword_witness w))"
    using assms by (rule zword_step_witness_not_div3_if_nonempty_F2)
  ultimately show False
    by simp
qed

lemma sigma_injective_if_trivial_kernel:
  assumes kernel: "\<And>w. w \<in> carrier F2 \<Longrightarrow> w \<noteq> [] \<Longrightarrow> sigma w \<noteq> id"
  shows "inj_on sigma (carrier F2)"
proof (rule inj_onI)
  interpret F: group F2
    by (rule F2_is_group)
  fix w v
  assume w: "w \<in> carrier F2" and v: "v \<in> carrier F2" and eq: "sigma w = sigma v"
  let ?iv = "inv\<^bsub>F2\<^esub> v"
  have iv: "?iv \<in> carrier F2"
    using v by (rule F.inv_closed)
  have prod: "w \<otimes>\<^bsub>F2\<^esub> ?iv \<in> carrier F2"
    using w iv by (rule F.m_closed)
  have "sigma (w \<otimes>\<^bsub>F2\<^esub> ?iv) = sigma w \<circ> sigma ?iv"
    using w iv by (rule sigma_homomorphism)
  also have "\<dots> = sigma v \<circ> sigma ?iv"
    using eq by simp
  also have "\<dots> = sigma (v \<otimes>\<^bsub>F2\<^esub> ?iv)"
    using v iv by (rule sigma_homomorphism[symmetric])
  also have "\<dots> = sigma []"
    using F.r_inv[OF v] by simp
  also have "\<dots> = id"
    by simp
  finally have prod_id: "sigma (w \<otimes>\<^bsub>F2\<^esub> ?iv) = id" .
  have prod_one: "w \<otimes>\<^bsub>F2\<^esub> ?iv = []"
  proof (rule ccontr)
    assume "w \<otimes>\<^bsub>F2\<^esub> ?iv \<noteq> []"
    with kernel[OF prod] prod_id show False
      by simp
  qed
  have "w = w \<otimes>\<^bsub>F2\<^esub> \<one>\<^bsub>F2\<^esub>"
    using w by simp
  moreover have "?iv \<otimes>\<^bsub>F2\<^esub> v = \<one>\<^bsub>F2\<^esub>"
    using v by (rule F.l_inv)
  ultimately have "w = w \<otimes>\<^bsub>F2\<^esub> (?iv \<otimes>\<^bsub>F2\<^esub> v)"
    by simp
  also have "\<dots> = (w \<otimes>\<^bsub>F2\<^esub> ?iv) \<otimes>\<^bsub>F2\<^esub> v"
    using w iv v by (simp add: F.m_assoc)
  also have "\<dots> = v"
    using prod_one v by simp
  finally show "w = v" .
qed

theorem sigma_injective_on_F2:
  "inj_on sigma (carrier F2)"
  by (rule sigma_injective_if_trivial_kernel) (rule sigma_nontrivial_word_not_id)

theorem sigma_image_in_SO3:
  assumes "w \<in> carrier F2"
  shows "sigma w \<in> SO3"
  by (rule sigma_in_SO3)

text \<open>
  These three theorems together establish that \<open>sigma\<close> is a
  group monomorphism from \<open>F\<^sub>2\<close> to SO(3) -- i.e., the image
  is a copy of \<open>F\<^sub>2\<close> inside SO(3). This supplies the free subgroup
  used in the geometric part of the Banach-Tarski theorem.
\<close>

end
