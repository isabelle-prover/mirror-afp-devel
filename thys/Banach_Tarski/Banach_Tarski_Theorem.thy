(*  Title:       Banach_Tarski_Theorem.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    The main theorem.

    Statement (Banach-Tarski, modern form):
      The closed unit ball B^3 in R^3 admits a finite partition into pieces
      that can be reassembled, by isometries of R^3, into TWO disjoint copies
      of B^3.
*)

theory Banach_Tarski_Theorem
  imports Ball_Decomposition
begin

text \<open>
  Two copies of the ball, embedded in disjoint regions of \<open>\<real>\<^sup>3\<close>.
\<close>

definition shift3 :: "real^3" where
  "shift3 = vector [3, 0, 0]"

definition ball3_copy_left :: "(real^3) set" where
  "ball3_copy_left = ball3"  (* the ball in the original location *)

definition ball3_copy_right :: "(real^3) set" where
  "ball3_copy_right = (+) shift3 ` ball3"  (* shifted by 3e_1 *)

lemma norm_shift3 [simp]: "norm shift3 = 3"
  unfolding shift3_def
  by (simp add: norm_eq_sqrt_inner inner_vec_def sum_3)

lemma ball3_copies_disjoint:
  "ball3_copy_left \<inter> ball3_copy_right = {}"
proof
  show "ball3_copy_left \<inter> ball3_copy_right \<subseteq> {}"
  proof
    fix z
    assume "z \<in> ball3_copy_left \<inter> ball3_copy_right"
    then obtain y where z_ball: "z \<in> ball3" and y_ball: "y \<in> ball3" and z_eq: "z = shift3 + y"
      unfolding ball3_copy_left_def ball3_copy_right_def by auto
    have z_norm: "norm z \<le> 1" and y_norm: "norm y \<le> 1"
      using z_ball y_ball by (simp_all add: ball3_def)
    have tri: "norm (z - y) \<le> norm z + norm y"
      using norm_triangle_ineq4 by blast
    have "3 = norm (z - y)"
      using z_eq by simp
    also have "\<dots> \<le> norm z + norm y"
      by (rule tri)
    also have "\<dots> \<le> 2"
      using z_norm y_norm by simp
    finally show "z \<in> {}"
      by simp
  qed
qed simp

text \<open>
  Isometries of \<open>\<real>\<^sup>3\<close> are the motions used in the final assembly.
  Rotations from \<open>SO(3)\<close>, translations, and their compositions are
  isometries.
\<close>

definition isometry :: "(real^3 \<Rightarrow> real^3) \<Rightarrow> bool" where
  "isometry f \<longleftrightarrow> (\<forall>x y. dist (f x) (f y) = dist x y)"

lemma id_isometry [simp]: "isometry id"
  by (simp add: isometry_def)

lemma translation_isometry [simp]: "isometry ((+) a)"
  by (simp add: isometry_def dist_norm)

lemma SO3_isometry:
  assumes "g \<in> SO3"
  shows "isometry g"
  using assms
  by (auto simp add: SO3_def rotation_def isometry_def orthogonal_transformation_isometry)

lemma isometry_compose:
  assumes "isometry f" "isometry g"
  shows "isometry (f \<circ> g)"
  using assms by (simp add: isometry_def)

lemma translation_compose_SO3_isometry [simp]:
  assumes "g \<in> SO3"
  shows "isometry ((+) a \<circ> g)"
  using assms by (intro isometry_compose translation_isometry SO3_isometry)

lemma offcenter_rotation_isometry:
  assumes "R \<in> SO3"
  shows "isometry (\<lambda>x. c + R (x - c))"
proof -
  have "(\<lambda>x. c + R (x - c)) = (+) c \<circ> R \<circ> (+) (- c)"
    by (rule ext) simp
  thus ?thesis
    using assms by (simp add: isometry_compose SO3_isometry)
qed

lemma offcenter_rotation_inverse_left:
  fixes c :: "real^3"
  assumes inv_left: "Rinv \<circ> R = id"
  defines "T \<equiv> \<lambda>x. c + R (x - c)"
    and "U \<equiv> \<lambda>x. c + Rinv (x - c)"
  shows "U (T x) = x"
  using fun_cong[OF inv_left, of "x - c"]
  by (simp add: T_def U_def)

lemma offcenter_rotation_inverse_right:
  fixes c :: "real^3"
  assumes inv_right: "R \<circ> Rinv = id"
  defines "T \<equiv> \<lambda>x. c + R (x - c)"
    and "U \<equiv> \<lambda>x. c + Rinv (x - c)"
  shows "T (U x) = x"
  using fun_cong[OF inv_right, of "x - c"]
  by (simp add: T_def U_def)

lemma offcenter_rotation_funpow_zero:
  fixes c :: "real^3" and R :: "real^3 \<Rightarrow> real^3"
  defines "T \<equiv> \<lambda>x. c + R (x - c)"
  shows "(T ^^ n) 0 = c + (R ^^ n) (- c)"
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have "(T ^^ Suc n) 0 = T ((T ^^ n) 0)"
    by simp
  also have "\<dots> = T (c + (R ^^ n) (- c))"
    using Suc.IH by simp
  also have "\<dots> = c + R ((R ^^ n) (- c))"
    by (simp add: T_def)
  also have "\<dots> = c + (R ^^ Suc n) (- c)"
    by simp
  finally show ?case .
qed

lemma sigma_replicate_b:
  "sigma (replicate n (False, B)) = (Rz ^^ n)"
  by (induction n) (simp_all add: letter_to_rot_def)

lemma canceled_replicate_b: "canceled (replicate n (False, B))"
  unfolding canceled_def
proof
  assume "Domainp cancels_to_1 (replicate n (False, B))"
  then obtain w where "cancels_to_1 (replicate n (False, B)) w"
    by auto
  then obtain i where i: "Suc i < length (replicate n (False, B))"
    and "canceling (replicate n (False, B) ! i) (replicate n (False, B) ! Suc i)"
    by (auto simp: cancels_to_1_def cancels_to_1_at_def)
  hence "canceling (False, B) (False, B)"
    by simp
  thus False
    by (simp add: canceling_def)
qed

lemma replicate_b_in_F2: "replicate n (False, B) \<in> carrier F2"
  by (intro canceled_in_F2 canceled_replicate_b)

theorem ball3_paradoxical_strong:
  "\<exists>P Q :: (real^3) set list. \<exists>gP gQ :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gP \<and> length Q = length gQ \<and>
       (\<forall>g \<in> set gP. isometry g) \<and> (\<forall>g \<in> set gQ. isometry g) \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P) \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q) \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3) \<and>
       ball3 = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       ball3 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
proof -
  obtain a where a_sphere: "a \<in> sphere2" and a_not_D: "a \<notin> bad_set_D"
    using exists_antipodal_axis_avoiding_countable[OF bad_set_D_countable] by blast
  let ?c = "- (1 / 2) *\<^sub>R a"
  define T where "T = (\<lambda>x. ?c + Rz (x - ?c))"
  define U where "U = (\<lambda>x. ?c + Rz_inv (x - ?c))"
  have T_iso: "isometry T"
    unfolding T_def by (rule offcenter_rotation_isometry[OF Rz_in_SO3])
  have U_iso: "isometry U"
    unfolding U_def by (rule offcenter_rotation_isometry[OF Rz_inv_in_SO3])
  have U_T: "\<And>x. U (T x) = x"
    unfolding T_def U_def
    by (rule offcenter_rotation_inverse_left[OF Rz_inv_left])
  have T_U: "\<And>x. T (U x) = x"
    unfolding T_def U_def
    by (rule offcenter_rotation_inverse_right[OF Rz_inv_right])

  have no_Rz_power_fix: "\<And>n. n > 0 \<Longrightarrow> (Rz ^^ n) a \<noteq> a"
  proof
    fix n :: nat
    assume n_pos: "n > 0" and fixed: "(Rz ^^ n) a = a"
    let ?w = "replicate n (False, B)"
    have w_carrier: "?w \<in> carrier F2"
      by (rule replicate_b_in_F2)
    have w_ne: "?w \<noteq> []"
      using n_pos by auto
    have "sigma ?w a = a"
      using fixed by (simp add: sigma_replicate_b)
    hence "a \<in> fixed_point_set (sigma ?w)"
      using a_sphere by (simp add: fixed_point_set_def)
    hence "a \<in> bad_set_D"
      unfolding bad_set_D_def using w_carrier w_ne by blast
    with a_not_D show False
      by contradiction
  qed

  have Rz_power_a_inj: "\<And>n m. (Rz ^^ n) a = (Rz ^^ m) a \<Longrightarrow> n = m"
  proof -
    fix n m :: nat
    assume eq: "(Rz ^^ n) a = (Rz ^^ m) a"
    show "n = m"
    proof (cases n m rule: linorder_cases)
      case less
      let ?d = "m - n"
      have d_pos: "?d > 0"
        using less by simp
      have m_eq: "m = n + ?d"
        using less by simp
      have "(Rz ^^ n) a = (Rz ^^ n) ((Rz ^^ ?d) a)"
        using eq m_eq by (metis comp_apply funpow_add)
      hence "a = (Rz ^^ ?d) a"
        using SO3_inj[OF SO3_funpow[OF Rz_in_SO3, of n]] by (auto simp: inj_def)
      with no_Rz_power_fix[OF d_pos] show ?thesis
        by simp
    next
      case equal
      then show ?thesis .
    next
      case greater
      let ?d = "n - m"
      have d_pos: "?d > 0"
        using greater by simp
      have n_eq: "n = m + ?d"
        using greater by simp
      have "(Rz ^^ m) a = (Rz ^^ m) ((Rz ^^ ?d) a)"
        using eq n_eq by (metis comp_apply funpow_add)
      hence "a = (Rz ^^ ?d) a"
        using SO3_inj[OF SO3_funpow[OF Rz_in_SO3, of m]] by (auto simp: inj_def)
      with no_Rz_power_fix[OF d_pos] show ?thesis
        by simp
    qed
  qed

  have T_pow_zero: "\<And>n. (T ^^ n) 0 = ?c + (Rz ^^ n) (- ?c)"
    unfolding T_def by (rule offcenter_rotation_funpow_zero)
  have T_pow_zero_diff: "\<And>n. (T ^^ n) 0 = (1 / 2) *\<^sub>R ((Rz ^^ n) a - a)"
  proof -
    fix n
    have lin: "linear (Rz ^^ n)"
      by (rule SO3_linear[OF SO3_funpow[OF Rz_in_SO3]])
    have "(T ^^ n) 0 = ?c + (Rz ^^ n) (- ?c)"
      by (rule T_pow_zero)
    also have "\<dots> = (- (1 / 2) *\<^sub>R a) + (1 / 2) *\<^sub>R ((Rz ^^ n) a)"
      using linear_scale[OF lin, of "1 / 2" a] by simp
    also have "\<dots> = (1 / 2) *\<^sub>R ((Rz ^^ n) a - a)"
      by (simp add: scaleR_right_diff_distrib)
    finally show "(T ^^ n) 0 = (1 / 2) *\<^sub>R ((Rz ^^ n) a - a)" .
  qed

  have T_orbit_inj: "\<And>n m. (T ^^ n) 0 = (T ^^ m) 0 \<Longrightarrow> n = m"
  proof -
    fix n m :: nat
    assume eq: "(T ^^ n) 0 = (T ^^ m) 0"
    have "(Rz ^^ n) a = (Rz ^^ m) a"
      using eq T_pow_zero_diff by simp
    thus "n = m"
      by (rule Rz_power_a_inj)
  qed
  have orbit_disj:
    "\<forall>n m. n \<noteq> m \<longrightarrow> ((T^^n) ` {0}) \<inter> ((T^^m) ` {0}) = {}"
    using T_orbit_inj by auto

  define E where "E = (\<Union>n. (T^^n) ` {0::real^3})"
  have T_E: "T ` E = E - {0}"
    unfolding E_def by (rule absorbing_rotation_shift[OF orbit_disj])
  have zero_subset_E: "{0::real^3} \<subseteq> E"
  proof
    fix x :: "real^3"
    assume "x \<in> {0}"
    hence "x \<in> (T ^^ 0) ` {0}"
      by simp
    thus "x \<in> E"
      unfolding E_def by blast
  qed
  have E_subset_ball3: "E \<subseteq> ball3"
  proof
    fix x
    assume "x \<in> E"
    then obtain n where x_eq: "x = (T ^^ n) 0"
      unfolding E_def by blast
    have Rza_sphere: "(Rz ^^ n) a \<in> sphere2"
      using SO3_funpow_preserves_sphere2[OF Rz_in_SO3 a_sphere] .
    have "norm x = norm ((1 / 2) *\<^sub>R ((Rz ^^ n) a - a))"
      using x_eq T_pow_zero_diff by simp
    also have "\<dots> = (1 / 2) * norm ((Rz ^^ n) a - a)"
      by simp
    also have "\<dots> \<le> (1 / 2) * (norm ((Rz ^^ n) a) + norm a)"
      by (intro mult_left_mono norm_triangle_ineq4) simp
    also have "\<dots> = 1"
      using Rza_sphere a_sphere by (simp add: sphere2_def)
    finally show "x \<in> ball3"
      by (simp add: ball3_def)
  qed

  let ?X = "ball3 - {0::real^3}"
  let ?Y = "ball3"
  let ?A = "[E, ball3 - E]"
  let ?B = "[T ` E, ball3 - E]"
  let ?e = "[T, id]"
  let ?t = "[U, id]"
  have A_cover: "?Y = (\<Union>k<length ?A. ?A ! k)"
    using E_subset_ball3 by (auto simp: lessThan_Suc)
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
        with x T_E show ?thesis
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
        with xk T_E E_subset_ball3 show ?thesis
          by auto
      next
        assume "k = 1"
        with xk zero_subset_E show ?thesis
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
      using T_E by auto
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
      with x U_T show ?thesis
        by auto
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
      then obtain x where x: "x \<in> E" and y_eq: "y = T x"
        using y by auto
      hence "U y = x"
        using U_T by simp
      with x y_eq T_U \<open>k = 0\<close> show ?thesis
        by simp
    next
      assume "k = 1"
      with y show ?thesis
        by auto
    qed
  qed

  from ball3_minus_origin_paradoxical_strong obtain P Q :: "(real^3) set list"
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
    using SO3_inj gP_SO3 lenP nth_mem by auto
  have gQ_inj: "\<And>i. i < length Q \<Longrightarrow> inj (gQ ! i)"
    using SO3_inj gQ_SO3 lenQ nth_mem by auto
  have mapsP: "\<And>k i l. \<lbrakk>k < length ?A; i < length P; l < length ?B\<rbrakk>
      \<Longrightarrow> transfer_map ?t gP ?e k i l \<in> {f. isometry f}"
  proof -
    fix k i l
    assume k: "k < length ?A" and i: "i < length P" and l: "l < length ?B"
    have gi_SO3: "gP ! i \<in> SO3"
      using gP_SO3 i lenP by auto
    have gi_iso: "isometry (gP ! i)"
      by (rule SO3_isometry[OF gi_SO3])
    have ek_iso: "isometry (?e ! k)"
      using T_iso k less_Suc_eq by fastforce
    have tl_iso: "isometry (?t ! l)"
      using U_iso l less_Suc_eq by fastforce
    show "transfer_map ?t gP ?e k i l \<in> {f. isometry f}"
      unfolding transfer_map_def
      by (simp add: isometry_compose tl_iso gi_iso ek_iso)
  qed
  have mapsQ: "\<And>k i l. \<lbrakk>k < length ?A; i < length Q; l < length ?B\<rbrakk>
      \<Longrightarrow> transfer_map ?t gQ ?e k i l \<in> {f. isometry f}"
  proof -
    fix k i l
    assume k: "k < length ?A" and i: "i < length Q" and l: "l < length ?B"
    have gi_SO3: "gQ ! i \<in> SO3"
      using gQ_SO3 i lenQ by auto
    have gi_iso: "isometry (gQ ! i)"
      by (rule SO3_isometry[OF gi_SO3])
    have ek_iso: "isometry (?e ! k)"
      using T_iso k less_Suc_eq by fastforce
    have tl_iso: "isometry (?t ! l)"
      using U_iso l less_Suc_eq by fastforce
    show "transfer_map ?t gQ ?e k i l \<in> {f. isometry f}"
      unfolding transfer_map_def
      by (simp add: isometry_compose tl_iso gi_iso ek_iso)
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
      and hP_iso: "set hP \<subseteq> {f. isometry f}"
      and hQ_iso: "set hQ \<subseteq> {f. isometry f}"
      and source_disj': "pairwise_disjoint (P' @ Q')"
      and imageP_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hP P')"
      and imageQ_disj': "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hQ Q')"
      and source_cover': "?Y = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
      and imageP_cover': "?Y = (\<Union>i<length P'. (hP ! i) ` (P' ! i))"
      and imageQ_cover': "?Y = (\<Union>i<length Q'. (hQ ! i) ` (Q' ! i))"
    by auto
  have P'_sub: "\<forall>i < length P'. P' ! i \<subseteq> ball3"
    using source_cover' by blast
  have Q'_sub: "\<forall>i < length Q'. Q' ! i \<subseteq> ball3"
    using source_cover' by blast
  show ?thesis
  proof (intro exI conjI)
    show "length P' = length hP"
      by (rule lenP')
    show "length Q' = length hQ"
      by (rule lenQ')
    show "\<forall>g\<in>set hP. isometry g"
      using hP_iso by blast
    show "\<forall>g\<in>set hQ. isometry g"
      using hQ_iso by blast
    show "pairwise_disjoint (P' @ Q')"
      by (rule source_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hP P')"
      by (rule imageP_disj')
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hQ Q')"
      by (rule imageQ_disj')
    show "\<forall>i<length P'. P' ! i \<subseteq> ball3"
      by (rule P'_sub)
    show "\<forall>i<length Q'. Q' ! i \<subseteq> ball3"
      by (rule Q'_sub)
    show "ball3 = (\<Union>i<length P'. P' ! i) \<union> (\<Union>i<length Q'. Q' ! i)"
      by (rule source_cover')
    show "ball3 = (\<Union>i<length P'. (hP ! i) ` (P' ! i))"
      by (rule imageP_cover')
    show "ball3 = (\<Union>i<length Q'. (hQ ! i) ` (Q' ! i))"
      by (rule imageQ_cover')
  qed
qed

text \<open>An auxiliary finite-cover theorem for the closed unit ball.\<close>
theorem banach_tarski_finite_cover:
  "\<exists>P :: (real^3) set list. \<exists>gs :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gs \<and>
       (\<forall>g \<in> set gs. isometry g) \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3) \<and>
       ball3 = (\<Union>i<length P. P ! i) \<and>
       (ball3_copy_left \<union> ball3_copy_right) =
         (\<Union>i<length P. (gs ! i) ` (P ! i)) \<and>
       ball3_copy_left \<inter> ball3_copy_right = {}"
proof -
  from ball3_paradoxical obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3 \<Rightarrow> real^3)) list"
    where decomp:
      "length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> SO3 \<and> set gQ \<subseteq> SO3 \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3) \<and>
       (\<forall>i < length Q. Q ! i \<subseteq> ball3) \<and>
       ball3 = (\<Union>i<length P. P ! i) \<and>
       ball3 = (\<Union>i<length Q. Q ! i) \<and>
       ball3 = (\<Union>i<length P. (gP ! i) ` (P ! i)) \<and>
       ball3 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim exE)
  from decomp have lenP: "length P = length gP"
    by (elim conjE)
  from decomp have lenQ: "length Q = length gQ"
    by (elim conjE)
  from decomp have gP_SO3: "set gP \<subseteq> SO3"
    by (elim conjE)
  from decomp have gQ_SO3: "set gQ \<subseteq> SO3"
    by (elim conjE)
  from decomp have P_sub: "\<forall>i < length P. P ! i \<subseteq> ball3"
    by (elim conjE)
  from decomp have Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> ball3"
    by (elim conjE)
  from decomp have P_src: "ball3 = (\<Union>i<length P. P ! i)"
    by (elim conjE)
  from decomp have Q_src: "ball3 = (\<Union>i<length Q. Q ! i)"
    by (elim conjE)
  from decomp have P_cov: "ball3 = (\<Union>i<length P. (gP ! i) ` (P ! i))"
    by (elim conjE)
  from decomp have Q_cov: "ball3 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by (elim conjE)

  define pieces where "pieces = P @ Q"
  define hQ where "hQ = map (\<lambda>g. (+) shift3 \<circ> g) gQ"
  define gs where "gs = gP @ hQ"
  have len_hQ: "length Q = length hQ"
    by (simp add: hQ_def lenQ)
  have len: "length pieces = length gs"
    by (simp add: pieces_def gs_def lenP len_hQ)
  have iso: "\<forall>g \<in> set gs. isometry g"
    using gP_SO3 gQ_SO3
    by (auto simp add: gs_def hQ_def SO3_isometry)
  have sub: "\<forall>i < length pieces. pieces ! i \<subseteq> ball3"
    using P_sub Q_sub by (auto simp add: pieces_def nth_append)
  have src: "ball3 = (\<Union>i<length pieces. pieces ! i)"
  proof -
    have append_union:
      "(\<Union>i<length (P @ Q). (P @ Q) ! i) =
        (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      using indexed_union_append[of P Q] .
    have "(\<Union>i<length pieces. pieces ! i) =
        (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      unfolding pieces_def
      using append_union .
    also have "\<dots> = ball3"
      using P_src Q_src by simp
    finally show ?thesis by simp
  qed
  have right_cov:
    "ball3_copy_right = (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
  proof -
    have right_union:
      "(\<Union>i<length Q. (hQ ! i) ` (Q ! i)) =
        (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    proof (rule equalityI)
      show "(\<Union>i<length Q. (hQ ! i) ` (Q ! i)) \<subseteq>
          (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
      proof
        fix x assume "x \<in> (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
        then obtain i y where i_lt: "i < length Q" and y_in: "y \<in> Q ! i"
          and x_eq: "x = (hQ ! i) y"
          by blast
        have h_eq: "hQ ! i = (+) shift3 \<circ> (gQ ! i)"
          using i_lt lenQ by (simp add: hQ_def)
        have "(gQ ! i) y \<in> (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
          using i_lt y_in by blast
        moreover have "x = shift3 + (gQ ! i) y"
          using x_eq h_eq by simp
        ultimately show "x \<in> (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
          by blast
      qed
      show "(+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i)) \<subseteq>
          (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      proof
        fix x assume "x \<in> (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
        then obtain z i y where x_eq: "x = shift3 + z"
          and i_lt: "i < length Q" and y_in: "y \<in> Q ! i" and z_eq: "z = (gQ ! i) y"
          by blast
        have h_eq: "hQ ! i = (+) shift3 \<circ> (gQ ! i)"
          using i_lt lenQ by (simp add: hQ_def)
        have "x = (hQ ! i) y"
          using x_eq z_eq h_eq by simp
        thus "x \<in> (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
          using i_lt y_in by blast
      qed
    qed
    show ?thesis
      unfolding ball3_copy_right_def
      using right_union Q_cov by simp
  qed
  have images:
    "ball3_copy_left \<union> ball3_copy_right =
      (\<Union>i<length pieces. (gs ! i) ` (pieces ! i))"
  proof -
    have append_images:
      "(\<Union>i<length (P @ Q). (gP @ hQ) ! i ` ((P @ Q) ! i)) =
        (\<Union>i<length P. (gP ! i) ` (P ! i)) \<union>
        (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      using indexed_image_union_append[OF lenP len_hQ] .
    have "(\<Union>i<length pieces. (gs ! i) ` (pieces ! i)) =
        (\<Union>i<length P. (gP ! i) ` (P ! i)) \<union>
        (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      unfolding pieces_def gs_def
      using append_images .
    also have "\<dots> = ball3_copy_left \<union> ball3_copy_right"
      using P_cov right_cov by (simp add: ball3_copy_left_def)
    finally show ?thesis by simp
  qed
  show ?thesis
    apply (rule exI[of _ pieces])
    apply (rule exI[of _ gs])
    using len iso sub src images ball3_copies_disjoint
    by simp
qed

text \<open>The Banach--Tarski theorem for the closed unit ball, as a partition theorem.\<close>
theorem banach_tarski:
  "\<exists>P :: (real^3) set list. \<exists>gs :: ((real^3) \<Rightarrow> (real^3)) list.
       length P = length gs \<and>
       (\<forall>g \<in> set gs. isometry g) \<and>
       pairwise_disjoint P \<and>
       pairwise_disjoint (map2 (\<lambda>g A. g ` A) gs P) \<and>
       (\<forall>i < length P. P ! i \<subseteq> ball3) \<and>
       ball3 = (\<Union>i<length P. P ! i) \<and>
       (ball3_copy_left \<union> ball3_copy_right) =
         (\<Union>i<length P. (gs ! i) ` (P ! i)) \<and>
       ball3_copy_left \<inter> ball3_copy_right = {}"
proof -
  from ball3_paradoxical_strong obtain P Q :: "(real^3) set list"
    and gP gQ :: "((real^3 \<Rightarrow> real^3)) list"
    where lenP: "length P = length gP"
      and lenQ: "length Q = length gQ"
      and gP_iso: "\<forall>g \<in> set gP. isometry g"
      and gQ_iso: "\<forall>g \<in> set gQ. isometry g"
      and source_disj: "pairwise_disjoint (P @ Q)"
      and imageP_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gP P)"
      and imageQ_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gQ Q)"
      and P_sub: "\<forall>i < length P. P ! i \<subseteq> ball3"
      and Q_sub: "\<forall>i < length Q. Q ! i \<subseteq> ball3"
      and source_cover: "ball3 = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
      and P_cov: "ball3 = (\<Union>i<length P. (gP ! i) ` (P ! i))"
      and Q_cov: "ball3 = (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    by auto
  define pieces where "pieces = P @ Q"
  define hQ where "hQ = map (\<lambda>g. (+) shift3 \<circ> g) gQ"
  define gs where "gs = gP @ hQ"
  have len_hQ: "length Q = length hQ"
    by (simp add: hQ_def lenQ)
  have len: "length pieces = length gs"
    by (simp add: pieces_def gs_def lenP len_hQ)
  have iso: "\<forall>g \<in> set gs. isometry g"
    using gP_iso gQ_iso
    by (auto simp add: gs_def hQ_def isometry_compose)
  have sub: "\<forall>i < length pieces. pieces ! i \<subseteq> ball3"
    using P_sub Q_sub by (auto simp add: pieces_def nth_append)
  have src: "ball3 = (\<Union>i<length pieces. pieces ! i)"
    by (metis indexed_union_append pieces_def source_cover)
  have source_disj_pieces: "pairwise_disjoint pieces"
    using source_disj by (simp add: pieces_def)

  have right_cov:
    "ball3_copy_right = (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
  proof -
    have right_union:
      "(\<Union>i<length Q. (hQ ! i) ` (Q ! i)) =
        (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
    proof (rule equalityI)
      show "(\<Union>i<length Q. (hQ ! i) ` (Q ! i)) \<subseteq>
          (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
      proof
        fix x assume "x \<in> (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
        then obtain i y where i_lt: "i < length Q" and y_in: "y \<in> Q ! i"
          and x_eq: "x = (hQ ! i) y"
          by blast
        have h_eq: "hQ ! i = (+) shift3 \<circ> (gQ ! i)"
          using i_lt lenQ by (simp add: hQ_def)
        have "(gQ ! i) y \<in> (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
          using i_lt y_in by blast
        moreover have "x = shift3 + (gQ ! i) y"
          using x_eq h_eq by simp
        ultimately show "x \<in> (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
          by blast
      qed
      show "(+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i)) \<subseteq>
          (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      proof
        fix x assume "x \<in> (+) shift3 ` (\<Union>i<length Q. (gQ ! i) ` (Q ! i))"
        then obtain z i y where x_eq: "x = shift3 + z"
          and i_lt: "i < length Q" and y_in: "y \<in> Q ! i" and z_eq: "z = (gQ ! i) y"
          by blast
        have h_eq: "hQ ! i = (+) shift3 \<circ> (gQ ! i)"
          using i_lt lenQ by (simp add: hQ_def)
        have "x = (hQ ! i) y"
          using x_eq z_eq h_eq by simp
        thus "x \<in> (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
          using i_lt y_in by blast
      qed
    qed
    show ?thesis
      unfolding ball3_copy_right_def
      using right_union Q_cov by simp
  qed
  have images:
    "ball3_copy_left \<union> ball3_copy_right =
      (\<Union>i<length pieces. (gs ! i) ` (pieces ! i))"
  proof -
    have "(\<Union>i<length pieces. (gs ! i) ` (pieces ! i)) =
        (\<Union>i<length P. (gP ! i) ` (P ! i)) \<union>
        (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      unfolding pieces_def gs_def
      by (rule indexed_image_union_append[OF lenP len_hQ])
    also have "\<dots> = ball3_copy_left \<union> ball3_copy_right"
      using P_cov right_cov by (simp add: ball3_copy_left_def)
    finally show ?thesis by simp
  qed

  have shift_inj: "inj ((+) shift3)"
    by (simp add: inj_def)
  have right_image_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) hQ Q)"
    unfolding pairwise_disjoint_def
  proof (intro allI impI)
    fix i j
    assume i: "i < length (map2 (\<lambda>g A. g ` A) hQ Q)"
      and j: "j < length (map2 (\<lambda>g A. g ` A) hQ Q)"
      and ij: "i \<noteq> j"
    have iQ: "i < length Q" and jQ: "j < length Q"
      using i j len_hQ by auto
    have base_disj: "(gQ ! i ` (Q ! i)) \<inter> (gQ ! j ` (Q ! j)) = {}"
      using imageQ_disj lenQ iQ jQ ij by (simp add: pairwise_disjoint_def)
    have hi: "hQ ! i = (+) shift3 \<circ> (gQ ! i)"
      using iQ lenQ by (simp add: hQ_def)
    have hj: "hQ ! j = (+) shift3 \<circ> (gQ ! j)"
      using jQ lenQ by (simp add: hQ_def)
    show "map2 (\<lambda>g A. g ` A) hQ Q ! i \<inter> map2 (\<lambda>g A. g ` A) hQ Q ! j = {}"
      using base_disj shift_inj iQ jQ len_hQ
      by (auto simp: hi hj inj_def)
  qed
  have left_sets_sub: "\<And>A. A \<in> set (map2 (\<lambda>g A. g ` A) gP P) \<Longrightarrow> A \<subseteq> ball3_copy_left"
  proof -
    fix A
    assume A: "A \<in> set (map2 (\<lambda>g A. g ` A) gP P)"
    then obtain i where i: "i < length P" and A_eq: "A = (gP ! i) ` (P ! i)"
      using lenP by (auto simp: in_set_conv_nth)
    have "A \<subseteq> (\<Union>i<length P. (gP ! i) ` (P ! i))"
      using i A_eq by blast
    thus "A \<subseteq> ball3_copy_left"
      using P_cov by (simp add: ball3_copy_left_def)
  qed
  have right_sets_sub: "\<And>A. A \<in> set (map2 (\<lambda>g A. g ` A) hQ Q) \<Longrightarrow> A \<subseteq> ball3_copy_right"
  proof -
    fix A
    assume A: "A \<in> set (map2 (\<lambda>g A. g ` A) hQ Q)"
    then obtain i where i: "i < length Q" and A_eq: "A = (hQ ! i) ` (Q ! i)"
      using len_hQ by (auto simp: in_set_conv_nth)
    have "A \<subseteq> (\<Union>i<length Q. (hQ ! i) ` (Q ! i))"
      using i A_eq by blast
    thus "A \<subseteq> ball3_copy_right"
      using right_cov by simp
  qed
  have image_cross_disj:
    "\<And>A B. \<lbrakk>A \<in> set (map2 (\<lambda>g A. g ` A) gP P);
      B \<in> set (map2 (\<lambda>g A. g ` A) hQ Q)\<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  proof -
    fix A B
    assume A: "A \<in> set (map2 (\<lambda>g A. g ` A) gP P)"
      and B: "B \<in> set (map2 (\<lambda>g A. g ` A) hQ Q)"
    have "A \<inter> B \<subseteq> ball3_copy_left \<inter> ball3_copy_right"
      using left_sets_sub[OF A] right_sets_sub[OF B] by blast
    thus "A \<inter> B = {}"
      using ball3_copies_disjoint by blast
  qed
  have image_disj: "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gs pieces)"
    unfolding gs_def pieces_def
    using pairwise_disjoint_appendI[OF imageP_disj right_image_disj image_cross_disj]
    using lenP by fastforce
  show ?thesis
  proof (intro exI conjI)
    show "length pieces = length gs"
      by (rule len)
    show "\<forall>g\<in>set gs. isometry g"
      by (rule iso)
    show "pairwise_disjoint pieces"
      by (rule source_disj_pieces)
    show "pairwise_disjoint (map2 (\<lambda>g A. g ` A) gs pieces)"
      by (rule image_disj)
    show "\<forall>i<length pieces. pieces ! i \<subseteq> ball3"
      by (rule sub)
    show "ball3 = (\<Union>i<length pieces. pieces ! i)"
      by (rule src)
    show "ball3_copy_left \<union> ball3_copy_right =
        (\<Union>i<length pieces. (gs ! i) ` (pieces ! i))"
      by (rule images)
    show "ball3_copy_left \<inter> ball3_copy_right = {}"
      by (rule ball3_copies_disjoint)
  qed
qed

end
