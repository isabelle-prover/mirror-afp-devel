section \<open>Properties of Klein's $J$ invariant\<close>
theory Klein_J
  imports Modular_Functions
begin

text \<open>
  The Klein $J$ function has degree 1.
\<close>
lemma degree_modfun_J: "degree_modfun \<J> = 1"
proof -
  have "int (degree_modfun \<J>) = 1"
    by (subst int_degree_modfun_conv_poles) (auto intro: mform_intros)
  thus ?thesis
    by simp
qed

text \<open>Theorem 2.7\<close>

lemma zorder_J_mero_uhp_conv_Klein_J:
  assumes "Im z > 0"
  shows   "zorder \<J> z = zorder Klein_J z"
proof -
  have "eventually (\<lambda>w. w \<in> {w. Im w > 0}) (at z)"
    by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms in auto)
  hence "eventually (\<lambda>w. \<J> w = Klein_J w) (at z)"
    by eventually_elim auto
  thus ?thesis
    by (intro zorder_cong) auto
qed

lemma zorder_modgrp_J_minus_const:
  assumes "Im w > 0"
  shows   "zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w = (if Klein_J w = c then 1 else 0)"
proof -
  have rel: "mero_uhp_rel (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) (\<lambda>z. Klein_J z - c)"
    by mero_uhp_rel
  hence "is_pole (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) w \<longleftrightarrow> is_pole (\<lambda>z. Klein_J z - c) w"
    using assms
    by (intro is_pole_cong refl)
       (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
  moreover have "(\<lambda>z. Klein_J z - c) analytic_on {w}"
    using assms by (auto intro!: analytic_intros simp: complex_is_Real_iff)
  ultimately have not_pole: "\<not>is_pole (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) w"
    using analytic_at_imp_no_pole by blast

  have "\<not>is_const_mero_uhp \<J>"
    using degree_modfun_J by force
  hence [simp]: "\<J> \<noteq> \<langle>c\<rangle>"
    by (metis is_const_mero_uhp_const_mero_uhp)

  show ?thesis
  proof (cases "Klein_J w = c")
    case False
    have "zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w = 0"
      by (subst zorder_modgrp_eq_0_iff) (use assms not_pole False in \<open>auto intro!: mform_intros\<close>)
    with False show ?thesis
      by simp
  next
    case True
    have "\<bar>zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w\<bar> \<le> degree_modfun (\<J> - \<langle>c\<rangle>)"
      by (intro abs_zorder_modgrp_le_degree_modfun) (use assms in \<open>auto intro!: mform_intros\<close>)
    also have "\<dots> = degree_modfun (\<J> + \<langle>-c\<rangle>)"
      by (simp add: hom_distribs)
    also have "\<dots> = degree_modfun \<J>"
      by (subst degree_modfun_plus_const_eq) (auto intro!: mform_intros)
    also have "\<dots> = 1"
      by (simp add: degree_modfun_J)
    finally have "\<bar>zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w\<bar> \<le> 1" .
    moreover have "zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w > 0"
      by (subst zorder_modgrp_pos_iff) (use assms not_pole True in \<open>auto intro!: mform_intros\<close>)
    ultimately have "zorder[\<Gamma>] (\<J> - \<langle>c\<rangle>) w = 1"
      by linarith
    thus ?thesis
      using True by simp
  qed
qed 

lemma zorder_modgrp_J_rho [simp]: "zorder[\<Gamma>] \<J> \<^bold>\<rho> = 1"
proof -
  have "zorder[\<Gamma>] (\<J> - \<langle>0\<rangle>) \<^bold>\<rho> = 1"
    by (subst zorder_modgrp_J_minus_const) auto
  thus ?thesis
    by simp
qed

lemma zorder_modgrp_J_rho' [simp]: "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> zorder[\<Gamma>] \<J> z = 1"
  by (force dest: Klein_J.rel_imp_zorder_modgrp_eq)

lemma zorder_modgrp_J_ii [simp]: "zorder[\<Gamma>] (\<J> - 1) \<i> = 1"
  unfolding one_mero_uhp_def by (subst zorder_modgrp_J_minus_const) auto

lemma zorder_modgrp_J_ii' [simp]: "z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> zorder[\<Gamma>] (\<J> - 1) z = 1"
  by (metis Klein_J_cong const_mero_uhp.hom_one linorder_not_less 
            modular_group.Im_nonpos_imp_not_rel zorder_modgrp_J_ii zorder_modgrp_J_minus_const)

lemma zorder_Klein_J: 
  assumes "Im z > 0"
  shows   "zorder (\<lambda>u. Klein_J u - Klein_J z) z = ellorder_modgrp UNIV z"
proof -
  have [simp]: "\<J> \<noteq> \<langle>Klein_J z\<rangle>"
    by (metis degree_modfun_J degree_modfun_is_const is_const_mero_uhp_const_mero_uhp zero_neq_one)
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
    by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms in auto)
  hence "eventually (\<lambda>u. Klein_J u - Klein_J z = eval_mero_uhp (\<J> - \<langle>\<J> z\<rangle>) u) (at z)"
    by eventually_elim (use assms in auto)
  hence "zorder (\<lambda>u. Klein_J u - Klein_J z) z = zorder_mero_uhp (\<J> - \<langle>\<J> z\<rangle>) z"
    by (intro zorder_cong) auto
  also have "\<dots> = zorder[\<Gamma>] (\<J> - \<langle>\<J> z\<rangle>) z * ellorder_modgrp UNIV z"
    using assms by (subst zorder_conv_zorder_modgrp) (auto intro!: mform_intros)
  also have "zorder[\<Gamma>] (\<J> - \<langle>\<J> z\<rangle>) z = 1"
    by (subst zorder_modgrp_J_minus_const) (use assms in auto)
  finally show ?thesis
    by simp
qed

text \<open>
  Apostol's Theorem 2.7
\<close>
lemma zorder_Klein_J_rho: "zorder Klein_J \<^bold>\<rho> = 3"
  using zorder_Klein_J[of "\<^bold>\<rho>"] by simp

lemma zorder_Klein_J_rho':
  assumes "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  shows   "zorder Klein_J z = 3"
proof -
  have "zorder (\<lambda>u. Klein_J u - Klein_J z) z = ellorder_modgrp UNIV z"
    using assms by (intro zorder_Klein_J) (auto simp: modular_group.rel_def)
  also have "Klein_J z = 0"
    using assms by (simp add: Klein_J_cong)
  also have "ellorder_modgrp UNIV z = 3"
    using assms by (simp add: ellorder_modgrp_UNIV_rho')
  finally show ?thesis
    by simp
qed

lemma zorder_Klein_J_ii: "zorder (\<lambda>z. Klein_J z - 1) \<i> = 2"
  using zorder_Klein_J[of \<i>] by simp

lemma zorder_Klein_J_ii':
  assumes "z \<sim>\<^sub>\<Gamma> \<i>"
  shows   "zorder (\<lambda>w. Klein_J w - 1) z = 2"
proof -
  have "zorder (\<lambda>u. Klein_J u - Klein_J z) z = ellorder_modgrp UNIV z"
    using assms by (intro zorder_Klein_J) (auto simp: modular_group.rel_def)
  also have "Klein_J z = 1"
    using assms by (simp add: Klein_J_cong)
  also have "ellorder_modgrp UNIV z = 2"
    using assms by (simp add: ellorder_modgrp_UNIV_ii')
  finally show ?thesis
    by simp
qed



subsection \<open>Bijectivity\<close>

theorem bij_betw_Klein_J: "bij_betw Klein_J \<R>\<^sub>\<Gamma>' UNIV"
proof -
  have "inj_on \<J> (\<R>\<^sub>\<Gamma>' - poles_mero_uhp \<J>)"
    by (intro MFuns_degree_1_imp_inj_on mform_intros degree_modfun_J)
  also have "?this \<longleftrightarrow> inj_on Klein_J (\<R>\<^sub>\<Gamma>' - poles_mero_uhp \<J>)"
    by (intro inj_on_cong) (auto simp: in_std_fund_region'_iff)
  finally have "inj_on Klein_J \<R>\<^sub>\<Gamma>'" by simp
  moreover have "Klein_J ` \<R>\<^sub>\<Gamma>' = UNIV"
  proof safe
    fix c :: complex
    have J: "\<J> \<in> MFuns"
      by (auto intro: mform_intros)
    have nonconst: "\<not>is_const_mero_uhp \<J>"
      using degree_modfun_J by fastforce
    show "c \<in> Klein_J ` \<R>\<^sub>\<Gamma>'"
    proof (rule MFuns_surj_obtain[OF J nonconst, of c], goal_cases)
      case (1 z)
      thus ?case by (auto simp: in_std_fund_region'_iff)
    qed auto
  qed auto
  ultimately show ?thesis
    unfolding bij_betw_def by blast
qed

lemma inj_on_Klein_J: "inj_on Klein_J \<R>\<^sub>\<Gamma>'"
  using bij_betw_Klein_J by (auto simp: bij_betw_def)

lemma Klein_J_eqD:
  assumes "Klein_J z1 = Klein_J z2" "Im z1 > 0" "Im z2 > 0"
  shows   "z1 \<sim>\<^sub>\<Gamma> z2"
proof -
  from assms(2) obtain z1' where z1': "z1' \<in> \<R>\<^sub>\<Gamma>'" "z1 \<sim>\<^sub>\<Gamma> z1'"
    by (meson canonical_point_in_std_fund_region')
  from assms(3) obtain z2' where z2': "z2' \<in> \<R>\<^sub>\<Gamma>'" "z2 \<sim>\<^sub>\<Gamma> z2'"
    by (meson canonical_point_in_std_fund_region')
  have "Klein_J z1' = Klein_J z2'"
    using Klein_J_cong[OF z1'(2)] Klein_J_cong[OF z2'(2)] assms by simp
  hence "z1' = z2'"
    by (rule inj_onD[OF inj_on_Klein_J]) (use z1' z2' in auto)
  thus ?thesis
    using z1'(2) z2'(2) modular_group.rel_trans modular_group.rel_sym by blast
qed

lemma Klein_J_eq_iff:
  assumes "Im z1 > 0" "Im z2 > 0"
  shows   "Klein_J z1 = Klein_J z2 \<longleftrightarrow> z1 \<sim>\<^sub>\<Gamma> z2"
  using Klein_J_eqD[of z1 z2] assms by (auto intro: Klein_J_cong)

lemma Klein_J_eq_0_iff: "Im z > 0 \<Longrightarrow> Klein_J z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  by (metis Klein_J_eq_iff Klein_J_rho in_std_fund_region'_iff modfun_rho_in_std_fund_region')

lemma Klein_J_eq_1_iff: "Im z > 0 \<Longrightarrow> Klein_J z = 1 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<i>"
  by (metis Klein_J_eq_iff Klein_J_ii in_std_fund_region'_iff i_in_std_fund_region')

lemma surj_Klein_J: "\<exists>z. z \<in> \<R>\<^sub>\<Gamma>' \<and> Klein_J z = u"
proof -
  have "u \<in> UNIV"
    by simp
  also have "UNIV = Klein_J ` \<R>\<^sub>\<Gamma>'"
    using bij_betw_Klein_J unfolding bij_betw_def by simp
  finally show ?thesis
    by blast
qed

lemma std_fund_region'_unique:
  assumes "z \<in> \<R>\<^sub>\<Gamma>'" "z' \<in> \<R>\<^sub>\<Gamma>'" "z \<sim>\<^sub>\<Gamma> z'"
  shows   "z = z'"
proof -
  have "Klein_J z = Klein_J z'"
    using assms Klein_J_cong by blast
  with inj_on_Klein_J assms(1,2) show "z = z'"
    by (auto simp: inj_on_def)
qed

definition modular_group_repr :: "complex \<Rightarrow> complex" where
  "modular_group_repr z = (if Im z \<le> 0 then 0 else (THE z'. z \<sim>\<^sub>\<Gamma> z' \<and> z' \<in> \<R>\<^sub>\<Gamma>'))"

lemma modular_group_repr:
  assumes "Im z > 0"
  shows   "z \<sim>\<^sub>\<Gamma> modular_group_repr z" and [intro]: "modular_group_repr z \<in> \<R>\<^sub>\<Gamma>'"
proof -
  have "\<exists>!z'. z \<sim>\<^sub>\<Gamma> z' \<and> z' \<in> \<R>\<^sub>\<Gamma>'"
  proof (rule ex_ex1I)
    show "\<exists>z'. z \<sim>\<^sub>\<Gamma> z' \<and> z' \<in> \<R>\<^sub>\<Gamma>'"
      using canonical_point_in_std_fund_region'[OF assms] by metis
  next
    fix z1 z2 assume *: "z \<sim>\<^sub>\<Gamma> z1 \<and> z1 \<in> \<R>\<^sub>\<Gamma>'" "z \<sim>\<^sub>\<Gamma> z2 \<and> z2 \<in> \<R>\<^sub>\<Gamma>'"
    hence "z1 \<sim>\<^sub>\<Gamma> z2"
      using modular_group.rel_trans modular_group.rel_sym by blast
    with * show "z1 = z2"
      by (intro std_fund_region'_unique) auto
  qed
  from theI' [OF this] show "z \<sim>\<^sub>\<Gamma> modular_group_repr z" "modular_group_repr z \<in> \<R>\<^sub>\<Gamma>'"
    using assms unfolding modular_group_repr_def by auto
qed

lemma modular_group_repr_eqI: "z \<sim>\<^sub>\<Gamma> z' \<Longrightarrow> z' \<in> \<R>\<^sub>\<Gamma>' \<Longrightarrow> modular_group_repr z = z'"
  by (meson modular_group.rel_imp_Im_pos(1) modular_group.rel_sym modular_group.rel_trans
             modular_group_repr std_fund_region'_unique)

lemma Im_modular_group_repr_pos_iff [simp]:
  "Im (modular_group_repr z) > 0 \<longleftrightarrow> Im z > 0"
  using modular_group_repr(1)[of z] unfolding modular_group_repr_def by auto

lemma Im_modular_group_repr_nonneg_iff [simp]:
  "Im (modular_group_repr z) \<le> 0 \<longleftrightarrow> Im z \<le> 0"
  using Im_modular_group_repr_pos_iff[of z] by linarith

lemma modular_group_repr_rel_iff_left [simp]: "modular_group_repr z \<sim>\<^sub>\<Gamma> z' \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> z'"
  by (meson Im_modular_group_repr_pos_iff modular_group.rel_def modular_group.rel_sym
            modular_group.rel_trans modular_group_repr(1))

lemma modular_group_repr_rel_iff_right [simp]: "z' \<sim>\<^sub>\<Gamma> modular_group_repr z \<longleftrightarrow> z' \<sim>\<^sub>\<Gamma> z"
  by (meson modular_group.rel_sym modular_group_repr_rel_iff_left)

lemma modular_group_repr_in_std_fund_region'_iff: "modular_group_repr z \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> Im z > 0"
  using Im_modular_group_repr_pos_iff in_std_fund_region'_iff modular_group_repr(2) by blast

lemma modular_group_repr_eq_iff:
  assumes "Im z > 0" "Im z' > 0"
  shows   "modular_group_repr z = modular_group_repr z' \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> z'"
  using assms
  by (metis modular_group_repr modular_group_repr_eqI modular_group_repr_rel_iff_right)

lemma modular_group_repr_eq_iff':
  assumes "Im z > 0"
  shows   "modular_group_repr z = z' \<longleftrightarrow> z' \<in> \<R>\<^sub>\<Gamma>' \<and> z \<sim>\<^sub>\<Gamma> z'"
  using assms modular_group_repr(1) modular_group_repr_eqI by blast
  
lemma ellorder_modgrp_UNIV_modular_group_repr [simp]:
  "ellorder_modgrp UNIV (modular_group_repr z) = ellorder_modgrp UNIV z"
proof (cases "Im z > 0")
  case True
  thus ?thesis
    by (intro modular_group.ellorder_modgrp_cong) auto
qed (auto simp: modular_group_repr_def ellorder_modgrp_def)


subsection \<open>Modular functions as rational functions of $J$\<close>

lemma poly_in_MFuns:
  assumes "\<And>i. poly.coeff p i \<in> MFuns[G]" "f \<in> MFuns[G]" "k = 0"
  shows   "poly p f \<in> MeForms[G, k]"
proof -
  have "poly.coeff p 0 \<in> MFuns[G]"
    by (intro assms)
  then interpret modular_function "poly.coeff p 0" ..
  have "cong_subgroup G " ..
  thus ?thesis
    using assms unfolding poly_altdef by (auto intro!: mform_intros)
qed

text \<open>
  The theorems in this subsection consitute Apostol's Theorem 2.8.
  First of all: any function that can be expressed as a rational function of $J$ is
  a modular function.
\<close>
theorem ratfun_J_modform_in_MFuns:
  fixes p q :: "complex poly"
  defines "f \<equiv> eval_poly const_mero_uhp p \<J> / eval_poly const_mero_uhp q \<J>"
  shows   "f \<in> MFuns"
proof (cases "eval_poly const_mero_uhp q \<J> = 0")
  case False
  note [mform_intros] = poly_in_MFuns
  interpret map_poly_inj_idom_hom const_mero_uhp
    by standard auto
  have *: "poly.coeff (map_poly const_mero_uhp p) i \<in> MFuns" for p i
    by (auto simp: coeff_map_poly)
  show ?thesis
    unfolding f_def eval_poly_def
    by (rule mform_intros * refl)+ (use False in \<open>auto simp: eval_poly_def\<close>)
qed (auto simp: f_def)

text \<open>
  In the other direction: every modular function can be expressed as a rational function in $J$.
\<close>
lemma in_terms_of_J_aux:
  assumes f: "f \<in> MFuns - {0}"
  defines "Z \<equiv> zeros_mero_uhp f \<union> poles_mero_uhp f"
  obtains c :: complex
    where "f = \<langle>c\<rangle> * (\<Prod>w\<in>Z. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w)"
proof -
  interpret modular_function f UNIV
    using f by auto
  have fin: "finite Z"
    unfolding Z_def using f by auto
  have "\<not>is_const_mero_uhp \<J>"
    using degree_modfun_J by force
  hence [simp]: "\<J> \<noteq> \<langle>c\<rangle>" for c
    by (metis is_const_mero_uhp_const_mero_uhp)
  have [simp]: "Im z > 0" if "z \<in> Z" for z
    using that by (auto simp: Z_def inv_image_mero_uhp_def poles_mero_uhp_def in_std_fund_region'_iff)
  define g where "g = (\<Prod>w\<in>Z. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w)"

  have 1: "zorder[\<Gamma>] (f / g) z = 0"
    if z: "z \<in> \<R>\<^sub>\<Gamma>'" for z
  proof -
    have [simp]: "Im z > 0"
      using z by (auto simp: in_std_fund_region'_iff)
    have zorder_mform_eq_0: "zorder[\<Gamma>] f z = 0" if "z \<notin> Z"
      using z that f unfolding Z_def inv_image_mero_uhp_def poles_mero_uhp_def by auto
    have "zorder[\<Gamma>] (f / g) z = zorder[\<Gamma>] f z - zorder[\<Gamma>] g z"
      using f fin unfolding g_def by (subst zorder_modgrp_divide) (auto intro!: mform_intros)
    also have "zorder[\<Gamma>] g z = (\<Sum>w\<in>Z. zorder[\<Gamma>] ((\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w) z)"
      unfolding g_def using z f fin by (subst zorder_modgrp_prod) (auto intro!: mform_intros)
    also have "\<dots> = (\<Sum>w\<in>Z. if w = z then zorder[\<Gamma>] f z else 0)"
    proof (intro sum.cong refl, goal_cases)
      case (1 w)
      hence w: "w \<in> \<R>\<^sub>\<Gamma>'"
        by (auto simp: inv_image_mero_uhp_def poles_mero_uhp_def Z_def)
      with z have [simp]: "Klein_J z = Klein_J w \<longleftrightarrow> z = w"
        using inj_on_Klein_J unfolding inj_on_def by blast
      have "zorder[\<Gamma>] ((\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w) z =
            zorder[\<Gamma>] f w * zorder[\<Gamma>] (\<J> - \<langle>Klein_J w\<rangle>) z"
        by (subst zorder_modgrp_power_int) (auto intro!: mform_intros)
      also have "\<dots> = (if w = z then zorder[\<Gamma>] f z else 0)"
        using w z by (subst zorder_modgrp_J_minus_const) auto
      finally show ?case .
    qed
    also have "\<dots> = (\<Sum>w\<in>{z}. zorder[\<Gamma>] f z)"
      using fin zorder_mform_eq_0 by (intro sum.mono_neutral_cong) auto
    also have "\<dots> = zorder[\<Gamma>] f z"
      by simp
    finally show ?thesis
      by simp
  qed

  have "is_const_mero_uhp (f / g)"
  proof (rule ccontr)
    assume *: "\<not>is_const_mero_uhp (f / g)"
    hence **: "f / g \<in> MFuns - {0}"
      unfolding g_def using f by (auto intro!: mform_intros)
    interpret fg: modular_function "f / g" UNIV
      using ** by auto
    have "poles_mero_uhp (f / g) \<union> zeros_mero_uhp (f / g) \<noteq> {}"
      by (rule MFuns_zero_or_pole_exists[OF _ *]) (use f * ** in auto)
    hence "\<exists>z\<in>\<R>\<^sub>\<Gamma>'. zorder[\<Gamma>] (f / g) z \<noteq> 0"
      using ** by (auto simp: poles_mero_uhp_def inv_image_mero_uhp_def in_std_fund_region'_iff)
    with 1 show False
      by auto
  qed
  then obtain c where "f / g = \<langle>c\<rangle>"
    by (auto simp: is_const_mero_uhp_def)
  hence "f = \<langle>c\<rangle> * g"
    using fin by (simp add: field_simps g_def)
  thus ?thesis
    using that unfolding g_def by blast
qed      

theorem in_terms_of_J:
  assumes f: "f \<in> MFuns"
  obtains p q :: "complex poly"
  where "q \<noteq> 0" "f = eval_poly const_mero_uhp p \<J> / eval_poly const_mero_uhp q \<J>"
proof (cases "f = 0")
  case True
  thus ?thesis
    by (intro that[of 1 0]) (auto simp: eval_poly_def)
next
  case [simp]: False
  interpret map_poly_inj_idom_hom const_mero_uhp
    by standard auto
  interpret modular_function f UNIV
    using assms by auto
  define Z1 where "Z1 = zeros_mero_uhp f"
  define Z2 where "Z2 = poles_mero_uhp f"
  have disjoint: "Z1 \<inter> Z2 = {}"
    by (auto simp: Z1_def Z2_def inv_image_mero_uhp_def poles_mero_uhp_def)
  define P where "P = (\<Prod>w\<in>Z1. [:-Klein_J w, 1:] ^ nat (zorder[\<Gamma>] f w))"
  define Q where "Q = (\<Prod>w\<in>Z2. [:-Klein_J w, 1:] ^ nat (-zorder[\<Gamma>] f w))"
  have "Q \<noteq> 0"
    using f unfolding Q_def Z2_def by (subst prod_zero_iff) auto
  obtain c where "f = \<langle>c\<rangle> * (\<Prod>w\<in>Z1 \<union> Z2. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w)"
    using in_terms_of_J_aux[of f] f \<open>f \<noteq> 0\<close> unfolding Z1_def Z2_def by blast
  also have "\<dots> = \<langle>c\<rangle> * (\<Prod>w\<in>Z1. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w) * 
                    (\<Prod>w\<in>Z2. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w)"
    using disjoint f by (subst prod.union_disjoint) (auto simp: Z1_def Z2_def)
  also have "(\<Prod>w\<in>Z1. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w) =
             (\<Prod>w\<in>Z1. (\<J> - \<langle>Klein_J w\<rangle>) ^ nat (zorder[\<Gamma>] f w))" using f
    by (intro prod.cong refl)
       (auto simp: Z1_def inv_image_mero_uhp_def in_std_fund_region'_iff power_int_def)
  also have "(\<Prod>w\<in>Z2. (\<J> - \<langle>Klein_J w\<rangle>) powi zorder[\<Gamma>] f w) =
             (\<Prod>w\<in>Z2. inverse (\<J> - \<langle>Klein_J w\<rangle>) ^ nat (-zorder[\<Gamma>] f w))" using f
    by (intro prod.cong refl)
       (auto simp: Z2_def poles_mero_uhp_def in_std_fund_region'_iff power_int_def)
  also have "\<dots> = inverse (\<Prod>w\<in>Z2. (\<J> - \<langle>Klein_J w\<rangle>) ^ nat (-zorder[\<Gamma>] f w))"
    by (subst prod_inversef [symmetric]) (simp add: field_simps)
  also have "\<langle>c\<rangle> * (\<Prod>w\<in>Z1. (\<J> - \<langle>Klein_J w\<rangle>) ^ nat (zorder[\<Gamma>] f w)) * \<dots> = 
             eval_poly const_mero_uhp (Polynomial.smult c P) \<J> / eval_poly const_mero_uhp Q \<J>"
    by (simp add: hom_distribs P_def Q_def eval_poly_def map_poly_smult field_simps)
  finally show ?thesis
    using \<open>Q \<noteq> 0\<close> that[of Q "Polynomial.smult c P"] by blast
qed



subsection \<open>Non-conformality of modular functions at \<open>\<i>\<close> and \<open>\<rho>\<close>\<close>

context meromorphic_form
begin

context
  fixes f' h c d fac z
  defines "f' \<equiv> deriv_mero_uhp f"
  defines "c \<equiv> modgrp_c h" and "d \<equiv> modgrp_d h"
  defines "fac \<equiv> automorphy_factor h z"
  assumes z: "Im z > 0" "apply_modgrp h z = z" "\<not>is_pole f z" and h [simp]: "h \<in> G"
begin

lemma apply_modgrp_fixpoint_imp_deriv_eq:
  "(1 - fac powi (weight+2)) * f' z = of_int (weight * c) * fac powi (weight+1) * f z"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  from z have [simp]: "fac \<noteq> 0"
    by (auto simp: fac_def)

  have deriv: "((\<lambda>w. f (apply_modgrp h w)) has_field_derivative
          f' z  / fac ^ 2) (at z)"
    unfolding f'_def fac_def using z 
    by (auto intro!: derivative_eq_intros simp del: invariant_apply_modgrp)
  have "((\<lambda>w. automorphy_factor h w powi weight * f w) has_field_derivative
          (of_int weight * fac powi (weight - 1) * c * f z + f' z * fac powi weight)) (at z)"
    unfolding f'_def fac_def c_def using z by (auto intro!: derivative_eq_intros)
  also have "?this \<longleftrightarrow> ((\<lambda>w. f (apply_modgrp h w)) has_field_derivative
                (of_int weight * fac powi (weight - 1) * c * f z + f' z * fac powi weight)) (at z)"
    by simp
  finally have "f' z / fac ^ 2 = of_int weight * fac powi (weight - 1) * c * f z + f' z * fac powi weight"
    using DERIV_unique deriv by blast
  thus ?thesis
    by (simp add: power_int_add power_int_diff field_simps power2_eq_square)
qed

text \<open>
  If we have a meromorphic function $f(z)$ of weight \<open>\<Gamma>\<close> and some singular transformation
  $h\in\Gamma$, then the derivative of $f$ must vanish at any fixed points of $h$ (i.e.\ 
  $f$ is not conformal there).
\<close>
theorem apply_modgrp_fixpoint_imp_deriv_eq_0:
  assumes "weight = 0" "is_singular_modgrp h"
  shows "deriv f z = 0"
proof -
  have "fac \<notin> \<real>"
    using z assms
    by (auto simp: fac_def complex_is_Real_iff automorphy_factor_altdef
                   c_def is_singular_modgrp_altdef)
  hence "fac\<^sup>2 \<noteq> 1"
    by (metis Reals_1 Reals_minus_iff power2_eq_1_iff)
  hence "f' z = 0"
    using apply_modgrp_fixpoint_imp_deriv_eq assms by simp
  thus ?thesis
    using z by (simp add: eval_deriv_mero_uhp f'_def)
qed

end

end


context modular_function
begin

lemma deriv_apply_modgrp:
  assumes "Im z > 0" "\<not>is_pole f z" "h \<in> G"
  shows   "deriv f (apply_modgrp h z) = deriv f z * automorphy_factor h z ^ 2"
proof -
  define z' where "z' = apply_modgrp h z"
  have z': "Im z' > 0"
    using assms by (auto simp: z'_def)
  have "((f \<circ> apply_modgrp h) has_field_derivative
            deriv_mero_uhp f (apply_modgrp h z) * (1 / automorphy_factor h z ^ 2)) (at z)"
    using assms by (intro DERIV_chain derivative_intros) (auto simp: z'_def)
  hence "deriv (f \<circ> apply_modgrp h) z = deriv_mero_uhp f z' / automorphy_factor h z ^ 2"
    using assms by (intro DERIV_imp_deriv) (auto simp: z'_def)
  also have "deriv_mero_uhp f z' = deriv f z'"
    using assms eval_deriv_mero_uhp is_pole_apply_modgrp_iff z' z'_def by blast
  also have "(f \<circ> apply_modgrp h) = f"
    using assms by auto
  finally show "deriv f (apply_modgrp h z) = deriv f z * automorphy_factor h z ^ 2"
    using assms by (auto simp: field_simps z'_def)
qed

text \<open>
  Since $\rho$ and $i$ are fixed points of the transformations $T^{-1}S$ and $S$, respectively,
  any modular function over a subgroup containing the corresponding transformation is non-conformal
  at $\rho$ and $i$, respectively:
\<close>
corollary deriv_rho_eq_0:
  assumes "\<not> is_pole f \<^bold>\<rho>" "shift_modgrp (-1) * S_modgrp \<in> G"
  shows "deriv f \<^bold>\<rho> = 0"
proof (rule apply_modgrp_fixpoint_imp_deriv_eq_0)
  have "apply_modgrp (shift_modgrp (-1) * S_modgrp) \<^bold>\<rho> = - (inverse \<^bold>\<rho>) - 1"
    by (simp add: apply_modgrp_mult field_simps)
  also have "inverse \<^bold>\<rho> = cnj \<^bold>\<rho>"
    by (simp add: modfun_rho_def cis_cnj)
  also have "-cnj \<^bold>\<rho> - 1 = \<^bold>\<rho>"
    by (simp add: complex_eq_iff)
  finally show "apply_modgrp (shift_modgrp (-1) * S_modgrp) \<^bold>\<rho> = \<^bold>\<rho>" .
qed (use assms in \<open>simp_all add: is_singular_modgrp_altdef\<close>)
  
corollary deriv_ii_eq_0:
  assumes "\<not> is_pole f \<i>" "S_modgrp \<in> G"
  shows "deriv f \<i> = 0"
  by (rule apply_modgrp_fixpoint_imp_deriv_eq_0[where h = S_modgrp])
     (use assms in \<open>simp_all add: is_singular_modgrp_altdef\<close>)

corollary deriv_rho_eq_0':
  assumes "\<not>is_pole f z" "rel z \<^bold>\<rho>" "shift_modgrp (-1) * S_modgrp \<in> G"
  shows   "deriv f z = 0"
proof -
  from assms obtain g where g: "g \<in> G" "z = apply_modgrp g \<^bold>\<rho>" "Im z > 0"
    using rel_commutes rel_def by auto
  have "deriv f z = deriv f \<^bold>\<rho> * automorphy_factor g \<^bold>\<rho> ^ 2"
    using assms g by (auto simp: deriv_apply_modgrp)
  also have "\<dots> = 0"
    using assms g by (subst deriv_rho_eq_0) auto
  finally show ?thesis .
qed

corollary deriv_ii_eq_0':
  assumes "\<not>is_pole f z" "rel z \<i>" "S_modgrp \<in> G"
  shows   "deriv f z = 0"
proof -
  from assms obtain g where g: "g \<in> G" "z = apply_modgrp g \<i>" "Im z > 0"
    using rel_commutes rel_def by auto
  have "deriv f z = deriv f \<i> * automorphy_factor g \<i> ^ 2"
    using assms g by (auto simp: deriv_apply_modgrp)
  also have "\<dots> = 0"
    using assms g by (subst deriv_ii_eq_0) auto
  finally show ?thesis .
qed

end


text \<open>
  We now show that every point in \<open>\<R>\<^sub>\<Gamma>'\<close> except for the special points \<open>\<rho>\<close> and \<open>\<i>\<close> has an
  open neighbourhood in which no two points are equivalent. This means that in principle, a 
  modular function \<^emph>\<open>can\<close> be conformal (i.e.\ locally injective) there, and indeed that Klein's
  \<open>J\<close> function is conformal there.

  Any point inside \<open>\<R>\<^sub>\<Gamma>\<close> clearly has such a neighbourhood (namely \<open>\<R>\<^sub>\<Gamma>\<close> itself) since \<open>\<R>\<^sub>\<Gamma>\<close> is open
  and does not contain equivalent points. The problematic cases are the ones where \<open>z\<close> lies on
  the border of \<open>\<R>\<^sub>\<Gamma>\<close>, i.e.\ either on the left vertical line \<open>L\<close> or on the left half \<open>C\<close> of the
  circular arc.

  The geometric intuition in both cases is fairly obvious: we can find a suitably small
  neighbourhood such that each point in it either lies in \<open>\<R>\<^sub>\<Gamma>\<close>, the adjacent region, or the
  border between them. Thus any two equivalent points \<open>x\<close>, \<open>y\<close> in that neighbourhood that are not 
  equal must fulfil w.l.o.g.\ \<open>x = y + 1\<close> (in the case of \<open>L\<close>) or \<open>x = -1/y\<close> (in the case of \<open>C\<close>).
  But in both cases, this transformation sends \<open>y\<close> relatively far away from \<open>x\<close>, so by making
  our neighbourhood sufficiently small, we preclude that case.
\<close>
proposition std_fund_region'_locally_no_equiv_points:
  assumes "z \<in> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>}"
  obtains A where "open A" "z \<in> A" "A \<subseteq> {z. Im z > 0}" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y \<Longrightarrow> x = y"
proof (cases "z \<in> \<R>\<^sub>\<Gamma>")
  case True
  text \<open>If the point in question lies inside the standard region, things are easy.\<close>
  show ?thesis
  proof
    show "open \<R>\<^sub>\<Gamma>" "z \<in> \<R>\<^sub>\<Gamma>"
      using True by auto
    show "x = y" if "x \<sim>\<^sub>\<Gamma> y" "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>" for x y
      using that std_fund_region.unique by blast
  qed (auto simp: in_std_fund_region_iff)
next
  case False
  text \<open>
    If the point does not lie inside the standard region, it either lies on the left
    vertical line or on the left half of the circular arc.
  \<close>
  with assms have "z \<in> \<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma>"
    by blast
  thus ?thesis
    unfolding std_fund_region'_minus_std_fund_region
  proof safe
    text \<open>
      The vertical line case: Here the trick is to choose our open set \<open>A\<close> such that every point
      in it has real value strictly between -1 and 0 and norm greater than 1.
      Then any point in \<open>A\<close> either lies in the standard region or the one to its immediate left.
      Thus if we have two points \<open>x\<close> and \<open>y\<close> in \<open>A\<close>, the canonical representative of \<open>x\<close> is
      either \<open>x\<close> or \<open>x + 1\<close> (and analogously for \<open>y\<close>).

      If \<open>x\<close> and \<open>y\<close> are equivalent, their representatives must be the same.
      But since the real values of any two points in \<open>A\<close> differ by less than 1, \<open>x\<close> and \<open>y\<close> must
      then be equal.      
    \<close>
    assume "Re z = -1/2" "Im z \<ge> sqrt 3 / 2"
    with assms have "Im z \<noteq> sqrt 3 / 2"
      by (auto simp: complex_eq_iff)
    with \<open>Im z \<ge> _\<close> have "Im z > sqrt 3 / 2"
      by auto
    note z = \<open>Re z = -1/2\<close> this

    have "1 = Re z ^ 2 + (sqrt 3 / 2) ^ 2"
      by (simp add: power2_eq_square z)
    also have "\<dots> < norm z ^ 2"
      unfolding cmod_power2 using z by (intro add_strict_left_mono power_strict_mono) auto
    finally have "norm z > 1"
      by (simp add: power2_nonneg_gt_1_iff)
    have [simp]: "dist z (-1) = norm z" "dist (-1) z = norm z"
      by (simp_all add: dist_norm norm_complex_def z)

    define \<epsilon> where "\<epsilon> = (Im z - sqrt 3 / 2) / 2"
    have \<epsilon>: "\<epsilon> > 0" "Im z - \<epsilon> > sqrt 3 / 2"
      using z by (auto simp: \<epsilon>_def field_simps)

    define \<delta> where "\<delta> = norm z - 1"
    have \<delta>: "\<delta> > 0" "norm z = 1 + \<delta>"
      using \<open>norm z > 1\<close> by (simp_all add: \<delta>_def)

    define A where "A = box (z - 1/2 - \<epsilon> * \<i>) (z + 1/2 + \<epsilon> * \<i>) \<inter> ball z \<delta>"
    have A_subset1: "A \<subseteq> {z. Im z > sqrt 3 / 2}"
      using z \<epsilon> by (auto simp: A_def in_box_complex_iff)
    also have "\<dots> \<subseteq> {z. Im z > 0}"
      by (intro Collect_mono impI[OF less_trans[of 0 "sqrt 3 / 2"]]) auto
    finally have A_subset2: "A \<subseteq> {z. Im z > 0}" .
    have Re_A: "Re x \<in> {-1<..<0}" if "x \<in> A" for x
      using that by (auto simp: A_def in_box_complex_iff z)

    have dist_A1: "norm x > 1" if "x \<in> A" for x
    proof -
      have "dist x 0 \<ge> dist z 0 - dist z x"
        using dist_triangle2[of z 0 x] by (simp add: dist_commute algebra_simps)
      moreover have "dist z x < \<delta>"
        using that by (auto simp: A_def)
      ultimately show ?thesis
        using \<delta> by auto
    qed

    have dist_A2: "dist x (-1) > 1" if "x \<in> A" for x
    proof -
      have "dist x (-1) \<ge> dist z (-1) - dist z x"
        using dist_triangle2[of z "-1" x] by (simp add: dist_commute algebra_simps)
      moreover have "dist z x < \<delta>"
        using that by (auto simp: A_def)
      ultimately show ?thesis
        using \<delta> by auto
    qed

    have repr_eq: "modular_group_repr x = (if Re x < -1/2 then x + 1 else x)" if "x \<in> A" for x
      using that A_subset2 dist_A1[of x] dist_A2[of x] Re_A[of x]
      by (intro modular_group_repr_eqI) (auto simp: in_std_fund_region'_iff dist_norm)

    show ?thesis
    proof (rule that[of A])
      show "open A" "z \<in> A"
        using \<epsilon> \<delta> by (auto simp: A_def in_box_complex_iff)
    next
      fix x y assume xy: "x \<in> A" "y \<in> A" "x \<sim>\<^sub>\<Gamma> y"
      have xy': "Im x > 0" "Im y > 0"
        using A_subset2 xy by auto

      define x' y' where "x' = modular_group_repr x" and "y' = modular_group_repr y"
      have "x' = y'"
        using xy xy' by (auto simp: x'_def y'_def modular_group_repr_eq_iff)

      have "\<bar>Re x - Re y\<bar> < 1"
        using xy Re_A[of x] Re_A[of y] by auto
      thus "x = y"
        using \<open>x' = y'\<close> xy by (auto simp: x'_def y'_def repr_eq split: if_splits)
    qed fact+

  next

    text \<open>
      The circular arc case works in a very similar fashion: now we choose \<open>A\<close> such that
      for any point \<open>x \<in> A\<close> we have $\text{Re}(x) \in (-\frac{1}{2}, 0)$ and
      \<open>Im(x) > 0\<close> and \<open>2\<bar>Re(x)\<bar> < \<bar>x\<bar>\<^sup>2\<close>.

      Then any the canonical representative of any point \<open>x \<in> A\<close> is either \<open>x\<close> itself or \<open>-1/x\<close>.
      If we have two equivalent points \<open>x, y \<in> A\<close>, we thus have w.l.o.g.\ \<open>x = y\<close> or \<open>x = -1/y\<close>,
      but the latter case is not possible because \<open>Re(x)\<close> and \<open>Re(y)\<close> are both negative.
    \<close>
    assume z: "norm z = 1" "Im z > 0" "Re z \<in> {-1/2..0}"
    have [simp]: "z \<noteq> 0"
      using z by auto
    define \<phi> where "\<phi> = Arg z"
    have "\<phi> \<ge> 0" "\<phi> \<le> pi"
      using z Arg_bounded[of z] by (auto simp: \<phi>_def Arg_less_0)
    have z_eq: "z = cis \<phi>"
      by (auto simp: \<phi>_def cis_Arg complex_sgn_def z)

    have \<phi>: "\<phi> \<in> {pi/2<..<2*pi/3}"
    proof -
      have "cos \<phi> \<le> cos (pi/2)"
        using z by (simp add: z_eq)
      hence "\<phi> \<ge> pi / 2"
        using \<open>\<phi> \<ge> 0\<close> \<open>\<phi> \<le> pi\<close> by (subst (asm) cos_mono_le_eq) auto
      moreover have "cos \<phi> \<ge> cos (2/3*pi)"
        using z by (simp add: z_eq cos_120 cos_120')
      hence "\<phi> \<le> 2/3*pi"
        using \<open>\<phi> \<ge> 0\<close> \<open>\<phi> \<le> pi\<close> by (subst (asm) cos_mono_le_eq) auto
      moreover have "\<phi> \<noteq> pi / 2"
      proof
        assume *: "\<phi> = pi / 2"
        show False
          using assms by (auto simp: z_eq *)
      qed
      moreover have "\<phi> \<noteq> 2/3*pi"
      proof
        assume *: "\<phi> = 2/3*pi"
        show False
          using assms by (auto simp: z_eq * modfun_rho_def)
      qed
      ultimately show ?thesis
        by auto
    qed

    have "Re z > -1/2"
    proof -
      have "Re z = cos \<phi>"
        by (auto simp: z_eq)
      also have "cos \<phi> > cos (2/3*pi)"
        using \<phi> by (subst cos_mono_less_eq) auto
      finally show ?thesis
        by (auto simp: cos_120 cos_120')
    qed

    have "Re z < 0"
    proof -
      have "Re z = cos \<phi>"
        by (auto simp: z_eq)
      also have "cos \<phi> < cos (pi/2)"
        using \<phi> by (subst cos_mono_less_eq) auto
      finally show ?thesis
        by auto
    qed

    define A' where "A' = (\<lambda>z. norm z ^ 2 - 2 * \<bar>Re z\<bar>) -` {0<..}"
    define A :: "complex set" where "A = Re -` {-1/2<..<0} \<inter> Im -` {0<..} \<inter> A'"
    have Im_A: "Im x > 0" if "x \<in> A" for x
      using that by (auto simp: A_def)
    have Re_A: "Re x \<in> {-1/2<..<0}" if "x \<in> A" for x
      using that by (auto simp: A_def)

    have repr_eq: "modular_group_repr x = (if norm x \<ge> 1 then x else -1/x)" if "x \<in> A" for x
    proof (rule modular_group_repr_eqI)
      show "(if norm x \<ge> 1 then x else - 1 / x) \<in> \<R>\<^sub>\<Gamma>'"
      proof (cases "norm x \<ge> 1")
        case True
        thus ?thesis using Im_A[of x] Re_A[of x] that
          by (auto simp: in_std_fund_region'_iff)
      next
        case False
        have Re: "Re (1 / x) = Re x / norm x ^ 2"
          by (auto simp: Re_divide norm_complex_def)
        have Im: "Im (1 / x) = -Im x / norm x ^ 2"
          by (auto simp: Im_divide norm_complex_def)
        have "\<bar>Re x\<bar> < norm x ^ 2 / 2"
          using that by (auto simp: A_def A'_def)
        thus ?thesis using Im_A[of x] Re_A[of x] that
          by (auto simp: in_std_fund_region'_iff Re Im norm_divide divide_simps)
      qed
    qed (use Im_A[of x] that in auto)

    show ?thesis
    proof (rule that[of A])
      show "open A"
        unfolding A_def A'_def by (intro open_Int open_vimage continuous_intros)
    next
      show "z \<in> A"
        unfolding A_def A'_def using z \<open>Re z > -1/2\<close> \<open>Re z < 0\<close> by auto
    next
      fix x y assume xy: "x \<in> A" "y \<in> A" "x \<sim>\<^sub>\<Gamma> y"
      have xy': "Im x > 0" "Im y > 0"
        using Im_A xy by auto
      have [simp]: "x \<noteq> 0" "y \<noteq> 0"
        using xy' by auto

      define x' y' where "x' = modular_group_repr x" and "y' = modular_group_repr y"
      have "x' = y'"
        using xy xy' by (auto simp: x'_def y'_def modular_group_repr_eq_iff)

      have "x \<noteq> -1/y"
      proof
        assume *: "x = -1/y"
        have "Re x = -Re y / norm y ^ 2"
          by (auto simp: * Re_divide norm_complex_def)
        with Re_A[of x] xy have "Re y > 0"
          by (auto simp: field_simps)
        with Re_A[of y] xy show False
          by auto
      qed
      thus "x = y"
        using \<open>x' = y'\<close> xy by (auto simp: x'_def y'_def repr_eq split: if_splits)
    qed (auto simp: Im_A)
  qed
qed

text \<open>
  The Klein \<open>J\<close> function is conformal everywhere except at \<open>\<i>\<close> and \<open>\<rho>\<close> (where no modular
  function can be conformal).
\<close>
lemma deriv_Klein_J_nonzero':
  assumes "z \<in> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>}"
  shows   "deriv Klein_J z \<noteq> 0"
proof -
  from assms obtain A where A: "open A" "z \<in> A" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y \<Longrightarrow> x = y"
    using std_fund_region'_locally_no_equiv_points by metis
  show ?thesis
  proof (rule holomorphic_injective_imp_regular)
    show "Klein_J holomorphic_on {z. Im z > 0} \<inter> A"
      by (intro holomorphic_intros) (auto simp: complex_is_Real_iff)
    show "open ({z. Im z > 0} \<inter> A)"
      by (intro open_Int open_halfspace_Im_gt A)
    show "z \<in> {z. 0 < Im z} \<inter> A"
      using assms A by (auto simp: in_std_fund_region'_iff)
    show "inj_on Klein_J ({z. 0 < Im z} \<inter> A)"
    proof
      fix u v assume uv: "u \<in> {z. Im z > 0} \<inter> A" "v \<in> {z. Im z > 0} \<inter> A" "Klein_J u = Klein_J v"
      hence "u \<sim>\<^sub>\<Gamma> v"
        by (simp add: Klein_J_eq_iff)
      with uv A show "u = v"
        by auto
    qed
  qed
qed

lemma deriv_Klein_J_nonzero:
  assumes "Im z > 0" "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" "\<not>z \<sim>\<^sub>\<Gamma> \<i>"
  shows   "deriv Klein_J z \<noteq> 0"
proof -
  define z' where "z' = modular_group_repr z"
  have z': "z' \<in> \<R>\<^sub>\<Gamma>'" "z \<sim>\<^sub>\<Gamma> z'" "Im z' > 0"
    using assms(1) modular_group_repr by (auto simp: z'_def)
  then obtain g where g: "z' = apply_modgrp g z"
    by (auto simp: modular_group.rel_def)
  have [simp]: "z' \<noteq> \<^bold>\<rho>" "z' \<noteq> \<i>"
    using z' assms by (auto simp: z'_def modular_group_repr_eq_iff')

  have "(Klein_J has_field_derivative deriv Klein_J z') (at z')"
    using z' by (intro analytic_derivI analytic_intros) (auto simp: complex_is_Real_iff)
  hence "((Klein_J \<circ> apply_modgrp g) has_field_derivative
            deriv Klein_J (apply_modgrp g z) * (1 / automorphy_factor g z ^ 2)) (at z)"
    using assms(1) by (intro DERIV_chain derivative_intros) (auto simp: g)
  hence deriv: "deriv (Klein_J \<circ> apply_modgrp g) z = deriv Klein_J z' / automorphy_factor g z ^ 2"
    by (intro DERIV_imp_deriv) (use g in auto)

  have "deriv Klein_J z = deriv (Klein_J \<circ> apply_modgrp g) z"
  proof (rule deriv_cong_ev)
    have "\<forall>\<^sub>F x in nhds z. x \<in> {x. Im x > 0}"
      using \<open>Im z > 0\<close> by (intro eventually_nhds_in_open open_halfspace_Im_gt) auto
    thus "\<forall>\<^sub>F x in nhds z. Klein_J x = (Klein_J \<circ> apply_modgrp g) x"
      by eventually_elim (auto intro!: Klein_J_cong)
  qed auto
  also note deriv
  also have "deriv Klein_J z' / automorphy_factor g z ^ 2 \<noteq> 0"
    using z' using deriv_Klein_J_nonzero' by auto
  finally show ?thesis .
qed

lemma deriv_J_modform [simp]:
  assumes "Im z > 0"
  shows   "deriv \<J> z = deriv Klein_J z"
proof (rule deriv_cong_ev)
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (nhds z)"
    using assms by (intro eventually_nhds_in_open open_halfspace_Im_gt) auto
  thus "\<forall>\<^sub>F x in nhds z. eval_mero_uhp \<J> x = Klein_J x"
    by eventually_elim auto
qed auto

theorem deriv_Klein_J_eq_0_iff:
  assumes "Im z > 0"
  shows   "deriv Klein_J z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<i> \<or> z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" 
  using deriv_Klein_J_nonzero[of z] Klein_J.deriv_rho_eq_0'[of z] Klein_J.deriv_ii_eq_0'[of z] assms
  by auto


subsection \<open>Real values\<close>

text \<open>
  Since the power series for $J$ only has real coefficients, it has a certain symmetry
  with respect to the imaginary axis.
\<close>
lemma Klein_J_mirror:
  assumes z: "Im z > 0"
  shows   "Klein_J (-cnj z) = cnj (Klein_J z)"
proof -
  define q where "q = to_q 1 z"
  have "(\<lambda>n. of_int (Klein_c n) / 1728 * (to_q 1 (-cnj z)) ^ n) sums 
           (Klein_J (-cnj z) - 1 / (1728 * to_q 1 (-cnj z)))"
    using sums_Klein_J[of "-cnj z"] z by simp
  also have "to_q 1 (-cnj z) = cnj q"
    by (simp add: to_q_def exp_cnj q_def)
  also have "Klein_J (-cnj z) - 1 / (1728 * cnj q) = 
               cnj (cnj (Klein_J (-cnj z)) - 1 / (1728 * q))"
    by simp
  also have "(\<lambda>n. of_int (Klein_c n) / 1728 * cnj q ^ n) =
             (\<lambda>n. cnj (of_int (Klein_c n) / 1728 * q ^ n))" by simp
  finally have "(\<lambda>n. of_int (Klein_c n) / 1728 * q ^ n) sums (cnj (Klein_J (-cnj z)) - 1 / (1728 * q))"
    by (simp only: sums_cnj)
  moreover have "(\<lambda>n. of_int (Klein_c n) / 1728 * q ^ n) sums (Klein_J z - 1 / (1728 * q))"
    using sums_Klein_J[of "z"] z by (simp add: q_def)
  ultimately have "cnj (Klein_J (-cnj z)) - 1 / (1728 * q) = Klein_J z - 1 / (1728 * q)"
    using sums_unique2 by blast
  hence "cnj (Klein_J (-cnj z)) = Klein_J z"
    by simp
  thus "Klein_J (-cnj z) = cnj (Klein_J z)"
    using complex_cnj_cnj by metis
qed

text \<open>
  In particular, this means that $J$ takes real values on the half-circle of radius 1 around the
  origin, on the vertical axes at real value $\pm\frac{1}{2}$, and on the imaginary axis (i.e.\ 
  in particular on the border of the fundamental domain).
\<close>
lemma Klein_J_arc_is_real:
  assumes "norm z = 1" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
proof -
  have "cnj (Klein_J z) = Klein_J (-cnj z)"
    using assms by (simp add: Klein_J_mirror)
  also have "-cnj z = -1 / z"
    using assms by (subst complex_div_cnj) auto
  also have "Klein_J (-1 / z) = Klein_J z"
    using assms by (simp add: Klein_J_minus_one_over)
  finally show ?thesis
    by (simp add: complex_is_Real_iff complex_eq_iff)
qed

lemma Klein_J_vertical_onehalf_is_real:
  assumes "\<bar>Re z\<bar> = 1 / 2" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
proof -
  have "Klein_J z \<in> \<real>" if z: "Re z = -1/2" "Im z > 0" for z
  proof -
    have "cnj (Klein_J z) = Klein_J (-cnj z)"
      using z by (simp add: Klein_J_mirror)
    also have "-cnj z = z + 1"
      using z by (simp add: complex_eq_iff)
    also have "Klein_J (z + 1) = Klein_J z"
      using z by (simp add: Klein_J_plus1) 
    finally show "Klein_J z \<in> \<real>"
      by (simp add: complex_is_Real_iff complex_eq_iff)
  qed
  from this[of z] this[of "z - 1"] Klein_J_plus1[of "z - 1"] show ?thesis
    using assms by (auto simp: abs_if split: if_splits)
qed

lemma Klein_J_imag_axis_is_real:
  assumes "Re z = 0" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
proof -
  have "cnj (Klein_J z) = Klein_J (-cnj z)"
    using assms by (simp add: Klein_J_mirror)
  also have "-cnj z = z"
    using assms by (simp add: complex_eq_iff)
  finally show ?thesis
    using Reals_cnj_iff by blast
qed


text \<open>
  We now show a few more mapping properties of Klein's \<open>J\<close> function, hinted at (mostly without
  proof) in Section~2.7 in Apostol's book. We will look at three regions in and around the
  standard fundamental region \<open>\<R>\<^sub>\<Gamma>\<close>: the left vertical line, the left half of the circular arc,
  and the segment of the imaginary axis with \<open>Im(z) \<ge> 1\<close>.

  We will show that Klein's \<open>J\<close> function takes on precisely all real numbers on these regions.
  To be more precise:
    \<^item> On the left vertical line, it starts with the value 0 at \<open>\<rho>\<close> and then decreases
      strictly monotonically towards \<open>-\<infinity>\<close> as one moves up.

    \<^item> On the circular arc, it starts with the value 0 at \<open>\<rho>\<close> and increases strictly monotonically
      until reaching the value 1 at \<open>\<i>\<close>

    \<^item> On the \<open>Im(z) \<ge> 1\<close>-segment of the imaginary axis, it starts with the value 1 at \<open>\<i>\<close>
      and increases strictly monotonically to \<open>\<infinity>\<close> as one moves up.

\<close>
 

text \<open>
  We define a path with domain \<open>\<real>\<close> whose image is precisely all the values in \<open>\<R>\<^sub>\<Gamma>'\<close> at which
  Klein's \<open>J\<close> function takes real values. We will furthermore show that that real value
  strictly increases as we traverse the path, and that it tends to \<open>\<infinity>\<close> towards the end of the
  path and towards \<open>-\<infinity>\<close> at the beginning of the path.

  Together with the injectivity of \<open>J\<close> on \<open>\<R>\<^sub>\<Gamma>'\<close>, this implies that these are the \<^emph>\<open>only\<close> points
  at which \<open>J\<close> takes real values.

  The path consists of precisely the three edges described earlier: a vertical line with
  real value $-\frac{1}{2}$ that ends at \<open>\<rho>\<close>, a circular arc of radius 1 connecting \<open>\<rho>\<close> and \<open>\<i>\<close>,
  and another vertical line extending upwards from \<open>\<i>\<close> (lying on the imaginary axis):
\<close>
definition Klein_J_aux_path :: "real \<Rightarrow> complex" where
  "Klein_J_aux_path x =
     (if x \<le> 0 then -1/2 + (sqrt 3 / 2 - x) * \<i>
      else if x \<le> 1 then cis (2 / 3 * pi - pi / 6 * x)
      else x * \<i>)"

lemma Klein_J_aux_path_0 [simp]: "Klein_J_aux_path 0 = \<^bold>\<rho>"
  by (simp add: Klein_J_aux_path_def complex_eq_iff)

lemma Klein_J_aux_path_1 [simp]: "Klein_J_aux_path 1 = \<i>"
  by (simp add: Klein_J_aux_path_def complex_eq_iff)

lemma continuous_Klein_J_aux_path: "continuous_on A Klein_J_aux_path"
proof -
  have "continuous_on ({..0} \<union> ({0..1} \<union> {1..})) Klein_J_aux_path"
    unfolding Klein_J_aux_path_def
    by (intro continuous_on_cases closed_Un continuous_intros)
       (auto simp: complex_eq_iff cos_120 sin_120)
  also have "{..(0::real)} \<union> ({0..1} \<union> {1..}) = UNIV"
    by auto
  finally show ?thesis
    by (rule continuous_on_subset) auto
qed

lemma Im_Klein_J_aux_path_pos: "Im (Klein_J_aux_path x) > 0"
proof -
  consider "x \<le> 0" | "x \<in> {0<..1}" | "x > 1"
    by force
  thus ?thesis
  proof cases
    assume "x \<le> 0"
    have "0 < sqrt 3 / 2"
      by simp
    also have "\<dots> \<le> sqrt 3 / 2 - x"
      using \<open>x \<le> 0\<close> by simp
    finally show ?thesis using \<open>x \<le> 0\<close>
      by (auto simp: Klein_J_aux_path_def)
  next
    assume x: "x \<in> {0<..1}"
    have "2 / 3 * pi - pi / 6 * x \<le> 2 / 3 * pi"
      using x by auto
    also have "\<dots> < pi"
      by simp
    finally have "0 < sin (2 * pi / 3 - pi * x / 6)"
      using x by (intro sin_gt_zero) auto
    thus ?thesis using x
      by (auto simp: Klein_J_aux_path_def)
  next
    assume x: "x > 1"
    thus ?thesis
      by (auto simp: Klein_J_aux_path_def)
  qed
qed

lemma Im_Klein_J_aux_path_nonzero: "Im (Klein_J_aux_path x) \<noteq> 0"
  using Im_Klein_J_aux_path_pos[of x] by auto

lemma Klein_J_aux_path_left:
  "x \<le> 0 \<Longrightarrow> Klein_J_aux_path x = -1/2 + (sqrt 3 / 2 - x) *\<^sub>R \<i>"
  by (simp add: Klein_J_aux_path_def scaleR_conv_of_real)

lemma Klein_J_aux_path_middle:
  "x \<in> {0..1} \<Longrightarrow> Klein_J_aux_path x = cis (2 * pi / 3 - x * pi / 6)"
  by (auto simp: Klein_J_aux_path_def algebra_simps complex_eq_iff cos_120' sin_120' cos_120 sin_120)

lemma Klein_J_aux_path_right:
  "x \<ge> 1 \<Longrightarrow> Klein_J_aux_path x = x *\<^sub>R \<i>"
  by (auto simp: Klein_J_aux_path_def algebra_simps complex_eq_iff)

lemma Klein_J_aux_path_inj: "inj Klein_J_aux_path"
proof
  fix x y :: real
  assume eq: "Klein_J_aux_path x = Klein_J_aux_path y"
  have *: "u = w \<longleftrightarrow> Re u = Re w \<and> Im u = Im w \<and> norm u = norm w" for u w
    by (auto simp: complex_eq_iff norm_complex_def)
  have *: "Klein_J_aux_path x \<noteq> Klein_J_aux_path y" if "x < y" for x y
  proof -
    note [simp] = Klein_J_aux_path_left Klein_J_aux_path_middle Klein_J_aux_path_right
    consider "x \<le> 0" "y \<le> 0" | "x \<le> 0" "y \<in> {0<..<1}" | "x \<le> 0" "y \<ge> 1"
           | "x \<in> {0<..<1}" "y \<in> {0<..<1}" | "x \<in> {0<..<1}" "y \<ge> 1" | "x \<ge> 1" "y \<ge> 1"
      using \<open>x < y\<close> unfolding greaterThanLessThan_iff by argo
    thus ?thesis
    proof cases
      assume xy: "x \<le> 0" "y \<in> {0<..<1}"
      hence "cos (2 * pi / 3) < cos (2 * pi / 3 - pi * y / 6)"
        by (subst cos_mono_less_eq) (auto simp: field_simps)
      hence "- (1 / 2) \<noteq> cos (2 * pi / 3 - y * pi / 6)"
        by (simp add: cos_120 cos_120' mult_ac)
      thus ?thesis using xy
        by (auto simp: cos_120 complex_eq_iff)
    next
      assume xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}"
      hence "cos (2 * pi / 3 - pi * x / 6) < cos (2 * pi / 3 - pi * y / 6)"
        using \<open>x < y\<close> by (subst cos_mono_less_eq) (auto simp: field_simps)
      thus ?thesis using xy
        by (simp add: complex_eq_iff mult_ac)
    next
      assume xy: "x \<in> {0<..<1}" "y \<ge> 1"
      hence "cos (pi * 2 / 3 - pi * x / 6) < cos (pi / 2)" 
        by (subst cos_mono_less_eq) (auto simp: field_simps)
      hence "cos (pi * 2 / 3 - pi * x / 6) \<noteq> 0"
        by auto
      thus ?thesis using xy
        by (simp add: complex_eq_iff mult_ac)
    qed (use \<open>x < y\<close>in \<open>auto simp: complex_eq_iff\<close>)
  qed
  show "x = y"
    using eq by (cases x y rule: linorder_cases) (use *[of x y] *[of y x] in auto)
qed 

lemma Klein_J_aux_path_range: "range Klein_J_aux_path \<subseteq> \<R>\<^sub>\<Gamma>'"
proof safe
  fix x :: real
  consider "x \<le> 0" | "x \<in> {0<..1}" | "x > 1"
    by force
  thus "Klein_J_aux_path x \<in> \<R>\<^sub>\<Gamma>'"
  proof cases
    assume x: "x \<in> {0<..1}"
    have "cis (2 * pi / 3 - pi * x / 6) \<in> \<R>\<^sub>\<Gamma>'"
      using x by (subst cis_in_std_fund_region'_iff) (auto simp: field_simps)
    thus ?thesis
      using x by (auto simp: Klein_J_aux_path_def scaleR_conv_of_real)
  qed (use imag_axis_in_std_fund_region'_iff[of x]
           vertical_left_in_std_fund_region'_iff[of "-x + sqrt 3 / 2"] 
       in  \<open>auto simp: Klein_J_aux_path_def scaleR_conv_of_real\<close>)
qed


definition Klein_J_aux_path' :: "real \<Rightarrow> real" where
  "Klein_J_aux_path' = Re \<circ> Klein_J \<circ> Klein_J_aux_path"

lemma continuous_Klein_J_aux_path': "continuous_on A Klein_J_aux_path'"
  unfolding Klein_J_aux_path'_def
  by (intro continuous_on_compose continuous_intros continuous_Klein_J_aux_path)
     (auto simp: complex_is_Real_iff Im_Klein_J_aux_path_nonzero)  

lemma Klein_J_Klein_J_aux_path_in_Reals: "Klein_J (Klein_J_aux_path x) \<in> \<real>"
proof -
  consider "x \<le> 0" | "x \<in> {0<..1}" | "x > 1"
    by force
  thus ?thesis
  proof cases
    assume x: "x \<le> 0"
    have "x < sqrt 3 / 2"
      by (rule le_less_trans [OF x]) auto
    thus ?thesis
      using x using Klein_J_vertical_onehalf_is_real[of "-1/2 + (sqrt 3 / 2 - x) * \<i>"]
        by (auto simp: Klein_J_aux_path_def scaleR_conv_of_real)
  next
    assume x: "x \<in> {0<..1}"
    hence "0 < pi * x + pi * 2"
      by (intro add_nonneg_pos) auto
    hence "Klein_J (cis (2 * pi / 3 - pi * x / 6)) \<in> \<real>"
      using x by (intro Klein_J_arc_is_real) (auto intro!: sin_gt_zero simp: field_simps)
    thus ?thesis
      using x by (auto simp: Klein_J_aux_path_def)
  next
    assume x: "x > 1"
    thus ?thesis
      using x using Klein_J_imag_axis_is_real[of "x * \<i>"]
      by (auto simp: Klein_J_aux_path_def scaleR_conv_of_real)
  qed
qed

lemma inj_on_Re [intro]: "A \<subseteq> \<real> \<Longrightarrow> inj_on Re A"
  by (erule inj_on_subset[rotated]) (auto simp: inj_on_def complex_eq_iff complex_is_Real_iff)

lemma Klein_J_aux_path'_inj: "inj Klein_J_aux_path'"
  unfolding Klein_J_aux_path'_def
proof (intro comp_inj_on)
  show "inj Klein_J_aux_path"
    by (fact Klein_J_aux_path_inj)
  show "inj_on Re (Klein_J ` range Klein_J_aux_path)"
    by (intro inj_on_Re) (use Klein_J_Klein_J_aux_path_in_Reals in auto)
  show "inj_on Klein_J (range Klein_J_aux_path)"
    by (rule inj_on_subset [OF inj_on_Klein_J]) (use Klein_J_aux_path_range in auto)
qed

lemma Klein_J_aux_path'_strict_mono: "strict_mono Klein_J_aux_path'"
proof -
  have "strict_mono Klein_J_aux_path' \<or> strict_mono (\<lambda>x. -Klein_J_aux_path' x)"
    by (intro continuous_inj_on_real_imp_strict_mono Klein_J_aux_path'_inj 
              continuous_Klein_J_aux_path')
  moreover have "\<not>strict_mono (\<lambda>x. -Klein_J_aux_path' x)"
  proof
    assume "strict_mono (\<lambda>x. -Klein_J_aux_path' x)"
    hence "-Klein_J_aux_path' 0 < -Klein_J_aux_path' 1"
      by (rule strict_monoD) auto
    thus False
      by (simp add: Klein_J_aux_path'_def)
  qed
  ultimately show ?thesis
    by blast
qed

lemma Re_Klein_J_left_vertical_less:
  assumes "Re x = -1 / 2" "Re y = - 1 / 2" "sqrt 3 / 2 \<le> Im x" "Im x < Im y"
  shows   "Re (Klein_J x) > Re (Klein_J y)"
proof -
  have "Klein_J_aux_path' (-(Im y - sqrt 3 / 2)) < Klein_J_aux_path' (-(Im x - sqrt 3 / 2))"
    by (intro strict_monoD [OF Klein_J_aux_path'_strict_mono]) (use assms in auto)
  moreover have "Im y *\<^sub>R \<i> - 1 / 2 = y" "Im x *\<^sub>R \<i> - 1 / 2 = x"
    using assms by (auto simp: complex_eq_iff)
  ultimately show ?thesis using assms
    by (simp add: Klein_J_aux_path'_def Klein_J_aux_path_left)
qed

lemma Re_Klein_J_left_vertical_le:
  assumes "Re x = -1 / 2" "Re y = - 1 / 2" "sqrt 3 / 2 \<le> Im x" "Im x \<le> Im y"
  shows   "Re (Klein_J x) \<ge> Re (Klein_J y)"
proof (cases "Im x = Im y")
  case True
  hence "x = y"
    using assms by (auto simp: complex_eq_iff)
  thus ?thesis
    by simp
qed (use Re_Klein_J_left_vertical_less[of x y] assms in auto)

lemma Re_Klein_J_arc_less:
  assumes "pi / 2 \<le> x" "x < y" "y \<le> 2 * pi / 3"
  shows   "Re (Klein_J (cis x)) > Re (Klein_J (cis y))"
proof -
  define x' where "x' = 1 - (x - pi / 2) / (pi / 6)"
  define y' where "y' = 1 - (y - pi / 2) / (pi / 6)"
  have "Klein_J_aux_path' x' > Klein_J_aux_path' y'"
    by (intro strict_monoD [OF Klein_J_aux_path'_strict_mono])
       (use assms in \<open>auto simp: field_simps x'_def y'_def\<close>)
  moreover have "x' \<in> {0..1}" "y' \<in> {0..1}"
    using assms by (auto simp: x'_def y'_def field_simps)
  ultimately show ?thesis using assms
    by (simp add: Klein_J_aux_path'_def Klein_J_aux_path_middle x'_def y'_def field_simps)
qed

lemma Re_Klein_J_arc_le:
  assumes "pi / 2 \<le> x" "x \<le> y" "y \<le> 2 * pi / 3"
  shows   "Re (Klein_J (cis x)) \<ge> Re (Klein_J (cis y))"
  by (cases "x = y") (use Re_Klein_J_arc_less[of x y] assms in auto)

lemma Re_Klein_J_arc_less':
  assumes "norm x = 1" "norm y = 1" "pi / 2 \<le> Arg x" "Arg x < Arg y" "Arg y \<le> 2 * pi / 3"
  shows   "Re (Klein_J x) > Re (Klein_J y)"
proof -
  have [simp]: "x \<noteq> 0" "y \<noteq> 0"
    using assms by auto
  have "Re (Klein_J (cis (Arg x))) > Re (Klein_J (cis (Arg y)))"
    using assms by (intro Re_Klein_J_arc_less) auto
  moreover have "cis (Arg x) = x" "cis (Arg y) = y"
    by (simp_all add: cis_Arg complex_sgn_def assms)
  ultimately show ?thesis
    by simp
qed

lemma Re_Klein_J_arc_le':
  assumes "norm x = 1" "norm y = 1" "pi / 2 \<le> Arg x" "Arg x \<le> Arg y" "Arg y \<le> 2 * pi / 3"
  shows   "Re (Klein_J x) \<ge> Re (Klein_J y)"
proof (cases "Arg x = Arg y")
  case True
  hence "cis (Arg x) = cis (Arg y)"
    by simp
  hence "x = y"
    by (subst (asm) (1 2) cis_Arg) (use assms in \<open>auto simp: complex_sgn_def\<close>)
  thus ?thesis
    by simp
qed (use Re_Klein_J_arc_less'[of x y] assms in auto)

lemma Re_Klein_J_imag_axis_less:
  assumes "Re x = 0" "Re y = 0" "1 \<le> Im x" "Im x < Im y"
  shows   "Re (Klein_J x) < Re (Klein_J y)"
proof -
  have "Klein_J_aux_path' (Im x) < Klein_J_aux_path' (Im y)"
    by (intro strict_monoD [OF Klein_J_aux_path'_strict_mono]) (use assms in auto)
  moreover have "Im x *\<^sub>R \<i> = x" "Im y *\<^sub>R \<i> = y"
    using assms by (auto simp: complex_eq_iff)
  ultimately show ?thesis using assms
    by (simp add: Klein_J_aux_path'_def Klein_J_aux_path_right)
qed

lemma Re_Klein_J_imag_axis_le:
  assumes "Re x = 0" "Re y = 0" "1 \<le> Im x" "Im x \<le> Im y"
  shows   "Re (Klein_J x) \<le> Re (Klein_J y)"
proof (cases "Im x = Im y")
  case True
  hence "x = y"
    using assms by (auto simp: complex_eq_iff)
  thus ?thesis
    by simp
qed (use Re_Klein_J_imag_axis_less[of x y] assms in auto)

lemma Re_Klein_J_neg:
  "Re x = -1 / 2 \<Longrightarrow> Im x > sqrt 3 / 2 \<Longrightarrow> Re (Klein_J x) < 0"
  using Re_Klein_J_left_vertical_less[of "\<^bold>\<rho>" x] by simp

lemma Re_Klein_J_nonpos:
  "Re x = -1 / 2 \<Longrightarrow> Im x \<ge> sqrt 3 / 2 \<Longrightarrow> Re (Klein_J x) \<le> 0"
  using Re_Klein_J_left_vertical_le[of "\<^bold>\<rho>" x] by simp

lemma Re_Klein_J_gt_1:
  "Re x = 0 \<Longrightarrow> Im x > 1 \<Longrightarrow> Re (Klein_J x) > 1"
  using Re_Klein_J_imag_axis_less[of "\<i>" x] by simp

lemma Re_Klein_J_ge_1:
  "Re x = 0 \<Longrightarrow> Im x \<ge> 1 \<Longrightarrow> Re (Klein_J x) \<ge> 1"
  using Re_Klein_J_imag_axis_le[of "\<i>" x] by simp

lemma Re_Klein_J_pos:
  "x \<in> {pi/2..<2/3*pi} \<Longrightarrow> Re (Klein_J (cis x)) > 0"
  using Re_Klein_J_arc_less[of x "2 * pi / 3"] modfun_rho_def [symmetric] by simp

lemma Re_Klein_J_pos':
  "norm x = 1 \<Longrightarrow> Arg x \<in> {pi/2..<2/3*pi} \<Longrightarrow> Re (Klein_J x) > 0"
  using Re_Klein_J_pos [of "Arg x"]
  by (subst (asm) cis_Arg) (auto simp: complex_sgn_def)

lemma Re_Klein_J_nonneg:
  assumes "x \<in> {pi/2..2/3*pi}"
  shows   "Re (Klein_J (cis x)) \<in> {0..1}"
proof -
  have "Re (Klein_J (cis x)) \<le> Re (Klein_J (cis (pi / 2)))"
    by (intro Re_Klein_J_arc_le) (use assms in auto)
  moreover have "Re (Klein_J (cis x)) \<ge> Re (Klein_J (cis (2/3*pi)))"
    by (intro Re_Klein_J_arc_le) (use assms in auto)
  moreover have "cis (2/3*pi) = \<^bold>\<rho>"
    by (simp add: modfun_rho_def)
  ultimately show ?thesis
    by auto
qed

lemma Re_Klein_J_nonneg':
  "norm x = 1 \<Longrightarrow> Arg x \<in> {pi/2..2/3*pi} \<Longrightarrow> Re (Klein_J x) \<ge> 0"
  using Re_Klein_J_nonneg [of "Arg x"]
  by (subst (asm) cis_Arg) (auto simp: complex_sgn_def)

lemma Re_Klein_J_less_1:
  "x \<in> {pi/2<..2/3*pi} \<Longrightarrow> Re (Klein_J (cis x)) < 1"
  using Re_Klein_J_arc_less[of "pi / 2" x] by simp

lemma Re_Klein_J_less_1':
  "norm x = 1 \<Longrightarrow> Arg x \<in> {pi/2<..2/3*pi} \<Longrightarrow> Re (Klein_J x) < 1"
  using Re_Klein_J_less_1 [of "Arg x"]
  by (subst (asm) cis_Arg) (auto simp: complex_sgn_def)

lemma filterlim_Klein_J_at_ii_inf: "filterlim Klein_J at_infinity at_\<i>\<infinity>"
proof -
  have "is_pole (fourier_expansion (Suc 0) \<J>) 0"
    using Klein_J.fourier_expansion_meromorphic_axioms Klein_J.zorder_at_ii_inf_conv_fourier
          fourier_expansion_meromorphic.zorder_fourier_nonneg_iff by force
  hence "filterlim \<J> at_infinity at_\<i>\<infinity>"
    using Klein_J.fourier_is_pole_0_iff by blast
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro filterlim_cong eventually_mono[OF eventually_at_ii_inf[of 0]]) auto
  finally show ?thesis .
qed

lemma filterlim_Re_Klein_J_at_bot:
  "filterlim (\<lambda>x. Re (Klein_J (-1/2 + x *\<^sub>R \<i>))) at_bot at_top"
proof -
  have "filterlim (\<lambda>x. - 1 / 2 + x *\<^sub>R \<i>) at_\<i>\<infinity> at_top"
    unfolding at_ii_inf_def filterlim_filtercomap_iff o_def by (simp add: filterlim_ident)
  hence "filterlim (\<lambda>x. Klein_J (-1/2 + x *\<^sub>R \<i>)) at_infinity at_top"
    by (rule filterlim_compose[OF filterlim_Klein_J_at_ii_inf])
  hence "filterlim (\<lambda>x. norm (Klein_J (-1/2 + x *\<^sub>R \<i>))) at_top at_top"
    using filterlim_at_infinity_imp_norm_at_top by blast
  also have "?this \<longleftrightarrow> filterlim (\<lambda>x. - Re (Klein_J (-1/2 + x *\<^sub>R \<i>))) at_top at_top"
  proof (intro filterlim_cong)
    show "\<forall>\<^sub>F x in at_top. cmod (Klein_J (- 1 / 2 + x *\<^sub>R \<i>)) = - Re (Klein_J (- 1 / 2 + x *\<^sub>R \<i>))"
      using eventually_gt_at_top[of "sqrt 3 / 2"] eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim x)
      thus ?case
        using Re_Klein_J_neg[of "-1/2 + x *\<^sub>R \<i>"]
              Klein_J_vertical_onehalf_is_real[of "-1/2 + x *\<^sub>R \<i>"]
        by (auto elim!: Reals_cases)
    qed
  qed auto
  also have "\<dots> \<longleftrightarrow> ?thesis"
    by (simp add: filterlim_uminus_at_bot)
  finally show ?thesis .
qed

lemma filterlim_Re_Klein_J_at_top:
  "filterlim (\<lambda>x. Re (Klein_J (x *\<^sub>R \<i>))) at_top at_top"
proof -
  have "filterlim (\<lambda>x. x *\<^sub>R \<i>) at_\<i>\<infinity> at_top"
    unfolding at_ii_inf_def filterlim_filtercomap_iff o_def by (simp add: filterlim_ident)
  hence "filterlim (\<lambda>x. Klein_J (x *\<^sub>R \<i>)) at_infinity at_top"
    by (rule filterlim_compose [OF filterlim_Klein_J_at_ii_inf])
  hence "filterlim (\<lambda>x. norm (Klein_J (x *\<^sub>R \<i>))) at_top at_top"
    using filterlim_at_infinity_imp_norm_at_top by blast
  also have "?this \<longleftrightarrow> filterlim (\<lambda>x. Re (Klein_J (x *\<^sub>R \<i>))) at_top at_top"
  proof (intro filterlim_cong)
    show "\<forall>\<^sub>F x in at_top. cmod (Klein_J (x *\<^sub>R \<i>)) = Re (Klein_J (x *\<^sub>R \<i>))"
      using eventually_gt_at_top[of "sqrt 3 / 2"] eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim x)
      thus ?case
        using Re_Klein_J_gt_1[of "x *\<^sub>R \<i>"] Klein_J_imag_axis_is_real[of "x *\<^sub>R \<i>"]
        by (auto elim!: Reals_cases)
    qed
  qed auto
  finally show ?thesis .
qed

lemma Klein_J_on_arc: "(Klein_J \<circ> cis) ` {pi/2..2/3*pi} = of_real ` {0..1}"
  unfolding o_def
proof safe
  fix t :: real assume t: "t \<in> {pi/2..2/3*pi}"
  have "t > 0"
    by (rule less_le_trans[of _ "pi/2"]) (use t in auto)
  moreover have "t < pi"
    by (rule le_less_trans[of _ "2/3*pi"]) (use t in auto)
  ultimately have "Klein_J (cis t) \<in> \<real>"
    by (intro Klein_J_arc_is_real) (auto intro!: sin_gt_zero)
  moreover have "Re (Klein_J (cis t)) \<in> {0..1}"
    using t Re_Klein_J_nonneg by blast
  ultimately show "Klein_J (cis t) \<in> complex_of_real ` {0..1}"
    by (auto elim!: Reals_cases)
next
  fix x :: real assume x: "x \<in> {0..1}"
  thm IVT'
  have "\<exists>t. 0 \<le> t \<and> t \<le> 1 \<and> Klein_J_aux_path' t = x"
    using x by (intro IVT' continuous_intros continuous_Klein_J_aux_path')
               (auto simp: Klein_J_aux_path'_def)
  then obtain t where t: "t \<in> {0..1}" "Klein_J_aux_path' t = x"
    by auto
  show "x \<in> (\<lambda>x. Klein_J (cis x)) ` {pi/2..2/3*pi}"
  proof (rule rev_image_eqI)
    show "2 * pi / 3 - t * pi / 6 \<in> {pi / 2..2 / 3 * pi}"
      using t by (auto simp: field_simps)
    have "0 < pi * t + pi * 2"
      using t by (intro add_nonneg_pos) auto
    hence "Klein_J (cis (2 * pi / 3 - t * pi / 6)) \<in> \<real>"
      using t by (intro Klein_J_arc_is_real)
                 (auto intro!: sin_gt_zero simp: field_simps)
    moreover have "x = Re (Klein_J (cis (2 * pi / 3 - t * pi / 6)))"
      using t by (auto simp: Klein_J_aux_path'_def Klein_J_aux_path_middle)
    ultimately show "complex_of_real x = Klein_J (cis (2 * pi / 3 - t * pi / 6))"
      by auto
  qed
qed

lemma Klein_J_on_left_vline:
  "(\<lambda>x. Klein_J (-1/2 + x *\<^sub>R \<i>)) ` {sqrt 3/2..} = of_real ` {..0}"
proof safe
  fix t :: real assume t: "t \<ge> sqrt 3 / 2"
  have "t > 0"
    by (rule less_le_trans[OF _ t]) auto
  have "Klein_J (- 1 / 2 + t *\<^sub>R \<i>) \<in> \<real>"
    using \<open>t > 0\<close> by (intro Klein_J_vertical_onehalf_is_real) auto
  moreover have "Re (Klein_J (- 1 / 2 + t *\<^sub>R \<i>)) \<le> 0"
    using t by (intro Re_Klein_J_nonpos) auto
  ultimately show "Klein_J (- 1 / 2 + t *\<^sub>R \<i>) \<in> complex_of_real ` {..0}"
    by (auto elim!: Reals_cases)
next
  fix x :: real assume x: "x \<le> 0"
  have ev: "eventually (\<lambda>y. Re (Klein_J (-1/2 + y *\<^sub>R \<i>)) < x) at_top"
    using filterlim_Re_Klein_J_at_bot unfolding filterlim_at_bot_dense by blast
  have rho: "(sqrt 3 / 2) *\<^sub>R \<i> - 1 / 2 = \<^bold>\<rho>"
    by (auto simp: complex_eq_iff)
  have rho': "Klein_J ((sqrt 3 / 2) *\<^sub>R \<i> - 1 / 2) = 0"
    by (subst rho) auto
  obtain y where y: "y > sqrt 3 / 2" "Re (Klein_J (-1/2 + y *\<^sub>R \<i>)) < x"
    using eventually_happens[OF eventually_conj[OF ev eventually_gt_at_top[of "sqrt 3 / 2"]]]
    by auto
  have "y > 0"
    by (rule less_trans[OF _ y(1)]) auto
  hence "\<exists>z. sqrt 3 / 2 \<le> z \<and> z \<le> y \<and> Re (Klein_J (-1/2 + z *\<^sub>R \<i>)) = x"
    using y x rho' by (intro IVT2' continuous_intros) (auto simp: complex_is_Real_iff)
  then obtain z where z: "sqrt 3 / 2 \<le> z" "z \<le> y" "Re (Klein_J (-1/2 + z *\<^sub>R \<i>)) = x"
    by auto
  have "z > 0"
    by (rule less_le_trans[OF _ z(1)]) auto
  show "complex_of_real x \<in> (\<lambda>x. Klein_J (- 1 / 2 + x *\<^sub>R \<i>)) ` {sqrt 3 / 2..}"
  proof (rule rev_image_eqI)
    show "z \<in> {sqrt 3 / 2..}"
      using z by auto
    have "Klein_J (- 1 / 2 + z *\<^sub>R \<i>) \<in> \<real>"
      using \<open>z > 0\<close> by (intro Klein_J_vertical_onehalf_is_real) auto
    with z show "complex_of_real x = Klein_J (- 1 / 2 + z *\<^sub>R \<i>)"
      by auto
  qed
qed

lemma Klein_J_on_imag_axis:
  "(\<lambda>x. Klein_J (x *\<^sub>R \<i>)) ` {1..} = of_real ` {1..}"
proof safe
  fix t :: real assume t: "t \<ge> 1"
  have "Klein_J (t *\<^sub>R \<i>) \<in> \<real>"
    using t by (intro Klein_J_imag_axis_is_real) auto
  moreover have "Re (Klein_J (t *\<^sub>R \<i>)) \<ge> 1"
    using t by (intro Re_Klein_J_ge_1) auto
  ultimately show "Klein_J (t *\<^sub>R \<i>) \<in> complex_of_real ` {1..}"
    by (auto elim!: Reals_cases)
next
  fix x :: real assume x: "x \<ge> 1"
  have ev: "eventually (\<lambda>y. Re (Klein_J (y *\<^sub>R \<i>)) > x) at_top"
    using filterlim_Re_Klein_J_at_top unfolding filterlim_at_top_dense by blast
  obtain y where y: "y > 1" "Re (Klein_J (y *\<^sub>R \<i>)) > x"
    using eventually_happens[OF eventually_conj[OF ev eventually_gt_at_top[of 1]]]
    by auto
  hence "\<exists>z. 1 \<le> z \<and> z \<le> y \<and> Re (Klein_J (z *\<^sub>R \<i>)) = x"
    using y x by (intro IVT' continuous_intros) (auto simp: complex_is_Real_iff)
  then obtain z where z: "1 \<le> z" "z \<le> y" "Re (Klein_J (z *\<^sub>R \<i>)) = x"
    by auto
  show "complex_of_real x \<in> (\<lambda>x. Klein_J (x *\<^sub>R \<i>)) ` {1..}"
  proof (rule rev_image_eqI)
    show "z \<in> {1..}"
      using z by auto
    have "Klein_J (z *\<^sub>R \<i>) \<in> \<real>"
      using z by (intro Klein_J_imag_axis_is_real) auto
    with z show "complex_of_real x = Klein_J (z *\<^sub>R \<i>)"
      by auto
  qed
qed

lemma Klein_J_on_border: "Klein_J ` (\<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma>) = of_real ` {..1}"
proof -
  have "\<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma> = cis ` {pi/2..2/3*pi} \<union> (\<lambda>x. (-1/2 + x *\<^sub>R \<i>)) ` {sqrt 3/2..}"
    unfolding std_fund_region'_minus_std_fund_region
    using std_fund_region'_border_aux1 std_fund_region'_border_aux2 by argo
  also have "Klein_J ` \<dots> = of_real ` ({0..1} \<union> {..0})"
    using Klein_J_on_arc Klein_J_on_left_vline
    by (simp add: image_Un image_image)
  also have "{0..1} \<union> {..0} = {..(1::real)}"
    by auto
  finally show ?thesis .
qed


subsection \<open>Inverse function\<close>

text \<open>
  This is the branch of the inverse function to Klein's \<open>J\<close> function whose codomain is \<open>\<R>\<^sub>\<Gamma>'\<close>.
  It has a branch cut on the slit \<open>(-\<infinity>, 1]\<close>.
\<close>

definition Klein_J_inv :: "complex \<Rightarrow> complex" where
  "Klein_J_inv = the_inv_into \<R>\<^sub>\<Gamma>' Klein_J"

lemma Klein_J_inv_in_std_fund_region' [intro]: "Klein_J_inv z \<in> \<R>\<^sub>\<Gamma>'"
  using the_inv_into_into [OF inj_on_Klein_J _ order.refl, of z] bij_betw_Klein_J
  by (auto simp: bij_betw_def Klein_J_inv_def)

lemma Im_Klein_J_inv_pos [intro]: "Im (Klein_J_inv z) > 0"
  using Klein_J_inv_in_std_fund_region' in_std_fund_region'_iff by blast

lemma Klein_J_Klein_J_inv [simp]: "Klein_J (Klein_J_inv z) = z"
  unfolding Klein_J_inv_def using f_the_inv_into_f_bij_betw [OF bij_betw_Klein_J] by simp

lemma Klein_J_inv_Klein_J [simp]: "z \<in> \<R>\<^sub>\<Gamma>' \<Longrightarrow> Klein_J_inv (Klein_J z) = z"
  unfolding Klein_J_inv_def using the_inv_into_f_f[OF inj_on_Klein_J, of z] by simp

lemma Klein_J_inv_eq_iff: "Klein_J_inv z = u \<longleftrightarrow> Klein_J u = z \<and> u \<in> \<R>\<^sub>\<Gamma>'"
  using Klein_J_Klein_J_inv Klein_J_inv_Klein_J Klein_J_inv_in_std_fund_region' by blast

lemma Klein_J_inv_not_real [simp]: "Klein_J_inv z \<notin> \<real>"
  using Im_Klein_J_inv_pos[of z] by (auto simp: complex_is_Real_iff)

lemma Klein_J_inv_eqI: "Klein_J u = z \<Longrightarrow> u \<in> \<R>\<^sub>\<Gamma>' \<Longrightarrow> Klein_J_inv z = u"
  by (simp add: Klein_J_inv_eq_iff)

lemma Klein_J_inv_eq_i_iff [simp]: "Klein_J_inv z = \<i> \<longleftrightarrow> z = 1"
  by (simp add: Klein_J_inv_eq_iff)

lemma Klein_J_inv_eq_rho_iff [simp]: "Klein_J_inv z = \<^bold>\<rho> \<longleftrightarrow> z = 0"
  by (simp add: Klein_J_inv_eq_iff)

lemma Klein_J_inv_equiv_iff [simp]:
  assumes "Im x > 0"
  shows   "Klein_J_inv z \<sim>\<^sub>\<Gamma> x \<longleftrightarrow> Klein_J x = z"
  by (metis Im_Klein_J_inv_pos Klein_J_eq_iff Klein_J_inv_eq_iff assms)

lemma Klein_J_inv_equiv_iff' [simp]:
  assumes "Im x > 0"
  shows   "x \<sim>\<^sub>\<Gamma> Klein_J_inv z \<longleftrightarrow> Klein_J x = z"
  by (metis Im_Klein_J_inv_pos Klein_J_eq_iff Klein_J_inv_eq_iff assms)

lemma Klein_J_inv_has_field_derivative:
  assumes z: "z \<notin> of_real ` {..1}"
  shows   "(Klein_J_inv has_field_derivative inverse (deriv Klein_J (Klein_J_inv z))) (at z)"
proof (rule has_field_derivative_inverse_strong_x[where f = Klein_J])
  show "(Klein_J has_field_derivative deriv Klein_J (Klein_J_inv z)) (at (Klein_J_inv z))"
    by (rule analytic_intros analytic_derivI)+ auto
  show "deriv Klein_J (Klein_J_inv z) \<noteq> 0"
    using z by (subst deriv_Klein_J_eq_0_iff) auto
  show "open (\<R>\<^sub>\<Gamma> :: complex set)" "continuous_on \<R>\<^sub>\<Gamma> Klein_J"
    by (auto intro!: continuous_intros open_halfspace_Im_gt
             simp: complex_is_Real_iff in_std_fund_region_iff)
  have "Klein_J_inv z \<in> \<R>\<^sub>\<Gamma>'"
    by auto
  moreover have "Klein_J_inv z \<notin> \<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma>"
    using Klein_J_on_border z by force
  ultimately show "Klein_J_inv z \<in> \<R>\<^sub>\<Gamma>"
    unfolding std_fund_region'_def by auto
qed (auto simp: std_fund_region'_def)


subsection \<open>Covering properties\<close>

text \<open>
  Next, we show a topological fact that Apostol implicitly uses to prove Picard's little theorem
  without mentioning it: We view $J$ as a map from the upper half plane minus the elliptic points
  (i.e.\ the orbits of $i$ and $\rho$) to $\mathbb{C}\setminus\{0,1\}$.
  This map is then a \<^emph>\<open>covering\<close>, i.e.\ it maps infinitely many copies of the fundamental region
  to $\mathbb{C}\setminus\{0,1\}$.

  Some additional facts about coverings would probably make this proof less bulky.
  Most textbook also derive Picard's little theorem using the modular lamdba function instead, 
  whose derivative does not vanish, which means that no points have to be removed and the topology
  becomes easier to manage.
\<close>
theorem covering_map_Klein_J:
  defines "A \<equiv> {z. Im z > 0} - modular_group.orbit \<^bold>\<rho> - modular_group.orbit \<i>"
  shows   "open A" "covering_space A Klein_J (-{0,1})"
proof -
  have [simp]: "Im z > 0" if "z \<in> \<R>\<^sub>\<Gamma>'" for z
    using that by (auto simp: in_std_fund_region'_iff)
  have "openin (top_of_set {z. Im z > 0}) A"
    unfolding A_def
    by (intro openin_diff modular_group.closed_orbit)
       (auto simp: openin_open_eq open_halfspace_Im_gt)
  thus "open A"
    by (subst (asm) openin_open_eq) (auto simp: open_halfspace_Im_gt)

  show "covering_space A Klein_J (-{0,1})"
  proof (standard, goal_cases)
    show "continuous_on A Klein_J"
      by (intro continuous_intros) (auto simp: complex_is_Real_iff A_def)
  next
    have "bij_betw Klein_J (\<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>} - {\<i>}) (UNIV - {0} - {1})"
      by (intro bij_betw_DiffI bij_betw_singletonI bij_betw_Klein_J) auto
    hence "-{0,1} = Klein_J ` (\<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>})"
      by (auto simp: bij_betw_def)
    also have "\<dots> \<subseteq> Klein_J ` A"
      unfolding A_def using std_fund_region'_unique
      by (intro image_mono) (auto simp: modular_group.orbit_def)
    finally have "-{0, 1} \<subseteq> Klein_J ` A" .
    moreover have "Klein_J ` A \<subseteq> -{0, 1}"
      unfolding A_def by (auto simp: modular_group.orbit_def Klein_J_eqD)
    ultimately show "Klein_J ` A = -{0, 1}"
      by blast
  next
    case u: (3 u)
    define z where "z = Klein_J_inv u"
    have z: "z \<in> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>}"
      using u unfolding z_def by (simp add: Klein_J_inv_in_std_fund_region')
    obtain S where S: "open S" "z \<in> S" "S \<subseteq> {z. Im z > 0}"
                      "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y \<Longrightarrow> x = y"
      using std_fund_region'_locally_no_equiv_points[OF z] by metis
    define S' where "S' = S - modular_group.orbit \<^bold>\<rho> - modular_group.orbit \<i>"
    define T where "T = Klein_J ` S'"
    have "z \<in> S'"
      using z S  std_fund_region'_unique[of "\<^bold>\<rho>" z] std_fund_region'_unique[of "\<i>" z]
      by (auto simp: S'_def modular_group.orbit_def)
    have "openin (top_of_set {z. Im z > 0}) S'"
      unfolding S'_def using S
      by (intro openin_diff modular_group.closed_orbit)
         (auto simp: openin_open_eq open_halfspace_Im_gt)
    hence "open S'"
      by (auto simp: openin_open_eq open_halfspace_Im_gt)

    show ?case
    proof (rule exI[of _ T], safe)
      have "u = Klein_J z"
        by (auto simp: z_def)
      from \<open>z \<in> S'\<close> and this show "u \<in> T"
        unfolding T_def by (rule rev_image_eqI)
    next
      have "open (Klein_J ` S')"
      proof (rule open_mapping_thm2)
        show "S' \<subseteq> {z. Im z > 0}"
          unfolding S'_def using S by auto
      next
        fix X assume X: "open X" "X \<subseteq> {z. Im z > 0}" "X \<noteq> {}"
        show "\<not>Klein_J constant_on X"
        proof
          assume *: "Klein_J constant_on X"
          have "is_const_mero_uhp \<J>"
          proof (rule constant_on_extend_mero_uhp_rel[OF _ *])
            show "mero_uhp_rel (eval_mero_uhp \<J>) Klein_J"
              by mero_uhp_rel
          qed (use X in auto)
          thus False
            using degree_modfun_J by fastforce
        qed
      qed (use S \<open>open S'\<close>
           in  \<open>auto simp: open_halfspace_Im_gt complex_is_Real_iff intro!: holomorphic_intros\<close>)
      moreover have "Klein_J w \<noteq> 0" if "w \<in> S'" for w
        using that S
        by (subst Klein_J_eq_0_iff)
           (auto simp: S'_def modular_group.orbit_def modular_group.rel_commutes)
      moreover have "Klein_J w \<noteq> 1" if "w \<in> S'" for w
        using that S
        by (subst Klein_J_eq_1_iff)
           (auto simp: S'_def modular_group.orbit_def modular_group.rel_commutes)
      ultimately show "openin (top_of_set (-{0,1})) T"
        using S \<open>open S'\<close> by (subst openin_open_eq) (auto simp: T_def S'_def)
    next
      define V' where "V' = {h. abs h = (h :: modgrp)}"
      define V where "V = (\<lambda>f. apply_modgrp f ` S') ` V'"
      show "\<exists>V. \<Union>V = A \<inter> Klein_J -` T \<and> (\<forall>X\<in>V. openin (top_of_set A) X) \<and> disjoint V \<and>
                (\<forall>X\<in>V. \<exists>q. homeomorphism X T Klein_J q)"
      proof (rule exI[of _ V], intro conjI ballI)
        text \<open>\<^term>\<open>V\<close> is disjoint:\<close>
        have "disjoint_family_on (\<lambda>f. apply_modgrp f ` S') V'"
          unfolding disjoint_family_on_def
        proof (intro ballI impI)
          fix f g :: modgrp assume fg: "f \<noteq> g" "f \<in> V'" "g \<in> V'"
          show "apply_modgrp f ` S' \<inter> apply_modgrp g ` S' = {}"
          proof safe
            fix x y assume xy: "x \<in> S'" "y \<in> S'" "apply_modgrp f x = apply_modgrp g y"
            from xy have xy': "Im x > 0" "Im y > 0"
              using S by (auto simp: S'_def)
            with xy(3) have "x \<sim>\<^sub>\<Gamma> y"
              by (metis Klein_J_apply_modgrp Klein_J_eqD)
            with S(4)[of x y] xy have "x = y"
              by (auto simp: S'_def)
            with xy xy' have "apply_modgrp (inverse g * f) x = x"
              by (subst apply_modgrp_mult; force intro: apply_modgrp_inverse_eqI)
            hence "\<bar>inverse g * f\<bar> = 1"
              using xy xy' unfolding S'_def
              by (intro modgrp_fixed_point_trivial)
                 (auto simp: modular_group.orbit_def modular_group.rel_commutes)
            hence "abs f = abs g"
              by (metis abs_eq_modgrpE abs_uminus_modgrp mult_1_right
                        inverse_mult_assoc1_modgrp times_modgrp_uminus_right)
            with fg show "apply_modgrp f x \<in> {}"
              by (auto simp: V'_def)
          qed
        qed
        thus "disjoint V"
          unfolding V_def by (rule disjoint_family_on_disjoint_image)
      next
        show "\<Union>V = A \<inter> Klein_J -` T"
          unfolding V_def
        proof safe
          fix x :: complex and f :: modgrp
          assume x: "x \<in> S'"
          from x have "Im x > 0"
            using S by (auto simp: S'_def)
          show "apply_modgrp f x \<in> A"
            using S \<open>Im x > 0\<close> x unfolding A_def S'_def
            by (auto simp: modular_group.orbit_def)
          show "apply_modgrp f x \<in> Klein_J -` T"
            using \<open>Im x > 0\<close> x unfolding T_def by (auto simp: Klein_J_apply_modgrp)
        next
          fix x assume x: "x \<in> A" "Klein_J x \<in> T"
          from x(2) obtain y where y: "y \<in> S'" "Klein_J x = Klein_J y"
            by (auto simp: T_def)
          have "Im y > 0"
            using S y by (auto simp: S'_def)
          with x and y have "y \<sim>\<^sub>\<Gamma> x"
            by (subst (asm) Klein_J_eq_iff) (auto simp: A_def modular_group.rel_commutes)
          then obtain f where f: "x = apply_modgrp f y"
            by (auto simp: modular_group.rel_def)
          show "x \<in> (\<Union>f\<in>V'. apply_modgrp f ` S')"
            using f y by (auto intro!: exI[of _ "abs f"] simp: Klein_J_apply_modgrp V'_def)
        qed
      next
        fix X assume X: "X \<in> V"
        have "open (apply_modgrp f ` S')" for f
          using \<open>open S'\<close> S by (intro apply_modgrp_open_map) (auto simp: S'_def)
        thus "openin (top_of_set A) X"
          using \<open>open A\<close> X S by (subst openin_open_eq) (auto simp: V_def S'_def A_def)
      next
        fix X assume X: "X \<in> V"
        then obtain f where f: "X = apply_modgrp f ` S'"
          by (auto simp: V_def)
        have T_eq: "T = Klein_J ` X"
          unfolding f image_image T_def using S
          by (intro image_cong) (auto simp: S'_def Klein_J_apply_modgrp)
        have "X \<subseteq> {z. Im z > 0}"
          using S by (auto simp: f S'_def)
        hence 1: "Klein_J holomorphic_on X"
          by (intro holomorphic_intros) (auto simp: complex_is_Real_iff)
        have 2: "open X"
          using S unfolding f by (intro apply_modgrp_open_map \<open>open S'\<close>) (auto simp: S'_def)
        have 3: "inj_on Klein_J X"
          unfolding inj_on_def f
        proof safe
          fix x y
          assume xy: "x \<in> S'" "y \<in> S'" "Klein_J (apply_modgrp f x) = Klein_J (apply_modgrp f y)"
          from xy have xy': "Im x > 0" "Im y > 0"
            using S by (auto simp: S'_def)
          have "Klein_J x = Klein_J y"
            using xy xy' by (auto simp: Klein_J_apply_modgrp)
          hence "x \<sim>\<^sub>\<Gamma> y"
            using xy' by (subst (asm) Klein_J_eq_iff) auto
          with xy have "x = y"
            using S xy by (auto simp: S'_def)
          thus "apply_modgrp f x = apply_modgrp f y"
            by simp
        qed
        obtain g where g: "g holomorphic_on T" "\<And>w. w \<in> X \<Longrightarrow> g (Klein_J w) = w"
          using holomorphic_has_inverse[OF 1 2 3] unfolding T_eq by metis
        have "homeomorphism X T Klein_J g"
        proof
          show "continuous_on X Klein_J" "continuous_on T g"
            by (intro holomorphic_on_imp_continuous_on 1 g)+
          show "g ` T \<subseteq> X"
            unfolding T_eq by (auto simp: g)
          show "Klein_J ` X \<subseteq> T"
            unfolding f T_eq ..
          show "g (Klein_J x) = x" if "x \<in> X" for x
            using g that by auto
          show "Klein_J (g y) = y" if "y \<in> T" for y
            using that unfolding T_eq by (auto simp: g)
        qed
        thus "\<exists>q. homeomorphism X T Klein_J q" 
          by blast
      qed
    qed
  qed
qed



subsection \<open>Applications\<close>

subsection \<open>The Eisenstein inversion problem\<close>

text \<open>
We now prove Apostol's Theorem~2.9: The Eisenstein inversion problem.

It states that for any numbers $a_2, a_3\in\mathbb{C}$ with $a_2^3 - 27a_3^2\neq 0$ there is
a lattice whose $g_2$ and $g_3$ invariant have exactly the values $a_2$ and $a_3$.

The broader significance of this is that it relates elliptic curves to complex lattices: in our
earlier AFP entry on complex lattices and elliptic functions, we formalised the fact that for any
complex lattice $\Lambda$ with invariants $g_2$ and $g_3$, the map $z \mapsto (\wp(z), \wp'(z))$
is a group isomorphism between the additive group of $\mathbb{C}/\Lambda$ (a complex torus) and
the elliptic curve $y^2 = 4x^3 - g_2 x - g_3$.

The present theorem now shows that the reverse also holds, since for any elliptic curve in
the form $y^2 = 4x^3 - ax - b$ with non-zero discriminant $a^3 - 27b^2$, a lattice can be found
such that $a = g_2$ and $b = g_3$.
\<close>
theorem eisenstein_series_inversion:
  fixes a2 a3 :: complex
  assumes discr: "a2 ^ 3 - 27 * a3 ^ 2 \<noteq> 0"
  obtains \<omega>1 \<omega>2 where
    "Im (\<omega>1 / \<omega>2) \<noteq> 0"
    "complex_lattice.invariant_g2 \<omega>2 \<omega>1 = a2"
    "complex_lattice.invariant_g3 \<omega>2 \<omega>1 = a3"
proof -
  consider "a2 = 0" | "a3 = 0" | "a2 \<noteq> 0" "a3 \<noteq> 0"
    by blast
  thus ?thesis
  proof cases
    assume [simp]: "a2 = 0"
    hence [simp]: "a3 \<noteq> 0"
      using discr by auto
    define \<omega>1 where "\<omega>1 = (140 * Eisenstein_G 6 \<^bold>\<rho> / a3) powr (1 / 6)"
    define \<omega>2 where "\<omega>2 = \<^bold>\<rho> * \<omega>1"
    interpret complex_lattice \<omega>1 \<omega>2
    proof
      show "fundpair (\<omega>1, \<omega>2)"
        unfolding fundpair_def using Eisenstein_G_6_rho_nonzero by (auto simp: \<omega>2_def \<omega>1_def)
    qed
    show ?thesis
    proof (rule that)
      show "Im (\<omega>2 / \<omega>1) \<noteq> 0"
        by (metis complex_is_Real_iff fundpair fundpair_def prod.simps(2))
      show "invariant_g2 = a2"
        unfolding invariant_g2_eq_Eisenstein_G by (simp add: \<omega>2_def \<omega>1_def)
      show "invariant_g3 = a3"
        unfolding invariant_g3_eq_Eisenstein_G using Eisenstein_G_6_rho_nonzero
        by (auto simp: \<omega>2_def \<omega>1_def field_simps powr_power)
    qed
  next
    assume [simp]: "a3 = 0"
    hence [simp]: "a2 \<noteq> 0"
      using discr by auto
    define \<omega>1 where "\<omega>1 = (60 * Eisenstein_G 4 \<i> / a2) powr (1 / 4)"
    define \<omega>2 where "\<omega>2 = \<i> * \<omega>1"
    interpret complex_lattice \<omega>1 \<omega>2
    proof
      show "fundpair (\<omega>1, \<omega>2)"
        unfolding fundpair_def using Eisenstein_G_4_ii_nonzero by (auto simp: \<omega>2_def \<omega>1_def)
    qed
    show ?thesis
    proof (rule that)
      show "Im (\<omega>2 / \<omega>1) \<noteq> 0"
        by (metis complex_is_Real_iff fundpair fundpair_def prod.simps(2))
      show "invariant_g2 = a2"
        unfolding invariant_g2_eq_Eisenstein_G using Eisenstein_G_4_ii_nonzero 
        by (simp add: \<omega>2_def \<omega>1_def field_simps powr_power)
      show "invariant_g3 = a3"
        unfolding invariant_g3_eq_Eisenstein_G by (auto simp: \<omega>2_def \<omega>1_def)
    qed
  next
    assume [simp]: "a2 \<noteq> 0" "a3 \<noteq> 0"
    obtain \<tau> where \<tau>: "\<tau> \<in> \<R>\<^sub>\<Gamma>'" "Klein_J \<tau> = a2 ^ 3 / (a2 ^ 3 - 27 * a3 ^ 2)"
      using surj_Klein_J unfolding bij_betw_def by blast
    have [simp]: "Eisenstein_G 4 \<tau> \<noteq> 0"
      using \<tau> discr unfolding Klein_J_def modular_discr_def by auto
    have [simp]: "Eisenstein_G 6 \<tau> \<noteq> 0"
      using \<tau> unfolding Klein_J_def modular_discr_def by auto
    have "Im \<tau> > 0"
      using \<tau>(1) in_std_fund_region'_iff by blast
    hence [simp]: "\<tau> \<notin> \<real>"
      by (auto simp: complex_is_Real_iff)
    have "Klein_J \<tau> \<noteq> 0"
      using discr unfolding \<tau> by auto
    define \<omega>1 where "\<omega>1 = (140 * a2 * Eisenstein_G 6 \<tau> / (60 * a3 * Eisenstein_G 4 \<tau>)) powr (1/2)"
    define \<omega>2 where "\<omega>2 = \<tau> * \<omega>1"
    have [simp]: "\<omega>2 / \<omega>1 = \<tau>"
      by (simp add: \<omega>2_def \<omega>1_def)

    interpret complex_lattice \<omega>1 \<omega>2
    proof
      show "fundpair (\<omega>1, \<omega>2)"
        unfolding fundpair_def by (auto simp: \<omega>2_def \<omega>1_def)
    qed

    show ?thesis
    proof (rule that)
      show "Im (\<omega>2 / \<omega>1) \<noteq> 0"
        by (metis complex_is_Real_iff fundpair fundpair_def prod.simps(2))
      have *: "invariant_g3 = a3 / a2 * invariant_g2"
        unfolding invariant_g2_eq_Eisenstein_G invariant_g3_eq_Eisenstein_G
        by (auto simp: \<omega>1_def \<omega>2_def powr_power field_simps)
           (auto simp: eval_nat_numeral)?
      from discr_nonzero and * have [simp]: "invariant_g2 \<noteq> 0" "invariant_g3 \<noteq> 0"
        by (auto simp: discr_def)

       have "27 * a3 ^ 2 / a2 ^ 3 = (Klein_J \<tau> - 1) / Klein_J \<tau>"
        unfolding \<tau> using discr by (auto simp: divide_simps eval_nat_numeral)
      also have "(Klein_J \<tau> - 1) / Klein_J \<tau> = 27 * invariant_g3 ^ 2 / invariant_g2 ^ 3"
        using modular_discr_nonzero[of \<tau>]
        unfolding invariant_g2_eq_Eisenstein_G invariant_g3_eq_Eisenstein_G modular_discr_def
        by (auto simp: Klein_J_def modular_discr_def divide_simps)
      also have "\<dots> = 27 * a3 ^ 2 / (a2 ^ 2 * invariant_g2)"
        by (auto simp: * field_simps eval_nat_numeral)
      finally show "invariant_g2 = a2"
        by (simp add: field_simps eval_nat_numeral)
      with * show "invariant_g3 = a3"
        by (simp add: field_simps)
    qed
  qed
qed


subsection \<open>A short proof of Picard's Little Theorem\<close>

text \<open>
  Proving Picard's Little Theorem using our results on Klein's $J$ function is Apostol's
  Theorem~2.10. We already have this result in the library, but we re-prove it here again anyway
  to illustrate how simple the proof is.
\<close>
lemma little_Picard_01_via_Klein_J:
  fixes g :: "complex \<Rightarrow> complex"
  assumes g: "g holomorphic_on UNIV" "g \<in> UNIV \<rightarrow> -{0, 1}"
  shows   "g constant_on UNIV"
proof -
  define A where "A = ({z. Im z > 0} - modular_group.orbit \<^bold>\<rho> - modular_group.orbit \<i>)"
  have 1: "covering_space A Klein_J (-{0, 1})" and 2: "open A"
    using covering_map_Klein_J unfolding A_def by simp_all
  have 3: "Klein_J holomorphic_on A"
    by (intro holomorphic_intros) (auto simp: A_def complex_is_Real_iff)
  have 4: "simply_connected (UNIV :: complex set)" "locally path_connected (UNIV :: complex set)"
     by (auto intro!: convex_imp_simply_connected locally_path_connected_UNIV)
  obtain h where h: "h holomorphic_on UNIV" "range h \<subseteq> A" "\<And>u. Klein_J (h u) = g u"
    using covering_space_lift_holomorphic[OF 1 2 3 g 4]
    by (metis UNIV_I funcset_image)
  have Im_h: "Im (h z) > 0" for z
    using h(2) by (auto simp: A_def)
  have h_nz: "h z \<noteq> 0" for z
    using Im_h[of z] by auto

  define \<phi> where "\<phi> = (\<lambda>z. exp (\<i> * h z))"
  have "\<phi> constant_on UNIV"
  proof (rule Liouville_theorem)
    show "\<phi> holomorphic_on UNIV"
      unfolding \<phi>_def by (intro holomorphic_intros h)
  next
    have "norm (\<phi> z) \<le> 1" for z
      using h(2) by (auto simp: A_def \<phi>_def subset_iff intro!: less_imp_le)
    thus "bounded (range \<phi>)"
      unfolding bounded_iff by blast
  qed
  then obtain c where c: "\<And>z. \<phi> z = c"
    by (auto simp: constant_on_def)
  hence \<phi>_eq: "\<phi> = (\<lambda>_. c)"
    by (auto simp: c)

  have deriv_0: "deriv h z = 0" for z
  proof -
    have "(\<phi> has_field_derivative \<i> * deriv h z * \<phi> z) (at z)"
      by (auto simp: \<phi>_def intro!: derivative_eq_intros holomorphic_derivI[OF h(1)])
    moreover have "(\<phi> has_field_derivative 0) (at z)"
      unfolding \<phi>_eq by (intro derivative_intros)
    ultimately have "\<i> * deriv h z * \<phi> z = 0"
      using DERIV_unique by blast
    thus "deriv h z = 0"
      by (auto simp: \<phi>_def)
  qed

  have "h constant_on UNIV"
  proof (rule has_field_derivative_0_imp_constant_on)
    fix z :: complex
    have "(h has_field_derivative deriv h z) (at z)"
      by (intro holomorphic_derivI[OF h(1)]) auto
    with deriv_0[of z] show "(h has_field_derivative 0) (at z)"
      by simp
  qed auto
  hence "Klein_J \<circ> h constant_on UNIV"
    by (rule constant_on_compose)
  also have "Klein_J \<circ> h = g"
    using h(3) by (auto simp: fun_eq_iff)
  finally show ?thesis .
qed

lemma little_Picard:
  fixes g :: "complex \<Rightarrow> complex"
  assumes g: "g holomorphic_on UNIV" "g \<in> UNIV \<rightarrow> -{a,b}" "a \<noteq> b"
  shows   "g constant_on UNIV"
proof -
  define g' where "g' = (\<lambda>z. (g z - a) / (b - a))"
  have "g' constant_on UNIV"
  proof (rule little_Picard_01_via_Klein_J)
    show "g' holomorphic_on UNIV"
      using g(3) by (auto simp: g'_def intro!: holomorphic_intros g(1))
    show "g' \<in> UNIV \<rightarrow> -{0, 1}"
      using g(2,3) by (auto simp: g'_def)
  qed
  then obtain c where c: "\<And>z. g' z = c"
    by (auto simp: constant_on_def)
  have "g z = c * (b - a) + a" for z
    using c[of z] g(3) by (auto simp: field_simps g'_def)
  thus ?thesis
    by (auto simp: constant_on_def)
qed

end