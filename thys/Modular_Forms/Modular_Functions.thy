section \<open>Level 1 modular functions\<close>
theory Modular_Functions
  imports Meromorphic_Forms_Valence_Formula Basic_Modular_Forms_Mero_UHP
begin

unbundle modgrp_notation

subsection \<open>The weighted multiplicity of a zero/pole \<close>

(* TODO: Move to definition of ellorder_modgrp? *)

definition zorder_modgrp :: "modgrp set \<Rightarrow> mero_uhp \<Rightarrow> complex \<Rightarrow> int" where
  "zorder_modgrp G f z = (if f = 0 then 0 else zorder (eval_mero_uhp f) z div ellorder_modgrp G z)"

abbreviation zorder_modgrp_UNIV :: "mero_uhp \<Rightarrow> complex \<Rightarrow> int" ("(\<open>notation=prefix\<close>zorder[\<Gamma>])") where
  "zorder[\<Gamma>] \<equiv> zorder_modgrp UNIV"

lemma (in meromorphic_form) rel_imp_zorder_modgrp_eq:
  assumes "rel z z'"
  shows   "zorder[\<Gamma>] f z = zorder[\<Gamma>] f z'"
  using assms
  by (auto simp: zorder_modgrp_def
           intro!: arg_cong2[of _ _ _ _ "(div)"] rel_imp_zorder_eq 
                   modular_group.ellorder_modgrp_cong rel_imp_rel)


lemma
  assumes "f \<in> MFuns - {0}"
  shows    MFuns_zorder_rho_multiple_3: "3 dvd zorder f \<^bold>\<rho>"
  and      MFuns_zorder_i_multiple_2:   "2 dvd zorder f \<i>"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define P  Z where "P = poles_mero_uhp f" and "Z = zeros_mero_uhp f"
  define C where "C = (\<Sum>z\<in>Z\<union>P-{\<i>,\<^bold>\<rho>}. zorder f z)"
  have "12 * C + 4 * zorder f \<^bold>\<rho> + 6 * zorder f \<i> + 12 * zorder_at_ii_inf 1 f = 0"
    unfolding C_def using MeForms_valence_formula'[OF assms] by (simp add: P_def Z_def)
  hence *: "6 * C + 2 * zorder f \<^bold>\<rho> + 3 * zorder f \<i> + 6 * zorder_at_ii_inf 1 f = 0" (is "?lhs = 0")
    by simp
  have "3 dvd ?lhs" "2 dvd ?lhs"
    by (subst *; simp; fail)+
  thus "3 dvd zorder f \<^bold>\<rho>" "2 dvd zorder f \<i>"
    by (simp_all add: dvd_add_right_iff dvd_add_left_iff prime_dvd_mult_iff)
qed

lemma MFuns_ellorder_dvd_zorder:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "int (ellorder_modgrp UNIV z) dvd zorder f z"
proof -
  interpret meromorphic_form f 0 UNIV
    using assms by auto
  show ?thesis
    using MFuns_zorder_rho_multiple_3[OF assms(1)] MFuns_zorder_i_multiple_2[OF assms(1)] assms(2)
          rel_imp_zorder_eq by (auto simp: ellorder_modgrp_UNIV_eq)
qed

lemma zorder_conv_zorder_modgrp:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder f z = zorder[\<Gamma>] f z * ellorder_modgrp UNIV z"
  using MFuns_ellorder_dvd_zorder[OF assms] assms unfolding zorder_modgrp_def by auto

lemma zorder_modgrp_nonneg_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] f z \<ge> 0 \<longleftrightarrow> \<not>is_pole f z"
  using assms
  by (auto simp: pos_imp_zdiv_nonneg_iff zorder_modgrp_def 
                 MFuns_ellorder_dvd_zorder modular_group.ellorder_modgrp_pos)

lemma zorder_modgrp_neg_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] f z < 0 \<longleftrightarrow> is_pole f z"
  by (smt (verit, best) assms(1) assms(2) zorder_modgrp_nonneg_iff)

lemma zorder_modgrp_pos_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] f z > 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
  using assms zorder_conv_zorder_modgrp
  by (metis DiffE mult_zero_left less_asym' antisym
        div_0 insertI1 not_le zorder_mero_uhp_eq_0_iff zorder_modgrp_def zorder_modgrp_neg_iff)

lemma zorder_modgrp_nonpos_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] f z \<le> 0 \<longleftrightarrow> is_pole f z \<or> f z \<noteq> 0"
  by (smt (verit) assms(1) assms(2) zorder_modgrp_pos_iff)

lemma zorder_modgrp_eq_0_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] f z = 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z \<noteq> 0"
  by (metis assms nle_le zorder_modgrp_nonneg_iff zorder_modgrp_nonpos_iff)

lemma zorder_modgrp_cmult [simp]:
  assumes "Im z > 0" "c \<noteq> 0"
  shows   "zorder[\<Gamma>] (\<langle>c\<rangle> * f) z = zorder[\<Gamma>] f z"
  using assms by (auto simp add: zorder_modgrp_def)

lemma zorder_modgrp_cmult' [simp]:
  assumes "Im z > 0" "c \<noteq> 0"
  shows   "zorder[\<Gamma>] (f * \<langle>c\<rangle>) z = zorder[\<Gamma>] f z"
  using assms by (auto simp add: zorder_modgrp_def)

lemma zorder_modgrp_uminus [simp]:
  assumes "Im z > 0"
  shows   "zorder[\<Gamma>] (-f) z = zorder[\<Gamma>] f z"
  using assms by (auto simp add: zorder_modgrp_def)

lemma zorder_modgrp_const [simp]:
  assumes "Im z > 0"
  shows   "zorder[\<Gamma>] (const_mero_uhp c) z = 0"
proof (cases "c = 0")
  case False
  thus ?thesis
    using assms by (subst zorder_modgrp_eq_0_iff) auto
qed (auto simp: zorder_modgrp_def)

lemma zorder_modgrp_const' [simp]:
  assumes "Im z > 0" "is_const_mero_uhp f"
  shows   "zorder[\<Gamma>] f z = 0"
  using assms by (auto simp: is_const_mero_uhp_def)

lemma zorder_modgrp_inverse [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (inverse f) z = -zorder[\<Gamma>] f z"
proof -
  from assms have "inverse f \<in> MFuns - {0}"
    by (auto intro!: mform_intros)
  hence "zorder[\<Gamma>] (inverse f) z * ellorder_modgrp UNIV z =
         (-zorder[\<Gamma>] f z) * ellorder_modgrp UNIV z"
    using zorder_inverse_mero_uhp[of f z] assms
    by (simp add: zorder_conv_zorder_modgrp algebra_simps)
  thus ?thesis
    using modular_group.ellorder_modgrp_pos[OF assms(2)]
    by (subst (asm) mult_cancel_right) auto
qed

lemma zorder_modgrp_mult:
  assumes "f \<in> MFuns - {0}" "g \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (f * g) z = zorder[\<Gamma>] f z + zorder[\<Gamma>] g z"
proof -
  from assms have "f * g \<in> MFuns - {0}"
    by (auto intro!: mform_intros)
  hence "zorder[\<Gamma>] (f * g) z * ellorder_modgrp UNIV z =
         (zorder[\<Gamma>] f z + zorder[\<Gamma>] g z) * ellorder_modgrp UNIV z"
    using zorder_mult_mero_uhp[of f g z] assms
    by (simp add: zorder_conv_zorder_modgrp algebra_simps)
  thus ?thesis
    using modular_group.ellorder_modgrp_pos[OF assms(3)] by simp
qed

lemma zorder_modgrp_divide:
  assumes "f \<in> MFuns - {0}" "g \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (f / g) z = zorder[\<Gamma>] f z - zorder[\<Gamma>] g z"
proof -
  have "zorder[\<Gamma>] (f * inverse g) z = zorder[\<Gamma>] f z - zorder[\<Gamma>] g z"
    using assms by (subst zorder_modgrp_mult) (auto intro: mform_intros)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma zorder_modgrp_power_int [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (f powi n) z = n * zorder[\<Gamma>] f z"
proof -
  have "zorder (f powi n) z = n * zorder f z"
    using assms by (intro zorder_power_int_mero_uhp) auto
  thus ?thesis using assms modular_group.ellorder_modgrp_pos[of z]
    by (subst (asm) (1 2) zorder_conv_zorder_modgrp)
       (auto simp: zorder_conv_zorder_modgrp algebra_simps intro: mform_intros)
qed

lemma zorder_modgrp_power [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (f ^ n) z = n * zorder[\<Gamma>] f z"
  using zorder_modgrp_power_int[OF assms, of "int n"] by (simp del: zorder_modgrp_power_int)

lemma zorder_modgrp_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder[\<Gamma>] (\<Prod>x\<in>A. f x) z = (\<Sum>x\<in>A. zorder[\<Gamma>] (f x) z)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  have "zorder[\<Gamma>] (f x * prod f A) z = zorder[\<Gamma>] (f x) z + (\<Sum>x\<in>A. zorder[\<Gamma>] (f x) z)"
    using insert by (subst zorder_modgrp_mult) (auto intro!: mform_intros)
  thus ?case
    using insert.hyps by simp
qed auto

lemma MFuns_valence_formula:
  assumes "f \<in> MFuns - {0}"
  defines "Z \<equiv> zeros_mero_uhp f \<union> poles_mero_uhp f"
  shows   "(\<Sum>z\<in>Z. zorder[\<Gamma>] f z) + zorder_at_ii_inf 1 f = 0"
proof -
  interpret modular_function f UNIV
    using assms by auto
  define Z' where "Z' = Z - {\<^bold>\<rho>, \<i>}"
  have [intro]: "finite Z"
    unfolding Z_def using assms by auto

  have "(\<Sum>z\<in>Z. zorder[\<Gamma>] f z) = (\<Sum>z\<in>Z' \<union> {\<^bold>\<rho>, \<i>}. zorder[\<Gamma>] f z)"
  proof (intro sum.mono_neutral_left ballI)
    show "zorder[\<Gamma>] f z = 0" if "z \<in> Z' \<union> {\<^bold>\<rho>, \<i>} - Z" for z
    proof -
      from that have z: "z \<in> {\<^bold>\<rho>, \<i>}" "\<not>is_pole f z" "f z \<noteq> 0"
        by (auto simp: Z_def Z'_def inv_image_mero_uhp_def poles_mero_uhp_def)
      hence "zorder f z = 0"
        by (subst zorder_mero_uhp_eq_0_iff) auto
      thus ?thesis
        by (simp add: zorder_modgrp_def)
    qed
  qed (auto simp: Z'_def)
  also have "12 * \<dots> + 12 * zorder_at_ii_inf 1 f = 
               12 * (\<Sum>z\<in>Z'. zorder[\<Gamma>] f z) + 12 * zorder[\<Gamma>] f \<^bold>\<rho> + 12 * zorder[\<Gamma>] f \<i> +
               12 * zorder_at_ii_inf 1 f"
    by (subst sum.union_disjoint) (auto simp: Z'_def)
  also have "(\<Sum>z\<in>Z'. zorder[\<Gamma>] f z) = (\<Sum>z\<in>Z'. zorder f z)"
  proof (intro sum.cong refl)
    fix z assume "z \<in> Z'"
    hence z: "z \<in> \<R>\<^sub>\<Gamma>'" "z \<noteq> \<^bold>\<rho>" "z \<noteq> \<i>"
      by (auto simp: Z'_def Z_def inv_image_mero_uhp_def poles_mero_uhp_def)
    show "zorder[\<Gamma>] f z = zorder f z"
      using assms z by (simp add: zorder_modgrp_def ellorder_modgrp_UNIV_eq_1_std_fund_region')
  qed
  also have "zorder[\<Gamma>] f \<^bold>\<rho> = zorder f \<^bold>\<rho> div 3"
    using assms by (simp add: zorder_modgrp_def)
  also have "12 * \<dots> = 4 * zorder f \<^bold>\<rho>"
    using MFuns_ellorder_dvd_zorder[OF assms(1), of "\<^bold>\<rho>"] by auto
  also have "zorder[\<Gamma>] f \<i> = zorder f \<i> div 2"
    using assms by (simp add: zorder_modgrp_def)
  also have "12 * \<dots> = 6 * zorder f \<i>"
    using MFuns_ellorder_dvd_zorder[OF assms(1), of "\<i>"] by auto
  also have "12 * sum (zorder_mero_uhp f) Z' + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> +
               12 * zorder_at_ii_inf 1 f = 0"
    using MeForms_valence_formula'[OF assms(1)] by (simp add: Z'_def Z_def insert_commute)
  finally show ?thesis by simp
qed



subsection \<open>Degree\<close>

definition degree_modfun :: "mero_uhp \<Rightarrow> nat" where
  "degree_modfun f =
     (if is_const_mero_uhp f then 0
      else (\<Sum>z\<in>zeros_mero_uhp f. nat (zorder[\<Gamma>] f z)) + nat (zorder_at_ii_inf 1 f))"

lemma degree_modfun_is_const [simp]: "is_const_mero_uhp f \<Longrightarrow> degree_modfun f = 0"
  by (simp add: degree_modfun_def)

text \<open>
  The following two statements show that the number of zeros of a modular function is the same
  as the number of poles of a modular function, with all the usual conventions about counting
  zeros and poles of modular functions.
\<close>
lemma int_degree_modfun_conv_zeros:
  assumes "f \<in> MFuns"
  shows "int (degree_modfun f) = (\<Sum>z\<in>zeros_mero_uhp f. zorder[\<Gamma>] f z) + max 0 (zorder_at_ii_inf 1 f)"
proof (cases "is_const_mero_uhp f")
  case False
  hence "f \<noteq> 0"
    by auto
  have "int (degree_modfun f) =
          (\<Sum>z\<in>zeros_mero_uhp f. max 0 (zorder[\<Gamma>] f z)) + max 0 (zorder_at_ii_inf 1 f)"
    using assms False by (auto simp: degree_modfun_def max_def)
  also have "(\<Sum>z\<in>zeros_mero_uhp f. max 0 (zorder[\<Gamma>] f z)) = (\<Sum>z\<in>zeros_mero_uhp f. zorder[\<Gamma>] f z)"
    using \<open>f \<noteq> 0\<close> assms
    by (intro sum.cong refl) (auto simp: max_def inv_image_mero_uhp_def in_std_fund_region'_iff)
  finally show ?thesis .
next
  case True
  show ?thesis
  proof (cases "f = 0")
    case True
    thus ?thesis by (simp add: zorder_modgrp_def)
  next
    case False
    with True obtain c where [simp]: "f = const_mero_uhp c" "c \<noteq> 0"
      by (auto simp: is_const_mero_uhp_def)
    interpret modular_form "const_mero_uhp c" 0 UNIV
      using assms by (auto intro: modular_group.modular_form_const)
    have [simp]: "zeros_mero_uhp \<langle>c\<rangle> = {}"
      by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    show ?thesis
      by (auto simp add: degree_modfun_def)
  qed
qed

lemma int_degree_modfun_conv_poles:
  assumes "f \<in> MFuns"
  shows "int (degree_modfun f) = (\<Sum>z\<in>poles_mero_uhp f. -zorder[\<Gamma>] f z) - min 0 (zorder_at_ii_inf 1 f)"
proof (cases "f = 0")
  case False
  hence *: "f \<in> MFuns - {0}"
    using assms by auto
  interpret modular_function f UNIV
    using * by auto
  define Z P where "Z = zeros_mero_uhp f" and "P = poles_mero_uhp f"
  have disj: "Z \<inter> P = {}"
    by (auto simp: Z_def P_def inv_image_mero_uhp_def poles_mero_uhp_def)
  have "0 = sum (zorder[\<Gamma>] f) (Z \<union> P) + zorder_at_ii_inf 1 f"
    using MFuns_valence_formula[OF *] unfolding Z_def P_def ..
  also have "\<dots> = sum (zorder[\<Gamma>] f) Z + max 0 (zorder_at_ii_inf 1 f) + 
                  sum (zorder[\<Gamma>] f) P + min 0 (zorder_at_ii_inf 1 f)"
    using * disj by (subst sum.union_disjoint) (auto simp: Z_def P_def)
  also have "sum (zorder[\<Gamma>] f) Z + max 0 (zorder_at_ii_inf 1 f) = degree_modfun f"
    using * by (subst int_degree_modfun_conv_zeros) (auto simp: Z_def)
  finally show ?thesis
    unfolding P_def by (simp add: algebra_simps sum_negf)
qed auto

lemma abs_zorder_modgrp_le_degree_modfun:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "\<bar>zorder[\<Gamma>] f z\<bar> \<le> degree_modfun f"
proof -
  interpret modular_function f UNIV
    using assms by auto
  have [dest]: "Im z > 0" if "z \<in> \<R>\<^sub>\<Gamma>'" for z
    using that by (auto simp: in_std_fund_region'_iff)
  obtain z' where z': "z' \<in> \<R>\<^sub>\<Gamma>'" "z' \<sim>\<^sub>\<Gamma> z"
    by (meson assms(2) canonical_point_in_std_fund_region' modular_group.rel_sym)
  have z'': "Im z' > 0"
    using z' by (auto simp: in_std_fund_region'_iff)
  have "\<bar>zorder[\<Gamma>] f z'\<bar> \<le> degree_modfun f"
  proof (cases "zorder[\<Gamma>] f z'" "0 :: int" rule: linorder_cases)
    case greater
    hence "z' \<in> zeros_mero_uhp f"
      using z' z'' assms by (simp add: inv_image_mero_uhp_def)
    hence "(\<Sum>w\<in>{z'}. zorder[\<Gamma>] f w) \<le> (\<Sum>w\<in>zeros_mero_uhp f. zorder[\<Gamma>] f w)"
      by (intro sum_mono2 finite_inv_image_mero_uhp)
         (use assms in \<open>auto simp: inv_image_mero_uhp_def\<close>)
    also have "\<dots> \<le> int (degree_modfun f)"
      using assms by (simp add: int_degree_modfun_conv_zeros) 
    finally show ?thesis
      using greater by simp
  next
    case less
    hence "z' \<in> poles_mero_uhp f"
      using z' z'' assms by (simp add: poles_mero_uhp_def)
    hence "(\<Sum>w\<in>{z'}. -zorder[\<Gamma>] f w) \<le> (\<Sum>w\<in>poles_mero_uhp f. -zorder[\<Gamma>] f w)"
      by (intro sum_mono2 finite_poles_mero_uhp)
         (use assms in \<open>auto simp: poles_mero_uhp_def\<close>)
    also have "\<dots> \<le> int (degree_modfun f)"
      using assms by (simp add: int_degree_modfun_conv_poles) 
    finally show ?thesis
      using less by simp
  qed auto
  also have "zorder[\<Gamma>] f z' = zorder[\<Gamma>] f z"
    using z' rel_imp_zorder_modgrp_eq by blast
  finally show ?thesis .
qed  

lemma abs_zorder_at_ii_inf_le_degree_modfun:
  assumes "f \<in> MFuns - {0}"
  shows   "\<bar>zorder_at_ii_inf 1 f\<bar> \<le> degree_modfun f"
proof (cases "zorder_at_ii_inf 1 f" "0 :: int" rule: linorder_cases)
  case greater
  have "sum (zorder[\<Gamma>] f) (zeros_mero_uhp f) \<ge> 0"
    using assms by (intro sum_nonneg) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  thus ?thesis using greater assms
    by (simp add: int_degree_modfun_conv_zeros)
next
  case less
  have "sum (\<lambda>z. -zorder[\<Gamma>] f z) (poles_mero_uhp f) \<ge> 0"
    using assms by (intro sum_nonneg) (auto simp: poles_mero_uhp_def in_std_fund_region'_iff)
  thus ?thesis using less assms
    by (simp add: int_degree_modfun_conv_poles)
qed auto

(* FIXME Manuel: This was much more painful than it should be. *)
text \<open>
  Together with this, the previous two results directly imply Apostol's Theorem~2.5:
  If $f(z)$ is a non-constant modular function, then for any constant $c$, the modular function 
  $f(z) + c$ has the same degree as the modular function $f(z)$. Therefore, the number of zeros of
  $f(z) - c$ is the same as the number of zeros in $f(z)$.

  In other words: $f(z)$ takes every value $z\in\mathbb{C}$ equally (and finitely) often --
  and that number is its degree.
\<close>
lemma degree_modfun_plus_const_eq:
  assumes f: "f \<in> MFuns"
  shows "degree_modfun (f + const_mero_uhp c) = degree_modfun f"
proof (cases "is_const_mero_uhp f")
  case True
  thus ?thesis
    by (subst (1 2) degree_modfun_is_const) auto
next
  case not_const: False
  from not_const have [simp]: "f \<noteq> 0"
    by auto
  from not_const have "f + \<langle>c\<rangle> \<noteq> 0"
    by (metis add.commute add_diff_cancel_left' const_mero_uhp.hom_minus
          is_const_mero_uhp_const_mero_uhp zero_mero_uhp_def)
  interpret modular_function f UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    using assms by auto
  interpret ctxt: fourier_expansion_context "Suc 0" by standard auto
  interpret pair: fourier_expansion_meromorphic_pair "Suc 0" f "\<langle>c\<rangle>" ..
  interpret add: modular_function "f + \<langle>c\<rangle>" UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    using assms by auto

  define fq where "fq = fourier_expansion (Suc 0) f"
  let ?f' = "f + const_mero_uhp c"
  have "int (degree_modfun ?f') =
          (\<Sum>z\<in>poles_mero_uhp ?f'. -zorder[\<Gamma>] ?f' z) - min 0 (zorder_at_ii_inf 1 ?f')"
    by (intro int_degree_modfun_conv_poles mform_intros assms) auto
  also have "(\<Sum>z\<in>poles_mero_uhp ?f'. -zorder[\<Gamma>] ?f' z) =
             (\<Sum>z\<in>poles_mero_uhp f. -zorder[\<Gamma>] f z)"
  proof (rule sum.cong, goal_cases)
    case 1
    have "is_pole (eval_mero_uhp (f + \<langle>c\<rangle>)) z \<longleftrightarrow> is_pole (eval_mero_uhp f) z" if z: "z \<in> \<R>\<^sub>\<Gamma>'" for z
      by (intro is_pole_plus_analytic_mero_uhp_iff1) auto
    thus "poles_mero_uhp (f + \<langle>c\<rangle>) = poles_mero_uhp f"
      by (auto simp: zorder_mero_uhp_add1 poles_mero_uhp_def)
  next
    case (2 z)
    hence z: "Im z > 0" and [simp]: "f \<noteq> 0"
      by (auto simp: poles_mero_uhp_def in_std_fund_region'_iff)
    have "zorder (f + \<langle>c\<rangle>) z = zorder f z"
    proof (cases "c = 0")
      case [simp]: False
      show ?thesis
        using 2 z by (subst zorder_mero_uhp_add1) (auto simp: poles_mero_uhp_def)
    qed auto
    moreover have "f + \<langle>c\<rangle> \<noteq> 0"
      by fact
    ultimately show ?case
      by (simp add: zorder_modgrp_def)
  qed
  also have "min 0 (zorder_at_ii_inf 1 ?f') = min 0 (zorder_at_ii_inf 1 f)"
  proof (cases "zorder_at_ii_inf 1 f \<ge> 0")
    case True
    have freq: "\<exists>\<^sub>F z in at 0. fq z + c \<noteq> 0"
      using eventually_neq_fourier[of "-c" 0] \<open>f + \<langle>c\<rangle> \<noteq> 0\<close>
      by (intro eventually_frequently) (auto simp: add_eq_0_iff2 hom_distribs fq_def)

    from True have "zorder fq 0 \<ge> 0"
      using zorder_at_ii_inf_conv_fourier by (simp add: not_le fq_def)
    hence not_pole: "\<not>is_pole fq 0"
      by (simp add: fq_def)
    hence "\<not>is_pole (\<lambda>q. fq q + c) 0"
      by (subst is_pole_plus_analytic_iff1) auto
    hence "0 \<le> zorder (\<lambda>q. fq q + c) 0"
      using not_pole freq unfolding fq_def  by (intro zorder_ge_0 analytic_intros) auto
    also have "\<dots> = zorder (fourier_expansion (Suc 0) (f + \<langle>c\<rangle>)) 0"
    proof (intro zorder_cong)
      have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at 0)"
        by (intro eventually_at_in_open') auto
      moreover have "eventually (\<lambda>q. fourier_expansion (Suc 0) (f + \<langle>c\<rangle>) q = fq q + fourier_expansion (Suc 0) \<langle>c\<rangle> q) (at 0)"
        unfolding fq_def
        using eventually_cosparse_imp_eventually_at[OF pair.fourier_add_eventually_eq, of 0 UNIV]
        by auto
      ultimately show "eventually (\<lambda>q. fq q + c = fourier_expansion (Suc 0) (f + \<langle>c\<rangle>) q) (at 0)"
        by eventually_elim auto
    qed auto
    also have "\<dots> = zorder_at_ii_inf 1 (f + \<langle>c\<rangle>)"
      using pair.add.zorder_at_ii_inf_conv_fourier \<open>f + \<langle>c\<rangle> \<noteq> 0\<close> by simp
    finally show ?thesis
      using True by simp
  next
    case False
    have "eventually (\<lambda>q. fourier_expansion (Suc 0) (f + \<langle>c\<rangle>) q = 
            fq q + fourier_expansion (Suc 0) \<langle>c\<rangle> q) (at 0)"
      unfolding fq_def
      by (intro eventually_cosparse_imp_eventually_at[OF pair.fourier_add_eventually_eq]) auto
    moreover have "eventually (\<lambda>q. q \<in> ball 0 1) (at (0 :: complex))"
      by (rule eventually_at_in_open') auto
    ultimately have ev: "eventually (\<lambda>q. fourier_expansion (Suc 0) (f + \<langle>c\<rangle>) q = fq q + c) (at 0)"
      by eventually_elim auto

    from False have "zorder fq 0 < 0"
      using zorder_at_ii_inf_conv_fourier by (simp add: not_le fq_def)
    hence "is_pole fq 0"
      by (simp add: fq_def)
    hence "is_pole (\<lambda>q. fq q + c) 0"
      by (subst is_pole_plus_const_iff [symmetric])
    hence "zorder (\<lambda>q. fq q + c) 0 = zorder fq 0"
    proof (cases "c = 0")
      case [simp]: False
      show ?thesis using eventually_neq_fourier[of 0 0] \<open>is_pole fq 0\<close> unfolding fq_def
        by (intro zorder_add1 meromorphic_intros eventually_frequently) auto
    qed auto
    also have "zorder (\<lambda>q. fq q + c) 0 = zorder (fourier_expansion (Suc 0) (f + \<langle>c\<rangle>)) 0"
      by (intro zorder_cong) (use ev in \<open>simp_all add: eq_commute\<close>)
    also have "\<dots> = zorder_at_ii_inf 1 (f + \<langle>c\<rangle>)"
      using pair.add.zorder_at_ii_inf_conv_fourier \<open>f + \<langle>c\<rangle> \<noteq> 0\<close> by simp
    finally show ?thesis
      using zorder_at_ii_inf_conv_fourier by (simp add: fq_def)
  qed
  also have "(\<Sum>z\<in>poles_mero_uhp f. - zorder[\<Gamma>] f z) - min 0 (zorder_at_ii_inf 1 f) =
             int (degree_modfun f)"
    by (intro int_degree_modfun_conv_poles[symmetric] assms)
  finally show ?thesis
    by simp
qed

lemma WMForms_nonpole_exists:
  assumes "f \<in> WMForms[k]"
  obtains z where "Im z > 0" "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z"
proof -
  interpret weakly_meromorphic_form f k UNIV
    using assms by auto
  have "eventually (\<lambda>z. \<not>is_pole f z) (cosparse {z. Im z > 0})"
    by (simp add: eval_mero_uhp_meromorphic meromorphic_on_imp_not_pole_cosparse)
  hence ev: "eventually (\<lambda>z. z \<in> {z. Im z > 0} \<and> \<not>is_pole f z) (cosparse {z. Im z > 0})"
    by (intro eventually_conj eventually_in_cosparse open_halfspace_Im_gt order.refl)
  moreover have "\<exists>z. Im z > 0"
    by (intro exI[of _ \<i>]) auto
  ultimately obtain z where z: "Im z > 0" "\<not>is_pole f z"
    using eventually_happens[OF ev] by auto
  then obtain z' where z': "z' \<sim>\<^sub>\<Gamma> z" "z' \<in> \<R>\<^sub>\<Gamma>'"
    by (meson canonical_point_in_std_fund_region' modular_group.rel_sym)
  show ?thesis
    using z z' that[of z'] rel_imp_is_pole_iff[OF z'(1)] by auto
qed

text \<open>
  The only modular functions of degree 0 are the constant functions.
\<close>
theorem degree_modfun_eq_0_iff:
  assumes f: "f \<in> MFuns"
  shows   "degree_modfun f = 0 \<longleftrightarrow> is_const_mero_uhp f"
proof
  assume "degree_modfun f = 0"
  from assms interpret modular_function f UNIV
    by auto

  have "f \<in> WMForms[0]"
    using f by (simp add: WMForms_def weakly_meromorphic_form_axioms)
  then obtain z where z: "Im z > 0" "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z"
    using WMForms_nonpole_exists[of f 0] by blast

  show "is_const_mero_uhp f"
  proof (rule ccontr)
    assume not_const: "\<not>is_const_mero_uhp f"
    define c where "c = -f z"
    define g where "g = f + \<langle>c\<rangle>"
    have "g \<noteq> 0"
      using not_const by (auto simp: g_def add_eq_0_iff2)
    hence g: "g \<in> MFuns - {0}"
      using f by (auto simp: g_def intro: mform_intros)
    interpret g: modular_function g UNIV
      using g by auto

    have "0 < sum (zorder[\<Gamma>] g) (zeros_mero_uhp g)"
    proof (rule sum_pos)
      have "mero_uhp_rel g (\<lambda>z. f z + c)"
        unfolding g_def by mero_uhp_rel
      hence "is_pole g z \<longleftrightarrow> is_pole (\<lambda>z. f z + c) z"
        using z by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt mero_uhp_rel_def)
      hence "\<not>is_pole g z"
        using z by (subst (asm) is_pole_plus_const_iff[symmetric]) auto
      with z have "z \<in> zeros_mero_uhp g"
        by (auto simp: inv_image_mero_uhp_def g_def c_def)
      thus "zeros_mero_uhp g \<noteq> {}"
        by auto
    next
      show "zorder[\<Gamma>] g z > 0" if "z \<in> zeros_mero_uhp g" for z
        using that g unfolding inv_image_mero_uhp_def
        by (auto simp: in_std_fund_region'_iff)
    qed (use g in auto)
    also have "\<dots> \<le> int (degree_modfun g)"
      using g by (subst int_degree_modfun_conv_zeros) auto
    also have "degree_modfun g = degree_modfun f"
      using f unfolding g_def by (subst degree_modfun_plus_const_eq) auto
    finally show False
      using \<open>degree_modfun f = 0\<close> by simp
  qed
qed auto

lemma degree_modfun_pos_iff:
  assumes f: "f \<in> MFuns"
  shows   "degree_modfun f > 0 \<longleftrightarrow> \<not>is_const_mero_uhp f"
  using degree_modfun_eq_0_iff[OF f] by auto


subsection \<open>Range\<close>

text \<open>
  We define the \<^emph>\<open>range\<close> of a meromorphic function on the upper half plane to be the
  set of all the values it takes in the upper half plane (minus the places where it has poles)
  or at the cusp $i\infty$ (if there is one).
\<close>
(* TODO Manuel: This will have to be generalised a bit for functions with more than one cusp *)
definition range_mero_uhp :: "mero_uhp \<Rightarrow> complex set" where
  "range_mero_uhp f = f ` {z\<in>\<H>. \<not>is_pole f z} \<union> {L. (f \<longlongrightarrow> L) at_\<i>\<infinity>}"

lemma range_mero_uhpI1:
  assumes "eval_mero_uhp f z = y" "Im z > 0" "\<not>is_pole f z"
  shows   "y \<in> range_mero_uhp f"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhpI2:
  assumes "(eval_mero_uhp f \<longlongrightarrow> y) at_\<i>\<infinity>"
  shows   "y \<in> range_mero_uhp f"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhpE:
  assumes "y \<in> range_mero_uhp f"
  obtains z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhp_altdef1:
  assumes "f \<in> MeForms[G, k]"
  defines "n \<equiv> cusp_width\<^sub>\<infinity> G"
  defines "F \<equiv> fourier_expansion n f"
  shows   "range_mero_uhp f = F ` {z\<in>ball 0 1. \<not>is_pole F z}"
proof -
  interpret meromorphic_form f k G
    using assms by auto
  show ?thesis
  proof (intro equalityI subsetI; (elim imageE)?)
    fix y
    assume "y \<in> range_mero_uhp f"
    then consider z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
      by (elim range_mero_uhpE)
    thus "y \<in> F ` {z\<in>ball 0 1. \<not>is_pole F z}"
    proof cases
      case 1
      hence "F (to_q n z) \<in> F ` {z\<in>ball 0 1. \<not>is_pole F z}"
        using period_pos by (intro imageI) (auto simp: n_def F_def fourier_is_pole_to_q_iff)
      thus ?thesis
        using 1 by (simp add: n_def F_def)
    next
      case 2
      hence "F 0 = y \<and> \<not>is_pole F 0"
        unfolding F_def n_def using not_tendsto_and_filterlim_at_infinity[of "at_\<i>\<infinity>" f y]
        by (auto simp: fourier_0_aux fourier_is_pole_0_iff)
      thus ?thesis
        by auto
    qed
  next
    fix y q assume q: "q \<in> {z\<in>ball 0 1. \<not>is_pole F z}" "y = F q"
    show "y \<in> range_mero_uhp f"
    proof (cases "q = 0")
      case True
      hence "(eval_mero_uhp f \<longlongrightarrow> F 0) at_\<i>\<infinity>"
        using q assms(3) fourier_nicely_meromorphic fourier_tendsto_0_iff n_def nicely_meromorphic_on_def by auto
      thus ?thesis using q True
        by (auto simp: range_mero_uhp_def)
    next
      case False
      define z where "z = of_q n q"
      have q_eq: "q = to_q n z" and z: "Im z > 0"
        using False assms q period_pos
        by (auto simp: z_def n_def intro!: Im_of_q_gt)
      have z': "fourier_expansion (cusp_width\<^sub>\<infinity> G) f q = f z \<and> \<not>is_pole f z"
        using z q by (simp add: q_eq n_def F_def fourier_is_pole_to_q_iff)
      have "f z \<in> eval_mero_uhp f ` {z. 0 < Im z \<and> \<not> is_pole (eval_mero_uhp f) z}"
        by (intro imageI) (use z z' in auto)
      also have "f z = y"
        using z' q by (auto simp: F_def n_def)
      finally show ?thesis
        by (simp add: range_mero_uhp_def)
    qed
  qed
qed

lemma range_mero_uhp_altdef2:
  assumes "f \<in> MFuns"
  defines "P \<equiv> (if f \<noteq> 0 \<and> zorder_at_ii_inf (Suc 0) f \<ge> 0 then {eval_mero_uhp_at_ii_inf f} else {})"
  shows   "range_mero_uhp f = f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
proof -
  interpret modular_function f UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    using assms(1) by auto
  define fq where "fq = fourier_expansion (Suc 0) f"
  show ?thesis
  proof (intro equalityI subsetI; (elim imageE)?)
    fix y
    assume "y \<in> range_mero_uhp f"
    then consider z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_\<i>\<infinity>"
      by (elim range_mero_uhpE)
    thus "y \<in> f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
    proof cases
      case 1
      then obtain z' where z': "z' \<sim>\<^sub>\<Gamma> z" "z' \<in> \<R>\<^sub>\<Gamma>'"
        by (metis canonical_point_in_std_fund_region' mem_Collect_eq modular_group.rel_sym)
      from z' have "f z' = f z"
        by (meson rel_imp_eval_eq)
      moreover from z' 1 have "\<not>is_pole f z'"
        using rel_imp_is_pole_iff by blast
      ultimately show ?thesis using z'
        using 1 by (auto simp: poles_mero_uhp_def)
    next
      case 2
      show ?thesis
      proof (cases "f = 0")
        case [simp]: False
        from 2 have "\<not>filterlim f at_infinity at_\<i>\<infinity>"
          using not_tendsto_and_filterlim_at_infinity[of "at_\<i>\<infinity>" f y] by auto
        hence "\<not>is_pole fq 0" unfolding fq_def
          by (subst fourier_is_pole_0_iff)
        hence "zorder fq 0 \<ge> 0" unfolding fq_def
          by (subst zorder_fourier_nonneg_iff) auto
        hence "zorder_at_ii_inf (Suc 0) f \<ge> 0" unfolding fq_def
          by (subst zorder_at_ii_inf_conv_fourier) auto
        hence "y \<in> P"
          unfolding P_def using 2 
          by (auto simp: zorder_at_ii_inf_conv_fourier fourier_0_aux fq_def
                         fourier_0_aux eval_at_ii_inf_conv_fourier)
        thus ?thesis
          by blast
      next
        case True
        have "\<i> \<in> \<R>\<^sub>\<Gamma>'"
          by auto
        from True and 2 have "((\<lambda>_. 0) \<longlongrightarrow> y) at_\<i>\<infinity>"
          by simp
        hence [simp]: "y = 0"
          using True fourier_0_aux by auto
        show ?thesis using True 2 by (auto simp: P_def)
      qed
    qed
  next
    fix y assume "y \<in> eval_mero_uhp f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
    thus "y \<in> range_mero_uhp f"
    proof
      assume y: "y \<in> eval_mero_uhp f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)"
      thus ?thesis
        by (auto simp: range_mero_uhp_def in_std_fund_region'_iff poles_mero_uhp_def intro!: imageI)
    next
      assume "y \<in> P"
      hence "zorder_at_ii_inf (Suc 0) f \<ge> 0" and [simp]: "f \<noteq> 0" "y = fq 0" unfolding fq_def
        by (auto simp: P_def fq_def eval_at_ii_inf_conv_fourier split: if_splits)
      from this(1) have "zorder fq 0 \<ge> 0" unfolding fq_def
        by (subst (asm) zorder_at_ii_inf_conv_fourier) auto
      hence "\<not>is_pole fq 0" unfolding fq_def
        by (subst (asm) zorder_fourier_nonneg_iff) auto
      hence "(fq \<longlongrightarrow> fq 0) (at 0)" unfolding fq_def
        by (intro tendsto_intros) auto
      hence "(eval_mero_uhp f \<longlongrightarrow> fq 0) at_\<i>\<infinity>" unfolding fq_def
        by (subst (asm) fourier_tendsto_0_iff)
      thus "y \<in> range_mero_uhp f"
        by (auto simp: P_def range_mero_uhp_def split: if_splits)
    qed
  qed
qed


subsection \<open>Surjectivity and injectivity\<close>

text \<open>
  A non-constant meromorphic form w.r.t.\ the full modular group is always surjective.
\<close>
lemma MFuns_surj_obtain:
  assumes f: "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  obtains z where
    "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z" "f z = c"
  | "zorder_at_ii_inf 1 f \<ge> 0" "eval_mero_uhp_at_ii_inf f = c"
proof -
  from assms have [simp]: "f \<noteq> 0"
    by auto
  interpret modular_function f UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    using f by auto
  define fq where "fq = fourier_expansion (Suc 0) f"

  define g where "g = f + \<langle>-c\<rangle>"
  have "\<not>is_const_mero_uhp g"
    unfolding g_def using assms(2)
    by (metis add.commute add_minus_cancel const_mero_uhp.hom_uminus
        is_const_mero_uhp_add is_const_mero_uhp_const_mero_uhp)
  hence g: "g \<in> MFuns" "\<not>is_const_mero_uhp g"  
    using assms by (auto simp: g_def intro: mform_intros)
  interpret g: modular_function g UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    unfolding g_def by (intro modular_function_add modular_function_axioms) auto
  interpret ctxt: fourier_expansion_context "Suc 0" by standard auto
  interpret pair: fourier_expansion_meromorphic_pair "Suc 0" f "\<langle>-c\<rangle>" ..
  define gq where "gq = fourier_expansion (Suc 0) g"

  have "0 < int (degree_modfun g)"
    using g degree_modfun_pos_iff[of g] by auto
  also have "\<dots> = sum (zorder[\<Gamma>] g) (zeros_mero_uhp g) + max 0 (zorder_at_ii_inf 1 g)"
    using g by (subst int_degree_modfun_conv_zeros) auto
  finally have "zeros_mero_uhp g \<noteq> {} \<or> zorder_at_ii_inf 1 g > 0"
    by auto
  thus ?thesis
  proof
    assume "zeros_mero_uhp g \<noteq> {}"
    then obtain z' where z': "z' \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole g z'" "g z' = 0"
      by (auto simp: inv_image_mero_uhp_def)
    note z'(2)
    also have "mero_uhp_rel g (\<lambda>w. f w + (-c))"
      unfolding g_def by mero_uhp_rel
    hence "is_pole g z' \<longleftrightarrow> is_pole (\<lambda>w. f w + (-c)) z'" using z'
      by (intro is_pole_cong) 
         (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt 
                     in_std_fund_region'_iff mero_uhp_rel_def)
    also have "\<dots> \<longleftrightarrow> is_pole f z'"
      by (subst is_pole_plus_const_iff [symmetric]) auto
    finally have "\<not>is_pole f z'" .
    moreover from this have "f z' = c"
      using z' by (auto simp: g_def in_std_fund_region'_iff)
    ultimately show ?thesis
      using that(1)[of z'] z' by blast
  next
    assume *: "zorder_at_ii_inf 1 g > 0"
    from f have [simp]: "f + \<langle>- c\<rangle> \<noteq> 0"
      by (auto simp: add_eq_0_iff2)
    from * have "zorder gq 0 > 0"
      using g.zorder_at_ii_inf_conv_fourier by (simp add: g_def gq_def)
    hence "\<not>is_pole gq 0" unfolding gq_def
      by (metis const_mero_uhp.hom_zero g.not_pole_eval_fourier_outside
                g.zorder_fourier_pos_iff linorder_not_less ctxt.not_is_pole_const_fourier)
    also have "is_pole gq 0 \<longleftrightarrow> is_pole (\<lambda>q. fq q - c) 0"
    proof (rule is_pole_cong)
      have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at 0)"
        by (rule eventually_at_in_open') auto
      moreover have "eventually (\<lambda>q. gq q = fq q + fourier_expansion (Suc 0) \<langle>-c\<rangle> q) (at 0)"
        using eventually_cosparse_imp_eventually_at[OF pair.fourier_add_eventually_eq, of 0 UNIV]
        by (simp add: gq_def fq_def g_def)
      ultimately show "eventually (\<lambda>q. gq q = fq q - c) (at 0)"
        by eventually_elim auto
    qed auto
    also have "\<dots> \<longleftrightarrow> is_pole fq 0"
      by (subst is_pole_plus_const_iff[of _ _ c]) auto
    finally have not_pole: "\<not>is_pole fq 0" .

    from * have "eval_mero_uhp_at_ii_inf g = 0"
      by (metis One_nat_def g(2) g.eval_at_ii_inf_conv_fourier g.zorder_at_ii_inf_conv_fourier
                g.zorder_fourier_pos_iff is_const_mero_uhp_0 norm_zero zero_less_one_class.zero_less_one)
    also have "eval_mero_uhp_at_ii_inf g = eval_mero_uhp_at_ii_inf f - c"
      unfolding g_def using not_pole
      using pair.fourier_add_eq[of 0] eval_at_ii_inf_conv_fourier pair.add.eval_at_ii_inf_conv_fourier
      by (simp_all add: fq_def)
    finally have "eval_mero_uhp_at_ii_inf f = c"
      by simp
    moreover have "zorder fq 0 \<ge> 0"
      using eventually_neq_fourier[of 0 0] not_pole assms unfolding fq_def
      by (intro zorder_ge_0 analytic_intros eventually_frequently) auto
    hence "zorder_at_ii_inf 1 f \<ge> 0"
      using zorder_at_ii_inf_conv_fourier unfolding fq_def by simp
    ultimately show ?thesis
      using that(2) by blast
  qed
qed

theorem MFuns_surj:
  assumes f: "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "range_mero_uhp f = UNIV"
proof safe
  fix c :: complex
  show "c \<in> range_mero_uhp f"
  proof (rule MFuns_surj_obtain[OF assms, of c], goal_cases)
    case (1 z)
    thus ?case
      unfolding range_mero_uhp_altdef2[OF assms(1)]
      by (auto intro!: imageI simp: poles_mero_uhp_def)
  next
    case 2
    thus ?case
      unfolding range_mero_uhp_altdef2[OF assms(1)] by auto
  qed
qed auto

text \<open>
  A modular function of degree 1 is injective on the fundamental region.
  Note that one could prove something stronger, namely that it is injective on its fundamental
  region plus its cusp.
\<close>
lemma MFuns_degree_1_imp_inj_on:
  assumes f: "f \<in> MFuns" "degree_modfun f = 1"
  shows   "inj_on f (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)"
proof -
  interpret modular_function f UNIV
    using assms by auto
  have not_const: "\<not>is_const_mero_uhp f"
    using assms by auto
  have unique: "card (inv_image_mero_uhp f c) \<le> 1" for c
  proof -
    define g where "g = f + \<langle>- c\<rangle>"
    have deg_g: "degree_modfun g = 1"
      unfolding g_def using f by (subst degree_modfun_plus_const_eq) auto
    hence "g \<noteq> 0"
      by auto
    hence g: "g \<in> MFuns - {0}"
      using f by (auto simp: g_def intro: mform_intros)
  
    have "int (card (zeros_mero_uhp g)) = sum (\<lambda>_. 1 :: int) (zeros_mero_uhp g)"
      by simp
    also have "\<dots> \<le> sum (zorder[\<Gamma>] g) (zeros_mero_uhp g)"
    proof (intro sum_mono, goal_cases)
      case (1 z)
      hence "zorder[\<Gamma>] g z > 0"
        using g by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
      thus ?case
        by linarith
    qed
    also have "\<dots> \<le> int (degree_modfun g)"
      using g by (subst int_degree_modfun_conv_zeros) auto
    also have "\<dots> = 1"
      by (simp add: deg_g)
    finally have "card (zeros_mero_uhp g) \<le> 1"
      by simp
    also have "zeros_mero_uhp g = inv_image_mero_uhp f c"
      by (subst inv_image_mero_uhp_conv_zeros) (simp add: g_def hom_distribs)
    finally show "card (inv_image_mero_uhp f c) \<le> 1" .
  qed

  show ?thesis
  proof
    fix z z' assume z: "z \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f" "z' \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f" "f z = f z'"
    define c where "c = f z"
    from z have "{z, z'} \<subseteq> inv_image_mero_uhp f c"
      by (auto simp: inv_image_mero_uhp_def c_def poles_mero_uhp_def)
    hence "card {z, z'} \<le> card (inv_image_mero_uhp f c)"
      using f not_const by (intro card_mono finite_inv_image_mero_uhp) auto
    also have "\<dots> \<le> 1"
      by (rule unique)
    finally show "z = z'"
      by (cases "z = z'") auto
  qed
qed

text \<open>
  Every non-constant modular function either has a pole in the fundamental region or a
  pole at the cusp.
\<close>
theorem MFuns_pole_exists:
  assumes "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "poles_mero_uhp f \<noteq> {} \<or> zorder_at_ii_inf 1 f < 0"
proof -
  from assms have "int (degree_modfun f) > 0"
    by (simp add: degree_modfun_pos_iff)
  also have "int (degree_modfun f) = 
        (\<Sum>z\<in>poles_mero_uhp f. - zorder[\<Gamma>] f z) - min 0 (zorder_at_ii_inf (Suc 0) f)"
    using assms by (subst int_degree_modfun_conv_poles) auto
  finally show ?thesis
    by (cases "poles_mero_uhp f = {}") (auto simp: min_def split: if_splits)
qed

text \<open>
  Every non-constant modular function either has a pole or a zero in the fundamental region.
\<close>
lemma MFuns_zero_or_pole_exists:
  assumes "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "poles_mero_uhp f \<union> zeros_mero_uhp f \<noteq> {}"
proof -
  from MFuns_surj[OF assms] have "0 \<in> range_mero_uhp f"
    by auto
  moreover from MFuns_pole_exists[OF assms] have "poles_mero_uhp f \<noteq> {} \<or> zorder_at_ii_inf 1 f < 0"
    by auto
  ultimately show ?thesis
    by (subst (asm) range_mero_uhp_altdef2[OF assms(1)])
       (auto simp: inv_image_mero_uhp_def poles_mero_uhp_def)
qed

text \<open>
  Apostol's Theorem~2.6: a bounded modular function is constant.
\<close>
theorem modular_and_bounded_imply_constant:
  assumes "f \<in> MFuns" and "bounded (f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f))"
  shows   "is_const_mero_uhp f"
proof (rule ccontr)
  assume nonconst: "\<not>is_const_mero_uhp f"
  from assms obtain B where B: "\<And>z. z \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f \<Longrightarrow> norm (f z) \<le> B"
    unfolding bounded_iff by blast
  define x y where "x = \<i> * (B + 1)" and "y = \<i> * (B + 2)"
  have [simp]: "norm x > B" "norm y > B"
    by (auto simp: x_def y_def norm_mult)
  have *: "c \<notin> f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)" if "norm c > B" for c
    using B that by fastforce

  have "eval_mero_uhp_at_ii_inf f = x"
    by (rule MFuns_surj_obtain[OF assms(1) nonconst, of x])
       (use *[of x] in \<open>auto simp: poles_mero_uhp_def\<close>)
  moreover have "eval_mero_uhp_at_ii_inf f = y"
    by (rule MFuns_surj_obtain[OF assms(1) nonconst, of y])
       (use *[of y] in \<open>auto simp: poles_mero_uhp_def\<close>)
  ultimately have "x = y"
    by simp
  thus False
    by (simp add: x_def y_def)
qed

end