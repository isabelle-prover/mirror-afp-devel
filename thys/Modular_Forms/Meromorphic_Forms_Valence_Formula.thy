section \<open>The valence formula for level 1 meromorphic forms\<close>
theory Meromorphic_Forms_Valence_Formula
imports 
  "Winding_Number_Eval.Winding_Number_Eval"
  "Path_Automation.Path_Automation"
   Argument_Principle_Sparse
   Detour_Calculus.Detour_Calculus
   Modular_Forms
begin

(* TODO: might be of general interest. *)
text \<open>
  The following is an important ingedient in our evaluation of the integral in Theorem 2.4:
  If a function has an isolated non-essential singularity at \<open>u\<close> and is not identically zero,
  then consider the integral $\int_\gamma(\varepsilon) \frac{f'(w)}{f(w)}\,\text{d}w$ where
  \<open>\<gamma>(\<epsilon>)\<close> is a circular arc with radius \<open>\<epsilon>\<close> around \<open>u\<close> beginning at the angle
  \<open>a(\<epsilon>)\<close> and ending at the angle \<open>b(\<epsilon>)\<close>.

  Assume that \<open>a(\<epsilon>) \<rightarrow> a\<close> and \<open>b(\<epsilon>) \<rightarrow> b\<close> as \<open>\<epsilon> \<rightarrow> 0\<close>.
  Then as \<open>\<epsilon> \<rightarrow> 0\<close>, the value of that integral tends to \<open>n (b - a) \<i>\<close>, where \<^term>\<open>n = zorder f u\<close>.

  This is in some sense a more precise version of the Argument Principle for circular paths:
  The Residue Theorem would tell us in such a situation that the value of the integral will
  tend to $2 i \pi n m$ for a circular path that winds \<open>m\<close> times around \<open>u\<close>
  (where \<open>m\<close> is an integer). This proposition tells us that the same also holds for circular
  paths that do not wind around \<open>u\<close> an integer number of times; i.e.\ \<open>m\<close> can be an arbitrary
  real number.
\<close>
proposition contour_integral_logderiv_part_circlepath_not_essential:
  fixes f :: "complex \<Rightarrow> complex" and a b :: "real \<Rightarrow> real"
  assumes "f meromorphic_on {u}"
  assumes "eventually (\<lambda>z. f z \<noteq> 0) (at u)"
  assumes "(a \<longlongrightarrow> A) (at_right 0)" "(b \<longlongrightarrow> B) (at_right 0)"
  assumes "K = (of_int (zorder f u) * (B - A)) *\<^sub>R \<i>"
  defines "circ \<equiv> (\<lambda>\<epsilon>. part_circlepath u \<epsilon> (a \<epsilon>) (b \<epsilon>))"
  shows   "((\<lambda>\<epsilon>. contour_integral (circ \<epsilon>) (\<lambda>z. deriv f z / f z)) \<longlongrightarrow> K) (at_right 0)"
proof -
  note [tendsto_intros] = \<open>(a \<longlongrightarrow> A) (at_right 0)\<close> \<open>(b \<longlongrightarrow> B) (at_right 0)\<close>
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1

  from assms(1) have iso: "isolated_singularity_at f u"
    by (simp add: meromorphic_on_isolated_singularity)
  from assms(1) obtain R1 where R1: "R1 > 0" "f analytic_on ball u R1 - {u}"
    using iso unfolding isolated_singularity_at_def by blast
  obtain R2 where R2: "R2 > 0" "\<And>z. z \<in> ball u R2 - {u} \<Longrightarrow> f z \<noteq> 0"
    using \<open>eventually (\<lambda>z. f z \<noteq> 0) (at u)\<close> unfolding eventually_at by (auto simp: dist_commute)
  from R1(1) R2(1) obtain R where "R > 0" "R < R1" "R < R2"
    using field_lbound_gt_zero by auto
  have R: "R > 0" "f analytic_on cball u R - {u}" "\<And>z. z \<in> cball u R - {u} \<Longrightarrow> f z \<noteq> 0"
    using R2 \<open>R > 0\<close> \<open>R < R1\<close> \<open>R < R2\<close> by (auto intro!: analytic_on_subset [OF R1(2)])

  from assms(1) obtain F where F: "(\<lambda>w. f (u + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  have [simp]: "F \<noteq> 0"
    using \<open>eventually (\<lambda>z. f z \<noteq> 0) (at u)\<close> F
          has_laurent_expansion_eventually_nonzero_iff[of f u F] by auto

  define n where "n = zorder f u"
  define G where "G = fls_base_factor_to_fps F"
  define g where "g = (\<lambda>z. if z = u then fps_nth G 0 else f z * (z - u) powi -n)"
  define f' where "f' = (\<lambda>z. of_int n * (z - u) powi (n - 1) * g z + (z - u) powi n * deriv g z)"
  have f_eq: "f z = (z - u) powi n * g z" if z: "z \<noteq> u" for z
    using z by (auto simp: g_def power_int_minus)
  have n_eq: "n = fls_subdegree F"
    using has_laurent_expansion_zorder[OF F] by (simp add: n_def)
  have G: "(\<lambda>w. g (u + w)) has_fps_expansion G"                   
    unfolding g_def n_eq G_def using has_fps_expansion_fls_base_factor_to_fps[OF F]
    by (auto cong: if_cong)

  have g_ana [analytic_intros]: "g analytic_on cball u R"
  proof -
    obtain A where A: "open A" "cball u R - {u} \<subseteq> A" "f holomorphic_on A"
      using R(2) unfolding analytic_on_holomorphic by blast
    have "(\<lambda>z. f z * (z - u) powi -n) holomorphic_on A - {u}"
      by (intro holomorphic_intros holomorphic_on_subset [OF A(3)]) auto
    also have "?this \<longleftrightarrow> g holomorphic_on A - {u}"
      by (intro holomorphic_cong) (auto simp: g_def)
    finally have "g analytic_on cball u R - {u}"
      unfolding analytic_on_holomorphic using A by (intro exI[of _ "A-{u}"]) auto
    moreover have "g analytic_on {u}"
      using G has_fps_expansion_imp_analytic by blast
    ultimately have "g analytic_on (cball u R - {u}) \<union> {u}"
      by (subst analytic_on_Un) (auto simp: analytic_on_open)
    also have "\<dots> = cball u R"
      using R(1) by auto
    finally show "g analytic_on cball u R" .
  qed    

  have [derivative_intros]: "(g has_field_derivative deriv g z) (at z)" if "z \<in> cball u R" for z
  proof -
    obtain A where A: "open A" "cball u R \<subseteq> A" "g holomorphic_on A"
      using g_ana unfolding analytic_on_holomorphic by blast
    show ?thesis
      by (rule holomorphic_derivI[of _ A]) (use A that in auto)
  qed

  have deriv_f_eq: "deriv f z = f' z" if "z \<in> ball u R - {u}" for z
  proof (rule DERIV_imp_deriv)
    have "((\<lambda>z. (z - u) powi n * g z) has_field_derivative f' z) (at z)"
      using that by (auto simp: f'_def intro!: derivative_eq_intros)
    also have "?this \<longleftrightarrow> (f has_field_derivative f' z) (at z)"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>w. w \<in> ball u R - {u}) (nhds z)"
        by (intro eventually_nhds_in_open) (use that in auto)
      thus "eventually (\<lambda>w. (w - u) powi n * g w = f w) (nhds z)"
        by eventually_elim (auto simp: g_def power_int_minus)
    qed auto
    finally show "(f has_field_derivative f' z) (at z)" .
  qed

  have "g u = fps_nth G 0"
    by (simp add: g_def)
  also have "\<dots> \<noteq> 0"
    unfolding G_def using \<open>F \<noteq> 0\<close> fls_base_factor_to_fps_base by blast
  finally have g_nz: "g z \<noteq> 0" if "z \<in> cball u R" for z
    using that R(3)[of z] by (auto simp: g_def)

  define h where "h = (\<lambda>z. deriv g z / g z)"
  have h_ana: "h analytic_on cball u R"
    unfolding h_def by (intro analytic_intros g_nz) auto
  hence "continuous_on (cball u R) h"
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on)
  hence "compact (h ` cball u R)"
    by (intro compact_continuous_image) auto
  hence "bounded (h ` cball u R)"
    by (rule compact_imp_bounded)
  then obtain C where C: "\<And>z. z \<in> cball u R \<Longrightarrow> norm (h z) \<le> C"
    unfolding bounded_iff by (auto simp: cball_def)
  have "0 \<le> norm (h u)"
    by simp
  also have "\<dots> \<le> C"
    by (intro C) (use \<open>R > 0\<close> in auto)
  finally have "C \<ge> 0" .

  define result where "result = (\<lambda>\<epsilon>. of_int n * (\<i> * (b \<epsilon> - a \<epsilon>)))"
  define err where "err = (\<lambda>\<epsilon>. contour_integral (circ \<epsilon>) h)"
  have int_err: "(h has_contour_integral err \<epsilon>) (circ \<epsilon>)" if \<epsilon>: "\<epsilon> \<in> {0<..<R}" for \<epsilon>
    unfolding err_def circ_def
    by (rule has_contour_integral_integral, rule analytic_imp_contour_integrable)
       (use \<epsilon> in \<open>auto intro!: analytic_on_subset [OF h_ana]
                       simp: path_image_part_circlepath' dist_norm norm_mult\<close>)

  show ?thesis
  proof (rule Lim_transform_eventually)
    have "eventually (\<lambda>\<epsilon>. \<epsilon> \<in> {0<..<R}) (at_right 0)"
      using \<open>R > 0\<close> eventually_at_right_real by blast
    thus "eventually (\<lambda>\<epsilon>. result \<epsilon> + err \<epsilon> = contour_integral (circ \<epsilon>) (\<lambda>z. deriv f z / f z))
            (at_right 0)"
    proof eventually_elim
      case \<epsilon>: (elim \<epsilon>)
      have "u \<notin> path_image (circ \<epsilon>)"
        using \<epsilon> by (auto simp: circ_def path_image_part_circlepath')
      hence "((\<lambda>w. 1 / (w - u)) has_contour_integral \<i> * (b \<epsilon> - a \<epsilon>)) (circ \<epsilon>)"
        using has_contour_integral_winding_number[of "circ \<epsilon>" u] \<epsilon>
              winding_number_part_circlepath_centre[of \<epsilon> u "a \<epsilon>" "b \<epsilon>"]
        by (simp_all add: circ_def)
      hence "((\<lambda>w. of_int n * (1 / (w - u))) has_contour_integral result \<epsilon>) (circ \<epsilon>)"
        unfolding result_def by (rule has_contour_integral_lmul)
      hence "((\<lambda>w. of_int n / (w - u) + h w) has_contour_integral (result \<epsilon> + err \<epsilon>)) (circ \<epsilon>)"
        using \<epsilon> by (intro has_contour_integral_add int_err) simp_all
      hence "contour_integral (circ \<epsilon>) (\<lambda>w. of_int n / (w - u) + h w) = result \<epsilon> + err \<epsilon>"
        using contour_integral_unique by blast
      also have "contour_integral (circ \<epsilon>) (\<lambda>w. of_int n / (w - u) + h w) =
                   contour_integral (circ \<epsilon>) (\<lambda>w. deriv f w / f w)"
      proof (intro contour_integral_cong refl)
        fix w assume "w \<in> path_image (circ \<epsilon>)"
        hence w: "w \<in> ball u R - {u}"
          using \<epsilon> by (auto simp: circ_def path_image_part_circlepath' dist_norm)
        thus "of_int n / (w - u) + h w = deriv f w / f w"
          using g_nz by (auto simp: h_def deriv_f_eq f_eq f'_def field_simps power_int_diff)
      qed
      finally show ?case ..
    qed
  next
    have [tendsto_intros]: "(err \<longlongrightarrow> 0) (at_right 0)"
    proof (rule Lim_null_comparison)
      have "eventually (\<lambda>\<epsilon>. \<epsilon> \<in> {0<..<R}) (at_right 0)"
        using \<open>R > 0\<close> eventually_at_right_real by blast
      thus "eventually (\<lambda>\<epsilon>. norm (err \<epsilon>) \<le> C * \<epsilon> * \<bar>b \<epsilon> - a \<epsilon>\<bar>) (at_right 0)"
      proof eventually_elim
        case \<epsilon>: (elim \<epsilon>)
        show "norm (err \<epsilon>) \<le> C * \<epsilon> * \<bar>b \<epsilon> - a \<epsilon>\<bar>"
          unfolding err_def circ_def
        proof (rule contour_integral_bound_part_circlepath)
          show "norm (h z) \<le> C" if "z \<in> path_image (part_circlepath u \<epsilon> (a \<epsilon>) (b \<epsilon>))" for z
            using that \<epsilon> by (intro C) (auto simp: path_image_part_circlepath' dist_norm)
          show "h contour_integrable_on part_circlepath u \<epsilon> (a \<epsilon>) (b \<epsilon>)"
            by (intro analytic_imp_contour_integrable analytic_intros
                      analytic_on_subset [OF h_ana])
               (use \<epsilon> in \<open>auto simp: path_image_part_circlepath' dist_norm\<close>)
        qed (use \<open>C \<ge> 0\<close> \<epsilon> C in auto)
      qed
    next
      show "((\<lambda>\<epsilon>. C * \<epsilon> * \<bar>b \<epsilon> - a \<epsilon>\<bar>) \<longlongrightarrow> 0) (at_right 0)"
        by (auto intro!: tendsto_eq_intros)
    qed
    have [tendsto_intros]: "(result \<longlongrightarrow> (of_int n * (B - A)) *\<^sub>R \<i>) (at_right 0)"
      unfolding result_def by (auto intro!: tendsto_eq_intros simp: scaleR_conv_of_real)
    show "((\<lambda>\<epsilon>. result \<epsilon> + err \<epsilon>) \<longlongrightarrow> K) (at_right 0)"
      by (auto intro!: tendsto_eq_intros simp: scaleR_conv_of_real n_def \<open>K = _\<close>)
  qed
qed

lemma winding_preserving_inverse_upper_halfspace:
  assumes "A \<subseteq> {z. Im z > 0}"
  shows   "winding_preserving A inverse (\<lambda>x. x)"
proof
  show "inj_on inverse A"
    using assms by (auto simp: inj_on_def)
  show "continuous_on A inverse"
    using assms by (auto intro!: continuous_intros)
next
  fix p z assume p: "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p"
  assume z: "z \<in> A - path_image p"
  have "winding_number (inverse \<circ> p) (inverse z) = winding_number p z - winding_number p 0"
    using p z assms by (subst winding_number_inverse) auto
  also have "winding_number p 0 = 0"
    using assms p z
    by (intro winding_number_zero_outside[of _ "{z. Im z > 0}"])
       (auto simp: convex_halfspace_Im_gt)
  finally show "winding_number (inverse \<circ> p) (inverse z) = winding_number p z"
    by (simp add: o_def)
qed

lemmas [simp del] = pathstart_part_circlepath pathfinish_part_circlepath

text \<open>
  This is the contour around the fundamental region \<^term>\<open>\<R>\<^sub>\<Gamma>\<close> that we want to integrate on.
  Unfortunately, since there may be roots and zeros on the contour, we will have to deform
  it slightly later. But for now, we will show the basic properties of this contour: it is
  a positively oriented (i.e.\ counter-clockwise) simple closed curve that contains all points 
  in \<^term>\<open>\<R>\<^sub>\<Gamma>\<close> with imaginary part \<open>< b\<close>, and it does not contain any points outside the
  closure of \<^term>\<open>\<R>\<^sub>\<Gamma>\<close>.
\<close>
definition mypath :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "mypath b = part_circlepath 0 1 (2/3*pi) (1/3*pi) +++
              linepath (\<^bold>\<rho> + 1) (1 / 2 + b *\<^sub>R \<i>) +++
              linepath (1 / 2 + b *\<^sub>R \<i>) (-1 / 2 + b *\<^sub>R \<i>) +++
              linepath (-1 / 2 + b *\<^sub>R \<i>) \<^bold>\<rho>"

lemma mypath_ends: "cis (pi / 3) = \<^bold>\<rho> + 1" "cis (2 * pi / 3) = \<^bold>\<rho>"
  unfolding modfun_rho_altdef by (simp_all add: complex_eq_iff cos_60 cos_120 sin_60 sin_120)

lemma path_mypath [simp, intro]: "path (mypath b)"
  and valid_path_mypath [simp, intro]: "valid_path (mypath b)"
  and closed_mypath: "pathstart (mypath b) = pathfinish (mypath b)"
  unfolding mypath_def
  by (simp_all add: rcis_def mypath_ends pathfinish_part_circlepath' pathstart_part_circlepath')

lemma sin_not_gt_one [simp]: "\<not>sin (x :: real) > 1"
  using sin_le_one[of x] by linarith

lemma cos_not_gt_one [simp]: "\<not>cos (x :: real) > 1"
  using cos_le_one[of x] by linarith

lemma simple_path_mypath [simp, intro]:
  assumes "b > 1"
  shows   "simple_path (mypath b)"
proof -
  have "sqrt 3 \<le> 2"
    by (rule real_le_lsqrt) auto
  hence b: "b > sqrt 3 / 2"
    using assms by linarith
  note [simp] = mypath_ends closed_segment_same_Re closed_segment_same_Im
                closed_segment_eq_real_ivl rcis_def cos_60 cos_120

  show ?thesis
    unfolding mypath_def
    using [[goals_limit = 20]]
  proof path
    show "path_image (part_circlepath 0 1 (2 / 3 * pi) (1 / 3 * pi)) \<inter>
          closed_segment (\<^bold>\<rho> + 1) (1 / 2 + b *\<^sub>R \<i>) \<subseteq> {rcis 1 (1 / 3 * pi)}" (is "?A \<subseteq> ?B")
    proof
      fix z assume "z \<in> ?A"
      then obtain t where t: "cos t = cos (pi / 3)" "t \<in> {pi/3..2*pi/3}" "z = cis t"
        using b by (auto simp: path_image_part_circlepath' complex_eq_iff)
      have [simp]: "t = pi / 3"
        by (rule cos_inj_pi) (use t in auto)
      show "z \<in> ?B"
        using t by auto
    qed
  next
    show "path_image (part_circlepath 0 1 (2 / 3 * pi) (1 / 3 * pi)) \<inter>
            closed_segment (- 1 / 2 + b *\<^sub>R \<i>) \<^bold>\<rho> \<subseteq> {rcis 1 (2 / 3 * pi)} \<inter> {\<^bold>\<rho>}" (is "?A \<subseteq> ?B")
    proof
      fix z assume "z \<in> ?A"
      then obtain t where t: "cos t = cos (2 * pi / 3)" "t \<in> {pi/3..2*pi/3}" "z = cis t"
        using b by (auto simp: path_image_part_circlepath' complex_eq_iff)
      have [simp]: "t = 2 * pi / 3"
        by (rule cos_inj_pi) (use t in auto)
      show "z \<in> ?B"
        using t by auto
    qed
  qed (use assms b in \<open>auto simp: path_image_part_circlepath' complex_eq_iff\<close>)
qed

lemma simple_loop_mypath [simp, intro]: "b > 1 \<Longrightarrow> simple_loop (mypath b)"
  by (auto simp: simple_loop_def closed_mypath)

lemma path_image_mypath:
  assumes "b > sqrt 3 / 2"
  shows   "path_image (mypath b) =
             {z. norm z = 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> \<le> 1 / 2} \<union>
             {z. Im z = b \<and> \<bar>Re z\<bar> \<le> 1 / 2} \<union>
             {z. \<bar>Re z\<bar> = 1 / 2 \<and> Im z \<in> {sqrt 3 / 2..b}}"
proof -
  have "path_image (mypath b) =
          path_image (part_circlepath 0 1 (2 * pi / 3) (pi / 3)) \<union>
          {z. Im z = b \<and> Re z \<in> {-1/2..1/2}} \<union>
          ({z. Re z = 1 / 2 \<and> Im z \<in> {sqrt 3 / 2..b}} \<union>
           {z. Re z = - (1 / 2) \<and> Im z \<in> {sqrt 3 / 2..b}})" (is "_ = ?A \<union> ?B \<union> ?C")
    using assms
    by (simp add: mypath_def path_image_join mypath_ends rcis_def Un_ac
                  closed_segment_same_Re closed_segment_same_Im closed_segment_eq_real_ivl
                  pathfinish_part_circlepath')
  also have "?B = {z. Im z = b \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
    by auto
  also have "?C = {z. \<bar>Re z\<bar> = 1 / 2 \<and> Im z \<in> {sqrt 3 / 2..b}}"
    by auto
  also have "?A = {z. norm z = 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
  proof safe
    fix z assume "z \<in> ?A"
    then obtain t where t: "t \<in> {pi/3..2*pi/3}" "z = cis t"
      by (auto simp: path_image_part_circlepath' closed_segment_eq_real_ivl rcis_def)
    show "norm z = 1"
      by (simp add: t)
    have "t > 0"
      by (rule less_le_trans[of _ "pi / 3"]) (use t(1) in auto)
    have "t < pi"
      by (rule le_less_trans[of _ "2 * pi / 3"]) (use t(1) in auto)
    show "Im z > 0" using \<open>t > 0\<close> \<open>t < pi\<close>
      by (auto simp: t intro!: sin_gt_zero)
    have "cos t \<le> cos (pi / 3)" "cos t \<ge> cos (2 * pi / 3)"
      by (subst cos_mono_le_eq; use t in simp; fail)+
    thus "\<bar>Re z\<bar> \<le> 1 / 2"
      by (auto simp: t cos_60 cos_120)
  next
    fix z assume z: "norm z = 1" "Im z > 0" "\<bar>Re z\<bar> \<le> 1 / 2"
    have "cos (2 * pi / 3) \<le> cos (Arg z)"
      using z by (subst cos_Arg) (auto simp: cos_120 cos_60 divide_simps)
    hence "Arg z \<le> 2 * pi / 3"
      using z by (subst (asm) cos_mono_le_eq) (auto simp: Arg_less_0 Arg_le_pi)
    moreover have "cos (pi / 3) \<ge> cos (Arg z)"
      using z by (subst cos_Arg) (auto simp: cos_120 cos_60 divide_simps)
    hence "Arg z \<ge> pi / 3"
      using z by (subst (asm) cos_mono_le_eq) (auto simp: Arg_less_0 Arg_le_pi)
    ultimately have "Arg z \<in> {pi/3..2*pi/3}"
      by auto
    moreover have "cis (Arg z) = z"
      using z by (subst cis_Arg) (auto simp: complex_sgn_def)
    ultimately show "z \<in> path_image (part_circlepath 0 1 (2 * pi / 3) (pi / 3))"
      by (subst path_image_part_circlepath) (auto simp: closed_segment_eq_real_ivl \<open>norm z = 1\<close>)
  qed
  finally show ?thesis .
qed

lemma path_image_mypath_subset:
  assumes "b > 1"
  shows "path_image (mypath b) \<subseteq> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
proof -
  have "sqrt 3 < 2"
    by (rule real_less_lsqrt) auto
  have *: "sqrt 3 / 2 < b"
    by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
  have "b > 0"
    by (rule le_less_trans[OF _ assms]) auto
  have **: "x \<in> {-1/2..1/2} \<longleftrightarrow> \<bar>x\<bar> \<le> 1 / 2" for x :: real
    by auto
  show ?thesis
    unfolding path_image_mypath[OF *] **
  proof (intro Un_least subsetI)
    fix z assume z: "z \<in> {z. Im z = b \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
    have "1 < \<bar>Im z\<bar>"
      using z assms by simp
    also have "\<dots> \<le> norm z"
      by (rule abs_Im_le_cmod)
    finally have "norm z > 1" .
    thus "z \<in> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      using z \<open>b > 0\<close> by (auto simp: closure_std_fund_region)
  next
    fix z assume z: "z \<in> {z. \<bar>Re z\<bar> = 1 / 2 \<and> Im z \<in> {sqrt 3 / 2..b}}"
    have "0 \<le> sqrt 3 / 2"
      by simp
    also have "\<dots> \<le> Im z"
      using z by auto
    finally have "Im z \<ge> 0" .
    have "1 = (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
      by (simp add: power_divide)
    also have "\<dots> \<le> norm z ^ 2"
      unfolding cmod_power2 by (intro add_mono power2_mono) (use z in auto)
    finally have "norm z \<ge> 1"
      by (simp add: power2_nonneg_ge_1_iff)
    thus "z \<in> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      using z \<open>b > 1\<close> \<open>Im z \<ge> 0\<close> by (auto simp: closure_std_fund_region)
  next
    fix z assume z: "z \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
    have "Im z \<le> norm z"
      using abs_Im_le_cmod abs_le_iff by blast
    also have "\<dots> = 1"
      using z by auto
    also have "\<dots> < b"
      by fact
    finally show "z \<in> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      using z by (auto simp: closure_std_fund_region)
  qed
qed

lemma path_image_mypath_superset_frontier:
  assumes "b > sqrt 3 / 2"
  shows   "frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b} \<subseteq> path_image (mypath b)"
  unfolding frontier_std_fund_region Int_Un_distrib2
proof (intro Un_least subsetI)
  fix z assume z: "z \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> \<bar>Re z\<bar> \<le> 1 / 2} \<inter> {z. Im z \<le> b}"
  thus "z \<in> path_image (mypath b)"
    unfolding path_image_mypath[OF assms] by auto
next
  fix z assume z: "z \<in> {z. 1 \<le> cmod z \<and> 0 < Im z \<and> \<bar>Re z\<bar> = 1 / 2} \<inter> {z. Im z \<le> b}"
  hence "1 \<le> norm z ^ 2"
    by auto
  also have "\<dots> = \<bar>Re z\<bar> ^ 2 + Im z ^ 2"
    unfolding cmod_power2 by simp
  also have "\<bar>Re z\<bar> = 1 / 2"
    using z by auto
  finally have "Im z ^ 2 \<ge> 3 / 4"
    by (auto simp: field_simps simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  hence "2 * Im z \<ge> sqrt 3"
    using z by (intro real_le_lsqrt) (auto simp: field_simps)
  thus "z \<in> path_image (mypath b)"
    using z unfolding path_image_mypath[OF assms] by (intro UnI2) auto
qed

lemma frontier_subset_path_image_mypath:
  assumes "b > 1"
  shows   "path_image (mypath b) \<subseteq> frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b} \<union>
             closed_segment (-1/2 + b *\<^sub>R \<i>) (1/2 + b *\<^sub>R \<i>)" (is "_ \<subseteq> ?rhs")
proof -
  have "sqrt 3 < 2"
    by (rule real_less_lsqrt) auto
  have *: "sqrt 3 / 2 < b"
    by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
  show ?thesis
    unfolding path_image_mypath[OF *]
  proof (intro Un_least subsetI)
    fix z assume z: "z \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
    have "Im z \<le> norm z"
      using abs_Im_le_cmod abs_le_iff by blast
    also have "\<dots> = 1"
      using z by auto
    also have "\<dots> < b"
      using assms by auto
    finally show "z \<in> ?rhs"
      using z unfolding frontier_std_fund_region by (intro UnI1) auto
  next
    fix z assume z: "z \<in> {z. Im z = b \<and> \<bar>Re z\<bar> \<le> 1 / 2}"
    thus "z \<in> ?rhs"
      by (intro UnI2)
         (auto simp: frontier_std_fund_region closed_segment_same_Im closed_segment_eq_real_ivl)
  next
    fix z assume z: "z \<in> {z. \<bar>Re z\<bar> = 1 / 2 \<and> Im z \<in> {sqrt 3 / 2..b}}"
    have "0 < sqrt 3 / 2"
      by simp
    also have "\<dots> \<le> Im z"
      using z by auto
    finally have "Im z > 0" .
    have "1 = (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
      by (simp add: field_simps)
    also have "\<dots> \<le> \<bar>Re z\<bar> ^ 2 + Im z ^ 2"
      by (intro add_mono power2_mono) (use z \<open>Im z > 0\<close> in auto)
    finally have "norm z ^ 2 \<ge> 1"
      unfolding cmod_power2 by simp
    thus "z \<in> ?rhs"
      using z \<open>Im z > 0\<close> unfolding frontier_std_fund_region 
      by (intro UnI1) (auto simp: frontier_std_fund_region power2_nonneg_ge_1_iff)
  qed
qed

lemma path_image_mypath_conv_frontier:
  assumes "b > 1"
  shows   "path_image (mypath b) =
             frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b} \<union> closed_segment (-1/2 + b *\<^sub>R \<i>) (1/2 + b *\<^sub>R \<i>)"
proof -
  have "sqrt 3 < 2"
    by (rule real_less_lsqrt) auto
  have *: "sqrt 3 / 2 < b"
    by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
  have "closed_segment (- 1 / 2 + b *\<^sub>R \<i>) (1 / 2 + b *\<^sub>R \<i>) \<subseteq> path_image (mypath b)"
    unfolding path_image_mypath[OF *]
    by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl)
  thus ?thesis
    using frontier_subset_path_image_mypath[OF assms] path_image_mypath_superset_frontier[OF *]
    by blast
qed 

lemma winding_number_mypath_inside:
  assumes "z \<in> \<R>\<^sub>\<Gamma>" "Im z < b" "b > 1"
  shows   "winding_number (mypath b) z = 1"
proof -
  note [simp] = closed_segment_same_Re closed_segment_same_Im closed_segment_eq_real_ivl
                rcis_def mypath_ends cos_60 cos_120 sin_60 sin_120 in_std_fund_region_iff
                path_image_part_circlepath' sin_arccos Let_def jumpF_pathstart_part_circlepath
                jumpF_pathfinish_part_circlepath
  have 1: "arccos (1/2) < arccos (Re z)"
    by (intro arccos_less_arccos) (use assms in auto)
  have 2: "arccos (-1/2) > arccos (Re z)"
    by (intro arccos_less_arccos) (use assms in auto)
  hence 3: "Im z > sqrt (1 - (Re z)\<^sup>2)"
  proof -
    have "norm z ^ 2 > 1"
      using assms by simp
    hence "Im z ^ 2 > 1 - Re z ^ 2"
      unfolding cmod_power2 by linarith
    hence "sqrt (Im z ^ 2) > sqrt (1 - Re z ^ 2)"
      by (subst real_sqrt_less_iff)
    also have "sqrt (Im z ^ 2) = Im z"
      using assms by simp
    finally show ?thesis .
  qed

  have part1: "cindex_pathE (linepath (\<^bold>\<rho> + 1) (1 / 2 + b *\<^sub>R \<i>)) z = 0"
   and part2: "cindex_pathE (linepath (1 / 2 + b *\<^sub>R \<i>) (- 1 / 2 + b *\<^sub>R \<i>)) z = -1"
   and part3: "cindex_pathE (linepath (- 1 / 2 + b *\<^sub>R \<i>) \<^bold>\<rho>) z = 0"
    by (subst cindex_pathE_linepath; use assms in simp; fail)+

  have "cindex_pathE (part_circlepath 0 1 (2 / 3 * pi) (1 / 3 * pi)) z =
         -cindex_pathE (part_circlepath 0 1 (1 / 3 * pi) (2 / 3 * pi)) z"
    by (subst cindex_pathE_reversepath', subst reversepath_part_circlepath) (rule refl)
  also have "\<dots> = -1"
    by (subst cindex_pathE_part_circlepath) (use assms 1 2 3 in auto)
  finally have part4: "cindex_pathE (part_circlepath 0 1 (2 / 3 * pi) (1 / 3 * pi)) z = -1" .

  show ?thesis
    unfolding mypath_def
    by eval_winding 
       (use assms part1 part2 part3 part4 
        in \<open>auto simp: pathstart_part_circlepath' pathfinish_part_circlepath'\<close>)
qed

lemma simple_loop_ccw_mypath:
  assumes "b > 1"
  shows   "simple_loop_ccw (mypath b)"
proof -
  have "sqrt 3 < 2"
    by (rule real_less_lsqrt) auto
  have *: "sqrt 3 / 2 < b"
    by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
  from assms obtain y where y: "1 < y" "y < b"
    using dense by blast
  define z where "z = y *\<^sub>R \<i>"
  have z: "z \<in> \<R>\<^sub>\<Gamma>" "Im z < b" using assms y
    by (auto simp: in_std_fund_region_iff z_def)
  hence "winding_number (mypath b) z = 1"
    using assms z by (intro winding_number_mypath_inside)
  moreover have "z \<notin> path_image (mypath b)"
    using y * by (subst path_image_mypath) (auto simp: z_def)
  ultimately show ?thesis using assms
    by (intro simple_loop_ccwI[of _ z]) auto
qed

lemma simple_loop_orientation_mypath [simp]:
  assumes "b > 1"
  shows   "simple_loop_orientation (mypath b) = 1"
  using simple_loop_ccw_mypath[OF assms]
  unfolding simple_loop_orientation_def by auto

lemma winding_number_mypath_outside:
  assumes "z \<notin> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}" "b > 1"
  shows   "winding_number (mypath b) z = 0"
proof -
  consider "z \<notin> closure \<R>\<^sub>\<Gamma>" | "z \<in> closure \<R>\<^sub>\<Gamma>" "Im z > b"
    using assms(1) by force
  thus ?thesis
  proof cases
    assume z: "z \<notin> closure \<R>\<^sub>\<Gamma>"
    show ?thesis
    proof (rule simply_connected_imp_winding_number_zero)
      show "simply_connected (closure \<R>\<^sub>\<Gamma>)"
        by (fact simply_connected_closure_std_fund_region)
      show "path_image (mypath b) \<subseteq> closure \<R>\<^sub>\<Gamma>"
        using path_image_mypath_subset[of b] assms by blast
    qed (use z in \<open>auto simp: closed_mypath\<close>)
  next 
    assume z: "z \<in> closure \<R>\<^sub>\<Gamma>" "Im z > b"
    have "sqrt 3 < 2"
      by (rule real_less_lsqrt) auto
    have *: "sqrt 3 / 2 < b"
      by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
    show ?thesis
    proof (rule winding_number_zero_outside)
      show "path_image (mypath b) \<subseteq> cbox (-1/2) (1/2 + b *\<^sub>R \<i>)"
        using path_image_mypath_subset[OF assms(2)]
        by (auto simp: in_cbox_complex_iff closure_std_fund_region)
      show "z \<notin> cbox (- 1 / 2) (1 / 2 + b *\<^sub>R \<i>)"
        using z by (auto simp: in_cbox_complex_iff)
    qed (use assms in \<open>auto simp: closed_mypath in_cbox_complex_iff\<close>)
  qed
qed

lemma inside_mypath:
  assumes "b > 1"
  shows   "inside (path_image (mypath b)) = \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
proof -
  have "sqrt 3 < 2"
    by (rule real_less_lsqrt) auto
  have *: "sqrt 3 / 2 < b"
    by (rule less_trans[OF _ \<open>b > 1\<close>]) (use \<open>sqrt 3 < 2\<close> in auto)
  show ?thesis
  proof (intro equalityI subsetI)
    fix z assume z: "z \<in> inside (path_image (mypath b))"
    hence ind: "norm (winding_number (mypath b) z) = 1"
      using assms simple_closed_path_norm_winding_number_inside simple_path_mypath by blast
    from z have z': "z \<notin> path_image (mypath b)"
      by (simp add: inside_outside)
    show "z \<in> \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
    proof (rule ccontr)
      assume z: "z \<notin> \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
      moreover have "z \<notin> frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
        using path_image_mypath_superset_frontier[OF *] z' by auto
      ultimately have "z \<notin> (\<R>\<^sub>\<Gamma> \<union> frontier \<R>\<^sub>\<Gamma>) \<inter> {z. Im z \<le> b}" using z'
        unfolding frontier_std_fund_region std_fund_region_def path_image_mypath[OF *] by force
      also have "\<R>\<^sub>\<Gamma> \<union> frontier \<R>\<^sub>\<Gamma> = closure \<R>\<^sub>\<Gamma>"
        by (simp add: closure_Un_frontier)
      finally have "winding_number (mypath b) z = 0"
        by (intro winding_number_mypath_outside) (use assms in auto)
      with ind show False
        by simp
    qed
  next
    fix z assume z: "z \<in> \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
    hence "winding_number (mypath b) z = 1"
      by (intro winding_number_mypath_inside) (use assms in auto)
    moreover have "z \<notin> path_image (mypath b)"
      unfolding path_image_mypath_conv_frontier[OF assms] frontier_std_fund_region using z
      by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl in_std_fund_region_iff)
    ultimately show "z \<in> inside (path_image (mypath b))"
      using simple_loop_winding_number_cases[OF simple_loop_mypath[OF assms], of z]
      by (auto split: if_splits)
  qed
qed

lemma outside_mypath:
  assumes "b > 1"
  shows   "outside (path_image (mypath b)) = -(closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b})"
proof -
  define L where "L = closed_segment (- 1 / 2 + b *\<^sub>R \<i>) (1 / 2 + b *\<^sub>R \<i>)"
  have "outside (path_image (mypath b)) = - (path_image (mypath b) \<union> \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b})"
    unfolding outside_inside inside_mypath[OF assms] ..
  also have "\<dots> = -((frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}) \<union> L \<union> (\<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}))"
    unfolding path_image_mypath_conv_frontier[OF assms] L_def ..
  also have "x \<in> frontier \<R>\<^sub>\<Gamma>" if "x \<notin> L" "x \<in> \<R>\<^sub>\<Gamma>" "b = Im x" for x
    using that unfolding L_def frontier_std_fund_region
    by (auto simp: in_std_fund_region_iff closed_segment_same_Im closed_segment_eq_real_ivl)
  hence "((frontier \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}) \<union> L \<union> (\<R>\<^sub>\<Gamma> \<inter> {z. Im z < b})) =
             (frontier \<R>\<^sub>\<Gamma> \<union> \<R>\<^sub>\<Gamma>) \<inter> {z. Im z \<le> b} \<union> L"
    by auto
  also have "frontier \<R>\<^sub>\<Gamma> \<union> \<R>\<^sub>\<Gamma> = closure \<R>\<^sub>\<Gamma>"
    by (simp add: closure_Un_frontier Un_commute)
  also {
    have "L \<subseteq> path_image (mypath b)"
      by (subst path_image_mypath_conv_frontier) (use assms in \<open>auto simp: L_def\<close>)
    also have "\<dots> \<subseteq> closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      using path_image_mypath_subset[OF assms] by blast
    finally have "closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b} \<union> L = closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      by blast
  }
  finally show ?thesis .
qed

subsection \<open>Constructing the deformed path\<close>

definition mypath'_circ1 where
  "mypath'_circ1 \<epsilon> = part_circlepath (\<^bold>\<rho> + 1) \<epsilon> (5 * pi / 6 + arcsin (\<epsilon> / 2)) (pi / 2)"

definition mypath'_circ2 where
  "mypath'_circ2 \<epsilon> = part_circlepath \<^bold>\<rho> \<epsilon> (pi / 2) (pi / 6 - arcsin (\<epsilon> / 2))"

definition mypath'_circ3 where
  "mypath'_circ3 \<epsilon> = part_circlepath \<i> \<epsilon> (pi + arcsin (\<epsilon> / 2)) (- arcsin (\<epsilon> / 2))"

definition mypath'_line where
  "mypath'_line b = linepath (1/2 + b *\<^sub>R \<i>) (-1/2 + b *\<^sub>R \<i>)"


locale mypath_detour = meromorphic_form_full g k for g k +
  fixes A :: "complex set" and b :: real
  defines "A \<equiv> {z. Im z > 0 \<and> g z = 0} \<union> {z. Im z > 0 \<and> is_pole g z}"
  assumes g_nonzero: "g \<noteq> 0"
  assumes subset_zeros_poles: "A \<subseteq> {z. Im z \<in> {0<..<b}}"
  assumes b_gt: "b > 1"
begin

definition f where "f = (\<lambda>z. deriv g z / g z)"

lemma sparse_A: "A sparse_in {z. Im z > 0}"
proof -
  have "eventually (\<lambda>z. eval_mero_uhp g z \<noteq> 0 \<and> \<not>is_pole g z) (cosparse \<H>)"
    by (intro eventually_conj eval_mero_uhp_avoid_0 meromorphic_on_imp_not_pole_cosparse
              meromorphic_intros open_halfspace_Im_gt) (use g_nonzero in auto)
  hence "{z. eval_mero_uhp g z = 0 \<or> is_pole g z} sparse_in \<H>"
    by (simp add: eventually_cosparse)
  thus "A sparse_in \<H>"
    by (rule sparse_in_subset2) (auto simp: A_def)
qed

lemma open_A_compl [intro]: "open ({z. Im z > 0} - A)"
  using sparse_A by (simp add: open_diff_sparse_pts open_halfspace_Im_gt)

lemma open_A_compl_subset: "X \<subseteq> A \<Longrightarrow> open ({z. Im z > 0} - X)"
  by (rule open_diff_sparse_pts open_halfspace_Im_gt sparse_in_subset2[OF sparse_A])+


lemma g_has_field_derivative [derivative_intros]:
  "Im z > 0 \<Longrightarrow> z \<notin> A \<Longrightarrow> (g has_field_derivative deriv g z) (at z within X)"
  by (intro analytic_derivI analytic_intros) (auto simp: A_def)

lemma g_has_field_derivative' [derivative_intros]:
  assumes "(h has_field_derivative h') (at z within X)" "Im (h z) > 0" "h z \<notin> A"
  shows   "((\<lambda>x. g (h x)) has_field_derivative deriv g (h z) * h') (at z within X)"
  using DERIV_chain [of g "deriv g (h z)" h z h' X, OF g_has_field_derivative assms(1)] assms(2-)
  by (auto simp: o_def)

lemma f_holomorphic: "f holomorphic_on ({z. Im z > 0} - A)"
  unfolding f_def by (intro holomorphic_intros open_A_compl) (auto simp: A_def)

lemma f_analytic: "f analytic_on X" if "X \<subseteq> {z. Im z > 0} - A" for X
proof (rule analytic_on_subset)
  show "f analytic_on ({z. Im z > 0} - A)"
    by (subst analytic_on_open) (auto intro: open_A_compl f_holomorphic)
qed (fact that)

lemma g_plus1: "g (z + 1) = g z"
  using plus_1[of z] by simp

lemma g_invariant: "g (-(1 / z)) = z powi k * eval_mero_uhp g z"
proof -
  have "-(1 / z) = apply_modgrp S_modgrp z"
    by simp
  also have "g \<dots> = z powi k * eval_mero_uhp g z"
    by (subst invariant_apply_modgrp) auto
  finally show ?thesis .
qed

lemma A_invariant1: "z + 1 \<in> A \<longleftrightarrow> z \<in> A"
  using rel_imp_is_pole_iff[of "z" "z + 1"] unfolding A_def by (auto simp: g_plus1)

lemma A_invariant2: "-(1 / z) \<in> A \<longleftrightarrow> z \<in> A"
  unfolding A_def using rel_imp_is_pole_iff[of "z" "-1/z"] rel_imp_eval_eq_0_iff[of "z" "-1/z"]
  by auto

lemma deriv_g_invariant:
  assumes "Im z > 0" "z \<notin> A"
  shows   "deriv g (z + 1) = deriv g z"
    and   "deriv g (-(1 / z)) = deriv g z * z powi (k + 2) + of_int k * z * g (- 1 / z)"
proof -
  have "((\<lambda>z. g (z + 1)) has_field_derivative deriv g (z + 1)) (at z)"
    using assms by (auto intro!: derivative_eq_intros simp del: g_plus1) (auto simp: A_invariant1)
  also have "?this \<longleftrightarrow> (g has_field_derivative deriv g (z + 1)) (at z)"
    by (simp add: g_plus1)
  finally show "deriv g (z + 1) = deriv g z"
    by (simp add: DERIV_imp_deriv)

  let ?D1 = "deriv g (-1 / z) * z powi (-k - 2)"
  let ?D2 = "-of_int k * z powi (-k - 1) * g (-1 / z)"

  from assms have [simp]: "z \<noteq> 0"
    by auto
  have "Im (-1 / z) > 0" if "Im z > 0" for z
    using Im_complex_div_gt_0 that by fastforce
  hence "((\<lambda>z. z powi (-k) * g (-1 / z)) has_field_derivative ?D1 + ?D2) (at z)"
    using assms A_invariant2[of z]
    by (auto intro!: derivative_eq_intros simp: power2_eq_square power_int_diff)
  also have "?this \<longleftrightarrow> (g has_field_derivative ?D1 + ?D2) (at z)"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>w. w \<in> {w. Im w > 0} - A) (nhds z)"
      by (intro eventually_nhds_in_open) (use assms in \<open>auto intro!: open_A_compl\<close>)
    thus "\<forall>\<^sub>F x in nhds z. x powi (-k) * g (-1 / x) = g x"
    proof eventually_elim
      case (elim x)
      thus ?case
        by (auto simp: power_int_minus field_simps g_invariant)
    qed
  qed auto
  finally have "deriv g z = ?D1 + ?D2"
    by (intro DERIV_imp_deriv)
  thus "deriv g (-(1 / z)) = deriv g z * z powi (k + 2) + of_int k * z * g (- 1 / z)"
    by (simp add: field_simps power_int_diff power_int_minus power_int_add power2_eq_square)
qed

lemma f_invariant:
  assumes "Im z > 0" "z \<notin> A"
  shows   "f (z + 1) = f z" and "f (-1 / z) = f z * z ^ 2 + of_int k * z"
proof -
  have [simp]: "z \<noteq> 0" "g z \<noteq> 0"
    using assms by (auto simp: A_def)
  show "f (z + 1) = f z"
    using assms by (simp_all add: f_def g_invariant deriv_g_invariant g_plus1)
  have "f (-1 / z) = (deriv g z * z powi (k + 2) + of_int k * z * (z powi k * g z)) /
                       (z powi k * g z)"
    using assms by (simp add: f_def g_invariant deriv_g_invariant)
  also have "\<dots> = deriv g z * z ^ 2 / g z + of_int k * z"
    by (auto simp: field_simps power_int_add)
  also have "deriv g z * z ^ 2 / g z = f z * z ^ 2"
    by (simp add: f_def)
  finally show "f (-1 / z) = f z * z ^ 2 + of_int k * z" .
qed

text \<open>
  The singularities on the left vertical line and on the circular arc at the bottom, respectively:
\<close>
definition S_l where "S_l = {z\<in>A\<inter>closure \<R>\<^sub>\<Gamma>-{\<^bold>\<rho>}. Re z = -1/2}"
definition S_arc where "S_arc = {z\<in>A\<inter>closure \<R>\<^sub>\<Gamma>-{\<^bold>\<rho>, \<i>, \<^bold>\<rho>+1}. norm z = 1}"

text \<open>
  The vertical positions of the singularities on the vertical lines.
\<close>
definition Y where "Y = Im ` S_l"
definition ys where "ys = sorted_list_of_set Y"

text \<open>
  The angles of the singularities on the circular arc.
\<close>
definition \<Phi> where "\<Phi> = Arg ` {z\<in>S_arc. Arg z < pi / 2}"
definition phis where "phis = sorted_list_of_set \<Phi>"
definition phis' where "phis' = phis @ [pi/2] @ rev (map (\<lambda>x. pi - x) phis)"


text \<open>
  The following two functions turn a vertical position on the left/right line into
  the actual point.
\<close>
definition lv :: "real \<Rightarrow> complex" where "lv y = -1/2 + y *\<^sub>R \<i>"
definition rv :: "real \<Rightarrow> complex" where "rv y = 1/2 + y *\<^sub>R \<i>"

text \<open>
  The only points on the original contour that we want to include in the deformed contour
  are the singularities on the right vertical line (except for \<open>\<rho> + 1\<close>).
\<close>
definition I where "I = S_l \<union> cis ` (\<lambda>x. pi - x) ` \<Phi>"

text \<open>
  The points on the original contour that we want to exclude ar the singularities on the
  left vertical line and on the circular arc at the bottom (including \<open>\<rho>\<close>, \<open>i\<close>, and \<open>\<rho> + 1\<close>).
\<close>
definition X where "X = (+) 1 ` S_l \<union> cis ` \<Phi> \<union> {\<^bold>\<rho>, \<i>, \<^bold>\<rho>+1}"

text \<open>
  All the singularities not lying on the original curve should be preserved, i.e.\ they should
  be (strictly) inside the new curve if and only if they were inside before and (strictly) outside
  it if and only if they were outside before.
\<close>
definition P where "P = {z. Im z \<le> 0} \<union> (A - frontier \<R>\<^sub>\<Gamma>)"



lemma finite_A: "finite (A \<inter> closure \<R>\<^sub>\<Gamma>)"
proof -
  have "finite ((closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}) \<inter> A)"
  proof (rule sparse_in_compact_finite)
    show "A sparse_in closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}"
      using sparse_A by (rule sparse_in_subset) (use closure_std_fund_region_Im_pos in auto)
    have "closed (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b})"
      by (auto intro: closed_halfspace_Im_le)
    moreover have "bounded (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b})"
    proof (rule bounded_subset)
      show "closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b} \<subseteq> cbox (-1) (1 + \<i> * b)"
        by (auto simp: in_closure_std_fund_region_iff in_cbox_complex_iff)
    qed auto
    ultimately show "compact (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b})"
      using compact_eq_bounded_closed by blast
  qed
  also have "(closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> b}) \<inter> A = A \<inter> closure \<R>\<^sub>\<Gamma>"
    using subset_zeros_poles unfolding A_def by force
  finally show ?thesis .
qed

lemma Y_finite: "finite Y"
  unfolding Y_def by (intro finite_imageI finite_subset[OF _ finite_A])
                     (use std_fund_region'_subset in \<open>auto simp: S_l_def\<close>)

definition vjunc where "vjunc = (Min (insert b Y) + sqrt 3 / 2) / 2"
definition arcjunc where
  "arcjunc = (if \<Phi> = {} then pi/3 + pi/18 else (Min (insert (pi/2) \<Phi>) + pi / 3) / 2)"
definition arcjunc' where
  "arcjunc' = (if \<Phi> = {} then pi/3 + 2*pi/18 else (pi / 2 + Max (insert (pi / 3) \<Phi>)) / 2)"

lemma b_gt': "b > sqrt 3 / 2"
proof -
  have "sqrt 3 < 2"
    by (intro real_less_lsqrt) auto
  hence "sqrt 3 / 2 < 1"
    by simp
  thus ?thesis
    by (rule less_trans [OF _ b_gt]) 
qed

lemma Y_subset: "Y \<subseteq> {sqrt 3 / 2 <..< b}"
proof
  fix y assume y: "y \<in> Y"
  then obtain z where z: "Im z = y" "z \<in> S_l"
    by (auto simp: Y_def)
  hence "Re z = -1/2" "z \<noteq> \<^bold>\<rho>"
    by (auto simp: S_l_def)
  hence z_eq: "z = -1/2 + \<i> * y"
    using z by (auto simp: complex_eq_iff)
  have "y < b" "y > 0"
    using z subset_zeros_poles by (auto simp: S_l_def)
  have "(1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2 = 1"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> norm z ^ 2"
    using z by (auto simp: S_l_def closure_std_fund_region)
  also have "\<dots> = (1 / 2) ^ 2 + y ^ 2"
    unfolding cmod_power2 by (simp add: z_eq)
  finally have "y \<ge> sqrt 3 / 2"
    using \<open>y > 0\<close> by (simp flip: abs_le_square_iff)
  moreover have "y \<noteq> sqrt 3 / 2"
    using \<open>z \<noteq> \<^bold>\<rho>\<close> by (auto simp: complex_eq_iff z_eq)
  ultimately show "y \<in> {sqrt 3 / 2 <..< b}"
    using \<open>y < b\<close> by auto
qed

lemma ys: "set ys = Y" "sorted_wrt (<) ys"
  unfolding ys_def using Y_finite by auto

lemma vjunc: "vjunc \<in> {sqrt 3 / 2 <..< b}" "\<forall>y\<in>Y. vjunc < y"
proof -
  have "Min (insert b Y) > sqrt 3 / 2"
    using Y_subset Y_finite b_gt' by (subst Min_gr_iff) auto
  hence *: "vjunc > sqrt 3 / 2"
    by (simp add: vjunc_def)
  moreover have "Min (insert b Y) \<le> b"
    using Y_finite by (subst Min_le_iff) auto
  hence "vjunc < b" using b_gt'
    by (simp add: vjunc_def)
  ultimately show "vjunc \<in> {sqrt 3 / 2 <..< b}" by auto

  show "\<forall>y\<in>Y. vjunc < y"
  proof safe
    fix y assume y: "y \<in> Y"
    have "vjunc < Min (insert b Y)"
      using * unfolding vjunc_def add_divide_distrib by linarith
    also have "Min (insert b Y) \<le> y"
      by (rule Min.coboundedI) (use Y_finite y in auto)
    finally show "vjunc < y" .
  qed
qed

lemma vjunc_pos: "vjunc > 0"
proof -
  have "0 < sqrt 3 / 2"
    by simp
  also have "\<dots> < vjunc"
    using vjunc by auto
  finally show ?thesis .
qed


lemma \<Phi>_finite: "finite \<Phi>"
  unfolding \<Phi>_def by (intro finite_imageI finite_subset[OF _ finite_A])
                     (use std_fund_region'_subset in \<open>auto simp: S_arc_def\<close>)

lemma Arg_S_arc_gt: 
  assumes "z \<in> S_arc"
  shows   "Arg z > pi / 3"
proof -
  from assms have z: "norm z = 1" "Im z \<ge> 0" "z \<noteq> \<^bold>\<rho> + 1" "z \<in> closure \<R>\<^sub>\<Gamma>" "Re z \<le> 1 / 2"
    by (auto simp: S_arc_def closure_std_fund_region)
  have [simp]: "z \<noteq> 0"
    using z by auto
  have "Re z \<noteq> 1 / 2"
  proof
    assume "Re z = 1 / 2"
    have "1 = norm z ^ 2"
      using z by simp
    also have "\<dots> = Re z ^ 2 + Im z ^ 2"
      unfolding cmod_power2 ..
    finally have *: "Im z ^ 2 = 3 / 4"
      by (simp add: \<open>Re z = 1 / 2\<close> power_divide)
    have "sqrt (Im z ^ 2) = sqrt 3 / 2"
      using \<open>Im z \<ge> 0\<close> by (subst *) (auto simp: real_sqrt_divide)
    with \<open>Re z = 1 / 2\<close> show False
      using \<open>z \<noteq> \<^bold>\<rho> + 1\<close> \<open>Im z \<ge> 0\<close> by (simp add: complex_eq_iff)
  qed
  with \<open>Re z \<le> 1 / 2\<close> have "Re z < 1 / 2"
    by linarith
  also have "z = cis (Arg z)"
    by (simp add: cis_Arg complex_sgn_def z)
  also have "Re \<dots> = cos (Arg z)"
    by simp
  finally have "cos (Arg z) < cos (pi / 3)"
    by (simp add: cos_60)
  thus ?thesis
    using Arg_bounded [of z] Arg_less_0[of z] \<open>Im z \<ge> 0\<close>
    by (subst (asm) cos_mono_less_eq) auto
qed

lemma \<Phi>_subset: "\<Phi> \<subseteq> {pi / 3 <..< pi / 2}"
  using Arg_S_arc_gt unfolding \<Phi>_def by auto

lemma phis: "set phis = \<Phi>" "sorted_wrt (<) phis"
  unfolding phis_def using \<Phi>_finite by auto

lemma arcjunc: "arcjunc \<in> {pi/3 <..< pi/2}" "\<And>x. x \<in> \<Phi> \<Longrightarrow> arcjunc < x"
proof -
  have *: "Min (insert (pi / 2) \<Phi>) > pi / 3"
    using \<Phi>_subset \<Phi>_finite by (subst Min_gr_iff) auto
  show "arcjunc \<in> {pi/3 <..< pi/2}"
  proof (cases "\<Phi> = {}")
    case False
    have eq: "arcjunc = (Min (insert (pi / 2) \<Phi>) + pi / 3)/2"
      unfolding arcjunc_def using False by auto
    have "arcjunc > pi / 3"
      using * by (simp add: arcjunc_def)
    moreover have "Min (insert (pi / 2) \<Phi>) \<le> pi / 2"
      using \<Phi>_finite by (subst Min_le_iff) auto
    hence "arcjunc < pi / 2"
      unfolding eq add_divide_distrib using pi_gt_zero by linarith
    ultimately show "arcjunc \<in> {pi/3 <..< pi/2}" by auto
  qed (auto simp: arcjunc_def)

  show "arcjunc < y" if y: "y \<in> \<Phi>" for y
  proof -
    have eq: "arcjunc = (Min (insert (pi / 2) \<Phi>) + pi / 3)/2"
      unfolding arcjunc_def using y by auto
    have "arcjunc < Min (insert (pi/2) \<Phi>)"
      using * unfolding eq add_divide_distrib by linarith
    also have "Min (insert (pi/2) \<Phi>) \<le> y"
      by (rule Min.coboundedI) (use \<Phi>_finite y in auto)
    finally show "arcjunc < y" .
  qed
qed

lemma arcjunc': "arcjunc' \<in> {pi/3 <..< pi/2}" "\<And>x. x \<in> \<Phi> \<Longrightarrow> arcjunc' > x"
proof -
  have *: "Max (insert (pi / 3) \<Phi>) < pi / 2"
    using \<Phi>_subset \<Phi>_finite by (subst Max_less_iff) auto
  show "arcjunc' \<in> {pi/3 <..< pi/2}"
  proof (cases "\<Phi> = {}")
    case False
    have eq: "arcjunc' = (pi / 2 + Max (insert (pi / 3) \<Phi>)) / 2"
      unfolding arcjunc'_def using False by auto
    from * have "arcjunc' < pi / 2"
      by (simp add: arcjunc'_def)
    moreover have "Max (insert (pi / 3) \<Phi>) \<ge> pi / 3"
      using \<Phi>_finite by (subst Max_ge_iff) auto
    hence "arcjunc' > pi / 3"
      unfolding eq add_divide_distrib using pi_gt_zero by linarith
    ultimately show "arcjunc' \<in> {pi/3 <..< pi/2}" by auto
  qed (auto simp: arcjunc'_def)

  show "arcjunc' > y" if y: "y \<in> \<Phi>" for y
  proof -
    have eq: "arcjunc' = (pi / 2 + Max (insert (pi / 3) \<Phi>)) / 2"
      unfolding arcjunc'_def using y by auto
    have "y \<le> Max (insert (pi/3) \<Phi>)"
      by (rule Max.coboundedI) (use \<Phi>_finite y in auto)
    also have "Max (insert (pi/3) \<Phi>) < arcjunc'"
      using * unfolding eq add_divide_distrib by linarith
    finally show "arcjunc' > y" .
  qed
qed

lemma arcjunc_less_arcjunc': "arcjunc < arcjunc'"
proof (cases "\<Phi> = {}")
  case False
  then obtain y where "y \<in> \<Phi>"
    by blast
  with arcjunc(2)[of y] arcjunc'(2)[of y] show ?thesis
    by linarith
qed (auto simp: arcjunc_def arcjunc'_def)

lemma sorted1: "sorted_wrt (<) (vjunc # ys @ [b])"
  using vjunc ys Y_subset by (auto simp: sorted_wrt_append)

lemma sorted2: "sorted_wrt (<) (arcjunc # phis @ [arcjunc'])"
  using phis arcjunc_less_arcjunc' arcjunc arcjunc' by (auto simp: sorted_wrt_append)

lemma minus_cnj_in_A_iff: "norm z = 1 \<Longrightarrow> -cnj z \<in> A \<longleftrightarrow> z \<in> A"
  using A_invariant2[of z] by (simp add: divide_conv_cnj)

lemma minus_cnj_eq_rho_iff [simp]: "-cnj z = \<^bold>\<rho> \<longleftrightarrow> z = \<^bold>\<rho> + 1"
  and minus_cnj_eq_rho'_iff [simp]: "-cnj z = \<^bold>\<rho> + 1 \<longleftrightarrow> z = \<^bold>\<rho>"
  and minus_cnj_eq_i_iff [simp]: "-cnj z = \<i> \<longleftrightarrow> z = \<i>"
  by (auto simp: complex_eq_iff)

lemma minus_cnj_in_S_arc_iff [simp]: "-cnj z \<in> S_arc \<longleftrightarrow> z \<in> S_arc"
proof -
  have "-cnj z \<in> S_arc" if "z \<in> S_arc" for z
    using that unfolding S_arc_def
    by (auto simp: closure_std_fund_region minus_cnj_in_A_iff)
  from this[of z] this[of "-cnj z"] show ?thesis
    by auto
qed

lemma minus_cnj_in_closure_std_fund_region_iff [simp]:
  "- cnj z \<in> closure \<R>\<^sub>\<Gamma> \<longleftrightarrow> z \<in> closure \<R>\<^sub>\<Gamma>"
  by (auto simp: closure_std_fund_region)

lemma S_arc_decompose: "S_arc = cis ` \<Phi> \<union> cis ` (\<lambda>x. pi - x) ` \<Phi>"
proof
  have 1: "cis (Arg z) = z" if "norm z = 1" for z
    using that by (subst cis_Arg) (auto simp: complex_sgn_def)
  have "z \<in> S_arc" if "z \<in> cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi>" for z using that
    by (auto simp: S_arc_def \<Phi>_def 1 norm_divide divide_conv_cnj minus_cnj_in_A_iff
             simp flip: cis_divide)
  thus "cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi> \<subseteq> S_arc"
    by blast

  show "S_arc \<subseteq> cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi>"
  proof
    fix z assume z: "z \<in> S_arc"
    have [simp]: "z \<noteq> 0" "norm z = 1"
      using z by (auto simp: S_arc_def)
    have "Im z \<ge> 0"
      using z by (auto simp: S_arc_def closure_std_fund_region)
    thus "z \<in> cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi>"
    proof (cases "Arg z" "pi / 2" rule: linorder_cases)
      case less
      have "z \<in> {z \<in> S_arc. Arg z < pi / 2}"
        using less z by auto
      moreover have "z = cis (Arg z)"
        by (subst cis_Arg) (use z in \<open>auto simp: S_arc_def complex_sgn_def\<close>)
      ultimately show "z \<in> cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi>"
        unfolding \<Phi>_def image_image by blast
    next
      case greater
      have "Arg z < 2 * pi"
        by (rule le_less_trans[of _ pi]) (use Arg_bounded[of z] in auto)
      hence "Arg (-cnj z) = pi - Arg z"
        using z greater \<open>Im z \<ge> 0\<close>
        by (intro cis_Arg_unique)
           (auto simp: complex_sgn_def scaleR_conv_of_real S_arc_def divide_conv_cnj
                       cis_Arg Arg_less_0 simp flip: cis_divide)
      hence "-cnj z \<in> {z \<in> S_arc. Arg z < pi / 2}"
        using greater z by (auto simp: S_arc_def minus_cnj_in_A_iff)
      moreover have "z = cis (pi - Arg (-cnj z))"
        by (auto simp: cis_Arg complex_sgn_def divide_conv_cnj simp flip: cis_divide)
      ultimately show "z \<in> cis ` \<Phi> \<union> cis ` (-) pi ` \<Phi>"
        unfolding \<Phi>_def image_image by blast
    next
      case equal
      have "cis (Arg z) = z"
        by (simp add: cis_Arg complex_sgn_def)
      also have "Arg z = pi / 2"
        using equal by simp
      finally have "z = \<i>"
        by simp
      with z have False
        by (auto simp: S_arc_def)
      thus ?thesis ..
    qed
  qed
qed


subsubsection \<open>The vertical segments\<close>

fun mypath'_vert :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex" where
  "mypath'_vert left l u [] \<epsilon> = linepath (rv l) (rv u)"
| "mypath'_vert left l u [y] \<epsilon> = avoid_linepath left (rv l) (rv u) (rv y) \<epsilon>"
| "mypath'_vert left l u (y1 # y2 # ys') \<epsilon> =
     avoid_linepath left (rv l) (rv ((y1 + y2) / 2)) (rv y1) \<epsilon> +++
     mypath'_vert left ((y1 + y2) / 2) u (y2 # ys') \<epsilon>"

definition mypath'_vert'
  where "mypath'_vert' left l u ys' \<epsilon> = reversepath ((+) (-1) \<circ> mypath'_vert left l u ys' \<epsilon>)"

lemma detour_rel_mypath'_vert:
  assumes "sorted_wrt (<) (l # ys' @ [u])"
  shows   "detour_rel {} (rv ` set ys') (linepath (rv l) (rv u))
             (mypath'_vert False l u ys') (mypath'_vert True l u ys')"
  using assms
proof (induction ys' arbitrary: l rule: induct_list012)
  case 1
  thus ?case by auto
next
  case (2 y l)
  thus ?case
    by (auto intro!: detour_rel_linepath_semicircle_right
             simp: open_segment_eq_real_ivl rv_def open_segment_same_Re)
next
  case (3 y1 y2 ys l)
  define m where "m = (y1 + y2) / 2"
  have "detour_rel ({} \<union> {}) ({rv y1} \<union> rv ` set (y2 # ys))
          (linepath (rv l) (rv m) +++ linepath (rv m) (rv u))
          (\<lambda>\<epsilon>. avoid_linepath False (rv l) (rv m) (rv y1) \<epsilon> +++
                 mypath'_vert False m u (y2 # ys) \<epsilon>)
          (\<lambda>\<epsilon>. avoid_linepath True (rv l) (rv m) (rv y1) \<epsilon> +++
                 mypath'_vert True m u (y2 # ys) \<epsilon>)"
    using "3.prems"
    by (intro detour_rel_join detour_rel_linepath_semicircle_right "3.IH")
       (auto simp: rv_def m_def open_segment_same_Re open_segment_eq_real_ivl)
  also have "linepath (rv l) (rv m) +++ linepath (rv m) (rv u) \<equiv>\<^sub>p
             linepath (rv l) (rv u)"
    using "3.prems"
    by (intro eq_paths_linepaths)
       (auto simp: rv_def m_def closed_segment_same_Re closed_segment_eq_real_ivl complex_eq_iff)
  finally show ?case
    by (simp add: m_def insert_commute)
qed

lemma pathstart_mypath'_vert [simp]: "pathstart (mypath'_vert left l u ys' \<epsilon>) = rv l"
  and pathfinish_mypath'_vert [simp]: "pathfinish (mypath'_vert left l u ys' \<epsilon>) = rv u"
  by (induction left l u ys' \<epsilon> rule: mypath'_vert.induct;
      simp add: avoid_linepath_def rcis_def Let_def; fail)+

lemma valid_path_mypath'_vert:
  "sorted_wrt (<) (l # ys' @ [u]) \<Longrightarrow> valid_path (mypath'_vert left l u ys' \<epsilon>)"
proof (induction ys' arbitrary: l rule: induct_list012)
  case 1
  thus ?case by auto
next
  case (2 y l)
  thus ?case
    by (auto intro!: valid_path_avoid_linepath simp: rv_def)
next
  case (3 y1 y2 ys l)
  define m where "m = (y1 + y2) / 2"
  have "valid_path (mypath'_vert left m u (y2 # ys) \<epsilon>)"
    using "3.prems" by (intro "3.IH") (auto simp: m_def)
  moreover have "pathfinish (avoid_linepath left (rv l) (rv ((y1 + y2) / 2)) (rv y1) \<epsilon>) =
                   rv ((y1 + y2) / 2)"
    by (auto simp: avoid_linepath_def)
  moreover have "rv l \<noteq> rv m"
    using "3.prems" by (auto simp: rv_def m_def)
  ultimately show ?case using "3.prems"
    by (auto intro!: valid_path_join valid_path_avoid_linepath simp: m_def)
qed

lemma detour_rel_mypath'_vert':
  assumes "sorted_wrt (<) (l # ys' @ [u])"
  shows   "detour_rel (lv ` set ys') {} (linepath (lv u) (lv l))
             (mypath'_vert' False l u ys') (mypath'_vert' True l u ys')"
proof -
  have "detour_rel ((+) (-1) ` {}) ((+) (-1) ` rv ` set ys') ((+) (-1) \<circ> linepath (rv l) (rv u))
          (\<lambda>\<epsilon>. (+) (-1) \<circ> mypath'_vert False l u ys' \<epsilon>) (\<lambda>\<epsilon>. (+) (-1) \<circ> mypath'_vert True l u ys' \<epsilon>)"
    by (intro detour_rel_translate detour_rel_mypath'_vert[OF assms])
  also have "((+) (-1) ` rv ` set ys') = lv ` set ys'"
    unfolding image_image by (intro image_cong) (auto simp: rv_def lv_def)
  also have "((+) (-1) ` {}) = ({} :: complex set)"
    by auto
  also have "(+) (-1) \<circ> linepath (rv l) (rv u) = linepath (lv l) (lv u)"
    unfolding linepath_translate by (simp add: rv_def lv_def)
  finally have "detour_rel (lv ` set ys') {} (reversepath (linepath (lv l) (lv u)))
                   (mypath'_vert' False l u ys') (mypath'_vert' True l u ys')"
    unfolding mypath'_vert'_def by (rule detour_rel_reverse)
  thus ?thesis
    by simp
qed

lemma pathstart_mypath'_vert' [simp]: "pathstart (mypath'_vert' left l u ys' \<epsilon>) = lv u"
  and pathfinish_mypath'_vert' [simp]: "pathfinish (mypath'_vert' left l u ys' \<epsilon>) = lv l"
  by (simp_all add: mypath'_vert'_def lv_def rv_def pathfinish_compose pathstart_compose)

lemma valid_path_mypath'_vert':
  "sorted_wrt (<) (l # ys' @ [u]) \<Longrightarrow> valid_path (mypath'_vert' left l u ys' \<epsilon>)"
  unfolding mypath'_vert'_def valid_path_reversepath valid_path_translation_eq
  by (rule valid_path_mypath'_vert)


subsubsection \<open>The circular arcs\<close>

text \<open>
  On one half of the arc we will simply place circular arcs to avoid the bad points.
\<close>

fun arc_aux where
  "arc_aux left l u [] \<epsilon> = [part_circlepath 0 1 u l]"
| "arc_aux left l u [y] \<epsilon> = [avoid_part_circlepath left 0 1 u l y \<epsilon>]"
| "arc_aux left l u (y1 # y2 # ys') \<epsilon> =
     avoid_part_circlepath left 0 1 u ((y1 + y2) / 2) y1 \<epsilon> #
     arc_aux left l ((y1 + y2) / 2) (y2 # ys') \<epsilon>"

definition mypath'_arcm :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex" where
  "mypath'_arcm left \<epsilon> =
     avoid_part_circlepath left 0 1 (pi - arcjunc') arcjunc' (pi / 2) \<epsilon>"

definition mypath'_arcr :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
  where "mypath'_arcr left = joinpaths_list \<circ> arc_aux left arcjunc arcjunc' (rev phis)"

definition mypath'_arcl :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
  where "mypath'_arcl left \<epsilon> = (\<lambda>z. -(1/z)) \<circ> reversepath (mypath'_arcr left \<epsilon>)"

definition mypath'_arc :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex" where
  "mypath'_arc left \<epsilon> = mypath'_arcl left (\<epsilon>/2) +++ mypath'_arcm left \<epsilon> +++ mypath'_arcr left (\<epsilon>/2)"

lemma arc_aux_not_empty [simp]: "arc_aux left l u ys' \<epsilon> \<noteq> []"
  by (induction left l u ys' \<epsilon> rule: arc_aux.induct) simp_all

lemma detour_rel_arc_aux:
  assumes "ys' = [] \<or> sorted_wrt (>) (u # ys' @ [l])"
  shows   "detour_rel {} (cis ` set ys') (part_circlepath 0 1 u l)
             (\<lambda>\<epsilon>. joinpaths_list (arc_aux False l u ys' \<epsilon>))
             (\<lambda>\<epsilon>. joinpaths_list (arc_aux True l u ys' \<epsilon>))"
  using assms
proof (induction ys' arbitrary: u rule: induct_list012)
  case 1
  thus ?case by auto
next
  case (2 y l)
  thus ?case
    by (auto intro!: detour_rel_part_circlepath_semicircle_right
             simp: open_segment_eq_real_ivl open_segment_same_Re rcis_def)
next
  case (3 y1 y2 ys u)
  define m where "m = (y1 + y2) / 2"
  have "detour_rel ({} \<union> {}) ({cis y1} \<union> cis ` set (y2 # ys))
          (part_circlepath 0 1 u m +++ part_circlepath 0 1 m l)
          (\<lambda>\<epsilon>. avoid_part_circlepath False 0 1 u m y1 \<epsilon> +++
             joinpaths_list (arc_aux False l m (y2 # ys) \<epsilon>))
          (\<lambda>\<epsilon>. avoid_part_circlepath True 0 1 u m y1 \<epsilon> +++ 
             joinpaths_list (arc_aux True l m (y2 # ys) \<epsilon>))"
    using "3.prems"
    by (intro detour_rel_join detour_rel_part_circlepath_semicircle_right "3.IH")
       (auto simp: m_def open_segment_same_Re open_segment_eq_real_ivl rcis_def sorted_wrt_append
                   pathfinish_part_circlepath' pathstart_part_circlepath')
  also have "part_circlepath 0 1 u m +++ part_circlepath 0 1 m l \<equiv>\<^sub>p
             part_circlepath 0 1 u l"
    using "3.prems"
    by (intro eq_paths_part_circlepaths)
       (auto simp: m_def closed_segment_same_Re closed_segment_eq_real_ivl complex_eq_iff)
  finally show ?case
    by (simp add: m_def insert_commute pathfinish_part_circlepath' pathstart_part_circlepath')
qed

lemma detour_rel_arcr_aux:
  "detour_rel {} (cis ` \<Phi>) (part_circlepath 0 1 arcjunc' arcjunc)
     (mypath'_arcr False) (mypath'_arcr True)"
proof -
  have "phis = [] \<or> sorted_wrt (>) (rev (arcjunc # phis @ [arcjunc']))"
    using sorted2 unfolding sorted_wrt_rev by auto
  hence "detour_rel {} (cis ` set (rev phis)) (part_circlepath 0 1 arcjunc' arcjunc)
          (mypath'_arcr False) (mypath'_arcr True)"
    unfolding mypath'_arcr_def o_def by (intro detour_rel_arc_aux) simp_all
  also have "cis ` set (rev phis) = cis ` \<Phi>"
    by (simp add: image_Un phis)
  finally show ?thesis .
qed

lemma detour_rel_arcr:
  "detour_rel {} (cis ` \<Phi>) (part_circlepath 0 1 arcjunc' arcjunc)
     (\<lambda>\<epsilon>. mypath'_arcr False (\<epsilon> / 2)) (\<lambda>\<epsilon>. mypath'_arcr True (\<epsilon> / 2))"
  using detour_rel_arcr_aux by (rule detour_rel_rescale) auto

lemma detour_rel_arcl:
  "detour_rel (cis ` (\<lambda>x. pi - x) ` \<Phi>) {} (part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc'))
     (\<lambda>\<epsilon>. mypath'_arcl False (\<epsilon> / 2)) (\<lambda>\<epsilon>. mypath'_arcl True (\<epsilon> / 2))"
proof -
  define f where "f = (\<lambda>z. -(1 / z) :: complex)"
  have "detour_rel (cis ` \<Phi>) {} (reversepath (part_circlepath 0 1 arcjunc' arcjunc))
          (\<lambda>\<epsilon>. reversepath (mypath'_arcr False \<epsilon>)) (\<lambda>\<epsilon>. reversepath (mypath'_arcr True \<epsilon>))"
    unfolding o_def by (intro detour_rel_reverse detour_rel_arcr_aux)
  also have "reversepath (part_circlepath 0 1 arcjunc' arcjunc) =
             part_circlepath 0 1 arcjunc arcjunc'" by simp
  finally have "detour_rel (f ` cis ` \<Phi>) (f ` {})
                  (f \<circ> part_circlepath 0 1 arcjunc arcjunc')
                  (\<lambda>\<epsilon>. mypath'_arcl False (\<epsilon> / 2)) (\<lambda>\<epsilon>. mypath'_arcl True (\<epsilon> / 2))"
    unfolding mypath'_arcl_def f_def
  proof (intro detour_rel_image, fold f_def)
    have "winding_preserving {z. Im z \<ge> sqrt 2 / 2} (\<lambda>z. - inverse z) (\<lambda>z. z)"
    proof (rule winding_preserving_comp' [OF winding_preserving_uminus _ order.refl],
           rule winding_preserving_inverse_upper_halfspace)
      show "{z. sqrt 2 / 2 \<le> Im z} \<subseteq> {z. 0 < Im z}"
        by safe (erule less_le_trans [rotated], auto)
    qed
    thus "winding_preserving {z. Im z \<ge> sqrt 2 / 2} f (\<lambda>x. x)"
      by (simp add: f_def field_simps)
  next
    show "2-lipschitz_on {z. sqrt 2 / 2 \<le> Im z} f"
      unfolding f_def using lipschitz_on_complex_inverse[of "sqrt 2 / 2"]
      by (intro lipschitz_intros) (auto simp: field_simps)
  next
    show "f analytic_on {z. sqrt 2 / 2 \<le> Im z}"
      unfolding f_def by (auto intro!: analytic_intros)
  next
    show "closed {z. sqrt 2 / 2 \<le> Im z}"
      by (rule closed_halfspace_Im_ge)
  next
    show "path_image (part_circlepath 0 1 arcjunc arcjunc') \<subseteq> interior {z. sqrt 2 / 2 \<le> Im z}"
      unfolding path_image_part_circlepath'
    proof safe
      fix t assume t: "t \<in> closed_segment arcjunc arcjunc'"
      have "sqrt 2 / 2 < sin (pi / 3)"
        by (simp add: sin_60)
      also have "sin (pi / 3) \<le> sin t"
        using t arcjunc arcjunc' arcjunc_less_arcjunc'
        by (intro sin_monotone_2pi_le) (auto simp: closed_segment_eq_real_ivl)
      finally show "0 + rcis 1 t \<in> interior {z. sqrt 2 / 2 \<le> Im z}"
        unfolding interior_halfspace_Im_ge by (simp add: sin_60)
    qed
  qed (auto simp: closed_halfspace_Im_ge)
  also have "f ` cis ` \<Phi> = cis ` (\<lambda>x. pi - x) ` \<Phi>"
    unfolding image_image by (intro image_cong) (auto simp: f_def simp flip: cis_divide)
  also have "f \<circ> part_circlepath 0 1 arcjunc arcjunc' = part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc')"
    by (simp add: f_def part_circlepath_altdef rcis_def o_def linepath_def ring_distribs mult_ac
             flip: cis_mult cis_divide)
  finally show ?thesis
    by simp
qed

lemma detour_rel_arcm:
  "detour_rel {} {\<i>} (part_circlepath 0 1 (pi - arcjunc') arcjunc')
     (mypath'_arcm False) (mypath'_arcm True)"
  unfolding mypath'_arcm_def
  by (rule detour_rel_part_circlepath_semicircle_right)
     (use arcjunc' in \<open>auto simp: open_segment_eq_real_ivl rcis_def\<close>)

lemma detour_rel_arc:
  "detour_rel (cis ` (\<lambda>x. pi - x) ` \<Phi>) (insert \<i> (cis ` \<Phi>))
     (part_circlepath 0 1 (pi - arcjunc) arcjunc)
     (mypath'_arc False) (mypath'_arc True)"
proof -
  have "detour_rel (cis ` (\<lambda>x. pi - x) ` \<Phi> \<union> {} \<union> {}) ({} \<union> {\<i>} \<union> cis ` \<Phi>)
          (part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc') +++
           part_circlepath 0 1 (pi - arcjunc') arcjunc' +++
           part_circlepath 0 1 arcjunc' arcjunc)
          (\<lambda>\<epsilon>. mypath'_arc False \<epsilon>) (\<lambda>\<epsilon>. mypath'_arc True \<epsilon>)"
    unfolding mypath'_arc_def Un_assoc
    by (intro detour_rel_join detour_rel_arcr detour_rel_arcm detour_rel_arcl) 
       (auto simp: pathfinish_part_circlepath' pathstart_part_circlepath')
  also have "(part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc') +++
           part_circlepath 0 1 (pi - arcjunc') arcjunc' +++
           part_circlepath 0 1 arcjunc' arcjunc) \<equiv>\<^sub>p part_circlepath 0 1 (pi - arcjunc) arcjunc"
    using arcjunc_less_arcjunc' arcjunc(1) arcjunc'(1)
    by (intro eq_paths_joinpaths_part_circlepath) 
       (auto simp: closed_segment_eq_real_ivl pathfinish_part_circlepath' pathstart_part_circlepath')
  finally show ?thesis
    by (simp add: pathfinish_part_circlepath' pathstart_part_circlepath')
qed

lemma pathstart_mypath'_arc_aux [simp]: "pathstart (hd (arc_aux left l u ys' \<epsilon>)) = cis u"
  and pathfinish_mypath'_arc_aux [simp]: "pathfinish (last (arc_aux left l u ys' \<epsilon>)) = cis l"
  by (induction left l u ys' \<epsilon> rule: arc_aux.induct;
      simp add: avoid_part_circlepath_def rcis_def Let_def
                pathfinish_part_circlepath' pathstart_part_circlepath'; fail)+

lemma pathstart_mypath'_arcr [simp]: "pathstart (mypath'_arcr left \<epsilon>) = cis arcjunc'"
  and pathfinish_mypath'_arcr [simp]: "pathfinish (mypath'_arcr left \<epsilon>) = cis arcjunc"
  by (simp_all add: mypath'_arcr_def)

lemma pathstart_mypath'_arcl [simp]: "pathstart (mypath'_arcl left \<epsilon>) = cis (pi - arcjunc)"
  and pathfinish_mypath'_arcl [simp]: "pathfinish (mypath'_arcl left \<epsilon>) = cis (pi - arcjunc')"
  by (simp_all add: mypath'_arcl_def pathstart_compose pathfinish_compose divide_conv_cnj
               flip: cis_divide)

lemma pathstart_mypath'_arcm [simp]: "pathstart (mypath'_arcm left \<epsilon>) = cis (pi - arcjunc')"
  and pathfinish_mypath'_arcm [simp]: "pathfinish (mypath'_arcm left \<epsilon>) = cis arcjunc'"
  by (simp_all add: mypath'_arcm_def avoid_part_circlepath_def Let_def rcis_def
                    pathfinish_part_circlepath' pathstart_part_circlepath')

lemma pathstart_mypath'_arc [simp]: "pathstart (mypath'_arc left \<epsilon>) = cis (pi - arcjunc)"
  and pathfinish_mypath'_arc [simp]: "pathfinish (mypath'_arc left \<epsilon>) = cis arcjunc"
  by (simp_all add: mypath'_arc_def)

lemma valid_path_arc_aux:
  "\<epsilon> \<in> {0<..<2} \<Longrightarrow> ys' = [] \<or> sorted_wrt (>) (u # ys' @ [l]) \<Longrightarrow>
     valid_path (joinpaths_list (arc_aux left l u ys' \<epsilon>))"
proof (induction ys' arbitrary: u rule: induct_list012)
  case 1
  thus ?case by auto
next
  case (2 y u)
  thus ?case
    by (auto intro!: valid_path_avoid_part_circlepath)
next
  case (3 y1 y2 ys u)
  define m where "m = (y1 + y2) / 2"
  have "valid_path (joinpaths_list (arc_aux left l m (y2 # ys) \<epsilon>))"
    using "3.prems" by (intro "3.IH") (auto simp: m_def sorted_wrt_append)
  moreover have "pathfinish (avoid_part_circlepath left 0 1 u ((y1 + y2) / 2) y1 \<epsilon>) =
                 cis ((y1 + y2) / 2)"
    by (auto simp: avoid_part_circlepath_def Let_def rcis_def
                   pathfinish_part_circlepath' pathstart_part_circlepath')
  ultimately show ?case using "3.prems"
    by (auto intro!: valid_path_join valid_path_avoid_part_circlepath simp: m_def)
qed

lemma valid_path_arcm: "\<epsilon> \<in> {0<..<2} \<Longrightarrow> valid_path (mypath'_arcm left \<epsilon>)"
  using arcjunc' by (auto simp: mypath'_arcm_def intro!: valid_path_avoid_part_circlepath)

lemma valid_path_arcr: 
  assumes "\<epsilon> \<in> {0<..<2}"
  shows "valid_path (mypath'_arcr left \<epsilon>)"
proof -
  have "phis = [] \<or> sorted_wrt (>) (rev (arcjunc # phis @ [arcjunc']))"
    using sorted2 unfolding sorted_wrt_rev by auto
  thus ?thesis
    unfolding mypath'_arcr_def o_def using assms by (intro valid_path_arc_aux) simp_all
qed

lemma valid_path_arcl: "eventually (\<lambda>\<epsilon>. valid_path (mypath'_arcl left (\<epsilon> / 2))) (at_right 0)"
proof -
  have "simple_path (part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc'))"
       "valid_path (part_circlepath 0 1 (pi - arcjunc) (pi - arcjunc'))"
    using arcjunc_less_arcjunc' arcjunc(1) arcjunc'(1) by (auto simp: simple_path_part_circlepath)
  from detour_rel_imp_valid_simple_path [OF detour_rel_arcl this] show ?thesis
    by eventually_elim (cases left, auto)
qed


subsection \<open>The corners\<close>

definition mypath'_lcorner where
  "mypath'_lcorner left \<epsilon> = avoid_linepath_circlepath left vjunc (pi - arcjunc) \<epsilon>"

definition mypath'_rcorner where
  "mypath'_rcorner left \<epsilon> = (\<lambda>z. -cnj z) \<circ> reversepath (mypath'_lcorner left \<epsilon>)"

lemma pathstart_mypath'_lcorner [simp]: "pathstart (mypath'_lcorner left \<epsilon>) = lv vjunc"
  and pathfinish_mypath'_lcorner [simp]: "pathfinish (mypath'_lcorner left \<epsilon>) = cis (pi - arcjunc)"
  by (simp_all add: mypath'_lcorner_def avoid_linepath_circlepath_def Let_def lv_def rcis_def 
                    pathstart_part_circlepath' pathfinish_part_circlepath')

lemma pathstart_mypath'_rcorner [simp]: "pathstart (mypath'_rcorner left \<epsilon>) = cis arcjunc"
  and pathfinish_mypath'_rcorner [simp]: "pathfinish (mypath'_rcorner left \<epsilon>) = rv vjunc"
  by (simp_all add: mypath'_rcorner_def pathstart_compose pathfinish_compose flip: cis_divide
               add: avoid_linepath_circlepath_def Let_def lv_def rv_def rcis_def divide_conv_cnj)

lemma valid_path_lcorner: "\<epsilon> \<in> {0..2} \<Longrightarrow> valid_path (mypath'_lcorner left \<epsilon>)"
  unfolding mypath'_lcorner_def by (intro valid_path_avoid_linepath_circlepath) auto

lemma valid_path_rcorner:
  assumes "\<epsilon> \<in> {0..2}"
  shows   "valid_path (mypath'_rcorner left \<epsilon>)"
proof -
  have "valid_path (uminus \<circ> (cnj \<circ>
          reversepath (avoid_linepath_circlepath left vjunc (pi - arcjunc) \<epsilon>)))"
    unfolding valid_path_cnj valid_path_uminus_comp valid_path_reversepath
    by (intro valid_path_avoid_linepath_circlepath) (use assms in auto)
  thus ?thesis
    by (simp add: mypath'_rcorner_def mypath'_lcorner_def o_def)
qed

lemma detour_rel_mypath'_lcorner:
  "detour_rel {} {\<^bold>\<rho>}
     (linepath (lv vjunc) \<^bold>\<rho> +++ part_circlepath 0 1 (2 / 3 * pi) (pi - arcjunc))
     (mypath'_lcorner False) (mypath'_lcorner True)"
  unfolding mypath'_lcorner_def lv_def modfun_rho_def times_divide_eq_left
  by (rule detour_rel_avoid_linepath_circlepath_right) (use vjunc arcjunc in auto)

lemma detour_rel_mypath'_rcorner:
  "detour_rel {} {\<^bold>\<rho> + 1}
     (part_circlepath 0 1 arcjunc (pi / 3)  +++ linepath (\<^bold>\<rho> + 1) (rv vjunc))
     (mypath'_rcorner False) (mypath'_rcorner True)"
proof -
  define h where "h = (\<lambda>x. -x) \<circ> cnj"
  have "detour_rel {\<^bold>\<rho>} {}
          (reversepath (linepath (lv vjunc) \<^bold>\<rho> +++ part_circlepath 0 1 (2 * pi / 3) (pi - arcjunc)))
          (\<lambda>\<epsilon>. reversepath (mypath'_lcorner False \<epsilon>))
          (\<lambda>\<epsilon>. reversepath (mypath'_lcorner True \<epsilon>))"
    using detour_rel_reverse [OF detour_rel_mypath'_lcorner] by simp
  also have "reversepath (linepath (lv vjunc) \<^bold>\<rho> +++ part_circlepath 0 1 (2 * pi / 3) (pi - arcjunc)) =
             part_circlepath 0 1 (pi - arcjunc) (2 * pi / 3) +++ linepath \<^bold>\<rho> (lv vjunc)"
    by (subst reversepath_joinpaths) 
       (simp_all add: rcis_def modfun_rho_def pathfinish_part_circlepath' pathstart_part_circlepath')
  finally have "detour_rel (h ` {}) (h ` {\<^bold>\<rho>})
                  (h \<circ> (part_circlepath 0 1 (pi - arcjunc) (2 * pi / 3) +++ linepath \<^bold>\<rho> (lv vjunc)))
                  (\<lambda>\<epsilon>. h \<circ> reversepath (mypath'_lcorner False \<epsilon>))
                  (\<lambda>\<epsilon>. h \<circ> reversepath (mypath'_lcorner True \<epsilon>))" 
    unfolding h_def o_assoc [symmetric] image_comp [symmetric]
    by (intro detour_rel_uminus detour_rel_cnj)
  also have "(\<lambda>\<epsilon>. h \<circ> reversepath (mypath'_lcorner True \<epsilon>)) = mypath'_rcorner True"
    by (simp add: mypath'_rcorner_def [abs_def] h_def mypath'_lcorner_def o_def)
  also have "(\<lambda>\<epsilon>. h \<circ> reversepath (mypath'_lcorner False \<epsilon>)) = mypath'_rcorner False"
    by (simp add: mypath'_rcorner_def [abs_def] h_def mypath'_lcorner_def o_def)
  also have "(h ` {\<^bold>\<rho>}) = {\<^bold>\<rho> + 1}"
    by (auto simp: h_def complex_eq_iff sin_60 cos_60 sin_120 cos_120)
  also have "h ` {} = {}"
    by auto
  also have "h \<circ> (part_circlepath 0 1 (pi - arcjunc) (2 * pi / 3) +++ linepath \<^bold>\<rho> (lv vjunc)) =
             (h \<circ> part_circlepath 0 1 (pi - arcjunc) (2 * pi / 3)) +++ (h \<circ> linepath \<^bold>\<rho> (lv vjunc))"
    by (simp add: path_compose_join)
  also have "h \<circ> linepath \<^bold>\<rho> (lv vjunc) =
             linepath (- cnj (cis ((2 * pi / 3)))) (rv vjunc)"
    by (simp add: h_def o_def fun_eq_iff linepath_cnj lv_def rv_def modfun_rho_def flip: linepath_minus)
  also have "h \<circ> part_circlepath 0 1 (pi - arcjunc) (2 * pi / 3) = part_circlepath 0 1 arcjunc (pi / 3)"
    by (simp add: h_def fun_eq_iff part_circlepath_cnj minus_part_circlepath)
  also have "- cnj (cis (2 * pi / 3)) = \<^bold>\<rho> + 1"
    by (auto simp: complex_eq_iff sin_60 cos_60 sin_120 cos_120)
  finally show ?thesis .
qed


subsection \<open>Putting everything together\<close>

definition mypath' where
  "mypath' left \<epsilon> = (
      mypath'_lcorner left \<epsilon> +++
      mypath'_arc left \<epsilon> +++
      mypath'_rcorner left \<epsilon> +++
      mypath'_vert left vjunc b ys \<epsilon> +++
      linepath (rv b) (lv b) +++
      mypath'_vert' left vjunc b ys \<epsilon>)"

definition mypath_shifted :: "real \<Rightarrow> complex" where
  "mypath_shifted =
     (linepath (lv vjunc) \<^bold>\<rho> +++ 
      part_circlepath 0 1 (2/3*pi) (pi - arcjunc)) +++
      part_circlepath 0 1 (pi - arcjunc) arcjunc +++
     (part_circlepath 0 1 arcjunc (pi / 3) +++
      linepath (\<^bold>\<rho> + 1) (rv vjunc)) +++
     linepath (rv vjunc) (rv b) +++
     linepath (rv b) (lv b) +++
     linepath (lv b) (lv vjunc)"

lemma valid_path_mypath_shifted: "valid_path mypath_shifted"
  unfolding mypath_shifted_def
  by (intro valid_path_join valid_path_linepath valid_path_part_circlepath)
     (simp_all add: complex_eq_iff cos_60 sin_60 cos_120 sin_120
                    pathfinish_part_circlepath' pathstart_part_circlepath')

lemma eq_loops_mypath_shifted: "mypath b \<equiv>\<^sub>\<circle> mypath_shifted"
proof -
  have "mypath b \<equiv>\<^sub>p
          (part_circlepath 0 1 (2/3*pi) (pi - arcjunc) +++
           part_circlepath 0 1 (pi - arcjunc) arcjunc +++
           part_circlepath 0 1 arcjunc (1/3*pi)) +++
          (linepath (\<^bold>\<rho> + 1) (1 / 2 + vjunc *\<^sub>R \<i>) +++
           linepath (1 / 2 + vjunc *\<^sub>R \<i>) (1 / 2 + b *\<^sub>R \<i>)) +++
          linepath (1 / 2 + b *\<^sub>R \<i>) (-1 / 2 + b *\<^sub>R \<i>) +++
          (linepath (-1 / 2 + b *\<^sub>R \<i>) (-1 / 2 + vjunc *\<^sub>R \<i>) +++
           linepath (-1 / 2 + vjunc *\<^sub>R \<i>) \<^bold>\<rho>)"
    unfolding mypath_def using vjunc vjunc_pos arcjunc
    by (intro eq_paths_join eq_paths_refl eq_paths_linepaths'
              eq_paths_joinpaths_part_circlepath')
       (auto simp: rcis_def complex_eq_iff sin_60 cos_60 closed_segment_eq_real_ivl
                   closed_segment_same_Re pathfinish_part_circlepath' pathstart_part_circlepath')
  also have "\<dots> \<equiv>\<^sub>\<circle> mypath_shifted"
    unfolding mypath_shifted_def 
    by path (simp_all add: complex_eq_iff sin_60 cos_60 sin_120 cos_120 lv_def rv_def)
  finally show ?thesis .
qed

lemma eventually_detour:
  "eventually (\<lambda>\<epsilon>. detour \<epsilon> I X P (mypath b) mypath_shifted (mypath' True \<epsilon>)) (at_right 0)"
proof (rule detour_ccw)
  show "mypath b \<equiv>\<^sub>\<circle> mypath_shifted"
    by (fact eq_loops_mypath_shifted)
  show "simple_loop_ccw (mypath b)"
    using b_gt simple_loop_ccw_mypath [of b] by simp
  show "P \<inter> path_image (mypath b) = {}"
    unfolding P_def using b_gt subset_zeros_poles
    by (subst path_image_mypath_conv_frontier)
       (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl frontier_std_fund_region)

  show "closed P"
  proof -
    have *: "A - frontier \<R>\<^sub>\<Gamma> sparse_in {z. 0 < Im z}"
      using sparse_A by (rule sparse_in_subset2) auto
    have "closed (-({z. Im z > 0} - (A - frontier \<R>\<^sub>\<Gamma>)))"
      by (rule closed_Compl open_diff_sparse_pts open_halfspace_Im_gt *)+
    also have "\<dots> = P"
      by (auto simp: P_def)
    finally show "closed P" .
  qed

  have eq1: "complex_of_real (Im z) * \<i> - 1 / 2 = z" if "Re z = - 1 / 2" for z
    using that by (auto simp: complex_eq_iff)
  have "lv ` Y = S_l"
    by (auto simp: S_l_def Y_def lv_def complex_eq_iff scaleR_conv_of_real eq1)
  hence [simp]: "lv ` Y = S_l"
    by (auto simp: Y_def S_l_def lv_def complex_eq_iff)
  have "rv ` Y = (+) 1 ` lv ` Y"
    unfolding image_image by (intro image_cong) (auto simp: lv_def rv_def)
  hence [simp]: "rv ` Y = (+) 1 ` S_l"
    by simp
  have [simp]: "x \<noteq> 0" if "x \<in> \<R>\<^sub>\<Gamma>'" for x
    using that by (auto simp: in_std_fund_region'_iff)
  have [simp]: "sgn z = z" if "norm z = 1" for z :: complex
    using that by (simp add: complex_sgn_def)
  have [simp]: "S_arc = cis ` \<Phi> \<union> cis ` (\<lambda>x. pi - x) ` \<Phi>"
    by (rule S_arc_decompose)

  have "detour_rel
          ({} \<union> cis ` (\<lambda>x. pi - x) ` \<Phi> \<union> {} \<union> {} \<union> {} \<union> lv ` set ys)
          ({\<^bold>\<rho>} \<union> insert \<i> (cis ` \<Phi>) \<union> {\<^bold>\<rho>+1} \<union> rv ` set ys \<union> {} \<union> {})
          mypath_shifted (mypath' False) (mypath' True)"
    unfolding mypath_shifted_def mypath'_def Un_assoc
    by (intro detour_rel_join detour_rel_mypath'_lcorner detour_rel_mypath'_rcorner
              detour_rel_arc detour_rel_mypath'_vert detour_rel_mypath'_vert'
              detour_rel_refl sorted1 sorted2)
       (auto simp: pathfinish_part_circlepath' pathstart_part_circlepath')
  thus "detour_rel I X mypath_shifted (mypath' False) (mypath' True)"
    by (simp add: I_def X_def insert_commute Un_ac phis'_def phis ys image_Un)
qed (fact valid_path_mypath_shifted)

lemmas valid_intros =
  valid_path_join valid_path_lcorner valid_path_rcorner
  valid_path_mypath'_vert' valid_path_mypath'_vert

lemmas path_intros = valid_intros [THEN valid_path_imp_path]

lemma A_decompose: "A \<subseteq> I \<union> X \<union> P"
proof
  fix z assume z: "z \<in> A"
  show "z \<in> I \<union> X \<union> P"
  proof (cases "z \<in> frontier \<R>\<^sub>\<Gamma>")
    case False
    hence "z \<in> P"
      using z by (auto simp: P_def)
    thus ?thesis by blast
  next
    case True
    hence z': "Im z > 0" "norm z \<ge> 1"
      using True by (auto simp: frontier_std_fund_region)
    hence [simp]: "z \<noteq> 0"
      by auto
    consider "Re z = 1 / 2" | "Re z = -1 / 2" | "norm z = 1" "\<bar>Re z\<bar> < 1 / 2"
      using True unfolding frontier_std_fund_region
      by (force simp: abs_if split: if_splits)
    thus ?thesis
    proof cases
      assume z'': "Re z = -1 / 2"
      have "z \<in> I \<union> X"
        using z'' z' \<open>z \<in> A\<close> \<open>Im z > 0\<close>
        by (auto simp: I_def X_def S_l_def closure_std_fund_region)
      thus ?thesis by blast
    next
      assume z'': "Re z = 1 / 2"
      define y where "y = Im z"
      have z_eq: "z = 1 / 2 + y * \<i>"
        by (simp add: complex_eq_iff y_def z'')
      have norm_z_minus_1: "norm (z - 1) = norm z"
        by (simp add: norm_complex_def z_eq)
      show ?thesis
      proof (cases "z = \<^bold>\<rho> + 1")
        case False
        hence "z - 1 \<noteq> \<^bold>\<rho>"
          by Groebner_Basis.algebra
        hence "z - 1 \<in> S_l"
          using \<open>z \<in> A\<close> z' norm_z_minus_1 A_invariant1[of "z - 1"]
          by (auto simp: S_l_def closure_std_fund_region z'' )
        hence "z \<in> (+) 1 ` S_l"
          by (rule rev_image_eqI) auto
        thus ?thesis
          by (auto simp: X_def)
      qed (auto simp: X_def)
    next
      assume z'': "norm z = 1" "\<bar>Re z\<bar> < 1 / 2"
      show ?thesis
      proof (cases "z = \<i>")
        case False
        hence "z \<in> S_arc"
          using z \<open>z \<in> frontier _\<close> z'' by (auto simp: S_arc_def frontier_def)
        also note S_arc_decompose
        finally show ?thesis
          by (auto simp: X_def I_def)
      qed (auto simp: X_def)
    qed
  qed
qed

lemma Int_cong1: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<longleftrightarrow> x \<in> C) \<Longrightarrow> A \<inter> B = A \<inter> C"
  by blast

lemma S_l_in_region: "S_l \<subseteq> \<R>\<^sub>\<Gamma>'"
  using closure_std_fund_region_Im_pos
  unfolding S_l_def closure_std_fund_region std_fund_region'_def
  by (auto simp: in_std_fund_region_iff)

lemma S_r_not_in_region: "(+) 1 ` S_l \<inter> \<R>\<^sub>\<Gamma>' = {}"
  using closure_std_fund_region_Im_pos
  unfolding S_l_def closure_std_fund_region std_fund_region'_def
  by (auto simp: in_std_fund_region_iff)

lemma S_arc_left_in_region: "(\<lambda>\<phi>. cis (pi - \<phi>)) ` \<Phi> \<subseteq> \<R>\<^sub>\<Gamma>'"
proof safe
  fix \<phi> assume "\<phi> \<in> \<Phi>"
  hence "\<phi> \<in> {pi/3<..<pi/2}"
    using \<Phi>_subset by auto
  thus "cis (pi - \<phi>) \<in> \<R>\<^sub>\<Gamma>'"
    by (subst cis_in_std_fund_region'_iff) auto
qed

lemma S_arc_right_not_in_region: "cis ` \<Phi> \<inter> \<R>\<^sub>\<Gamma>' = {}"
proof safe
  fix \<phi> assume "\<phi> \<in> \<Phi>" "cis \<phi> \<in> \<R>\<^sub>\<Gamma>'"
  hence "\<phi> \<in> {pi/3<..<pi/2}"
    using \<Phi>_subset by auto
  hence "cis \<phi> \<notin> \<R>\<^sub>\<Gamma>'"
    by (subst cis_in_std_fund_region'_iff) auto
  with \<open>cis \<phi> \<in> \<R>\<^sub>\<Gamma>'\<close> show "cis \<phi> \<in> {}"
    by contradiction
qed

lemma I_subset_region: "I \<subseteq> \<R>\<^sub>\<Gamma>'"
  unfolding I_def using S_arc_left_in_region S_l_in_region by auto

lemma X_inter_region_eq: "X \<inter> \<R>\<^sub>\<Gamma>' = {\<^bold>\<rho>, \<i>}"
  unfolding X_def using S_arc_right_not_in_region S_r_not_in_region 
  by auto

definition err :: "real \<Rightarrow> complex" where
  "err \<epsilon> = k * \<i> * (pi / 6 - 4 * arcsin (\<epsilon> / 2))"

lemma eventually_between_0_and_onehalf:
  "eventually (\<lambda>x. x \<in> {0<..<1/2}) (at_right (0 :: real))"
  by (intro eventually_at_right_real) auto

lemma integral_eq1:
  "eventually (\<lambda>\<epsilon>. (\<Sum>p\<leftarrow>[mypath'_circ1 \<epsilon>, mypath'_circ2 \<epsilon>, mypath'_circ3 \<epsilon>, mypath'_line b].
                contour_integral p f) + err \<epsilon> = 
                of_real (2 * pi) * \<i> * (\<Sum>z\<in>A \<inter> \<R>\<^sub>\<Gamma>'-{\<i>, \<^bold>\<rho>}. zorder g z)) (at_right 0)"
  using eventually_detour eventually_between_0_and_onehalf
proof eventually_elim
  case (elim \<epsilon>)
  interpret detour \<epsilon> I X P "mypath b" mypath_shifted "mypath' True \<epsilon>"
    by (rule elim)
  have [simp]: "valid_path (mypath'_arc True \<epsilon>)"
    using valid unfolding mypath'_def by auto
  hence [simp]: "path (mypath'_arc True \<epsilon>)"
    by (rule valid_path_imp_path)
  have [simp]: "cnj \<^bold>\<rho> = -\<^bold>\<rho> - 1"
    by (simp add: complex_eq_iff cos_60 sin_60)
  note [simp] = pathfinish_part_circlepath' pathstart_part_circlepath'

  have "arcsin (\<epsilon> / 2) > 0"
    using elim(2) by (auto intro!: arcsin_pos)
  moreover have "arcsin (\<epsilon> / 2) < arcsin (1 / 2)"
    using elim by (subst arcsin_less_mono) auto
  ultimately have arcsin: "arcsin (\<epsilon> / 2) > 0" "arcsin (\<epsilon> / 2) < pi / 6"
    by auto

  have "path_image (mypath' True \<epsilon>) \<subseteq> {z. Im z > 0}"
    using P_not_on_path by (force simp: P_def)
  moreover have "path_image (mypath' True \<epsilon>) \<inter> A = {}"
    using A_decompose I_not_on_path X_not_on_path P_not_on_path by blast
  ultimately have subset: "path_image (mypath' True \<epsilon>) \<subseteq> {z. Im z > 0} - A"
    by blast

  have subset': "path_image p \<subseteq> {z. Im z > 0} - A" if "p \<le>\<^sub>p mypath' True \<epsilon>" for p
    using that is_subpath_imp_path_image_subset subset by blast

  define \<beta> where "\<beta> = pi / 3 + arcsin (\<epsilon> / 2)"
  define err1 where "err1 = k * \<i> * (pi/3 + 2 * arcsin (\<epsilon> / 2) - arcjunc)"
  define err2 where "err2 = k * \<i> * (arcjunc - arcjunc')"
  define err3 where "err3 = k * \<i> * (arcjunc' + 2 * arcsin (\<epsilon> / 2) - pi / 2)"

  define plc where "plc = mypath'_lcorner True \<epsilon>"
  define plc' where "plc' = part_circlepath \<^bold>\<rho> \<epsilon> (pi / 2) (pi / 6 - arcsin (\<epsilon> / 2))"

  define prc where "prc = mypath'_rcorner True \<epsilon>"
  define prc' where "prc' = (\<lambda>z. -z) \<circ> (cnj \<circ> reversepath plc')"

  define pa where "pa = mypath'_arc True \<epsilon>"
  define pam2 where "pam2 = part_circlepath \<i> \<epsilon> (pi + arcsin (\<epsilon> / 2)) (- arcsin (\<epsilon> / 2))"

  define pr where "pr = mypath'_vert True vjunc b ys \<epsilon>"
  define pu where "pu = linepath (rv b) (lv b)"
  define pl where "pl = mypath'_vert' True vjunc b ys \<epsilon>"
  note defs = plc_def pa_def prc_def pr_def pu_def pl_def
  write contour_integral ("\<integral>\<^sub>c")
  have [simp, intro]: "valid_path plc"  "valid_path prc"
    unfolding defs using elim by (auto intro!: valid_intros)
  note [simp] = valid_path_cnj contour_integral_negatepath contour_integral_cnj
                contour_integral_reversepath contour_integral_translate
                rcis_def scaleR_conv_of_real
  have [simp]: "cnj (cis (pi * 2 / 3)) = -cis (pi / 3)"
    by (auto simp: complex_eq_iff cos_120' sin_120' cos_60 sin_60)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1

  have inside_eq:"A \<inter> inside (path_image (mypath' True \<epsilon>)) 
          = A \<inter> (\<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>})"
  proof (intro Int_cong1)
    fix z assume "z \<in> A"
    hence "Im z > 0" "Im z < b"
      using subset_zeros_poles by auto
    from \<open>z \<in> A\<close> have "z \<in> I \<union> X \<union> P"
      using A_decompose by blast
    thus "z \<in> inside (path_image (mypath' True \<epsilon>)) \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>}"
    proof (elim UnE)
      assume z: "z \<in> I"
      hence "z \<in> inside (path_image (mypath' True \<epsilon>))"
        using I_inside by auto
      moreover from z have "z \<notin> {\<^bold>\<rho>, \<i>}"
        using I_X_disjoint \<open>z \<in> I\<close> by (auto simp: X_def)
      moreover have "z \<in> \<R>\<^sub>\<Gamma>'"
        using I_subset_region \<open>z \<in> I\<close> by auto
      ultimately show ?thesis by blast
    next
      assume z: "z \<in> X"
      hence "z \<in> outside (path_image (mypath' True \<epsilon>))"
        using X_outside by auto
      hence "z \<notin> inside (path_image (mypath' True \<epsilon>))"
        by (meson disjoint_iff inside_Int_outside)
      moreover have "z \<notin> \<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>}"
        using \<open>z \<in> X\<close> X_inter_region_eq by auto
      ultimately show ?thesis by blast
    next
      assume z: "z \<in> P"
      hence "z \<notin> {\<^bold>\<rho>, \<i>}"
        using X_P_disjoint unfolding X_def by blast
      hence "z \<in> inside (path_image (mypath' True \<epsilon>)) \<longleftrightarrow> z \<in> inside (path_image (mypath b))"
        by (intro P_inside_iff z)
      also have "inside (path_image (mypath b)) = \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
        by (intro inside_mypath b_gt)
      also have "z \<in> \<dots> \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>"
        using \<open>Im z < b\<close> by auto
      also from \<open>z \<in> P\<close> and \<open>Im z > 0\<close> have "z \<notin> frontier \<R>\<^sub>\<Gamma>"
        by (auto simp: P_def)
      hence "z \<in> \<R>\<^sub>\<Gamma> \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>'"
        by (rule in_std_fund_region'_not_on_frontier_iff [symmetric])
      finally show ?thesis
        using \<open>z \<notin> {\<^bold>\<rho>, \<i>}\<close> by blast
    qed
  qed

  have "contour_integral (mypath' True \<epsilon>) f =
          of_real (2 * pi) * \<i> * (\<Sum>z\<in>A \<inter> inside (path_image (mypath' True \<epsilon>)). zorder g z)"
    unfolding f_def 
  proof (rule argument_principle_ccw_analytic)
    show "eval_mero_uhp g analytic_on {z. Im z > 0} - A"
      using A_def analytic_on_eval_mero_uhp by force
    show "valid_path (mypath' True \<epsilon>)" by simp
    have "simple_loop_orientation (mypath' True \<epsilon>) = 1"
      using same_orientation simple_loop_orientation_mypath[of b] b_gt by simp
    thus "simple_loop_ccw (mypath' True \<epsilon>)"
      by (auto simp: simple_loop_orientation_def split: if_splits)
    show "path_image (mypath' True \<epsilon>) \<subseteq> {z. 0 < Im z} - A"
      by (rule subset)
    have "z \<notin> inside (path_image (mypath' True \<epsilon>))" if z: "Im z \<le> 0" for z
    proof -
      from z have "z \<in> P"
        by (auto simp: P_def)
      hence "winding_number (mypath' True \<epsilon>) z = winding_number (mypath b) z"
        using winding_number_unchanged by simp
      also have "\<dots> = 0"
        using z closure_std_fund_region_Im_pos by (intro winding_number_mypath_outside b_gt) auto
      finally show ?thesis
        using \<open>z \<in> P\<close> P_not_on_path simple_loop
              simple_closed_path_norm_winding_number_inside[of "mypath' True \<epsilon>" z] by auto
    qed
    thus "inside (path_image (mypath' True \<epsilon>)) \<subseteq> {z. 0 < Im z}"
      by force

    show "\<forall>p\<in>A. not_essential (eval_mero_uhp g) p"
      by (metis (no_types, lifting) A_def analytic_on_eval_mero_uhp 
          is_pole_imp_not_essential mem_Collect_eq mem_simps(3) 
          not_essential_analytic singletonD)
    show "A sparse_in {z. 0 < Im z}" using sparse_A by auto
    show "\<And>z. z \<in> {z. 0 < Im z} - A \<Longrightarrow> eval_mero_uhp g z \<noteq> 0"
      using A_def by blast
  qed
  also have "A \<inter> inside (path_image (mypath' True \<epsilon>)) = A \<inter> (\<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>})"
  proof (intro Int_cong1)
    fix z assume "z \<in> A"
    hence "Im z > 0" "Im z < b"
      using subset_zeros_poles by auto
    from \<open>z \<in> A\<close> have "z \<in> I \<union> X \<union> P"
      using A_decompose by blast
    thus "z \<in> inside (path_image (mypath' True \<epsilon>)) \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>}"
    proof (elim UnE)
      assume z: "z \<in> I"
      hence "z \<in> inside (path_image (mypath' True \<epsilon>))"
        using I_inside by auto
      moreover from z have "z \<notin> {\<^bold>\<rho>, \<i>}"
        using I_X_disjoint \<open>z \<in> I\<close> by (auto simp: X_def)
      moreover have "z \<in> \<R>\<^sub>\<Gamma>'"
        using I_subset_region \<open>z \<in> I\<close> by auto
      ultimately show ?thesis by blast
    next
      assume z: "z \<in> X"
      hence "z \<in> outside (path_image (mypath' True \<epsilon>))"
        using X_outside by auto
      hence "z \<notin> inside (path_image (mypath' True \<epsilon>))"
        by (meson disjoint_iff inside_Int_outside)
      moreover have "z \<notin> \<R>\<^sub>\<Gamma>' - {\<^bold>\<rho>, \<i>}"
        using \<open>z \<in> X\<close> X_inter_region_eq by auto
      ultimately show ?thesis by blast
    next
      assume z: "z \<in> P"
      hence "z \<notin> {\<^bold>\<rho>, \<i>}"
        using X_P_disjoint unfolding X_def by blast
      hence "z \<in> inside (path_image (mypath' True \<epsilon>)) \<longleftrightarrow> z \<in> inside (path_image (mypath b))"
        by (intro P_inside_iff z)
      also have "inside (path_image (mypath b)) = \<R>\<^sub>\<Gamma> \<inter> {z. Im z < b}"
        by (intro inside_mypath b_gt)
      also have "z \<in> \<dots> \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>"
        using \<open>Im z < b\<close> by auto
      also from \<open>z \<in> P\<close> and \<open>Im z > 0\<close> have "z \<notin> frontier \<R>\<^sub>\<Gamma>"
        by (auto simp: P_def)
      hence "z \<in> \<R>\<^sub>\<Gamma> \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>'"
        by (rule in_std_fund_region'_not_on_frontier_iff [symmetric])
      finally show ?thesis
        using \<open>z \<notin> {\<^bold>\<rho>, \<i>}\<close> by blast
    qed
  qed
  also have "\<dots> = A \<inter> \<R>\<^sub>\<Gamma>'-{\<^bold>\<rho>, \<i>}"
    by blast
  finally have "contour_integral (mypath' True \<epsilon>) f = 
                  of_real (2 * pi) * \<i> * of_int (sum (zorder g) (A \<inter> \<R>\<^sub>\<Gamma>'-{\<^bold>\<rho>, \<i>}))"
    by simp

  also have "contour_integral (mypath' True \<epsilon>) f =
          (\<integral>\<^sub>c plc f + \<integral>\<^sub>c prc f) + (\<integral>\<^sub>c pl f + \<integral>\<^sub>c pr f) + \<integral>\<^sub>c pa f + \<integral>\<^sub>c pu f"
    unfolding mypath'_def
  proof (path, fold mypath'_def)
    show "f analytic_on path_image (mypath' True \<epsilon>)"
      by (rule f_analytic) (use subset in auto)
  qed (use elim subset in \<open>auto intro!: valid_intros sorted1 sorted2 simp: defs add_ac\<close>)

  also have "\<integral>\<^sub>c pl f + \<integral>\<^sub>c pr f = 0"
  proof -
    have "\<integral>\<^sub>c pl f = - \<integral>\<^sub>c pr (\<lambda>x. f (x - 1))"
      unfolding pl_def pr_def mypath'_vert'_def
      by (subst contour_integral_reversepath)
         (auto intro!: valid_intros sorted1 sorted2 
               simp: contour_integral_translate valid_path_translation_eq)
    also have "\<integral>\<^sub>c pr (\<lambda>x. f (x - 1)) = \<integral>\<^sub>c pr f"
    proof (intro contour_integral_cong refl)
      fix z assume z: "z \<in> path_image pr"
      have "pr \<le>\<^sub>p mypath' True \<epsilon>"
        unfolding pr_def mypath'_def
        by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
      from subset' [OF this] and z have "Im z > 0 \<and> z \<notin> A"
        by auto
      with f_invariant(1)[of "z - 1"] A_invariant1[of "z - 1"] show "f (z - 1) = f z"
        by auto
    qed
    finally show ?thesis
      by simp
  qed

  also have "\<integral>\<^sub>c plc f + \<integral>\<^sub>c prc f = \<integral>\<^sub>c plc' f + \<integral>\<^sub>c prc' f - err1"
  proof -
    have ends1: "cis (2 * pi / 3) + complex_of_real \<epsilon> * cis (pi / 6 - arcsin (\<epsilon> / 2)) =
                 cis (2 * pi / 3 - 2 * arcsin (\<epsilon> / 2))"
    proof -
      interpret avoid_linepath_circlepath_locale vjunc "pi - arcjunc" \<epsilon>
        by unfold_locales (use elim in auto)
      show ?thesis
        using ends(1) ends(2)[of False] by (auto simp: bad_def \<alpha>_def \<beta>_def)
    qed

    define plc1 where "plc1 = linepath (- 1 / 2 + vjunc *\<^sub>R \<i>) (cis (2 * pi / 3) + \<epsilon> *\<^sub>R \<i>)"
    define plc2 where "plc2 = part_circlepath 0 1 (2 * pi / 3 - 2 * arcsin (\<epsilon> / 2)) (pi - arcjunc)"

    define prc1 where "prc1 = (\<lambda>x. -x) \<circ> (cnj \<circ> reversepath plc1)"
    define prc2 where "prc2 = (\<lambda>x. -x) \<circ> (cnj \<circ> reversepath plc2)"
    have [simp]: "pathfinish plc1 = pathstart plc'" "pathfinish plc' = pathstart plc2"
      using ends1 by (simp_all add: plc1_def plc'_def plc2_def modfun_rho_def)

    have plc_eq: "plc = plc1 +++ plc' +++ plc2"
      unfolding plc_def mypath'_lcorner_def avoid_linepath_circlepath_def Let_def
                plc1_def plc2_def plc'_def modfun_rho_def by simp

    have [simp, intro]: "valid_path plc1" "valid_path plc2"
      using \<open>valid_path plc\<close> unfolding plc_eq by auto

    have "plc1 \<le>\<^sub>p plc" unfolding plc_eq
      by path (use ends1 in \<open>auto simp: plc1_def plc'_def plc2_def modfun_rho_def\<close>)
    also have "plc \<le>\<^sub>p mypath' True \<epsilon>"
      unfolding plc_def mypath'_def
      by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
    finally have subpath_plc1: "plc1 \<le>\<^sub>p \<dots>" .

    have "plc2 \<le>\<^sub>p plc" unfolding plc_eq
      by path (use ends1 in \<open>auto simp: plc1_def plc'_def plc2_def modfun_rho_def\<close>)
    also have "plc \<le>\<^sub>p mypath' True \<epsilon>"
      unfolding plc_def mypath'_def
      by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
    finally have subpath_plc2: "plc2 \<le>\<^sub>p \<dots>" .

    have "prc = (\<lambda>z. - cnj z) \<circ> reversepath (plc1 +++ plc' +++ plc2)"
      using plc_eq by (simp add: prc_def plc_def mypath'_rcorner_def)
    also have "reversepath (plc1 +++ plc' +++ plc2) = reversepath (plc' +++ plc2) +++ reversepath plc1"
      by (subst reversepath_joinpaths)
         (auto simp: prc1_def o_def plc1_def plc'_def modfun_rho_def)
    also have "reversepath (plc' +++ plc2) = reversepath plc2 +++ reversepath plc'"
      using ends1 by (subst reversepath_joinpaths) (auto simp: plc'_def plc2_def modfun_rho_def)
    also have "(\<lambda>z. -cnj z) \<circ> (\<dots> +++ reversepath plc1) = (prc2 +++ prc') +++ prc1"
      unfolding path_compose_join by (simp add: prc2_def prc'_def prc1_def o_def)
    finally have prc_eq: "prc = (prc2 +++ prc') +++ prc1" .

    have "\<integral>\<^sub>c prc f = \<integral>\<^sub>c prc1 f + \<integral>\<^sub>c prc' f + \<integral>\<^sub>c prc2 f"
      unfolding prc_eq
    proof (path, fold prc_eq)
      have "prc \<le>\<^sub>p mypath' True \<epsilon>"
        unfolding prc_def mypath'_def
        by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
      from subset' [OF this] have "path_image prc \<subseteq> {z. Im z > 0} - A"
        by auto
      thus "f analytic_on path_image prc"
        by (rule f_analytic)
    qed (use ends1 in \<open>auto simp: prc1_def prc'_def prc2_def rcis_def pathfinish_compose
            pathstart_compose scaleR_conv_of_real modfun_rho_def valid_path_cnj plc2_def
            plc'_def plc1_def\<close>)

    also have "prc1 = (+) 1 \<circ> reversepath plc1"
      unfolding prc1_def plc1_def
      by (auto simp: complex_eq_iff cos_120' sin_120' cos_60 sin_60 fun_eq_iff
                     linepath_def reversepath_def algebra_simps scaleR_conv_of_real)
    also have "\<integral>\<^sub>c \<dots> f = - \<integral>\<^sub>c plc1 (\<lambda>x. f (x + 1))"
      by simp
    also have "\<integral>\<^sub>c plc1 (\<lambda>x. f (x + 1)) = \<integral>\<^sub>c plc1 f"
    proof (intro contour_integral_cong refl)
      fix z assume z: "z \<in> path_image plc1"
      from subset' [OF subpath_plc1] and z have "Im z > 0 \<and> z \<notin> A"
        by auto
      with f_invariant(1)[of z] show "f (z + 1) = f z"
        by blast
    qed

    also have "prc2 = uminus \<circ> (cnj \<circ> reversepath plc2)"
      unfolding prc2_def ..
    also have "\<dots> = (\<lambda>z. -1/z) \<circ> reversepath plc2"
      by (auto simp: fun_eq_iff reversepath_def plc2_def part_circlepath_altdef divide_conv_cnj)
    also have "\<integral>\<^sub>c \<dots> f = \<integral>\<^sub>c (reversepath plc2) (\<lambda>w. deriv (\<lambda>z. -1 / z) w * f (- 1 / w))"
    proof (rule contour_integral_comp_analyticW)
      show "(\<lambda>z. -1 / z) analytic_on {z. Im z > 0}"
        by (intro analytic_intros) auto
      from subset' [OF subpath_plc2] show "path_image (reversepath plc2) \<subseteq> {z. 0 < Im z}"
        by auto
    qed (auto simp: plc2_def)
    also have "\<dots> = - \<integral>\<^sub>c plc2 (\<lambda>w. deriv (\<lambda>z. -1 / z) w * f (- 1 / w))"
      by simp
    also have "\<integral>\<^sub>c plc2 (\<lambda>w. deriv (\<lambda>z. -1 / z) w * f (- 1 / w)) =
               \<integral>\<^sub>c plc2 (\<lambda>w. f w + k / w)"
    proof (intro contour_integral_cong refl)
      fix z assume "z \<in> path_image plc2"
      with subset'[OF subpath_plc2] have z: "Im z > 0 \<and> z \<notin> A"
        by auto
      from z have [simp]: "z \<noteq> 0"
        by auto
      from z have "deriv (\<lambda>z. -1 / z) z * f (-1 / z) = f (-1 / z) / z ^ 2"
        by (subst deriv_divide) auto
      also have "\<dots> = (f z * z ^ 2 + k * z) / z ^ 2"
        using z by (subst f_invariant(2)) auto
      also have "(f z * z\<^sup>2 + of_int k * z) / z\<^sup>2 = f z + k / z"
        by (simp add: field_simps power2_eq_square)
      finally show "deriv (\<lambda>z. -1 / z) z * f (-1 / z) = f z + k / z" .
    qed
    also have "\<dots> = \<integral>\<^sub>c plc2 f + \<integral>\<^sub>c plc2 (\<lambda>w. k / w)"
      using subset'[OF subpath_plc2]
      by (subst contour_integral_add)
         (auto intro!: analytic_imp_contour_integrable analytic_intros f_analytic)
    also have "\<integral>\<^sub>c plc2 (\<lambda>w. k / w) = k * ln (pathfinish plc2) - k * ln (pathstart plc2)"
      (is "_ = ?rhs")
    proof -
      have "((\<lambda>w. k / w) has_contour_integral ?rhs) plc2"
      proof (rule contour_integral_primitive)
        show "path_image plc2 \<subseteq> {z. 0 < Im z} - A"
          using subset'[OF subpath_plc2] .
      qed (auto intro!: derivative_eq_intros simp: field_simps elim!: nonpos_Reals_cases)
      thus ?thesis
        using contour_integral_unique by blast
    qed
    also have "\<dots> = k * (ln (cis (pi - arcjunc)) - ln (cis (2 * pi / 3 - 2 * arcsin (\<epsilon> / 2))))"
      by (simp add: plc2_def algebra_simps)
    also have "\<dots> = err1"
      using arcjunc arcsin by (subst (1 2) ln_cis) (auto simp: field_simps err1_def)
    finally have int_prc_eq: "\<integral>\<^sub>c prc f = \<integral>\<^sub>c prc' f - \<integral>\<^sub>c plc1 f - \<integral>\<^sub>c plc2 f - err1"
      by simp

    have "\<integral>\<^sub>c plc f = \<integral>\<^sub>c plc1 f + \<integral>\<^sub>c plc' f + \<integral>\<^sub>c plc2 f"
      unfolding plc_eq
    proof (path, fold plc_eq)
      have "plc \<le>\<^sub>p mypath' True \<epsilon>"
        unfolding plc_def mypath'_def
        by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
      from subset' [OF this] have "path_image plc \<subseteq> {z. Im z > 0} - A"
        by auto
      thus "f analytic_on path_image plc"
        by (rule f_analytic)
    qed (use ends1 in \<open>auto simp: plc1_def plc'_def plc2_def rcis_def
                                  scaleR_conv_of_real modfun_rho_def\<close>)

    with int_prc_eq show ?thesis
      by simp
  qed

  also have "\<integral>\<^sub>c pa f = \<integral>\<^sub>c pam2 f - err2 - err3"
  proof -
    define pal where "pal = mypath'_arcl True (\<epsilon> / 2)"
    define pam where "pam = mypath'_arcm True \<epsilon>"
    define par where "par = mypath'_arcr True (\<epsilon> / 2)"
    have val [simp, intro]: "valid_path pal" "valid_path par" "valid_path pam"
      using \<open>valid_path (mypath'_arc True \<epsilon>)\<close>
      unfolding mypath'_arc_def pal_def par_def pam_def by auto
    hence [simp]: "path pal" "path par" "path pam"
      using valid_path_imp_path by blast+
    have pa_eq: "pa = pal +++ pam +++ par"
      by (simp add: pa_def pal_def pam_def par_def mypath'_arc_def)
    have [simp]: "pathfinish pal = pathstart pam" "pathfinish pam = pathstart par"
      by (simp_all add: pal_def pam_def par_def)

    define pam1 where "pam1 = part_circlepath 0 1 (pi - arcjunc') (pi / 2 + 2 * arcsin (\<epsilon> / 2))"
    define pam3 where "pam3 = part_circlepath 0 1 (pi / 2 - 2 * arcsin (\<epsilon> / 2)) arcjunc'"
    interpret pam: avoid_part_circlepath_locale 0 1 "pi - arcjunc'" arcjunc' "pi/2" \<epsilon>
      by standard (use elim arcjunc(1) arcjunc'(1) in auto)
    have pam_eq: "pam = pam1 +++ pam2 +++ pam3"
      using arcjunc(1) arcjunc'(1)
      by (simp add: pam_def pam1_def pam2_def pam3_def mypath'_arcm_def
                    avoid_part_circlepath_def Let_def)
    have ends: "\<i> + complex_of_real \<epsilon> * cis (- arcsin (\<epsilon> / 2)) = cis (pi / 2 - 2 * arcsin (\<epsilon> / 2))"
               "cis (pi / 2 + 2 * arcsin (\<epsilon> / 2)) = \<i> + complex_of_real \<epsilon> * cis (pi + arcsin (\<epsilon> / 2))"
      using pam.ends(1)[of True] pam.ends(2) arcjunc(1) arcjunc'(1)
      by (auto simp: pam.bad_def pam.s_def pam.\<alpha>_def pam.\<beta>_def)

    have "par \<le>\<^sub>p pa"
      unfolding pa_eq by path auto
    also have "\<dots> \<le>\<^sub>p mypath' True \<epsilon>"
      unfolding pa_def mypath'_def
      by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
    finally have "par \<le>\<^sub>p mypath' True \<epsilon>" .
    from subset' [OF this] have par_subset: "path_image (reversepath par) \<subseteq> {z. Im z > 0} - A"
      by auto

    have "pam \<le>\<^sub>p pa"
      unfolding pa_eq by path auto
    also have "\<dots> \<le>\<^sub>p mypath' True \<epsilon>"
      unfolding pa_def mypath'_def
      by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
    finally have "pam \<le>\<^sub>p mypath' True \<epsilon>" .
    from subset' [OF this] have pam_subset: "path_image (reversepath pam) \<subseteq> {z. Im z > 0} - A"
      by auto

    have "pam1 \<le>\<^sub>p pam"
      unfolding pam_eq by path (use ends in \<open>auto simp: pam1_def pam2_def pam3_def\<close>)
    also have "\<dots> \<le>\<^sub>p mypath' True \<epsilon>"
      by fact
    finally have "pam1 \<le>\<^sub>p mypath' True \<epsilon>" .
    from subset' [OF this] have pam1_subset: "path_image pam1 \<subseteq> {z. Im z > 0} - A"
      by auto

    have valid_pam1 [simp, intro]: "valid_path pam1"
      unfolding pam1_def by auto
    have valid_pam1': "valid_path ((\<lambda>z. -(1/z)) \<circ> pam1)"
      by (intro valid_path_compose_holomorphic[OF _ _ _ pam1_subset] holomorphic_intros)
         (auto simp: open_halfspace_Im_gt pam1_def)

    have "\<integral>\<^sub>c pa f = \<integral>\<^sub>c pal f + \<integral>\<^sub>c par f + \<integral>\<^sub>c pam f"
      unfolding pa_def mypath'_arc_def
    proof (path, fold pa_def mypath'_arc_def)
      have "pa \<le>\<^sub>p mypath' True \<epsilon>"
        unfolding pa_def mypath'_def
        by path (use elim in \<open>auto intro!: path_intros sorted1 sorted2\<close>)
      from subset' [OF this] have "path_image pa \<subseteq> {z. Im z > 0} - A"
        by auto
      thus "f analytic_on path_image pa"
        by (rule f_analytic)
    qed (use val[unfolded pal_def par_def pam_def] in \<open>auto simp: pal_def par_def pam_def\<close>)
    also have "\<integral>\<^sub>c pal f = - \<integral>\<^sub>c par (\<lambda>w. deriv (\<lambda>z. - (1 / z)) w * f (- (1 / w)))"
      unfolding pal_def mypath'_arcl_def par_def [symmetric]
    proof (subst contour_integral_comp_analyticW)
      show "(\<lambda>z. -(1/z)) analytic_on {z. Im z > 0}"
        by (auto simp: open_halfspace_Im_gt intro!: analytic_intros)
    qed (use par_subset in auto)
    also have "\<integral>\<^sub>c par (\<lambda>w. deriv (\<lambda>z. - (1 / z)) w * f (- (1 / w))) = \<integral>\<^sub>c par (\<lambda>w. f w + k / w)"
    proof (intro contour_integral_cong refl)
      fix z assume "z \<in> path_image par"
      with par_subset have z: "Im z > 0" "z \<notin> A"
        by auto
      from z have [simp]: "z \<noteq> 0"
        by auto
      from z have "deriv (\<lambda>z. -1 / z) z * f (-1 / z) = f (-1 / z) / z ^ 2"
        by (subst deriv_divide) auto
      also have "\<dots> = (f z * z ^ 2 + k * z) / z ^ 2"
        using z by (subst f_invariant(2)) auto
      also have "(f z * z\<^sup>2 + of_int k * z) / z\<^sup>2 = f z + k / z"
        by (simp add: field_simps power2_eq_square)
      finally show "deriv (\<lambda>z. - (1 / z)) z * f (- (1 / z)) = f z + of_int k / z"
        by simp
    qed
    also have "\<dots> = \<integral>\<^sub>c par f + \<integral>\<^sub>c par (\<lambda>w. k / w)"
      using par_subset
      by (subst contour_integral_add)
         (auto intro!: analytic_imp_contour_integrable analytic_intros f_analytic)
    also have "\<integral>\<^sub>c par (\<lambda>w. k / w) = k * ln (pathfinish par) - k * ln (pathstart par)"
      (is "_ = ?rhs")
    proof -
      have "((\<lambda>w. k / w) has_contour_integral ?rhs) par"
      proof (rule contour_integral_primitive)
        show "path_image par \<subseteq> {z. 0 < Im z} - A"
          using par_subset by auto
      qed (auto intro!: derivative_eq_intros simp: field_simps elim!: nonpos_Reals_cases)
      thus ?thesis
        using contour_integral_unique by blast
    qed
    also have "\<dots> = k * (ln (cis arcjunc) - ln (cis arcjunc'))"
      by (simp add: par_def algebra_simps)
    also have "\<dots> = err2"
      using arcjunc arcjunc' by (subst (1 2) ln_cis) (auto simp: field_simps err2_def)

    also have "\<integral>\<^sub>c pam f = \<integral>\<^sub>c pam1 f + \<integral>\<^sub>c pam2 f + \<integral>\<^sub>c pam3 f"
      unfolding pam_eq
    proof (path, fold pam_eq)
      show "f analytic_on path_image pam"
        by (rule f_analytic) (use pam_subset in auto)
    qed (use ends in \<open>auto simp: pam1_def pam2_def pam3_def\<close>)
    also have "pam3 = reversepath ((\<lambda>z. -(1/z)) \<circ> pam1)"
      by (auto simp: pam3_def pam1_def fun_eq_iff part_circlepath_altdef linepath_def ring_distribs
                     add_divide_distrib diff_divide_distrib reversepath_def mult_ac
               simp flip: cis_mult cis_divide)
    also have "\<integral>\<^sub>c \<dots> f = -\<integral>\<^sub>c ((\<lambda>z. -(1/z)) \<circ> pam1) f"
      by (subst contour_integral_reversepath) (use valid_pam1' in auto)
    also have "\<integral>\<^sub>c ((\<lambda>z. -(1/z)) \<circ> pam1) f = \<integral>\<^sub>c pam1 (\<lambda>w. deriv (\<lambda>z. - (1 / z)) w * f (- (1 / w)))"
    proof (subst contour_integral_comp_analyticW)
      show "(\<lambda>z. -(1/z)) analytic_on {z. Im z > 0}"
        by (auto simp: open_halfspace_Im_gt intro!: analytic_intros)
    qed (use pam1_subset in \<open>auto simp: pam1_def\<close>)
    also have "\<dots> = \<integral>\<^sub>c pam1 (\<lambda>w. f w + k / w)"
    proof (intro contour_integral_cong refl)
      fix z assume "z \<in> path_image pam1"
      with pam1_subset have z: "Im z > 0" "z \<notin> A"
        by auto
      from z have [simp]: "z \<noteq> 0"
        by auto
      from z have "deriv (\<lambda>z. -1 / z) z * f (-1 / z) = f (-1 / z) / z ^ 2"
        by (subst deriv_divide) auto
      also have "\<dots> = (f z * z ^ 2 + k * z) / z ^ 2"
        using z by (subst f_invariant(2)) auto
      also have "(f z * z\<^sup>2 + of_int k * z) / z\<^sup>2 = f z + k / z"
        by (simp add: field_simps power2_eq_square)
      finally show "deriv (\<lambda>z. - (1 / z)) z * f (- (1 / z)) = f z + of_int k / z"
        by simp
    qed
    also have "\<dots> = \<integral>\<^sub>c pam1 f + \<integral>\<^sub>c pam1 (\<lambda>w. k / w)"
      using pam1_subset
      by (subst contour_integral_add)
         (auto intro!: analytic_imp_contour_integrable analytic_intros f_analytic)
    also have "\<integral>\<^sub>c pam1 (\<lambda>w. k / w) = k * ln (pathfinish pam1) - k * ln (pathstart pam1)"
      (is "_ = ?rhs")
    proof -
      have "((\<lambda>w. k / w) has_contour_integral ?rhs) pam1"
      proof (rule contour_integral_primitive)
        show "path_image pam1 \<subseteq> {z. 0 < Im z} - A"
          using pam1_subset by auto
      qed (auto intro!: derivative_eq_intros simp: field_simps elim!: nonpos_Reals_cases)
      thus ?thesis
        using contour_integral_unique by blast
    qed
    also have "\<dots> = k * (ln (cis (pi / 2 + 2 * arcsin (\<epsilon> / 2))) - ln (cis (pi - arcjunc')))"
      by (simp add: pam1_def algebra_simps)
    also have "\<dots> = err3"
      using arcjunc' arcsin by (subst (1 2) ln_cis) (auto simp: field_simps err3_def)
    finally show ?thesis
      by simp
  qed

  also have "\<integral>\<^sub>c plc' f + \<integral>\<^sub>c prc' f - err1 + 0 + (\<integral>\<^sub>c pam2 f - err2 - err3) + \<integral>\<^sub>c pu f =
             \<integral>\<^sub>c plc' f + \<integral>\<^sub>c prc' f + \<integral>\<^sub>c pam2 f + \<integral>\<^sub>c pu f + -(err1 + err2 + err3)"
    by (simp add: algebra_simps)

  also have "-(err1 + err2 + err3) = err \<epsilon>"
    unfolding err1_def err2_def err3_def err_def by (simp add: field_simps)

  also have i_times_cis: "\<i> * cis x = cis (x + pi / 2)" for x
    by (simp flip: cis_mult)
  have "cnj (cis (pi / 3)) = -cis (2 * pi / 3)" "cis (5 / 6 * pi) = \<i> * cis (pi / 3)"
    by (simp_all add: complex_eq_iff cos_60 cos_120 sin_60 sin_120 i_times_cis)
  hence "prc' = part_circlepath (\<^bold>\<rho> + 1) \<epsilon> (5 * pi / 6 + arcsin (\<epsilon> / 2)) (pi / 2)"
    unfolding prc'_def plc'_def
    by (auto simp: fun_eq_iff part_circlepath_altdef linepath_def ring_distribs add_divide_distrib
                   diff_divide_distrib reversepath_def mult_ac divide_conv_cnj
             simp flip: cis_mult cis_divide )

  finally show ?case
    by (simp add: plc'_def pam2_def pu_def mypath'_circ1_def mypath'_circ2_def mypath'_circ3_def
                  mypath'_line_def add_ac rv_def lv_def insert_commute)
qed


lemma circ1:
  "((\<lambda>\<epsilon>. contour_integral (mypath'_circ1 \<epsilon>) f) \<longlongrightarrow> -of_int (zorder g \<^bold>\<rho>) * \<i> * pi / 3) (at_right 0)"
  unfolding mypath'_circ1_def f_def
proof (rule contour_integral_logderiv_part_circlepath_not_essential)
  have "\<^bold>\<rho> + 1 \<in> {z. Im z > 0}"
    by auto
  show "eval_mero_uhp g meromorphic_on {\<^bold>\<rho> + 1}"
    by (auto intro!: meromorphic_intros)
  show "eventually (\<lambda>w. g w \<noteq> 0) (at (\<^bold>\<rho> + 1))"
    using eval_mero_uhp_avoid_0[OF g_nonzero]
    by (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt)
  show "((\<lambda>\<epsilon>. 5 * pi / 6 + arcsin (\<epsilon> / 2)) \<longlongrightarrow> 5 * pi / 6) (at_right 0)"
    by (auto intro!: tendsto_eq_intros)
  show "((\<lambda>\<epsilon>::real. pi / 2) \<longlongrightarrow> pi / 2) (at_right 0)"
    by (rule tendsto_const)
  have "zorder g (\<^bold>\<rho> + 1) = zorder (\<lambda>w. g (w + 1)) \<^bold>\<rho>"
    by (simp add: zorder_shift' algebra_simps)
  also have "\<dots> = zorder g \<^bold>\<rho>"
  proof (rule zorder_cong)
    have "eventually (\<lambda>w. w \<in> ({w. Im w > 0} - (A - {\<^bold>\<rho>})) - {\<^bold>\<rho>}) (at \<^bold>\<rho>)"
      by (intro eventually_at_in_open open_A_compl_subset) auto
    thus "eventually (\<lambda>w. g (w + 1) = g w) (at \<^bold>\<rho>)"
      by eventually_elim (auto simp: g_plus1)
  qed auto
  finally show "-of_int (zorder g \<^bold>\<rho>) * \<i> * complex_of_real pi / 3 =
                  (real_of_int (zorder g (\<^bold>\<rho> + 1)) * (pi / 2 - 5 * pi / 6)) *\<^sub>R \<i>"
    by (simp add: scaleR_conv_of_real)
qed

lemma circ2:
  "((\<lambda>\<epsilon>. contour_integral (mypath'_circ2 \<epsilon>) f) \<longlongrightarrow> -of_int (zorder g \<^bold>\<rho>) * \<i> * pi / 3) (at_right 0)"
  unfolding mypath'_circ2_def f_def
proof (rule contour_integral_logderiv_part_circlepath_not_essential)
  have "\<^bold>\<rho> \<in> {z. Im z > 0}"
    by auto
  show "eval_mero_uhp g meromorphic_on {\<^bold>\<rho>}"
    by (auto intro!: meromorphic_intros)
  show "eventually (\<lambda>w. g w \<noteq> 0) (at \<^bold>\<rho>)"
    using eval_mero_uhp_avoid_0[OF g_nonzero]
    by (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt)
  show "((\<lambda>\<epsilon>::real. pi / 2) \<longlongrightarrow> pi / 2) (at_right 0)"
    by (rule tendsto_const)
  show "((\<lambda>\<epsilon>. pi / 6 - arcsin (\<epsilon> / 2)) \<longlongrightarrow> pi / 6) (at_right 0)"
    by (auto intro!: tendsto_eq_intros)
qed (auto simp: field_simps scaleR_conv_of_real)

lemma circ3:
  "((\<lambda>\<epsilon>. contour_integral (mypath'_circ3 \<epsilon>) f) \<longlongrightarrow> -of_int (zorder g \<i>) * \<i> * pi) (at_right 0)"
  unfolding mypath'_circ3_def f_def
proof (rule contour_integral_logderiv_part_circlepath_not_essential)
  have "\<i> \<in> {z. Im z > 0}"
    by auto
  show "eval_mero_uhp g meromorphic_on {\<i>}"
    by (auto intro!: meromorphic_intros)
  show "eventually (\<lambda>w. g w \<noteq> 0) (at \<i>)"
    using eval_mero_uhp_avoid_0[OF g_nonzero]
    by (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt)
  show "((\<lambda>\<epsilon>::real. pi + arcsin (\<epsilon> / 2)) \<longlongrightarrow> pi) (at_right 0)"
    by (auto intro!: tendsto_eq_intros)
  show "((\<lambda>\<epsilon>. -arcsin (\<epsilon> / 2)) \<longlongrightarrow> 0) (at_right 0)"
    by (auto intro!: tendsto_eq_intros)
qed (auto simp: field_simps scaleR_conv_of_real)

lemma err: "(err \<longlongrightarrow> k * \<i> * pi / 6) (at_right 0)"
  unfolding err_def by (auto intro!: tendsto_eq_intros)

lemma integral_eq2:
  "contour_integral (mypath'_line b) f =
     of_real (2 * pi) * \<i> * (-of_int k / 12 + of_int (zorder g \<^bold>\<rho>) / 3 + of_int (zorder g \<i>) / 2 +
       (\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>,\<^bold>\<rho>}. of_int (zorder g z)))"
proof -
  note [tendsto_intros] = circ1 circ2 circ3
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define I where
    "I = (\<lambda>\<epsilon>. (\<Sum>p\<leftarrow>[mypath'_circ1 \<epsilon>, mypath'_circ2 \<epsilon>, mypath'_circ3 \<epsilon>]. contour_integral p f) + err \<epsilon>)"
  define C1 where
    "C1 = -2 * \<i> * of_real pi * (of_int (zorder g \<^bold>\<rho>) / 3 + of_int (zorder g \<i>) / 2 - of_int k / 12)"
  define C2 where
    "C2 = of_real (2 * pi) * \<i> * (\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>,\<^bold>\<rho>}. of_int (zorder g z)) - contour_integral (mypath'_line b) f"

  have "C1 = C2"
  proof (rule tendsto_unique)
    show "(I \<longlongrightarrow> C1) (at_right 0)"
      unfolding sum_list.Cons sum_list.Nil list.map add_0_right C1_def I_def
      by (rule tendsto_eq_intros err refl)+ (auto simp: field_simps)
  next
    have "eventually (\<lambda>\<epsilon>. I \<epsilon> = C2) (at_right 0)"
      using integral_eq1 unfolding C2_def I_def by eventually_elim (auto simp: algebra_simps)
    thus "(I \<longlongrightarrow> C2) (at_right 0)"
      using tendsto_eventually by blast
  qed auto
  thus "contour_integral (mypath'_line b) f =
           of_real (2 * pi) * \<i> * (-of_int k / 12 + of_int (zorder g \<^bold>\<rho>) / 3 + of_int (zorder g \<i>) / 2 +
              (\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>,\<^bold>\<rho>}. of_int (zorder g z)))"
    by (simp add: C1_def C2_def algebra_simps)
qed

end


text \<open>Theorem 6.1\<close>
theorem MeForms_valence_formula:
  assumes "f \<in> MeForms[k] - {0}"
  shows "(\<Sum>z\<in>zeros_mero_uhp f \<union> poles_mero_uhp f - {\<i>,\<^bold>\<rho>}. real_of_int (zorder f z)) + 
           of_int (zorder f \<^bold>\<rho>) / 3 + of_int (zorder f \<i>) / 2 + of_int (zorder_at_ii_inf 1 f) =
           of_int k / 12"
proof -
  interpret meromorphic_form_full f k
  proof -
    interpret meromorphic_form f k UNIV
      using assms by auto
    show "meromorphic_form_full f k" ..
  qed
  from assms have [simp]: "f \<noteq> 0"
    by auto
  define f' where "f' = fourier_expansion (Suc 0) f"

  let ?\<gamma> = mypath'_line
  let ?ord = "\<lambda>z. zorder f z"
  define A where "A = {z. Im z > 0 \<and> (eval_mero_uhp f z = 0 \<or> is_pole f z)}"
  define h where "h = (\<lambda>b. contour_integral (?\<gamma> b) (\<lambda>z. deriv f z / f z))"
  define C where "C = 2 * pi * \<i> * ((\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>, \<^bold>\<rho>}. ?ord z) - k / 12 + ?ord \<^bold>\<rho> / 3 + ?ord \<i> / 2)"
  define g where "g = (\<lambda>z. deriv f z / f z)"
  define g' where "g' = (\<lambda>z. deriv f' z / f' z)"
  define circ where "circ = (\<lambda>b. part_circlepath 0 (exp (-2*pi*b)) pi (-pi))"
  define Z where "Z = zeros_mero_uhp f \<union> poles_mero_uhp f"

  let ?q = "to_q (Suc 0)"
  have [simp]: "deriv ?q z = 2 * complex_of_real pi * \<i> * ?q z" for z
    by (subst deriv_to_q) auto

  have "eventually (\<lambda>z. f z \<noteq> 0 \<and> \<not>is_pole f z \<and> Im z > 1) at_\<i>\<infinity>"
    using \<open>f \<noteq> 0\<close> by (intro eventually_conj eventually_neq_at_ii_inf eventually_no_poles_at_ii_inf eventually_at_ii_inf) auto
  then obtain b0 where b0: "\<And>z. Im z \<ge> b0 \<Longrightarrow> f z \<noteq> 0 \<and> \<not>is_pole f z \<and> Im z > 1"
    unfolding eventually_at_ii_inf_iff' by blast
  from b0[of "\<i> * of_real b0"] have "b0 > 1"
    by simp

  have "C = -2 * of_real pi * \<i> * of_int (zorder_at_ii_inf 1 f)"
  proof (rule tendsto_unique)
    show "(h \<longlongrightarrow> -2 * of_real pi * \<i> * of_int (zorder_at_ii_inf 1 f)) at_top"
    proof (rule Lim_transform_eventually)
      show "eventually (\<lambda>b. contour_integral (circ b) g' = h b) at_top"
        using eventually_gt_at_top[of 0] eventually_gt_at_top[of b0]
      proof eventually_elim
        case (elim b)
        have "contour_integral (?\<gamma> b) (\<lambda>z. deriv f z / f z) =
              contour_integral (?\<gamma> b)
                (\<lambda>z. deriv f' (?q z) / f' (?q z) * (of_real (2 * pi) * \<i> * ?q z))"
        proof (intro contour_integral_cong refl, goal_cases)
          case (1 z)
          hence [simp]: "Im z = b"
            by (auto simp: mypath'_line_def closed_segment_same_Im)
          have "deriv f' (?q z) / f' (?q z) * (complex_of_real (2 * pi) * \<i> * ?q z) =
                eval_mero_uhp (deriv_mero_uhp f) z / eval_mero_uhp f z"
            using elim b0[of z] unfolding f'_def by (subst deriv_fourier[OF _ _ refl]) auto
          also have "eval_mero_uhp (deriv_mero_uhp f) z = deriv (eval_mero_uhp f) z"
            using elim b0[of z]by (simp add: eval_deriv_mero_uhp)
          finally show ?case ..
        qed
        also have "\<dots> = contour_integral (?q \<circ> ?\<gamma> b) g'"
          unfolding g'_def
          by (subst contour_integral_comp_analyticW[of _ UNIV])
             (auto intro!: analytic_intros simp: mypath'_line_def mult_ac)
        also have "?q \<circ> ?\<gamma> b = circ b"
          unfolding circ_def
          apply (rule ext)
          apply (simp add: circ_def to_q_def o_def mypath'_line_def part_circlepath_def)
          apply (simp add: scaleR_conv_of_real algebra_simps linepath_def exp_add exp_diff exp_minus of_real_exp)
          apply (simp add: field_simps)
          done
        finally show ?case
          by (simp add: h_def)
      qed
    next
      show "((\<lambda>b. contour_integral (circ b) g') \<longlongrightarrow> -2 * of_real pi * \<i> * of_int (zorder_at_ii_inf 1 f)) at_top"
        unfolding circ_def g'_def
      proof (rule filterlim_compose, rule contour_integral_logderiv_part_circlepath_not_essential)
        show "filterlim (\<lambda>b::real. exp (-2 * pi * b)) (at_right 0) at_top"
          by real_asymp
        show "f' meromorphic_on {0}" unfolding f'_def
          by (intro meromorphic_intros) auto
        show "eventually (\<lambda>z. f' z \<noteq> 0) (at 0)" unfolding f'_def
          by (simp add: eventually_neq_fourier)
        show "-2 * of_real pi * \<i> * of_int (zorder_at_ii_inf 1 f) =
                (real_of_int (zorder f' 0) * (-pi - pi)) *\<^sub>R \<i>"
          using zorder_at_ii_inf_conv_fourier by (simp add: scaleR_conv_of_real f'_def)
      qed auto
    qed
  next
    have "eventually (\<lambda>b. A \<subseteq> {z. Im z < b}) at_top"
    proof -
      show ?thesis
        using eventually_gt_at_top[of b0]
      proof eventually_elim
        case (elim b)
        have "A \<subseteq> {z. Im z \<le> b0}"
          using b0 elim unfolding A_def
          by (force simp: inv_image_mero_uhp_def poles_mero_uhp_def)
        also have "\<dots> \<subseteq> {z. Im z < b}"
          using elim by force
        finally show ?case .
      qed
    qed
    hence "eventually (\<lambda>b. h b = C) at_top"
      using eventually_gt_at_top[of b0]
    proof eventually_elim
      case (elim b)
      interpret mypath_detour f k A b
      proof unfold_locales
        show "f \<noteq> 0"
          by fact
        show "b > 1"
          using elim \<open>b0 > 1\<close> by simp
        show "{z. 0 < Im z \<and> eval_mero_uhp f z = 0} \<union> {z. 0 < Im z \<and> is_pole (eval_mero_uhp f) z} 
                \<subseteq> {z. Im z \<in> {0<..<b}}"
          using not_is_pole_eval_mero_uhp_outside[of _ f] b0 elim by force
        show "A \<equiv> {z. 0 < Im z \<and> eval_mero_uhp f z = 0} \<union> {z. Im z > 0 \<and> is_pole (eval_mero_uhp f) z}"
          using not_is_pole_eval_mero_uhp_outside[of _ f] b0 elim unfolding A_def
          by (force intro!: eq_reflection)
      qed
      from integral_eq2 show ?case
        by (simp add: f_def h_def C_def algebra_simps)
    qed
    thus "(h \<longlongrightarrow> C) at_top"
      by (simp add: tendsto_eventually)
  qed auto

  hence "-of_int (zorder_at_ii_inf 1 f) = C / (2 * of_real pi * \<i>)"
    by simp
  also have "\<dots> = (\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>,\<^bold>\<rho>}. ?ord z) - k / 12 + ?ord \<^bold>\<rho> / 3 + ?ord \<i> / 2"
    by (simp add: C_def)
  also have "(\<Sum>z\<in>A\<inter>\<R>\<^sub>\<Gamma>'-{\<i>,\<^bold>\<rho>}. ?ord z) = (\<Sum>z\<in>Z-{\<i>,\<^bold>\<rho>}. ?ord z)"
  proof (intro sum.mono_neutral_right ballI)
    have "A \<inter> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>} \<subseteq> zeros_mero_uhp f \<union> poles_mero_uhp f"
      by (auto simp: A_def inv_image_mero_uhp_def poles_mero_uhp_def)
    moreover have "finite (zeros_mero_uhp f \<union> poles_mero_uhp f)"
      using \<open>f \<noteq> 0\<close> by auto
    ultimately show "finite (A \<inter> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>})"
      using finite_subset by blast
  next
    fix z assume z: "z \<in> A \<inter> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>} - (Z - {\<i>, \<^bold>\<rho>})"
    hence z': "Im z > 0" "z \<notin> Z"
      by (auto simp: in_std_fund_region'_iff)
    thus "zorder f z = 0"
      unfolding Z_def using z by (auto simp: inv_image_mero_uhp_def poles_mero_uhp_def)
  next
    have "z \<in> Z - {\<i>, \<^bold>\<rho>} \<longrightarrow> z \<in> A \<inter> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>}" for z
      using not_is_pole_eval_mero_uhp_outside[of z f]
      by (cases "Im z > 0")
         (auto simp: A_def Z_def inv_image_mero_uhp_def poles_mero_uhp_def in_std_fund_region'_iff)
    thus "Z - {\<i>, \<^bold>\<rho>} \<subseteq> A \<inter> \<R>\<^sub>\<Gamma>' - {\<i>, \<^bold>\<rho>}"
      by blast
  qed
  finally show ?thesis
    by (simp add: complex_eq_iff Z_def)
qed

lemma MeForms_valence_formula':
  assumes "f \<in> MeForms[k] - {0}"
  defines "C \<equiv> (\<Sum>z\<in>zeros_mero_uhp f \<union> poles_mero_uhp f - {\<i>, \<^bold>\<rho>}. zorder_mero_uhp f z)"
  shows   "12 * C + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> + 12 * zorder_at_ii_inf 1 f = k"
    (is "?lhs = _")
proof -
  have "12 * (real_of_int k / 12) = ?lhs"
    by (subst MeForms_valence_formula[OF assms(1), symmetric]) (simp add: algebra_simps C_def)
  also have "12 * (real_of_int k / 12) = k"
    by simp
  finally show ?thesis
    by linarith
qed

lemma MForms_valence_formula':
  assumes "f \<in> MForms[k] - {0}"
  defines "C \<equiv> (\<Sum>z\<in>zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}. zorder_mero_uhp f z)"
  shows   "12 * C + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> + 12 * zorder_at_ii_inf 1 f = k"
proof -
  interpret modular_form f k UNIV
    using assms(1) by auto
  have f': "f \<in> MeForms[k] - {0}"
    using assms(1) by (auto simp: MeForms_def meromorphic_form_axioms)
  from assms have "poles_mero_uhp f = {}"
    by (auto simp: poles_mero_uhp_def)
  thus ?thesis
    using MeForms_valence_formula'[OF f'] by (simp add: C_def)
qed

end
