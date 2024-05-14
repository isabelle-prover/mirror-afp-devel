theory PNT_with_Remainder
imports
  "Relation_of_PNTs"
  "Zeta_Zerofree"
  "Perron_Formula"
begin
unbundle pnt_notation

section \<open>Estimation of the order of $\frac{\zeta'(s)}{\zeta(s)}$\<close>

notation primes_psi ("\<psi>")

lemma zeta_div_bound':
  assumes "1 + exp (- 4 * ln (14 + 4 * t)) \<le> \<sigma>"
    and "13 / 22 \<le> t"
    and "z \<in> cball (Complex \<sigma> t) (1 / 2)"
  shows "\<parallel>zeta z / zeta (Complex \<sigma> t)\<parallel> \<le> exp (12 * ln (14 + 4 * t))"
proof -
  interpret z: zeta_bound_param_2
    "\<lambda>t. 1 / 2" "\<lambda>t. 4 * ln (12 + 2 * max 0 t)" t \<sigma> t
    unfolding zeta_bound_param_1_def zeta_bound_param_2_def
              zeta_bound_param_1_axioms_def zeta_bound_param_2_axioms_def
    using assms by (auto intro: classical_zeta_bound.zeta_bound_param_axioms)
  show ?thesis using z.zeta_div_bound assms(2) assms(3)
    unfolding z.s_def z.r_def by auto
qed

lemma zeta_div_bound:
  assumes "1 + exp (- 4 * ln (14 + 4 * \<bar>t\<bar>)) \<le> \<sigma>"
    and "13 / 22 \<le> \<bar>t\<bar>"
    and "z \<in> cball (Complex \<sigma> t) (1 / 2)"
  shows "\<parallel>zeta z / zeta (Complex \<sigma> t)\<parallel> \<le> exp (12 * ln (14 + 4 * \<bar>t\<bar>))"
proof (cases "0 \<le> t")
  case True with assms(2) have "13 / 22 \<le> t" by auto
  thus ?thesis using assms by (auto intro: zeta_div_bound')
next
  case False with assms(2) have Ht: "t \<le> - 13 / 22" by auto
  moreover have 1: "Complex \<sigma> (- t) = cnj (Complex \<sigma> t)" by (auto simp add: legacy_Complex_simps)
  ultimately have "\<parallel>zeta (cnj z) / zeta (Complex \<sigma> (- t))\<parallel> \<le> exp (12 * ln (14 + 4 * (- t)))"
    using assms(1) assms(3)
    by (intro zeta_div_bound', auto simp add: dist_complex_def)
       (subst complex_cnj_diff [symmetric], subst complex_mod_cnj)
  thus ?thesis using Ht by (subst (asm) 1) (simp add: norm_divide)
qed

definition C\<^sub>2 where "C\<^sub>2 \<equiv> 319979520 :: real"

lemma C\<^sub>2_gt_zero: "0 < C\<^sub>2" unfolding C\<^sub>2_def by auto

lemma logderiv_zeta_order_estimate':
"\<forall>\<^sub>F t in (abs going_to at_top).
  \<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
  \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
proof -
  define F where "F :: real filter \<equiv> abs going_to at_top"
  define r where "r t \<equiv> C\<^sub>1 / ln (\<bar>t\<bar> + 3)" for t :: real
  define s where "s \<sigma> t \<equiv> Complex (\<sigma> + 2 / 7 * r t) t" for \<sigma> t
  have r_nonneg: "0 \<le> r t" for t unfolding PNT_const_C\<^sub>1_def r_def by auto
  have "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
    when h: "1 - 1 / 7 * r t \<le> \<sigma>"
            "exp (- 4 * ln (14 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t"
            "8 / 7 * r t \<le> \<bar>t\<bar>"
            "8 / 7 * r t \<le> 1 / 2"
            "13 / 22 \<le> \<bar>t\<bar>" for \<sigma> t
  proof -
    have "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> 8 * (12 * ln (14 + 4 * \<bar>t\<bar>)) / (8 / 7 * r t)"
    proof (rule lemma_3_9_beta1' [where ?s = "s \<sigma> t"], goal_cases)
      case 1 show ?case unfolding PNT_const_C\<^sub>1_def r_def by auto
      case 2 show ?case by auto
      have notin_ball: "1 \<notin> ball (s \<sigma> t) (8 / 7 * r t)"
      proof -
        note h(3)
        also have "\<bar>t\<bar> = \<bar>Im (Complex (\<sigma> + 2 / 7 * r t) t - 1)\<bar>" by auto
        also have "\<dots> \<le> \<parallel>Complex (\<sigma> + 2 / 7 * r t) t - 1\<parallel>" by (rule abs_Im_le_cmod)
        finally show ?thesis
          unfolding s_def by (auto simp add: dist_complex_def)
      qed
      case 3 show ?case by (intro holomorphic_zeta notin_ball)
      case 6 show ?case
        using r_nonneg unfolding s_def
        by (auto simp add: dist_complex_def legacy_Complex_simps)
      fix z assume Hz: "z \<in> ball (s \<sigma> t) (8 / 7 * r t)"
      show "zeta z \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> zeta z \<noteq> 0"
        hence zero: "zeta (Complex (Re z) (Im z)) = 0" by auto
        have "r t \<le> C\<^sub>1 / ln (\<bar>Im z\<bar> + 2)"
        proof -
          have "\<parallel>s \<sigma> t - z\<parallel> < 1"
            using Hz h(4) by (auto simp add: dist_complex_def)
          hence "\<bar>t - Im z\<bar> < 1"
            using abs_Im_le_cmod [of "s \<sigma> t - z"]
            unfolding s_def by (auto simp add: legacy_Complex_simps)
          hence "\<bar>Im z\<bar> < \<bar>t\<bar> + 1" by auto
          thus ?thesis unfolding r_def
            by (intro divide_left_mono mult_pos_pos)
               (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
        qed
        also have "\<dots> \<le> 1 - Re z"
          using notin_ball Hz by (intro zeta_nonzero_region zero) auto
        also have "\<dots> < 1 - Re (s \<sigma> t) + 8 / 7 * r t"
        proof -
          have "Re (s \<sigma> t - z) \<le> \<bar>Re (s \<sigma> t - z)\<bar>" by auto
          also have "\<dots> < 8 / 7 * r t"
            using Hz abs_Re_le_cmod [of "s \<sigma> t - z"]
            by (auto simp add: dist_complex_def)
          ultimately show ?thesis by auto
        qed
        also have "\<dots> = 1 - \<sigma> + 6 / 7 * r t" unfolding s_def by auto
        also have "\<dots> \<le> r t" using h(1) by auto
        finally show False by auto
      qed
      from Hz have "z \<in> cball (s \<sigma> t) (1 / 2)"
        using h(4) by auto
      thus "\<parallel>zeta z / zeta (s \<sigma> t)\<parallel> \<le> exp (12 * ln (14 + 4 * \<bar>t\<bar>))"
        using h(1) h(2) unfolding s_def
        by (intro zeta_div_bound h(5)) auto
    qed
    also have "\<dots> = 84 / r t * ln (14 + 4 * \<bar>t\<bar>)"
      by (auto simp add: field_simps)
    also have "\<dots> \<le> 336 / C\<^sub>1 * ln (\<bar>t\<bar> + 2) * ln (\<bar>t\<bar> + 3)"
    proof - 
      have "84 / r t * ln (14 + 4 * \<bar>t\<bar>) \<le> 84 / r t * (4 * ln (\<bar>t\<bar> + 2))"
        using r_nonneg by (intro mult_left_mono mult_right_mono ln_bound_1) auto
      thus ?thesis unfolding r_def by (simp add: mult_ac)
    qed
    also have "\<dots> \<le> 336 / C\<^sub>1 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
      unfolding power2_eq_square
      by (simp add: mult_ac, intro divide_right_mono mult_right_mono)
         (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
    also have "\<dots> = C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
      unfolding PNT_const_C\<^sub>1_def C\<^sub>2_def by auto
    finally show ?thesis .
  qed
  hence
    "\<forall>\<^sub>F t in F.
        exp (- 4 * ln (14 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t
    \<longrightarrow> 8 / 7 * r t \<le> \<bar>t\<bar>
    \<longrightarrow> 8 / 7 * r t \<le> 1 / 2
    \<longrightarrow> 13 / 22 \<le> \<bar>t\<bar>
    \<longrightarrow> (\<forall>\<sigma>. 1 - 1 / 7 * r t \<le> \<sigma>
      \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by (blast intro: eventuallyI)
  moreover have "\<forall>\<^sub>F t in F. exp (- 4 * ln (14 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t"
    unfolding F_def r_def PNT_const_C\<^sub>1_def
    by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * r t \<le> \<bar>t\<bar>"
    unfolding F_def r_def PNT_const_C\<^sub>1_def
    by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * r t \<le> 1 / 2"
    unfolding F_def r_def PNT_const_C\<^sub>1_def
    by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 13 / 22 \<le> \<bar>t\<bar>"
    unfolding F_def by (rule eventually_going_toI) real_asymp
  ultimately have
    "\<forall>\<^sub>F t in F. (\<forall>\<sigma>. 1 - 1 / 7 * r t \<le> \<sigma>
      \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by eventually_elim blast
  thus ?thesis unfolding F_def r_def by auto
qed

definition C\<^sub>3 where
"C\<^sub>3 \<equiv> SOME T. 0 < T \<and>
  (\<forall>t. T \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"

lemma C\<^sub>3_prop:
  "0 < C\<^sub>3 \<and>
  (\<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
    \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"
proof -
  obtain T' where hT:
  "\<And>t. T' \<le> \<bar>t\<bar> \<Longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    using logderiv_zeta_order_estimate'
      [unfolded going_to_def, THEN rev_iffD1,
      OF eventually_filtercomap_at_top_linorder] by blast
  define T where "T \<equiv> max 1 T'"
  show ?thesis unfolding C\<^sub>3_def
    by (rule someI [of _ T]) (unfold T_def, use hT in auto)
qed

lemma C\<^sub>3_gt_zero: "0 < C\<^sub>3" using C\<^sub>3_prop by blast

lemma logderiv_zeta_order_estimate:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>" "C\<^sub>3 \<le> \<bar>t\<bar>"
  shows "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
  using assms C\<^sub>3_prop by blast

definition zeta_zerofree_region
  where "zeta_zerofree_region \<equiv> {s. s \<noteq> 1 \<and> 1 - C\<^sub>1 / ln (\<bar>Im s\<bar> + 2) < Re s}"
definition logderiv_zeta_region
  where "logderiv_zeta_region \<equiv> {s. C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>Im s\<bar> + 3) \<le> Re s}"
definition zeta_strip_region
  where "zeta_strip_region \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> \<bar>Im s\<bar> \<le> T}"
definition zeta_strip_region'
  where "zeta_strip_region' \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> \<bar>Im s\<bar> \<le> T}"

lemma strip_in_zerofree_region:
  assumes "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
  shows "zeta_strip_region \<sigma> T \<subseteq> zeta_zerofree_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region_def by auto
  from this(3) have "C\<^sub>1 / ln (T + 2) \<le> C\<^sub>1 / ln (\<bar>Im s\<bar> + 2)"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> zeta_zerofree_region" using Hs' assms unfolding zeta_zerofree_region_def by auto
qed

lemma strip_in_logderiv_zeta_region:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "zeta_strip_region' \<sigma> T \<subseteq> logderiv_zeta_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region' \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "C\<^sub>3 \<le> \<bar>Im s\<bar>" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region'_def by auto
  from this(4) have "C\<^sub>1 / (7 * ln (T + 3)) \<le> C\<^sub>1 / (7 * ln (\<bar>Im s\<bar> + 3))"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> logderiv_zeta_region" using Hs' assms unfolding logderiv_zeta_region_def by auto
qed

lemma strip_condition_imp:
  assumes "0 \<le> T" "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
proof -
  have "ln (T + 2) \<le> 7 * ln (T + 2)" using assms(1) by auto
  also have "\<dots> < 7 * ln (T + 3)" using assms(1) by auto
  finally have "C\<^sub>1 / (7 * ln (T + 3)) < C\<^sub>1 / ln (T + 2)"
    using C\<^sub>1_gt_zero assms(1) by (intro divide_strict_left_mono mult_pos_pos) auto
  thus ?thesis using assms(2) by auto
qed

lemma zeta_zerofree_region:
  assumes "s \<in> zeta_zerofree_region"
  shows "zeta s \<noteq> 0"
  using zeta_nonzero_region [of "Re s" "Im s"] assms
  unfolding zeta_zerofree_region_def by auto

lemma logderiv_zeta_region_estimate:
  assumes "s \<in> logderiv_zeta_region"
  shows "\<parallel>logderiv zeta s\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
  using logderiv_zeta_order_estimate [of "Im s" "Re s"] assms
  unfolding logderiv_zeta_region_def by auto

definition C\<^sub>4 :: real where "C\<^sub>4 \<equiv> 1 / 6666241"

lemma C\<^sub>4_prop:
  "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
  unfolding PNT_const_C\<^sub>1_def C\<^sub>4_def by real_asymp

lemma C\<^sub>4_gt_zero: "0 < C\<^sub>4" unfolding C\<^sub>4_def by auto

definition C\<^sub>5_prop where
"C\<^sub>5_prop C\<^sub>5 \<equiv>
  0 < C\<^sub>5 \<and> (\<forall>\<^sub>F x in at_top. (\<forall>t. \<bar>t\<bar> \<le> x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2))"

lemma logderiv_zeta_bound_vertical':
  "\<exists>C\<^sub>5. C\<^sub>5_prop C\<^sub>5"
proof -
  define K where "K \<equiv> cbox (Complex 0 (-C\<^sub>3)) (Complex 2 C\<^sub>3)"
  define \<Gamma> where "\<Gamma> \<equiv> {s \<in> K. zeta' s = 0}"
  have "zeta' not_zero_on K"
    unfolding not_zero_on_def K_def using C\<^sub>3_gt_zero
    by (intro bexI [where x = 2])
       (auto simp add: zeta_eq_zero_iff_zeta' zeta_2 in_cbox_complex_iff)
  hence fin: "finite \<Gamma>"
    unfolding \<Gamma>_def K_def
    by (auto intro!: convex_connected analytic_compact_finite_zeros zeta'_analytic)
  define \<alpha> where "\<alpha> \<equiv> if \<Gamma> = {} then 0 else (1 + Max (Re ` \<Gamma>)) / 2"
  define K' where "K' \<equiv> cbox (Complex \<alpha> (-C\<^sub>3)) (Complex 1 C\<^sub>3)"
  have H\<alpha>: "\<alpha> \<in> {0..<1}"
  proof (cases "\<Gamma> = {}")
    case True thus ?thesis unfolding \<alpha>_def by auto
  next
    case False hence h\<Gamma>: "\<Gamma> \<noteq> {}" .
    moreover have "Re a < 1" if Ha: "a \<in> \<Gamma>" for a
    proof (rule ccontr)
      assume "\<not> Re a < 1" hence "1 \<le> Re a" by auto
      hence "zeta' a \<noteq> 0" by (subst zeta'_eq_zero_iff) (use zeta_Re_ge_1_nonzero in auto)
      thus False using Ha unfolding \<Gamma>_def by auto
    qed
    moreover have "\<exists>a\<in>\<Gamma>. 0 \<le> Re a"
    proof -
      from h\<Gamma> have "\<exists>a. a \<in> \<Gamma>" by auto
      moreover have "\<And>a. a \<in> \<Gamma> \<Longrightarrow> 0 \<le> Re a"
        unfolding \<Gamma>_def K_def by (auto simp add: in_cbox_complex_iff)
      ultimately show ?thesis by auto
    qed
    ultimately have "0 \<le> Max (Re ` \<Gamma>)" "Max (Re ` \<Gamma>) < 1"
      using fin by (auto simp add: Max_ge_iff)
    thus ?thesis unfolding \<alpha>_def using h\<Gamma> by auto
  qed
  have nonzero: "zeta' z \<noteq> 0" when "z \<in> K'" for z
  proof (rule ccontr)
    assume "\<not> zeta' z \<noteq> 0"
    moreover have "K' \<subseteq> K" unfolding K'_def K_def
      by (rule subset_box_imp) (insert H\<alpha>, simp add: Basis_complex_def)
    ultimately have Hz: "z \<in> \<Gamma>" unfolding \<Gamma>_def using that by auto
    hence "Re z \<le> Max (Re ` \<Gamma>)" using fin by (intro Max_ge) auto
    also have "\<dots> < \<alpha>"
    proof -
      from Hz have "\<Gamma> \<noteq> {}" by auto
      thus ?thesis using H\<alpha> unfolding \<alpha>_def by auto
    qed
    finally have "Re z < \<alpha>" .
    moreover from \<open>z \<in> K'\<close> have "\<alpha> \<le> Re z"
      unfolding K'_def by (simp add: in_cbox_complex_iff)
    ultimately show False by auto
  qed
  hence "logderiv zeta' analytic_on K'" by (intro analytic_intros)
  moreover have "compact K'" unfolding K'_def by auto
  ultimately have "bounded ((logderiv zeta') ` K')"
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on
        compact_imp_bounded compact_continuous_image)
  from this [THEN rev_iffD1, OF bounded_pos]
  obtain M where
    hM: "\<And>s. s \<in> K' \<Longrightarrow> \<parallel>logderiv zeta' s\<parallel> \<le> M" by auto
  have "(\<lambda>t. C\<^sub>2 * (ln (t + 3))\<^sup>2) \<in> O(\<lambda>x. (ln x)\<^sup>2)" using C\<^sub>2_gt_zero by real_asymp
  then obtain \<gamma> where
    H\<gamma>: "\<forall>\<^sub>F x in at_top. \<parallel>C\<^sub>2 * (ln (x + 3))\<^sup>2\<parallel> \<le> \<gamma> * \<parallel>(ln x)\<^sup>2\<parallel>"
    unfolding bigo_def by auto
  define C\<^sub>5 where "C\<^sub>5 \<equiv> max 1 \<gamma>"
  have C\<^sub>5_gt_zero: "0 < C\<^sub>5" unfolding C\<^sub>5_def by auto
  have "\<forall>\<^sub>F x in at_top. \<gamma> * (ln x)\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI mult_right_mono) (unfold C\<^sub>5_def, auto)
  with H\<gamma> have hC\<^sub>5: "\<forall>\<^sub>F x in at_top. C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by eventually_elim (use C\<^sub>2_gt_zero in auto)
  have "\<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    when h: "C\<^sub>3 \<le> \<bar>t\<bar>" "\<bar>t\<bar> \<le> x" "1 < x"
            "C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
            "C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2" for x t
  proof -
    have "Re (Complex (1 - C\<^sub>4 / ln x) t) \<noteq> Re 1" using C\<^sub>4_gt_zero h(3) by auto
    hence "Complex (1 - C\<^sub>4 / ln x) t \<noteq> 1" by metis
    hence "Complex (1 - C\<^sub>4 / ln x) t \<in> zeta_strip_region' (1 - C\<^sub>4 / ln x) x"
      unfolding zeta_strip_region'_def using h(1) h(2) by auto
    moreover hence "1 - 1 / 7 * C\<^sub>1 / ln (x + 3) \<le> 1 - C\<^sub>4 / ln x" using h(4) by auto
    ultimately have "\<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im (Complex (1 - C\<^sub>4 / ln x) t)\<bar> + 3))\<^sup>2"
      using strip_in_logderiv_zeta_region [where ?\<sigma> = "1 - C\<^sub>4 / ln x" and ?T = x]
      by (intro logderiv_zeta_region_estimate) auto
    also have "\<dots> \<le> C\<^sub>2 * (ln (x + 3))\<^sup>2"
      by (intro mult_left_mono, subst power2_le_iff_abs_le)
         (use C\<^sub>2_gt_zero h(2) h(3) in auto)
    also have "\<dots> \<le> C\<^sub>5 * (ln x)\<^sup>2" by (rule h(5))
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> 1 < x \<longrightarrow> C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))
    \<longrightarrow> C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F x in at_top. (1 :: real) < x" by auto
  ultimately have 1: "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    using C\<^sub>4_prop hC\<^sub>5 by eventually_elim blast
  define f where "f x \<equiv> 1 - C\<^sub>4 / ln x" for x
  define g where "g x t \<equiv> Complex (f x) t" for x t
  let ?P = "\<lambda>x t. \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + ln x / C\<^sub>4"
  have "\<alpha> < 1" using H\<alpha> by auto
  hence "\<forall>\<^sub>F x in at_top. \<alpha> \<le> f x" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  moreover have f_lt_1: "\<forall>\<^sub>F x in at_top. f x < 1" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> g x t \<in> K' - {1}"
    unfolding g_def K'_def by eventually_elim (auto simp add: in_cbox_complex_iff legacy_Complex_simps)
  moreover have "\<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)"
    when h: "g x t \<in> K' - {1}" "f x < 1" for x t
  proof -
    from h(1) have ne_1: "g x t \<noteq> 1" by auto
    hence "\<parallel>logderiv zeta (g x t)\<parallel> = \<parallel>logderiv zeta' (g x t) - 1 / (g x t - 1)\<parallel>"
      using h(1) nonzero
      by (subst logderiv_zeta_eq_zeta')
         (auto simp add: zeta_eq_zero_iff_zeta' [symmetric])
    also have "\<dots> \<le> \<parallel>logderiv zeta' (g x t)\<parallel> + \<parallel>1 / (g x t - 1)\<parallel>" by (rule norm_triangle_ineq4)
    also have "\<dots> \<le> M + 1 / (1 - f x)"
    proof -
      have "\<parallel>logderiv zeta' (g x t)\<parallel> \<le> M" using that by (auto intro: hM)
      moreover have "\<bar>Re (g x t - 1)\<bar> \<le> \<parallel>g x t - 1\<parallel>" by (rule abs_Re_le_cmod)
      hence "\<parallel>1 / (g x t - 1)\<parallel> \<le> 1 / (1 - f x)"
        using ne_1 h(2)
        by (auto simp add: norm_divide g_def
                 intro!: divide_left_mono mult_pos_pos)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. f x < 1
    \<longrightarrow> g x t \<in> K' - {1} 
    \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)" by auto
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)"
    using f_lt_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + ln x / C\<^sub>4" unfolding f_def by auto
  moreover have "\<forall>\<^sub>F x in at_top. M + ln x / C\<^sub>4 \<le> C\<^sub>5 * (ln x)\<^sup>2" using C\<^sub>4_gt_zero C\<^sub>5_gt_zero by real_asymp
  ultimately have 2: "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2" by eventually_elim auto
  show ?thesis
  proof (unfold C\<^sub>5_prop_def, intro exI conjI)
    show "0 < C\<^sub>5" by (rule C\<^sub>5_gt_zero)+
    have "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<or> \<bar>t\<bar> \<le> C\<^sub>3"
      by (rule eventuallyI) auto
    with 1 2 show "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> x \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
      unfolding f_def g_def by eventually_elim blast
  qed
qed

definition C\<^sub>5 where "C\<^sub>5 \<equiv> SOME C\<^sub>5. C\<^sub>5_prop C\<^sub>5"

lemma
  C\<^sub>5_gt_zero: "0 < C\<^sub>5" (is ?prop_1) and
  logderiv_zeta_bound_vertical:
    "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> x
      \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2" (is ?prop_2)
proof -
  have "C\<^sub>5_prop C\<^sub>5" unfolding C\<^sub>5_def
    by (rule someI_ex) (rule logderiv_zeta_bound_vertical')
  thus ?prop_1 ?prop_2 unfolding C\<^sub>5_prop_def by auto
qed

section \<open>Deducing prime number theorem using Perron's formula\<close>

locale prime_number_theorem =
  fixes c \<epsilon> :: real
  assumes Hc: "0 < c" and Hc': "c * c < 2 * C\<^sub>4" and H\<epsilon>: "0 < \<epsilon>" "2 * \<epsilon> < c"
begin
notation primes_psi ("\<psi>")
definition H where "H x \<equiv> exp (c / 2 * (ln x) powr (1 / 2))" for x :: real
definition T where "T x \<equiv> exp (c * (ln x) powr (1 / 2))" for x :: real
definition a where "a x \<equiv> 1 - C\<^sub>4 / (c * (ln x) powr (1 / 2))" for x :: real
definition b where "b x \<equiv> 1 + 1 / (ln x)" for x :: real
definition B where "B x \<equiv> 5 / 4 * ln x" for x :: real
definition f where "f x s \<equiv> x powr s / s * logderiv zeta s" for x :: real and s :: complex
definition R where "R x \<equiv>
  x powr (b x) * H x * B x / T x + 3 * (2 + ln (T x / b x))
  * (\<Sum>n | x - x / H x \<le> n \<and> n \<le> x + x / H x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)" for x :: real
definition Rc' where "Rc' \<equiv> O(\<lambda>x. x * exp (- (c / 2 - \<epsilon>) * ln x powr (1 / 2)))"
definition Rc where "Rc \<equiv> O(\<lambda>x. x * exp (- (c / 2 - 2 * \<epsilon>) * ln x powr (1 / 2)))"
definition z\<^sub>1 where "z\<^sub>1 x \<equiv> Complex (a x) (- T x)" for x
definition z\<^sub>2 where "z\<^sub>2 x \<equiv> Complex (b x) (- T x)" for x
definition z\<^sub>3 where "z\<^sub>3 x \<equiv> Complex (b x) (T x)" for x
definition z\<^sub>4 where "z\<^sub>4 x \<equiv> Complex (a x) (T x)" for x
definition rect where "rect x \<equiv> cbox (z\<^sub>1 x) (z\<^sub>3 x)" for x
definition rect' where "rect' x \<equiv> rect x - {1}" for x
definition P\<^sub>t where "P\<^sub>t x t \<equiv> linepath (Complex (a x) t) (Complex (b x) t)" for x t
definition P\<^sub>1 where "P\<^sub>1 x \<equiv> linepath (z\<^sub>1 x) (z\<^sub>4 x)" for x
definition P\<^sub>2 where "P\<^sub>2 x \<equiv> linepath (z\<^sub>2 x) (z\<^sub>3 x)" for x
definition P\<^sub>3 where "P\<^sub>3 x \<equiv> P\<^sub>t x (- T x)" for x
definition P\<^sub>4 where "P\<^sub>4 x \<equiv> P\<^sub>t x (T x)" for x
definition P\<^sub>r where "P\<^sub>r x \<equiv> rectpath (z\<^sub>1 x) (z\<^sub>3 x)" for x

lemma Rc_eq_rem_est:
  "Rc = rem_est (c / 2 - 2 * \<epsilon>) (1 / 2) 0"
proof -
  have *: "\<forall>\<^sub>F x :: real in at_top. 0 < ln (ln x)" by real_asymp
  show ?thesis unfolding Rc_def rem_est_def
    by (rule landau_o.big.cong) (use * in eventually_elim, auto)
qed

lemma residue_f:
  "residue (f x) 1 = - x"
proof -
  define A where "A \<equiv> box (Complex 0 (- 1 / 2)) (Complex 2 (1 / 2))"
  have hA: "0 \<notin> A" "1 \<in> A" "open A"
    unfolding A_def by (auto simp add: mem_box Basis_complex_def)
  have "zeta' s \<noteq> 0" when "s \<in> A" for s
  proof -
    have "s \<noteq> 1 \<Longrightarrow> zeta s \<noteq> 0"
      using that unfolding A_def
      by (intro zeta_nonzero_small_imag)
         (auto simp add: mem_box Basis_complex_def)
    thus ?thesis by (subst zeta'_eq_zero_iff) auto
  qed
  hence h: "(\<lambda>s. x powr s / s * logderiv zeta' s) holomorphic_on A"
    by (intro holomorphic_intros) (use hA in auto)
  have h': "(\<lambda>s. x powr s / (s * (s - 1))) holomorphic_on A - {1}"
    by (auto intro!: holomorphic_intros) (use hA in auto)
  have s_ne_1: "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 1"
    by (subst eventually_at_filter) auto
  moreover have "\<forall>\<^sub>F s in at 1. zeta s \<noteq> 0"
    by (intro non_zero_neighbour_pole is_pole_zeta)
  ultimately have "\<forall>\<^sub>F s in at 1. logderiv zeta s = logderiv zeta' s - 1 / (s - 1)"
    by eventually_elim (rule logderiv_zeta_eq_zeta')
  moreover have
    "f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    when "logderiv zeta s = logderiv zeta' s - 1 / (s - 1)" "s \<noteq> 0" "s \<noteq> 1" for s :: complex
    unfolding f_def by (subst that(1)) (insert that, auto simp add: field_simps)
  hence "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 0 \<longrightarrow> s \<noteq> 1
    \<longrightarrow> logderiv zeta s = logderiv zeta' s - 1 / (s - 1)
    \<longrightarrow> f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 0"
    by (subst eventually_at_topological)
       (intro exI [of _ "UNIV - {0}"], auto)
  ultimately have "\<forall>\<^sub>F s :: complex in at 1. f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    using s_ne_1 by eventually_elim blast
  hence "residue (f x) 1 = residue (\<lambda>s. x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)) 1"
    by (intro residue_cong refl)
  also have "\<dots> = residue (\<lambda>s. x powr s / s * logderiv zeta' s) 1 - residue (\<lambda>s. x powr s / s / (s - 1)) 1"
    by (subst residue_diff [where ?s = A]) (use h h' hA in auto)
  also have "\<dots> = - x"
  proof -
    have "residue (\<lambda>s. x powr s / s * logderiv zeta' s) 1 = 0"
      by (rule residue_holo [where ?s = A]) (use hA h in auto)
    moreover have "residue (\<lambda>s. x powr s / s / (s - 1)) 1 = (x :: complex) powr 1 / 1"
      by (rule residue_simple [where ?s = A]) (use hA in \<open>auto intro!: holomorphic_intros\<close>)
    ultimately show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma rect_in_strip:
  "rect x - {1} \<subseteq> zeta_strip_region (a x) (T x)"
  unfolding rect_def zeta_strip_region_def z\<^sub>1_def z\<^sub>3_def
  by (auto simp add: in_cbox_complex_iff)

lemma rect_in_strip':
  "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> zeta_strip_region' (a x) (T x)"
  unfolding rect_def zeta_strip_region'_def z\<^sub>1_def z\<^sub>3_def
  using C\<^sub>3_gt_zero by (auto simp add: in_cbox_complex_iff)

lemma
  rect'_in_zerofree: "\<forall>\<^sub>F x in at_top. rect' x \<subseteq> zeta_zerofree_region" and
  rect_in_logderiv_zeta: "\<forall>\<^sub>F x in at_top. {s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
proof (goal_cases)
  case 1 have
    "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))" by (rule C\<^sub>4_prop)
  moreover have "LIM x at_top. exp (c * (ln x) powr (1 / 2)) :> at_top" using Hc by real_asymp
  ultimately have h:
   "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln (exp (c * (ln x) powr (1 / 2)))
    \<le> C\<^sub>1 / (7 * ln (exp (c * (ln x) powr (1 / 2)) + 3))" (is "eventually ?P _")
    by (rule eventually_compose_filterlim)
  moreover have
    "?P x \<Longrightarrow> zeta_strip_region (a x) (T x) \<subseteq> zeta_zerofree_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_zerofree_region strip_condition_imp) auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  ultimately show ?case unfolding rect'_def by eventually_elim (use rect_in_strip in auto)
  case 2 from h have
    "?P x \<Longrightarrow> zeta_strip_region' (a x) (T x) \<subseteq> logderiv_zeta_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_logderiv_zeta_region) auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  thus ?case using h by eventually_elim (use rect_in_strip' in auto)
qed

lemma zeta_nonzero_in_rect:
  "\<forall>\<^sub>F x in at_top. \<forall>s. s \<in> rect' x \<longrightarrow> zeta s \<noteq> 0"
  using rect'_in_zerofree by eventually_elim (use zeta_zerofree_region in auto)

lemma zero_notin_rect: "\<forall>\<^sub>F x in at_top. 0 \<notin> rect' x"
proof -
  have "\<forall>\<^sub>F x in at_top. C\<^sub>4 / (c * (ln x) powr (1 / 2)) < 1"
    using Hc by real_asymp
  thus ?thesis
    unfolding rect'_def rect_def z\<^sub>1_def z\<^sub>4_def T_def a_def
    by eventually_elim (simp add: in_cbox_complex_iff)
qed

lemma f_analytic:
  "\<forall>\<^sub>F x in at_top. f x analytic_on rect' x"
  using zeta_nonzero_in_rect zero_notin_rect unfolding f_def
  by eventually_elim (intro analytic_intros, auto simp: rect'_def)

lemma path_image_in_rect_1:
  assumes "0 \<le> T x \<and> a x \<le> b x"
  shows "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
  unfolding P\<^sub>1_def P\<^sub>2_def rect_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

lemma path_image_in_rect_2:
  assumes "0 \<le> T x \<and> a x \<le> b x \<and> t \<in> {-T x..T x}"
  shows "path_image (P\<^sub>t x t) \<subseteq> rect x"
  unfolding P\<^sub>t_def rect_def z\<^sub>1_def z\<^sub>3_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

definition path_in_rect' where
"path_in_rect' x \<equiv>
  path_image (P\<^sub>1 x) \<subseteq> rect' x \<and> path_image (P\<^sub>2 x) \<subseteq> rect' x \<and>
  path_image (P\<^sub>3 x) \<subseteq> rect' x \<and> path_image (P\<^sub>4 x) \<subseteq> rect' x"

lemma path_image_in_rect':
  assumes "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "path_in_rect' x"
proof -
  have "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
    by (rule path_image_in_rect_1) (use assms in auto)
  moreover have "path_image (P\<^sub>3 x) \<subseteq> rect x" "path_image (P\<^sub>4 x) \<subseteq> rect x"
    unfolding P\<^sub>3_def P\<^sub>4_def
    by (intro path_image_in_rect_2, (use assms in auto)[1])+
  moreover have
    "1 \<notin> path_image (P\<^sub>1 x) \<and> 1 \<notin> path_image (P\<^sub>2 x) \<and>
     1 \<notin> path_image (P\<^sub>3 x) \<and> 1 \<notin> path_image (P\<^sub>4 x)"
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def using assms
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  ultimately show ?thesis unfolding path_in_rect'_def rect'_def by blast
qed

lemma asymp_1:
  "\<forall>\<^sub>F x in at_top. 0 < T x \<and> a x < 1 \<and> 1 < b x"
  unfolding T_def a_def b_def
  by (intro eventually_conj, insert Hc C\<^sub>4_gt_zero) (real_asymp)+

lemma f_continuous_on:
  "\<forall>\<^sub>F x in at_top. \<forall>A\<subseteq>rect' x. continuous_on A (f x)"
  using f_analytic
  by (eventually_elim, safe)
     (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic,
      elim analytic_on_subset)

lemma contour_integrability:
  "\<forall>\<^sub>F x in at_top.
    f x contour_integrable_on P\<^sub>1 x \<and> f x contour_integrable_on P\<^sub>2 x \<and>
    f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
proof -
  have "\<forall>\<^sub>F x in at_top. path_in_rect' x"
    using asymp_1 by eventually_elim (rule path_image_in_rect')
  thus ?thesis using f_continuous_on
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def path_in_rect'_def
    by eventually_elim
       (intro conjI contour_integrable_continuous_linepath,
        fold z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def, auto)
qed

lemma contour_integral_rectpath':
  assumes "f x analytic_on (rect' x)" "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "contour_integral (P\<^sub>r x) (f x) = - 2 * pi * \<i> * x"
proof -
  define z where "z \<equiv> (1 + b x) / 2"
  have Hz: "z \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2)
    by (auto simp add: mem_box Basis_complex_def)
  have Hz': "z \<noteq> 1" unfolding z_def using assms(2) by auto
  have "connected (rect' x)"
  proof -
    have box_nonempty: "box (z\<^sub>1 x) (z\<^sub>3 x) \<noteq> {}" using Hz by auto
    hence "aff_dim (closure (box (z\<^sub>1 x) (z\<^sub>3 x))) = 2"
      by (subst closure_aff_dim, subst aff_dim_open) auto
    thus ?thesis
      unfolding rect'_def using box_nonempty
      by (subst (asm) closure_box)
         (auto intro: connected_punctured_convex simp add: rect_def)
  qed
  moreover have Hz'': "z \<in> rect' x"
    unfolding rect'_def rect_def using box_subset_cbox Hz Hz' by auto
  ultimately obtain T where hT:
    "f x holomorphic_on T" "open T" "rect' x \<subseteq> T" "connected T"
    using analytic_on_holomorphic_connected assms(1) by (metis dual_order.refl)
  define U where "U \<equiv> T \<union> box (z\<^sub>1 x) (z\<^sub>3 x)"
  have one_in_box: "1 \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2) by (auto simp add: mem_box Basis_complex_def)
  have "contour_integral (P\<^sub>r x) (f x) = 2 * pi * \<i> *
    (\<Sum>s\<in>{1}. winding_number (P\<^sub>r x) s * residue (f x) s)"
  proof (rule Residue_theorem)
    show "finite {1}" "valid_path (P\<^sub>r x)" "pathfinish (P\<^sub>r x) = pathstart (P\<^sub>r x)"
      unfolding P\<^sub>r_def by auto
    show "open U" unfolding U_def using hT(2) by auto
    show "connected U" unfolding U_def
      by (intro connected_Un hT(4) convex_connected)
         (use Hz Hz'' hT(3) in auto)
    have "f x holomorphic_on box (z\<^sub>1 x) (z\<^sub>3 x) - {1}"
      by (rule holomorphic_on_subset, rule analytic_imp_holomorphic, rule assms(1))
         (unfold rect'_def rect_def, use box_subset_cbox in auto)
    hence "f x holomorphic_on ((T - {1}) \<union> (box (z\<^sub>1 x) (z\<^sub>3 x) - {1}))"
      by (intro holomorphic_on_Un) (use hT(1) hT(2) in auto)
    moreover have "\<dots> = U - {1}" unfolding U_def by auto
    ultimately show "f x holomorphic_on U - {1}" by auto
    have Hz: "Re (z\<^sub>1 x) \<le> Re (z\<^sub>3 x)" "Im (z\<^sub>1 x) \<le> Im (z\<^sub>3 x)"
      unfolding z\<^sub>1_def z\<^sub>3_def using assms(2) by auto
    have "path_image (P\<^sub>r x) = rect x - box (z\<^sub>1 x) (z\<^sub>3 x)"
      unfolding rect_def P\<^sub>r_def
      by (intro path_image_rectpath_cbox_minus_box Hz)
    thus "path_image (P\<^sub>r x) \<subseteq> U - {1}"
      using one_in_box hT(3) U_def unfolding rect'_def by auto
    have hU': "rect x \<subseteq> U"
      using hT(3) one_in_box unfolding U_def rect'_def by auto
    show "\<forall>z. z \<notin> U \<longrightarrow> winding_number (P\<^sub>r x) z = 0"
      using Hz P\<^sub>r_def hU' rect_def winding_number_rectpath_outside by fastforce
  qed
  also have "\<dots> = - 2 * pi * \<i> * x" unfolding P\<^sub>r_def
    by (simp add: residue_f, subst winding_number_rectpath, auto intro: one_in_box)
  finally show ?thesis .
qed

lemma contour_integral_rectpath:
  "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>r x) (f x) = - 2 * pi * \<i> * x"
  using f_analytic asymp_1 by eventually_elim (rule contour_integral_rectpath')

lemma valid_paths:
  "valid_path (P\<^sub>1 x)" "valid_path (P\<^sub>2 x)" "valid_path (P\<^sub>3 x)" "valid_path (P\<^sub>4 x)"
  unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def by auto

lemma integral_rectpath_split:
  assumes "f x contour_integrable_on P\<^sub>1 x \<and> f x contour_integrable_on P\<^sub>2 x \<and>
           f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
  shows "contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
       - contour_integral (P\<^sub>4 x) (f x) - contour_integral (P\<^sub>1 x) (f x) = contour_integral (P\<^sub>r x) (f x)"
proof -
  define Q\<^sub>1 where "Q\<^sub>1 \<equiv> linepath (z\<^sub>3 x) (z\<^sub>4 x)"
  define Q\<^sub>2 where "Q\<^sub>2 \<equiv> linepath (z\<^sub>4 x) (z\<^sub>1 x)"
  have Q_eq: "Q\<^sub>1 = reversepath (P\<^sub>4 x)" "Q\<^sub>2 = reversepath (P\<^sub>1 x)"
    unfolding Q\<^sub>1_def Q\<^sub>2_def P\<^sub>1_def P\<^sub>4_def P\<^sub>t_def by (fold z\<^sub>3_def z\<^sub>4_def) auto
  hence "contour_integral Q\<^sub>1 (f x) = - contour_integral (P\<^sub>4 x) (f x)"
        "contour_integral Q\<^sub>2 (f x) = - contour_integral (P\<^sub>1 x) (f x)"
    by (auto intro: contour_integral_reversepath valid_paths)
  moreover have "contour_integral (P\<^sub>3 x +++ P\<^sub>2 x +++ Q\<^sub>1 +++ Q\<^sub>2) (f x)
       = contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
       + contour_integral Q\<^sub>1 (f x) + contour_integral Q\<^sub>2 (f x)"
  proof -
    have 1: "pathfinish (P\<^sub>2 x) = pathstart (Q\<^sub>1 +++ Q\<^sub>2)" "pathfinish Q\<^sub>1 = pathstart Q\<^sub>2"
      unfolding P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def by auto
    have 2: "valid_path Q\<^sub>1" "valid_path Q\<^sub>2" unfolding Q\<^sub>1_def Q\<^sub>2_def by auto
    have 3: "f x contour_integrable_on P\<^sub>1 x" "f x contour_integrable_on P\<^sub>2 x"
            "f x contour_integrable_on P\<^sub>3 x" "f x contour_integrable_on P\<^sub>4 x"
            "f x contour_integrable_on Q\<^sub>1" "f x contour_integrable_on Q\<^sub>2"
      using assms by (auto simp add: Q_eq intro: contour_integrable_reversepath valid_paths)
    show ?thesis by (subst contour_integral_join |
      auto intro: valid_paths valid_path_join contour_integrable_joinI 1 2 3)+
  qed
  ultimately show ?thesis
    unfolding P\<^sub>r_def z\<^sub>1_def z\<^sub>3_def rectpath_def
    by (simp add: Let_def, fold P\<^sub>t_def P\<^sub>3_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def)
       (fold P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def, auto)
qed

lemma P\<^sub>2_eq:
  "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x
  = contour_integral (P\<^sub>1 x) (f x) - contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>4 x) (f x)"
proof -
  have "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
      - contour_integral (P\<^sub>4 x) (f x) - contour_integral (P\<^sub>1 x) (f x) = - 2 * pi * \<i> * x"
    using contour_integrability contour_integral_rectpath asymp_1 f_analytic
    by eventually_elim (metis integral_rectpath_split)
  thus ?thesis by (auto simp add: field_simps)
qed

lemma estimation_P\<^sub>1:
  "(\<lambda>x. \<parallel>contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv>
    C\<^sub>5 * (c * (ln x) powr (1 / 2))\<^sup>2 * x powr a x * ln (1 + T x / a x)" for x
  note logderiv_zeta_bound_vertical
  moreover have "LIM x at_top. T x :> at_top"
    unfolding T_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln (T x)) t)\<parallel> \<le> C\<^sub>5 * (ln (T x))\<^sup>2"
    unfolding a_def by (rule eventually_compose_filterlim)
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (a x) t)\<parallel> \<le> C\<^sub>5 * (c * (ln x) powr (1 / 2))\<^sup>2"
    unfolding a_def T_def by auto
  moreover have "\<forall>\<^sub>F x in at_top. (f x) contour_integrable_on (P\<^sub>1 x)"
    using contour_integrability by eventually_elim auto
  hence "\<forall>\<^sub>F x in at_top. (\<lambda>s. logderiv zeta s * x powr s / s) contour_integrable_on (P\<^sub>1 x)"
     unfolding f_def by eventually_elim (auto simp add: field_simps)
  moreover have "\<forall>\<^sub>F x :: real in at_top. 0 < x" by auto
  moreover have "\<forall>\<^sub>F x in at_top. 0 < a x" unfolding a_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (\<lambda>s. logderiv zeta s * x powr s / s)\<parallel> \<le> r x"
    unfolding r_def P\<^sub>1_def z\<^sub>1_def z\<^sub>4_def using asymp_1
    by eventually_elim (rule perron_aux_3', auto)
  hence "\<forall>\<^sub>F x in at_top. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel> \<le> r x"
    unfolding f_def by eventually_elim (auto simp add: mult_ac)
  hence "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> O(r)"
    unfolding f_def by (rule eventually_le_imp_bigo')
  moreover have "r \<in> Rc"
  proof -
    define r\<^sub>1 where "r\<^sub>1 x \<equiv> C\<^sub>5 * c\<^sup>2 * ln x * ln (1 + T x / a x)" for x
    define r\<^sub>2 where "r\<^sub>2 x \<equiv> exp (a x * ln x)" for x
    have "r\<^sub>1 \<in> O(\<lambda>x. (ln x)\<^sup>2)"
      unfolding r\<^sub>1_def T_def a_def using Hc C\<^sub>5_gt_zero by real_asymp
    moreover have "r\<^sub>2 \<in> Rc'"
    proof -
      have 1: "\<parallel>r\<^sub>2 x\<parallel> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
        when h: "0 < x" "0 < ln x" for x
      proof -
        have "a x * ln x = ln x + - C\<^sub>4 / c * (ln x) powr (1 / 2)"
          unfolding a_def using h(2) Hc
          by (auto simp add: field_simps powr_add [symmetric] frac_eq_eq)
        hence "r\<^sub>2 x = exp (\<dots>)" unfolding r\<^sub>2_def by blast
        also have "\<dots> = x * exp (- C\<^sub>4 / c * (ln x) powr (1 / 2))"
          by (subst exp_add) (use h(1) in auto)
        also have "\<dots> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
          by (intro mult_left_mono, subst exp_le_cancel_iff, intro mult_right_mono)
             (use Hc Hc' H\<epsilon> C\<^sub>4_gt_zero h in \<open>auto simp: field_simps intro: add_increasing2\<close>)
        finally show ?thesis unfolding r\<^sub>2_def by auto
      qed
      have "\<forall>\<^sub>F x in at_top. \<parallel>r\<^sub>2 x\<parallel> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
        using ln_asymp_pos x_asymp_pos by eventually_elim (rule 1)
      thus ?thesis unfolding Rc'_def by (rule eventually_le_imp_bigo)
    qed
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x)
      \<in> O(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))))"
      unfolding Rc'_def by (rule landau_o.big.mult)
    moreover have "(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2)))) \<in> Rc"
      unfolding Rc_def using Hc H\<epsilon>
      by (real_asymp simp add: field_simps)
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x) \<in> Rc"
      unfolding Rc_def by (rule landau_o.big_trans)
    moreover have "\<forall>\<^sub>F x in at_top. r x = r\<^sub>1 x * r\<^sub>2 x"
      using ln_ln_asymp_pos ln_asymp_pos x_asymp_pos
      unfolding r_def r\<^sub>1_def r\<^sub>2_def a_def powr_def power2_eq_square
      by (eventually_elim) (simp add: field_simps exp_add [symmetric])
    ultimately show ?thesis unfolding Rc_def
      using landau_o.big.ev_eq_trans2 by auto
  qed
  ultimately have "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  thus ?thesis unfolding Rc_def by (simp add: norm_divide)
qed

lemma estimation_P\<^sub>t':
  assumes h:
    "1 < x \<and> max 1 C\<^sub>3 \<le> T x" "a x < 1 \<and> 1 < b x"
    "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
    "f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
    and Ht: "\<bar>t\<bar> = T x"
  shows "\<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel> \<le> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
proof -
  consider "t = T x" | "t = - T x" using Ht by fastforce
  hence "f x contour_integrable_on P\<^sub>t x t"
    using Ht h(4) unfolding P\<^sub>t_def P\<^sub>3_def P\<^sub>4_def by cases auto
  moreover have "\<parallel>f x s\<parallel> \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2)"
    when "s \<in> closed_segment (Complex (a x) t) (Complex (b x) t)" for s
  proof -
    have Hs: "s \<in> path_image (P\<^sub>t x t)" using that unfolding P\<^sub>t_def by auto
    have "path_image (P\<^sub>t x t) \<subseteq> rect x"
      by (rule path_image_in_rect_2) (use h(2) Ht in auto)
    moreover have Hs': "Re s \<le> b x" "Im s = t"
    proof -
      have "u \<le> 1 \<Longrightarrow> (1 - u) * a x \<le> (1 - u) * b x" for u
        using h(2) by (intro mult_left_mono) auto
      thus "Re s \<le> b x" "Im s = t"
        using that h(2) unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
    qed
    hence "C\<^sub>3 \<le> \<bar>Im s\<bar>" using h(1) Ht by auto
    ultimately have "s \<in> logderiv_zeta_region" using Hs h(3) by auto
    hence "\<parallel>logderiv zeta s\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
      by (rule logderiv_zeta_region_estimate)
    also have "\<dots> = C\<^sub>2 * (ln (T x + 3))\<^sup>2" using Hs'(2) Ht by auto
    also have "\<parallel>x powr s / s\<parallel> \<le> exp 1 * x / T x"
    proof -
      have "\<parallel>x powr s\<parallel> = Re x powr Re s" using h(1) by (intro norm_powr_real_powr) auto
      also have "\<dots> = x powr Re s" by auto
      also have "\<dots> \<le> x powr b x" by (intro powr_mono Hs') (use h(1) in auto)
      also have "\<dots> = exp 1 * x"
        using h(1) unfolding powr_def b_def by (auto simp add: field_simps exp_add)
      finally have "\<parallel>x powr s\<parallel> \<le> exp 1 * x" .
      moreover have "T x \<le> \<parallel>s\<parallel>" using abs_Im_le_cmod [of s] Hs'(2) h(1) Ht by auto
      hence 1: "\<parallel>x powr s\<parallel> / \<parallel>s\<parallel> \<le> \<parallel>x powr s\<parallel> / T x"
        using h(1) by (intro divide_left_mono mult_pos_pos) auto
      ultimately have "\<dots> \<le> exp 1 * x / T x"
        by (intro divide_right_mono) (use h(1) in auto)
      thus ?thesis using 1 by (subst norm_divide) linarith
    qed
    ultimately show ?thesis unfolding f_def
      by (subst norm_mult, intro mult_mono, auto)
         (metis norm_ge_zero order.trans)
  qed
  ultimately have "\<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel>
    \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2) * \<parallel>Complex (b x) t - Complex (a x) t\<parallel>"
    unfolding P\<^sub>t_def
    by (intro contour_integral_bound_linepath)
       (use C\<^sub>2_gt_zero h(1) in auto)
  also have "\<dots> = C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
    using h(2) by (simp add: legacy_Complex_simps)
  finally show ?thesis .
qed

lemma estimation_P\<^sub>t:
  "(\<lambda>x. \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>) \<in> Rc \<and>
   (\<lambda>x. \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)" for x
  define p where "p x \<equiv> \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel> \<le> r x \<and> \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel> \<le> r x" for x
  have "\<forall>\<^sub>F x in at_top. 1 < x \<and> max 1 C\<^sub>3 \<le> T x"
    unfolding T_def by (rule eventually_conj) (simp, use Hc in real_asymp)
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> = T x \<longrightarrow> \<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel> \<le> r x" (is "eventually ?P _")
    unfolding r_def using asymp_1 rect_in_logderiv_zeta contour_integrability
    by eventually_elim (use estimation_P\<^sub>t' in blast)
  moreover have "\<And>x. ?P x \<Longrightarrow> 0 < T x \<Longrightarrow> p x"
    unfolding p_def P\<^sub>3_def P\<^sub>4_def by auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> 0 < T x \<longrightarrow> p x"
    by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in at_top. p x" using asymp_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in at_top.
    \<parallel>\<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>\<parallel> \<le> 1 * \<parallel>r x\<parallel> \<and>
    \<parallel>\<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>\<parallel> \<le> 1 * \<parallel>r x\<parallel>"
    unfolding p_def by eventually_elim auto
  hence "(\<lambda>x. \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>) \<in> O(r) \<and> (\<lambda>x. \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>) \<in> O(r)"
    by (subst (asm) eventually_conj_iff, blast)+
  moreover have "r \<in> Rc"
    unfolding r_def Rc_def a_def b_def T_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  ultimately show ?thesis
    unfolding Rc_def using landau_o.big_trans by blast
qed

lemma Re_path_P\<^sub>2:
  "\<And>z. z \<in> path_image (P\<^sub>2 x) \<Longrightarrow> Re z = b x"
  unfolding P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

lemma estimation_P\<^sub>2:
  "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x) + x\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv> \<parallel>contour_integral (P\<^sub>1 x) (f x)\<parallel> +
    \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel> + \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>" for x
  have [simp]: "\<parallel>a - b + c\<parallel> \<le> \<parallel>a\<parallel> + \<parallel>b\<parallel> + \<parallel>c\<parallel>" for a b c :: complex
    using adhoc_norm_triangle norm_triangle_ineq4 by blast
  have "\<forall>\<^sub>F x in at_top. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel> \<le> r x"
    unfolding r_def using P\<^sub>2_eq by eventually_elim auto
  hence "(\<lambda>x. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel>) \<in> O(r)"
    by (rule eventually_le_imp_bigo')
  moreover have "r \<in> Rc"
    using estimation_P\<^sub>1 estimation_P\<^sub>t
    unfolding r_def Rc_def by (intro sum_in_bigo) auto
  ultimately have "(\<lambda>x. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel>) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * (contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x)\<parallel>) \<in> Rc"
    unfolding Rc_def by (auto simp add: norm_mult norm_divide)
  thus ?thesis by (auto simp add: algebra_simps)
qed

lemma estimation_R:
  "R \<in> Rc"
proof -
  define \<Gamma> where "\<Gamma> x \<equiv> {n :: nat. x - x / H x \<le> n \<and> n \<le> x + x / H x}" for x
  have 1: "(\<lambda>x. x powr b x * H x * B x / T x) \<in> Rc"
    unfolding b_def H_def B_def T_def Rc_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  have "\<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    when h: "0 < x - x / H x" "0 < x / H x" "0 \<le> ln (x + x / H x)" for x
  proof -
    have "\<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> = (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)"
      by simp (subst abs_of_nonneg, auto intro: sum_nonneg)
    also have "\<dots> = sum mangoldt_real (\<Gamma> x)"
      by (subst norm_fds_mangoldt_complex) (rule refl)
    also have "\<dots> \<le> card (\<Gamma> x) * ln (x + x / H x)"
    proof (rule sum_bounded_above)
      fix n assume "n \<in> \<Gamma> x"
      hence Hn: "0 < n" "n \<le> x + x / H x" unfolding \<Gamma>_def using h by auto
      hence "mangoldt_real n \<le> ln n" by (intro mangoldt_le)
      also have "\<dots> \<le> ln (x + x / H x)" using Hn by auto
      finally show "mangoldt_real n \<le> ln (x + x / H x)" .
    qed
    also have "\<dots> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    proof -
      have \<Gamma>_eq: "\<Gamma> x = {nat \<lceil>x - x / H x\<rceil>..<nat (\<lfloor>x + x / H x\<rfloor> + 1)}"
        unfolding \<Gamma>_def by (subst nat_le_real_iff) (subst nat_ceiling_le_eq [symmetric], auto)
      moreover have "nat (\<lfloor>x + x / H x\<rfloor> + 1) = \<lfloor>x + x / H x\<rfloor> + 1" using h(1) h(2) by auto
      moreover have "nat \<lceil>x - x / H x\<rceil> = \<lceil>x - x / H x\<rceil>" using h(1) by auto
      moreover have "\<lfloor>x + x / H x\<rfloor> \<le> x + x / H x" by (rule floor_le)
      moreover have "\<lceil>x - x / H x\<rceil> \<ge> x - x / H x" by (rule ceil_ge)
      ultimately have "(nat (\<lfloor>x + x / H x\<rfloor> + 1) :: real) - nat \<lceil>x - x / H x\<rceil> \<le> 2 * x / H x + 1" by linarith
      hence "card (\<Gamma> x) \<le> 2 * x / H x + 1" using h(2) by (subst \<Gamma>_eq) (auto simp add: of_nat_diff_real)
      thus ?thesis using h(3) by (rule mult_right_mono)
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top.
    0 < x - x / H x \<longrightarrow> 0 < x / H x \<longrightarrow> 0 \<le> ln (x + x / H x)
    \<longrightarrow> \<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F x in at_top. 0 < x - x / H x" unfolding H_def using Hc H\<epsilon> by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. 0 < x / H x" unfolding H_def using Hc H\<epsilon>  by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. 0 \<le> ln (x + x / H x)" unfolding H_def using Hc H\<epsilon> by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by eventually_elim blast
  hence "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>) \<in> O(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x))"
    by (rule eventually_le_imp_bigo)
  moreover have "(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x)) \<in> Rc'"
    unfolding Rc'_def H_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  ultimately have "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>) \<in> Rc'"
    unfolding Rc'_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>))
      \<in> O(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))))"
    unfolding Rc'_def by (intro landau_o.big.mult_left) auto
  moreover have "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2)))) \<in> Rc"
    unfolding Rc_def T_def b_def using Hc H\<epsilon> by (real_asymp simp add: field_simps)
  ultimately have 2: "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  from 1 2 show ?thesis unfolding Rc_def R_def \<Gamma>_def by (rule sum_in_bigo)
qed

lemma perron_psi:
  "\<forall>\<^sub>F x in at_top. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel> \<le> R x"
proof -
  have Hb: "\<forall>\<^sub>F x in at_top. 1 < b x" unfolding b_def by real_asymp
  hence "\<forall>\<^sub>F x in at_top. 0 < b x" by eventually_elim auto
  moreover have "\<forall>\<^sub>F x in at_top. b x \<le> T x" unfolding b_def T_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. abs_conv_abscissa (fds mangoldt_complex) < ereal (b x)"
  proof -
    have "abs_conv_abscissa (fds mangoldt_complex) \<le> 1" by (rule abs_conv_abscissa_mangoldt)
    hence "\<forall>\<^sub>F x in at_top. 1 < b x \<longrightarrow> abs_conv_abscissa (fds mangoldt_complex) < ereal (b x)"
      by (auto intro: eventuallyI
               simp add: le_ereal_less one_ereal_def)
    thus ?thesis using Hb by (rule eventually_mp)
  qed
  moreover have "\<forall>\<^sub>F x in at_top. 2 \<le> H x" unfolding H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. b x + 1 \<le> H x" unfolding b_def H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x :: real in at_top. 2 \<le> x" by auto
  moreover have "\<forall>\<^sub>F x in at_top.
    (\<Sum>`n\<ge>1. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> / n nat_powr b x) \<le> B x"
    (is "eventually ?P ?F")
  proof -
    have "?P x" when Hb: "1 < b x \<and> b x \<le> 23 / 20" for x
    proof -
      have "(\<Sum>`n\<ge>1. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> / n nat_powr (b x))
          = (\<Sum>`n\<ge>1. mangoldt_real n / n nat_powr (b x))"
        by (subst norm_fds_mangoldt_complex) (rule refl)
      also have "\<dots> = - Re (logderiv zeta (b x))"
      proof -
        have "((\<lambda>n. mangoldt_real n * n nat_powr (-b x) * cos (0 * ln (real n)))
            has_sum Re (- deriv zeta (Complex (b x) 0) / zeta (Complex (b x) 0))) {1..}"
          by (intro sums_Re_logderiv_zeta) (use Hb in auto)
        moreover have "Complex (b x) 0 = b x" by (rule complex_eqI) auto
        moreover have "Re (- deriv zeta (b x) / zeta (b x)) = - Re (logderiv zeta (b x))"
          unfolding logderiv_def by auto
        ultimately have "((\<lambda>n. mangoldt_real n * n nat_powr (-b x)) has_sum
                         - Re (logderiv zeta (b x))) {1..}" by auto
        hence "- Re (logderiv zeta (b x)) = (\<Sum>`n\<ge>1. mangoldt_real n * n nat_powr (-b x))"
          by (intro has_sum_imp_has_subsum subsumI)
        also have "\<dots> = (\<Sum>`n\<ge>1. mangoldt_real n / n nat_powr (b x))"
          by (intro subsum_cong) (auto simp add: powr_minus_divide)
        finally show ?thesis by auto
      qed
      also have "\<dots> \<le> \<bar>Re (logderiv zeta (b x))\<bar>" by auto
      also have "\<dots> \<le> \<parallel>logderiv zeta (b x)\<parallel>" by (rule abs_Re_le_cmod)
      also have "\<dots> \<le> 5 / 4 * (1 / (b x - 1))"
        by (rule logderiv_zeta_bound) (use Hb in auto)
      also have "\<dots> = B x" unfolding b_def B_def by auto
      finally show ?thesis .
    qed
    hence "\<forall>\<^sub>F x in at_top. 1 < b x \<and> b x \<le> 23 / 20 \<longrightarrow> ?P x" by auto
    moreover have "\<forall>\<^sub>F x in at_top. b x \<le> 23 / 20" unfolding b_def by real_asymp
    ultimately show ?thesis using Hb by eventually_elim auto
  qed
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>sum_upto (fds_nth (fds mangoldt_complex)) x - 1 / (2 * pi * \<i>)
      * contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)\<parallel> \<le> R x"
    unfolding R_def P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
    by eventually_elim (rule perron_formula(2))
  moreover have "\<forall>\<^sub>F x in at_top. sum_upto (fds_nth (fds mangoldt_complex)) x = \<psi> x" for x :: real
    unfolding primes_psi_def sum_upto_def by auto
  moreover have
     "contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)
    = contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))"
    when "1 < b x" for x
  proof (rule contour_integral_eq, goal_cases)
    case (1 s)
    hence "Re s = b x" by (rule Re_path_P\<^sub>2)
    hence "eval_fds (fds mangoldt_complex) s = - deriv zeta s / zeta s"
      by (intro eval_fds_mangoldt) (use that in auto)
    thus ?case unfolding logderiv_def by (auto simp add: field_simps)
  qed
  hence "\<forall>\<^sub>F x in at_top. 1 < b x \<longrightarrow>
      contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)
    = contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))"
    using Hb by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>\<psi> x - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))\<parallel> \<le> R x"
    using Hb by eventually_elim auto
  thus ?thesis unfolding f_def
    by eventually_elim (auto simp add: contour_integral_neg)
qed

lemma estimation_perron_psi:
  "(\<lambda>x. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>) \<in> Rc"
proof -
  have "(\<lambda>x. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>) \<in> O(R)"
    by (intro eventually_le_imp_bigo' perron_psi)
  moreover have "R \<in> Rc" by (rule estimation_R)
  ultimately show ?thesis unfolding Rc_def by (rule landau_o.big_trans)
qed

theorem prime_number_theorem:
  "PNT_3 (c / 2 - 2 * \<epsilon>) (1 / 2) 0"
proof -
  define r where "r x \<equiv>
      \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>
    + \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x) + x\<parallel>" for x
  have "\<parallel>\<psi> x - x\<parallel> \<le> r x" for x
  proof -
    have "\<parallel>\<psi> x - x\<parallel> = \<parallel>(\<psi> x :: complex) - x\<parallel>"
      by (fold dist_complex_def, simp add: dist_real_def)
    also have "\<dots> \<le> \<parallel>\<psi> x - - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>
      + \<parallel>x - - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>"
      by (fold dist_complex_def, rule dist_triangle2)
    finally show ?thesis unfolding r_def by (simp add: add_ac)
  qed
  hence "(\<lambda>x. \<psi> x - x) \<in> O(r)" by (rule le_imp_bigo)
  moreover have "r \<in> Rc"
    unfolding r_def Rc_def
    by (intro sum_in_bigo, fold Rc_def)
       (rule estimation_perron_psi, rule estimation_P\<^sub>2)
  ultimately show ?thesis unfolding PNT_3_def
    by (subst Rc_eq_rem_est [symmetric], unfold Rc_def)
       (rule landau_o.big_trans)
qed

no_notation primes_psi ("\<psi>")
end

unbundle prime_counting_notation

theorem prime_number_theorem:
  shows "(\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (- 1 / 3653 * (ln x) powr (1 / 2)))"
proof -
  define c :: real where "c \<equiv> 1 / 1826"
  define \<epsilon> :: real where "\<epsilon> \<equiv> 1 / 26681512"
  interpret z: prime_number_theorem c \<epsilon>
    unfolding c_def \<epsilon>_def by standard (auto simp: C\<^sub>4_def)
  have "PNT_3 (c / 2 - 2 * \<epsilon>) (1 / 2) 0" by (rule z.prime_number_theorem)
  hence "PNT_1 (c / 2 - 2 * \<epsilon>) (1 / 2) 0" by (auto intro: PNT_3_imp_PNT_1)
  thus "(\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (- 1 / 3653 * (ln x) powr (1 / 2)))"
    unfolding PNT_1_def rem_est_def c_def \<epsilon>_def
    by (rule landau_o.big.ev_eq_trans1, use ln_ln_asymp_pos in eventually_elim)
       (auto intro: eventually_at_top_linorderI [of 1] simp: powr_half_sqrt)
qed

hide_const (open) C\<^sub>3 C\<^sub>4 C\<^sub>5
unbundle no_prime_counting_notation
unbundle no_pnt_notation
end
