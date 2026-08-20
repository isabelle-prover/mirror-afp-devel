section \<open>The type of meromorphic functions in the upper half plane\<close>
theory Meromorphic_Upper_Half_Plane
imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Library.Going_To_Filter"
  "Polynomial_Interpolation.Ring_Hom"
  "Elliptic_Functions.Modular_Fundamental_Region"
  Modular_Forms_Library
begin

definition is_mero_uhp :: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "is_mero_uhp f \<longleftrightarrow>
     f nicely_meromorphic_on {z. Im z > 0} \<and>
     (\<forall>z. Im z \<le> 0 \<or> is_pole f z \<longrightarrow> f z = 0)"

typedef mero_uhp =
  "{f :: complex \<Rightarrow> complex. is_mero_uhp f}"
  morphisms eval_mero_uhp Abs_mero_uhp
  by (rule exI[of _ "\<lambda>_. 0"])
     (auto intro: meromorphic_intros simp: is_mero_uhp_def nicely_meromorphic_on_def)

setup_lifting type_definition_mero_uhp

lemma nicely_meromorphic_on_cong:
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z = g z" "open A"
  assumes "A = B"
  shows "f nicely_meromorphic_on A \<longleftrightarrow> g nicely_meromorphic_on B"
proof -
  have *: "eventually (\<lambda>z. f z = g z) (at z)"
    if f: "f meromorphic_on A" and z: "z \<in> A"
    and fg: "\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole f z \<Longrightarrow> f z = g z" for z f g
  proof -
    have "eventually (\<lambda>z. \<not>is_pole f z) (at z)"
      using f z by (metis eventually_not_pole meromorphic_onE)
    moreover have "eventually (\<lambda>z. z \<in> A) (at z)"
      by (intro eventually_at_in_open' assms z)
    ultimately show "eventually (\<lambda>z. f z = g z) (at z)"
      by eventually_elim (use fg in auto)
  qed

  show ?thesis
  proof
    assume "f nicely_meromorphic_on A"
    hence mero: "f meromorphic_on A"
      by (auto simp: nicely_meromorphic_on_def)
    have ev: "eventually (\<lambda>z. f z = g z) (at z)" if "z \<in> A" for z
      by (rule *[OF mero that]) (use assms in auto)
    show "g nicely_meromorphic_on B"
      unfolding nicely_meromorphic_on_def assms(3) [symmetric]
    proof (intro ballI conjI impI)
      have "f meromorphic_on A \<longleftrightarrow> g meromorphic_on A"
        by (intro meromorphic_on_cong ev refl)
      with mero show "g meromorphic_on A"
        by auto
    next
      fix z assume z: "z \<in> A"
      have pole_iff: "is_pole f z \<longleftrightarrow> is_pole g z"
        using ev z by (intro is_pole_cong refl) auto
      show "is_pole g z \<and> g z = 0 \<or> g \<midarrow>z\<rightarrow> g z"
      proof (cases "is_pole g z")
        case False
        with pole_iff have "f \<midarrow>z\<rightarrow> g z"
          using \<open>f nicely_meromorphic_on A\<close> z assms by (auto simp: nicely_meromorphic_on_def)
        also have "?this \<longleftrightarrow> g \<midarrow>z\<rightarrow> g z"
          by (intro tendsto_cong ev z)
        finally show ?thesis
          by blast
      next
        case True
        hence "is_pole f z"
          by (simp add: pole_iff)
        hence "f z = 0"
          using \<open>f nicely_meromorphic_on A\<close> 
          by (metis nicely_meromorphic_on_def remove_sings_at_pole remove_sings_eqI z)
        thus ?thesis using True assms z by auto
      qed
    qed
  next
    assume "g nicely_meromorphic_on B"
    hence mero: "g meromorphic_on A"
      by (auto simp: nicely_meromorphic_on_def \<open>A = B\<close>)
    have ev: "eventually (\<lambda>z. g z = f z) (at z)" if "z \<in> A" for z
      by (rule *[OF mero that]) (use assms in \<open>auto simp: eq_commute\<close>)
    show "f nicely_meromorphic_on A"
      unfolding nicely_meromorphic_on_def assms(3) [symmetric]
    proof (intro ballI conjI impI)
      have "g meromorphic_on A \<longleftrightarrow> f meromorphic_on A"
        by (intro meromorphic_on_cong ev refl)
      with mero show "f meromorphic_on A"
        by auto
    next
      fix z assume z: "z \<in> A"
      have pole_iff: "is_pole f z \<longleftrightarrow> is_pole g z"
        using ev z by (intro is_pole_cong refl) (auto simp: eq_commute)
      show "is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z"
      proof (cases "is_pole f z")
        case False
        with pole_iff have "g \<midarrow>z\<rightarrow> f z"
          using \<open>g nicely_meromorphic_on B\<close> z assms by (auto simp: nicely_meromorphic_on_def)
        also have "?this \<longleftrightarrow> f \<midarrow>z\<rightarrow> f z"
          by (intro ev tendsto_cong z)
        finally show ?thesis
          by blast
      next
        case True
        hence "is_pole g z"
          by (simp add: pole_iff)
        hence "g z = 0"
          using \<open>g nicely_meromorphic_on B\<close> 
          by (metis remove_sings_at_pole remove_sings_eqI 
                assms(3) nicely_meromorphic_on_def z)
        thus ?thesis using True assms z by auto
      qed
    qed
  qed
qed

lift_definition mero_uhp :: "(complex \<Rightarrow> complex) \<Rightarrow> mero_uhp" is
  "\<lambda>f. if f meromorphic_on {z. Im z > 0}
       then (\<lambda>z. if Im z > 0 \<and> \<not>is_pole f z then remove_sings f z else 0)
       else (\<lambda>_. 0)"
proof goal_cases
  case (1 f)
  show ?case
  proof (cases "f meromorphic_on {z. Im z > 0}")
    case False
    thus ?thesis
      by (auto simp: is_mero_uhp_def nicely_meromorphic_on_def intro!: meromorphic_intros)
  next
    case True
    have *: "is_pole (\<lambda>z. if 0 < Im z \<and> \<not> is_pole f z then remove_sings f z else 0) z \<longleftrightarrow>
             is_pole f z" if z: "Im z > 0" for z
    proof -
      have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
        using z by (intro eventually_at_in_open') (auto intro!: open_halfspace_Im_gt)
      moreover have "eventually (\<lambda>z. remove_sings f z = f z) (at z)" using z
        using eventually_remove_sings_eq_at meromorphic_on_isolated_singularity True
              meromorphic_on_subset by auto
      moreover have "eventually (\<lambda>z. \<not>is_pole f z) (at z)"
        by (metis True eventually_not_pole mem_Collect_eq meromorphic_onE z)
      ultimately have "eventually (\<lambda>z. (if 0 < Im z \<and> \<not> is_pole f z then remove_sings f z else 0) = f z) (at z)"
        by eventually_elim auto
      thus ?thesis
        by (intro is_pole_cong) auto
    qed          
    have "remove_sings f nicely_meromorphic_on {z. 0 < Im z}"
      by (intro remove_sings_nicely_meromorphic True)
    also have "?this \<longleftrightarrow> (\<lambda>z. if Im z > 0 \<and> \<not>is_pole f z then remove_sings f z else 0) 
                           nicely_meromorphic_on {z. 0 < Im z}"
      by (intro nicely_meromorphic_on_cong) (auto simp: open_halfspace_Im_gt)
    finally show ?thesis unfolding is_mero_uhp_def using True
      by (auto simp: *)
  qed
qed

lemma mero_uhp_cong_weak: "(\<And>z. Im z > 0 \<Longrightarrow> f z = g z) \<Longrightarrow> mero_uhp f = mero_uhp g"
  by (transfer, intro if_cong meromorphic_on_cong ext refl conj_cong arg_cong[of _ _ Not]
                  is_pole_cong remove_sings_cong
                  eventually_mono[OF eventually_at_in_open[OF open_halfspace_Im_gt[of 0]]]) auto

lemma eval_mero_uhp_outside: "Im z \<le> 0 \<Longrightarrow> eval_mero_uhp f z = 0"
  by transfer (auto simp: is_mero_uhp_def)

lemma eval_mero_uhp_pole: "is_pole (eval_mero_uhp f) z \<Longrightarrow> eval_mero_uhp f z = 0"
  by transfer (auto simp: is_mero_uhp_def)

lemma eval_mero_uhp_mero_uhp_eq:
  assumes "f meromorphic_on {z. Im z > 0}" "Im z > 0"
  shows   "eval_mero_uhp (mero_uhp f) z = remove_sings f z"
  using assms by transfer auto

lemma eval_mero_uhp_mero_uhp:
  assumes "f meromorphic_on {z. Im z > 0}" "f analytic_on {z}" "Im z > 0"
  shows   "eval_mero_uhp (mero_uhp f) z = f z"
  using assms by transfer (auto dest: analytic_at_imp_no_pole)

lemma eval_mero_uhp_meromorphic:
  "eval_mero_uhp f meromorphic_on {z. Im z > 0}"
  by transfer (auto simp: is_mero_uhp_def nicely_meromorphic_on_def intro: meromorphic_on_subset)

lemma eval_mero_uhp_meromorphic':
  "A \<subseteq> {z. Im z > 0} \<Longrightarrow> eval_mero_uhp f meromorphic_on A"
  by transfer (auto simp: is_mero_uhp_def nicely_meromorphic_on_def intro: meromorphic_on_subset)

lemma eventually_eval_mero_uhp_mero_uhp_eq:
  assumes "f meromorphic_on {z. Im z > 0}" "Im z > 0"
  shows   "eventually (\<lambda>w. eval_mero_uhp (mero_uhp f) w = f w) (at z)"
proof -
  have "isolated_singularity_at f z"
    using assms meromorphic_on_isolated_singularity meromorphic_on_subset by blast
  hence "eventually (\<lambda>w. f analytic_on {w}) (at z)"
    by (simp add: isolated_singularity_at_altdef)
  moreover have "eventually (\<lambda>w. w \<in> {w. Im w > 0}) (at z)"
    using assms(2) by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
  ultimately show ?thesis
    by eventually_elim (rule eval_mero_uhp_mero_uhp, use assms in auto)
qed    

lemma is_pole_eval_mero_uhp_mero_uhp_iff:
  assumes "f meromorphic_on {z. Im z > 0}" "Im z > 0"
  shows   "is_pole (eval_mero_uhp (mero_uhp f)) z \<longleftrightarrow> is_pole f z"
  by (intro is_pole_cong eventually_eval_mero_uhp_mero_uhp_eq assms refl)

lemma eval_mero_uhp_nicely_meromorphic:
  "A \<subseteq> {z. Im z > 0} \<Longrightarrow> eval_mero_uhp f nicely_meromorphic_on A"
  by transfer (auto simp: is_mero_uhp_def nicely_meromorphic_on_def intro: meromorphic_on_subset)

lemma eval_mero_uhp_analytic:
  assumes "\<not>is_pole (eval_mero_uhp f) z" "Im z > 0"
  shows   "eval_mero_uhp f analytic_on {z}"
proof -
  have "eval_mero_uhp f nicely_meromorphic_on {z}"
    by (rule eval_mero_uhp_nicely_meromorphic) (use assms(2) in auto)
  thus ?thesis
    using assms nicely_meromorphic_on_imp_analytic_at by blast
qed

lemma not_is_pole_eval_mero_uhp_outside:
  assumes "Im z \<le> 0"
  shows   "\<not>is_pole (eval_mero_uhp f) z"
proof
  assume "is_pole (eval_mero_uhp f) z"
  moreover have "LIM x at_right 0. z - complex_of_real x * \<i> :> at z"
  proof (rule filterlim_atI)
    show "((\<lambda>x. z - complex_of_real x * \<i>) \<longlongrightarrow> z) (at_right 0)"
      by (auto intro!: tendsto_eq_intros)
  next
    have "eventually (\<lambda>x::real. x \<noteq> 0) (at_right 0)"
      by (intro eventually_neq_at_within)
    thus "\<forall>\<^sub>F x in at_right 0. z - complex_of_real x * \<i> \<noteq> z"
      by eventually_elim auto
  qed
  ultimately have "filterlim (eval_mero_uhp f \<circ> (\<lambda>x. z - of_real x * \<i>)) at_infinity (at_right 0)"
    unfolding is_pole_def o_def by (rule filterlim_compose)
  moreover {
    have "eventually (\<lambda>x::real. x > 0) (at_right 0)"
      by (auto simp: eventually_at_topological)
    hence "eventually (\<lambda>x. (eval_mero_uhp f \<circ> (\<lambda>x. z - of_real x * \<i>)) x = 0) (at_right 0)"
      by eventually_elim (use assms in \<open>auto simp: eval_mero_uhp_outside\<close>)
    hence "((eval_mero_uhp f \<circ> (\<lambda>x. z - of_real x * \<i>)) \<longlongrightarrow> 0) (at_right 0)"
      using tendsto_eventually by blast
  }
  moreover have "at_right (0 :: real) \<noteq> bot"
    by simp
  ultimately show False
    using not_tendsto_and_filterlim_at_infinity by blast
qed

lemma meromorphic_on_eval_mero_uhp' [meromorphic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "(\<lambda>w. eval_mero_uhp f (g w)) meromorphic_on A"
  by (rule meromorphic_on_compose[OF eval_mero_uhp_meromorphic'[OF order.refl] assms(1)])
     (use assms(2) in auto)

lemma analytic_on_eval_mero_uhp [analytic_intros]:
  "(\<And>z. z \<in> A \<Longrightarrow> Im z > 0) \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole (eval_mero_uhp f) z) \<Longrightarrow>
     eval_mero_uhp f analytic_on A"
  using eval_mero_uhp_analytic analytic_on_analytic_at by blast

lemma holomorphic_on_eval_mero_uhp [holomorphic_intros]:
  "(\<And>z. z \<in> A \<Longrightarrow> Im z > 0) \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole (eval_mero_uhp f) z) \<Longrightarrow>
     eval_mero_uhp f holomorphic_on A"
  by (intro analytic_imp_holomorphic analytic_intros)

lemma analytic_on_eval_mero_uhp' [analytic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0 \<and> \<not>is_pole (eval_mero_uhp f) (g z)"
  shows   "(\<lambda>w. eval_mero_uhp f (g w)) analytic_on A"
  by (rule analytic_on_compose[OF assms(1) analytic_on_eval_mero_uhp, unfolded o_def])
     (use assms(2) in auto)

lemma holomorphic_on_eval_mero_uhp' [holomorphic_intros]:
  assumes "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0 \<and> \<not>is_pole (eval_mero_uhp f) (g z)"
  shows   "(\<lambda>w. eval_mero_uhp f (g w)) holomorphic_on A"
  by (rule holomorphic_on_compose[OF assms(1) holomorphic_on_eval_mero_uhp, unfolded o_def])
     (use assms(2) in auto)


definition const_mero_uhp :: "complex \<Rightarrow> mero_uhp" where
  "const_mero_uhp c = mero_uhp (\<lambda>_. c)"

lemma eval_const_mero_uhp [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp (const_mero_uhp c) z = c"
  unfolding const_mero_uhp_def
  by (rule eval_mero_uhp_mero_uhp) auto

lemma not_pole_const_mero_uhp [simp]: "Im z > 0 \<Longrightarrow> \<not>is_pole (eval_mero_uhp (const_mero_uhp c)) z"
  unfolding const_mero_uhp_def by (subst is_pole_eval_mero_uhp_mero_uhp_iff) auto

declare [[coercion eval_mero_uhp]]

lemma not_essential_frequently_0_imp_eventually_0':
  fixes f :: "complex \<Rightarrow> complex"
  assumes sing: "isolated_singularity_at f z" "not_essential f z"
  assumes freq: "frequently (\<lambda>z. f z = 0) (at z within A)"
  shows   "eventually (\<lambda>z. f z = 0) (at z within B)"
proof -
  from freq have "frequently (\<lambda>z. f z = 0) (at z)"
    unfolding frequently_def by (auto simp: eventually_at_topological)
  from not_essential_frequently_0_imp_eventually_0[OF sing this] show ?thesis
    by (metis UNIV_I eventually_at_topological)
qed

lemma frequently_eq_at_imp_eq_at:
  assumes "frequently (\<lambda>z. f z = g z) (at z within A)"
  assumes "f analytic_on {z}" "g analytic_on {z}"
  shows   "f z = g z"
proof -
  have "(\<lambda>z. f z - g z) analytic_on {z}"
    by (intro analytic_intros assms)
  hence "isolated_singularity_at (\<lambda>z. f z - g z) z" "not_essential (\<lambda>z. f z - g z) z"
    using isolated_singularity_at_analytic not_essential_analytic by blast+
  moreover have "\<exists>\<^sub>F z in at z within A. f z - g z = 0"
    using assms(1) by simp
  ultimately have ev: "eventually (\<lambda>z. f z - g z = 0) (at z)"
    by (rule not_essential_frequently_0_imp_eventually_0')

  have "filterlim (\<lambda>z. f z - g z) (nhds (f z - g z)) (at z)"
    by (intro isContD analytic_at_imp_isCont assms analytic_intros)
  also have "?this \<longleftrightarrow> filterlim (\<lambda>z. 0) (nhds (f z - g z)) (at z)"
    by (intro tendsto_cong eventually_mono[OF ev]) auto
  finally have lim1: "((\<lambda>z. 0) \<longlongrightarrow> f z - g z) (at z)"
    by simp
  moreover have lim2: "((\<lambda>z. 0) \<longlongrightarrow> 0) (at z)"
    by simp
  show ?thesis
    using tendsto_unique[OF _ lim1 lim2] by (auto simp: trivial_limit_within)
qed

lemma mero_uhp_eqI_strong:
  fixes f g :: mero_uhp
  assumes "frequently (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp g z) (cosparse {z. Im z > 0})"
  shows "f = g"
proof -
  let ?f = "eval_mero_uhp f" and ?g = "eval_mero_uhp g"
  let ?h = "\<lambda>z. ?f z - ?g z"
  have "(\<forall>\<^sub>\<approx>z | Im z > 0. ?h z = 0) \<or> (\<forall>\<^sub>\<approx>z | Im z > 0. ?h z \<noteq> 0)"
  proof (rule meromorphic_imp_constant_or_avoid)
    show "?h meromorphic_on {z. Im z > 0}"
      by (intro meromorphic_intros) auto
  qed (auto intro: open_halfspace_Im_gt connected_halfspace_Im_gt)
  with assms have ev: "\<forall>\<^sub>\<approx>z | Im z > 0. ?h z = 0"
    by (auto simp: frequently_def)
  have pole_iff: "is_pole ?f z \<longleftrightarrow> is_pole ?g z" if "Im z > 0" for z
    using that ev
    by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt)

  have "?f z = ?g z" for z
  proof -
    consider "Im z \<le> 0" | "Im z > 0" "is_pole ?f z" | "Im z > 0" "\<not>is_pole ?f z"
      by linarith
    thus ?thesis
    proof cases
      assume "Im z > 0" "is_pole ?f z"
      thus "?f z = ?g z"
        using pole_iff[of z] by (simp add: eval_mero_uhp_pole)
    next
      assume "Im z > 0" "\<not>is_pole ?f z"
      hence ana: "?f analytic_on {z}" "?g analytic_on {z}"
        using eval_mero_uhp_analytic pole_iff by blast+
      have "\<exists>\<^sub>F z in at z. eval_mero_uhp f z = eval_mero_uhp g z"
        by (intro eventually_frequently)
           (use ev \<open>Im z > 0\<close> in \<open>auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt\<close>)
      from this and ana show "?f z = ?g z"
        by (rule frequently_eq_at_imp_eq_at)
    qed (auto simp: eval_mero_uhp_outside)
  qed    
  hence "eval_mero_uhp f = eval_mero_uhp g"
    by blast
  thus "f = g"
    using eval_mero_uhp_inject by blast
qed

lemma mero_uhp_eqI_strong':
  fixes f g :: mero_uhp
  assumes "frequently (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp g z) (at z0)" "Im z0 > 0"
  shows "f = g"
proof (rule mero_uhp_eqI_strong)
  show "\<exists>\<^sub>F z in cosparse {z. 0 < Im z}. eval_mero_uhp f z = eval_mero_uhp g z"
    using assms unfolding frequently_def
    by (subst eventually_cosparse_open_eq) (auto simp: open_halfspace_Im_gt)
qed

lemma mero_uhp_eqI:
  fixes f g :: mero_uhp
  assumes "eventually (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp g z) (cosparse {z. Im z > 0})"
  shows "f = g"
  by (intro mero_uhp_eqI_strong eventually_frequently assms) (auto intro: exI[of _ \<i>])

lemma mero_uhp_eqI_weak:
  fixes f g :: mero_uhp
  assumes "\<And>z. Im z > 0 \<Longrightarrow> eval_mero_uhp f z = eval_mero_uhp g z"
  shows "f = g"
proof -
  have "eval_mero_uhp f = eval_mero_uhp g"
  proof
    fix z show "eval_mero_uhp f z = eval_mero_uhp g z"
      by (cases "Im z > 0") (use assms in \<open>auto simp: eval_mero_uhp_outside\<close>)
  qed
  thus ?thesis
    by (simp only: eval_mero_uhp_inject)
qed



lemma frequently_eval_mero_uhp_eq_imp_const:
  assumes "frequently (\<lambda>w. eval_mero_uhp f w = c) (at z)" "Im z > 0"
  shows   "f = const_mero_uhp c"
proof (rule mero_uhp_eqI_strong')
  have ev: "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
    by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms(2) in auto)
  show "\<exists>\<^sub>F z in at z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z"
    by (rule frequently_elim1[OF frequently_eventually_frequently[OF assms(1) ev]]) auto
qed fact+

lemma eventually_neq_eval_mero_uhp:
  assumes "f \<noteq> const_mero_uhp c" "Im z > 0"
  shows   "eventually (\<lambda>z. eval_mero_uhp f z \<noteq> c) (at z)"
  using frequently_eval_mero_uhp_eq_imp_const[of f c z] assms by (auto simp: frequently_def)


definition mero_uhp_rel where
  "mero_uhp_rel f g \<longleftrightarrow> eventually (\<lambda>z. f z = g z) (cosparse {z. Im z > 0})"

named_theorems mero_uhp_rel_intros

lemma mero_uhp_rel_refl [simp, intro]: "mero_uhp_rel f f"
  by (simp add: mero_uhp_rel_def)
         
lemma mero_uhp_rel_sym: "mero_uhp_rel f g \<Longrightarrow> mero_uhp_rel g f"
  by (simp add: mero_uhp_rel_def eq_commute)

lemma mero_uhp_rel_sym_eq: "mero_uhp_rel f g \<longleftrightarrow> mero_uhp_rel g f"
  by (simp add: mero_uhp_rel_def eq_commute)

lemma mero_uhp_rel_trans [trans]: "mero_uhp_rel f g \<Longrightarrow> mero_uhp_rel g h \<Longrightarrow> mero_uhp_rel f h"
  unfolding mero_uhp_rel_def by (erule (1) eventually_elim2) simp_all

lemma mero_uhp_relI_weak:
  assumes "\<And>z. Im z > 0 \<Longrightarrow> f z = g z"
  shows   "mero_uhp_rel f g"
proof -
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
    by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
  thus ?thesis
    unfolding mero_uhp_rel_def by eventually_elim (use assms in auto)
qed

lemma mero_uhp_rel_mero_uhp [mero_uhp_rel_intros]:
  assumes "f meromorphic_on {z. Im z > 0}"
  shows   "mero_uhp_rel (eval_mero_uhp (mero_uhp f)) f"
  unfolding mero_uhp_rel_def
  by (subst eventually_cosparse_open_eq[OF open_halfspace_Im_gt])
     (use eventually_eval_mero_uhp_mero_uhp_eq assms in blast)

lemma mero_uhp_rel_imp_eq_mero_uhp:
  "mero_uhp_rel (eval_mero_uhp f) (eval_mero_uhp g) \<Longrightarrow> f = g"
  unfolding mero_uhp_rel_def by (rule mero_uhp_eqI)


definition deriv_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp" where
  "deriv_mero_uhp f = mero_uhp (deriv f)"

lemma mero_uhp_rel_unop:
  assumes "mero_uhp_rel f f'"
  shows   "mero_uhp_rel (\<lambda>z. h (f z)) (\<lambda>z. h (f' z))"
  using assms unfolding mero_uhp_rel_def by eventually_elim auto

lemma mero_uhp_rel_binop:
  assumes "mero_uhp_rel f f'" "mero_uhp_rel g g'"
  shows   "mero_uhp_rel (\<lambda>z. h (f z) (g z)) (\<lambda>z. h (f' z) (g' z))"
  using assms unfolding mero_uhp_rel_def by eventually_elim auto


named_theorems mero_uhp_rel_cong

lemmas mero_uhp_rel_cong_uminus [mero_uhp_rel_cong] = mero_uhp_rel_unop[where h = "\<lambda>x. -x"]
lemmas mero_uhp_rel_cong_inverse [mero_uhp_rel_cong] = mero_uhp_rel_unop[where h = "inverse"]
lemmas mero_uhp_rel_cong_add [mero_uhp_rel_cong] = mero_uhp_rel_binop[where h = "(+)"]
lemmas mero_uhp_rel_cong_diff [mero_uhp_rel_cong] = mero_uhp_rel_binop[where h = "(-)"]
lemmas mero_uhp_rel_cong_mult [mero_uhp_rel_cong] = mero_uhp_rel_binop[where h = "(*)"]
lemmas mero_uhp_rel_cong_divide [mero_uhp_rel_cong] = mero_uhp_rel_binop[where h = "(/)"]
lemmas mero_uhp_rel_cong_power [mero_uhp_rel_cong] = mero_uhp_rel_unop[where h = "\<lambda>z. z ^ n" for n]
lemmas mero_uhp_rel_cong_powi [mero_uhp_rel_cong] = mero_uhp_rel_unop[where h = "\<lambda>z. z powi n" for n]

lemma mero_uhp_rel_cong_sum [mero_uhp_rel_cong]:
  "(\<And>x. x \<in> A \<Longrightarrow> mero_uhp_rel (f x) (f' x)) \<Longrightarrow> 
         mero_uhp_rel (\<lambda>z. sum (\<lambda>x. f x z) A) (\<lambda>z. sum (\<lambda>x. f' x z) A)"
  by (induction A rule: infinite_finite_induct) (auto intro!: mero_uhp_rel_cong)

lemma mero_uhp_rel_cong_prod [mero_uhp_rel_cong]:
  "(\<And>x. x \<in> A \<Longrightarrow> mero_uhp_rel (f x) (f' x)) \<Longrightarrow> 
         mero_uhp_rel (\<lambda>z. prod (\<lambda>x. f x z) A) (\<lambda>z. prod (\<lambda>x. f' x z) A)"
  by (induction A rule: infinite_finite_induct) (auto intro!: mero_uhp_rel_cong)

lemma sparse_in_union':
  assumes "pts1 sparse_in D" "pts2 sparse_in D"
  shows "(pts1 \<union> pts2) sparse_in D" 
  using sparse_in_union[OF assms, of D] by simp

lemma mero_uhp_rel_cong_deriv [mero_uhp_rel_cong]:
  assumes "mero_uhp_rel f g"
  shows   "mero_uhp_rel (deriv f) (deriv g)"
proof -
  define pts where "pts = {z. f z \<noteq> g z}"
  have "pts sparse_in {z. Im z > 0}"
    using assms unfolding pts_def by (auto simp: mero_uhp_rel_def eventually_cosparse)
  hence ev: "eventually (\<lambda>z. z \<notin> pts) (cosparse {z. Im z > 0})"
    by (simp add: eventually_cosparse)

  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
    by (metis dual_order.refl eventually_in_cosparse open_halfspace_Im_gt)
  hence "eventually (\<lambda>z. deriv f z = deriv g z) (cosparse {z. Im z > 0})"
    using ev
  proof eventually_elim
    case z: (elim z)    
    have "eventually (\<lambda>z. z \<notin> pts) (at z)"
      using ev z by (subst (asm) eventually_cosparse_open_eq[OF open_halfspace_Im_gt]) auto
    with z(2) have "eventually (\<lambda>z. z \<notin> pts) (nhds z)"
      using eventually_nhds_conv_at by blast
    hence "eventually (\<lambda>z. f z = g z) (nhds z)"
      by eventually_elim (auto simp: pts_def)
    thus "deriv f z = deriv g z"
      by (intro deriv_cong_ev refl)
  qed
  thus ?thesis
    by (simp add: mero_uhp_rel_def)
qed

lemma mero_uhp_rel_cong_higher_deriv [mero_uhp_rel_cong]:
  "mero_uhp_rel f g \<Longrightarrow> mero_uhp_rel ((deriv ^^ n) f) ((deriv ^^ n) g)"
  by (induction n) (auto intro: mero_uhp_rel_cong_deriv)

lemma mero_uhp_rel_simpI: "mero_uhp_rel f h \<Longrightarrow> mero_uhp_rel g h' \<Longrightarrow> h = h' \<Longrightarrow> mero_uhp_rel f g"
  using mero_uhp_rel_sym mero_uhp_rel_trans by blast

lemma mero_uhp_rel_eval_mero_uhp_const [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (const_mero_uhp c)) (\<lambda>_. c)"
  unfolding const_mero_uhp_def by (intro mero_uhp_rel_intros) auto


lemma eval_deriv_mero_uhp:
  assumes "Im z > 0" "\<not>is_pole (eval_mero_uhp f) z"
  shows   "eval_mero_uhp (deriv_mero_uhp f) z = deriv (eval_mero_uhp f) z"
  unfolding deriv_mero_uhp_def
  by (rule eval_mero_uhp_mero_uhp) (use assms in \<open>auto intro!: meromorphic_intros analytic_intros\<close>)

lemma is_pole_deriv_mero_uhp_iff:
  assumes "Im z > 0"
  shows   "is_pole (eval_mero_uhp (deriv_mero_uhp f)) z \<longleftrightarrow> is_pole (eval_mero_uhp f) z"
proof -
  have "is_pole (eval_mero_uhp (deriv_mero_uhp f)) z \<longleftrightarrow> is_pole (deriv (eval_mero_uhp f)) z"
    unfolding deriv_mero_uhp_def
    using assms by (intro is_pole_eval_mero_uhp_mero_uhp_iff meromorphic_intros) auto
  also have "\<dots> \<longleftrightarrow> is_pole (eval_mero_uhp f) z"
    by (intro is_pole_deriv_iff meromorphic_on_isolated_singularity meromorphic_on_not_essential
              meromorphic_intros) (use assms in auto)
  finally show ?thesis .
qed

lemma mero_uhp_rel_imp_eval_mero_uhp_eq:
  assumes "mero_uhp_rel (eval_mero_uhp f) g"
  assumes "g analytic_on {z}" "Im z > 0"
  shows   "eval_mero_uhp f z = g z"
proof -
  from assms have ev: "eventually (\<lambda>z. f z = g z) (at z)"
    by (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
  with assms have "f analytic_on {z}"
    using analytic_at_imp_no_pole eval_mero_uhp_analytic is_pole_cong by blast
  hence "f \<midarrow>z\<rightarrow> f z"
    by (intro isContD analytic_at_imp_isCont)
  also have "?this \<longleftrightarrow> g \<midarrow>z\<rightarrow> f z"
    by (intro tendsto_cong ev)
  finally have "g \<midarrow>z\<rightarrow> f z" .
  moreover from assms(2) have "g \<midarrow>z\<rightarrow> g z"
    by (intro isContD analytic_at_imp_isCont)
  ultimately show ?thesis
    using LIM_unique by blast
qed

lemma mero_uhp_rel_const_refl: "mero_uhp_rel (\<lambda>_. c) (\<lambda>_. c)"
  by (rule mero_uhp_rel_refl)

method_setup mero_uhp_rel = \<open>
let
  fun tac ctxt simp =
    let
      fun rtac ctxt thms = DETERM o resolve_tac ctxt thms
      val raw_intros =
        Named_Theorems.get ctxt @{named_theorems mero_uhp_rel_intros}
      val extra_intros =
        maps (Named_Theorems.get ctxt)
          [@{named_theorems mero_uhp_rel_cong},
           @{named_theorems meromorphic_intros},
           @{named_theorems analytic_intros}] @ @{thms eval_mero_uhp_meromorphic}
      val intros = map (fn thm => thm RS @{thm mero_uhp_rel_trans}) raw_intros
      val intros = intros @ extra_intros
      val tac' =
        TRY o REPEAT_ALL_NEW (rtac ctxt (@{thm mero_uhp_rel_const_refl} :: intros))
        THEN_ALL_NEW TRY o rtac ctxt @{thms mero_uhp_rel_refl}
    in SELECT_GOAL (
      HEADGOAL (rtac ctxt @{thms mero_uhp_rel_imp_eq_mero_uhp[OF mero_uhp_rel_simpI] mero_uhp_rel_simpI})
      THEN HEADGOAL (RANGE [tac', tac', if simp then simp_tac ctxt THEN_ALL_NEW K no_tac else K all_tac])
      )
    end
  val parser = Scan.optional (Args.parens (Args.$$$ "nosimp" >> K false)) true
in
  Scan.lift parser >> (fn simp => fn ctxt => SIMPLE_METHOD' (tac ctxt simp))
end
\<close>

lemma mero_uhp_eval_mero_uhp [simp]: "mero_uhp (eval_mero_uhp f) = f"
  by mero_uhp_rel auto

lemma mero_uhp_rel_deriv [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (deriv_mero_uhp f)) (deriv (eval_mero_uhp f))"
  unfolding deriv_mero_uhp_def by mero_uhp_rel auto

lemma mero_uhp_rel_higher_deriv [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp ((deriv_mero_uhp ^^ n) f)) ((deriv ^^ n) (eval_mero_uhp f))"
proof (induction n)
  case [mero_uhp_rel_intros]: (Suc n)
  show ?case
    unfolding funpow.simps o_def by mero_uhp_rel
qed auto


lemma has_field_derivative_deriv_mero_uhp [derivative_intros]:
  assumes "Im z > 0" "\<not>is_pole (eval_mero_uhp f) z"
  shows   "(eval_mero_uhp f has_field_derivative eval_mero_uhp (deriv_mero_uhp f) z) (at z)"
proof -
  have "eval_mero_uhp f analytic_on {z}"
    using assms eval_mero_uhp_analytic by blast
  hence "(eval_mero_uhp f has_field_derivative deriv (eval_mero_uhp f) z) (at z)"
    using analytic_at_two holomorphic_derivI by blast
  also have "deriv (eval_mero_uhp f) z = deriv_mero_uhp f z"
    unfolding deriv_mero_uhp_def using assms
    by (subst eval_mero_uhp_mero_uhp) (auto intro!: meromorphic_intros analytic_intros)
  finally show ?thesis .
qed

lemma has_field_derivative_deriv_mero_uhp' [derivative_intros]:
  assumes "(g has_field_derivative g') (at z within A)"
  assumes "Im (g z) > 0" "\<not>is_pole (eval_mero_uhp f) (g z)"
  shows   "((\<lambda>z. eval_mero_uhp f (g z)) has_field_derivative
             eval_mero_uhp (deriv_mero_uhp f) (g z) * g') (at z within A)"
  using DERIV_chain[OF has_field_derivative_deriv_mero_uhp[of _ f] assms(1)] assms(2,3)
  by (auto simp: o_def)


instantiation mero_uhp :: comm_ring_1
begin

definition zero_mero_uhp where "zero_mero_uhp = const_mero_uhp 0"

definition one_mero_uhp where "one_mero_uhp = const_mero_uhp 1"

definition plus_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" where
  "f + g = mero_uhp (\<lambda>z. eval_mero_uhp f z + eval_mero_uhp g z)"

definition uminus_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp" where
  "-f = mero_uhp (\<lambda>z. -eval_mero_uhp f z)"

definition minus_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" where
  "f - g = mero_uhp (\<lambda>z. eval_mero_uhp f z - eval_mero_uhp g z)"

definition times_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" where
  "f * g = mero_uhp (\<lambda>z. eval_mero_uhp f z * eval_mero_uhp g z)"

lemma mero_uhp_rel_eval_mero_uhp_0 [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp 0) (\<lambda>_. 0)"
  and mero_uhp_rel_eval_mero_uhp_1 [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp 1) (\<lambda>_. 1)"
  and mero_uhp_rel_eval_mero_uhp_minus [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (-f)) (\<lambda>z. -eval_mero_uhp f z)"
  and mero_uhp_rel_eval_mero_uhp_add [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (f + g)) (\<lambda>z. eval_mero_uhp f z + eval_mero_uhp g z)"
  and mero_uhp_rel_eval_mero_uhp_diff [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (f - g)) (\<lambda>z. eval_mero_uhp f z - eval_mero_uhp g z)"
  and mero_uhp_rel_eval_mero_uhp_times [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (f * g)) (\<lambda>z. eval_mero_uhp f z * eval_mero_uhp g z)"
  unfolding zero_mero_uhp_def one_mero_uhp_def uminus_mero_uhp_def 
            plus_mero_uhp_def minus_mero_uhp_def times_mero_uhp_def
  by (mero_uhp_rel; simp; fail)+

lemma eval_mero_uhp_0 [simp]: "eval_mero_uhp 0 = (\<lambda>_. 0)"
proof
  show "eval_mero_uhp 0 z = 0" for z
    by (cases "Im z > 0") (auto simp: zero_mero_uhp_def eval_mero_uhp_outside)
qed

lemma eval_mero_uhp_1 [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp 1 z = 1"
  unfolding one_mero_uhp_def by (cases "Im z > 0") (auto simp: eval_mero_uhp_outside)

lemma not_pole_0_mero_uhp [simp]: "Im z > 0 \<Longrightarrow> \<not>is_pole (eval_mero_uhp 0) z"
  and not_pole_1_mero_uhp [simp]: "Im z > 0 \<Longrightarrow> \<not>is_pole (eval_mero_uhp 1) z"
  unfolding zero_mero_uhp_def one_mero_uhp_def by auto

lemma
  assumes "Im z > 0" "\<not>is_pole (eval_mero_uhp f) z" "\<not>is_pole (eval_mero_uhp g) z"
  shows eval_mero_uhp_add [simp]: "eval_mero_uhp (f + g) z = eval_mero_uhp f z + eval_mero_uhp g z"
  and   eval_mero_uhp_diff [simp]: "eval_mero_uhp (f - g) z = eval_mero_uhp f z - eval_mero_uhp g z"
  and   eval_mero_uhp_mult [simp]: "eval_mero_uhp (f * g) z = eval_mero_uhp f z * eval_mero_uhp g z"
  using assms
  unfolding plus_mero_uhp_def minus_mero_uhp_def times_mero_uhp_def
  by (subst eval_mero_uhp_mero_uhp; force intro!: meromorphic_intros analytic_intros)+

instance proof -
  have "eval_mero_uhp 0 \<i> = 0" "eval_mero_uhp 1 \<i> \<noteq> 0"
    by auto
  hence "0 \<noteq> (1 :: mero_uhp)"
    by force
  show "OFCLASS(mero_uhp, comm_ring_1_class)"
    by standard (fact | mero_uhp_rel (nosimp), simp add: algebra_simps)+
qed

end

lemma eval_mero_uhp_cmult [simp]:
  "eval_mero_uhp (const_mero_uhp c * f) z = c * eval_mero_uhp f z"
proof (cases "c = 0")
  case True
  thus ?thesis by (simp flip: zero_mero_uhp_def)
next
  case [simp]: False
  have [simp]: "eval_mero_uhp (const_mero_uhp c * f) z = c * eval_mero_uhp f z"
    if "\<not>is_pole f z" for z
  proof (cases "Im z > 0")
    case True
    thus ?thesis
      unfolding times_mero_uhp_def using that
      by (subst eval_mero_uhp_mero_uhp; force intro!: meromorphic_intros analytic_intros)+
  qed (auto simp: eval_mero_uhp_outside)

  show ?thesis
  proof (cases "Im z > 0")
    case True
    have ev: "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
      using True by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
    moreover have "eventually (\<lambda>z. \<not>is_pole f z) (at z)"
      by (metis True eval_mero_uhp_meromorphic eventually_not_pole mem_Collect_eq meromorphic_onE)
    ultimately have "eventually (\<lambda>z. eval_mero_uhp (const_mero_uhp c * f) z = c * eval_mero_uhp f z) (at z)"
      by eventually_elim auto
    hence "is_pole (eval_mero_uhp (const_mero_uhp c * f)) z \<longleftrightarrow> is_pole (\<lambda>z. c * f z) z"
      by (intro is_pole_cong) auto
    thus ?thesis
      by (cases "is_pole f z") (auto simp: eval_mero_uhp_pole)
  qed (auto simp: eval_mero_uhp_outside)
qed

lemma eval_mero_uhp_cmult' [simp]:
  "eval_mero_uhp (f * const_mero_uhp c) z = eval_mero_uhp f z * c"
  using eval_mero_uhp_cmult[of c f z] by (simp only: mult.commute)

lemma const_mero_uhp_eq_iff [simp]: "const_mero_uhp c = const_mero_uhp c' \<longleftrightarrow> c = c'"
proof
  assume "const_mero_uhp c = const_mero_uhp c'"
  hence "eval_mero_uhp (const_mero_uhp c) \<i> = eval_mero_uhp (const_mero_uhp c') \<i>"
    by (simp only: )
  thus "c = c'"
    by simp
qed auto

lemma const_mero_uhp_eq_0_iff [simp]: "const_mero_uhp c = 0 \<longleftrightarrow> c = 0"
  unfolding zero_mero_uhp_def by simp

lemma const_mero_uhp_eq_1_iff [simp]: "const_mero_uhp c = 1 \<longleftrightarrow> c = 1"
  unfolding one_mero_uhp_def by simp

interpretation const_mero_uhp: comm_ring_hom const_mero_uhp
  by standard mero_uhp_rel+

lemma eval_mero_uhp_minus [simp]: "eval_mero_uhp (-f) z = -eval_mero_uhp f z"
  using eval_mero_uhp_cmult[of "-1" f z] by (simp del: eval_mero_uhp_cmult add: hom_distribs)

lemma of_nat_mero_uhp: "of_nat n = const_mero_uhp (of_nat n)"
  by (induction n) (simp_all add: const_mero_uhp.hom_add)

lemma of_int_mero_uhp: "of_int n = const_mero_uhp (of_int n)"
  by (metis const_mero_uhp.hom_uminus int_cases2 of_int_minus of_int_of_nat_eq of_nat_mero_uhp)

lemma numeral_mero_uhp: "numeral n = const_mero_uhp (numeral n)"
  by (subst of_nat_numeral [symmetric], subst of_nat_mero_uhp) simp

lemma mero_uhp_rel_of_nat [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (of_nat n)) (\<lambda>_. of_nat n)"
  unfolding of_nat_mero_uhp by mero_uhp_rel

lemma mero_uhp_rel_of_int [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (of_int n)) (\<lambda>_. of_int n)"
  unfolding of_int_mero_uhp by mero_uhp_rel

lemma mero_uhp_rel_numeral [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (numeral n)) (\<lambda>_. numeral n)"
  unfolding numeral_mero_uhp by mero_uhp_rel

lemma mero_uhp_rel_sum [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (\<Sum>x\<in>A. f x)) (\<lambda>z. \<Sum>x\<in>A. eval_mero_uhp (f x) z)"
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  note [mero_uhp_rel_intros] = insert.IH
  show ?case
    using insert.hyps by simp mero_uhp_rel
qed (simp; mero_uhp_rel; fail)+

lemma mero_uhp_rel_prod [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (\<Prod>x\<in>A. f x)) (\<lambda>z. \<Prod>x\<in>A. eval_mero_uhp (f x) z)"
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  note [mero_uhp_rel_intros] = insert.IH
  show ?case
    using insert.hyps by simp mero_uhp_rel
qed (simp; mero_uhp_rel; fail)+

lemma mero_uhp_rel_power [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (f ^ n)) (\<lambda>z. eval_mero_uhp f z ^ n)"
proof (induction n)
  case 0
  show ?case by simp mero_uhp_rel
next
  case (Suc n)
  have "mero_uhp_rel (eval_mero_uhp (f ^ Suc n)) (\<lambda>z. eval_mero_uhp f z * eval_mero_uhp (f ^ n) z)"
    unfolding power_Suc by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. eval_mero_uhp f z ^ Suc n)"
    unfolding power_Suc by (intro mero_uhp_rel_cong mero_uhp_rel_refl Suc)
  finally show ?case .
qed


instantiation mero_uhp :: field_char_0
begin

definition inverse_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp" where
  "inverse f = mero_uhp (\<lambda>z. inverse (eval_mero_uhp f z))"

definition divide_mero_uhp :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" where
  "divide_mero_uhp f g = f * inverse g"

lemma mero_uhp_rel_eval_mero_uhp_inverse [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (inverse f)) (\<lambda>z. inverse (eval_mero_uhp f z))"
  unfolding inverse_mero_uhp_def by mero_uhp_rel auto

lemma mero_uhp_rel_eval_mero_uhp_divide [mero_uhp_rel_intros]:
       "mero_uhp_rel (eval_mero_uhp (f div g)) (\<lambda>z. eval_mero_uhp f z / eval_mero_uhp g z)"
  unfolding divide_mero_uhp_def by (mero_uhp_rel (nosimp)) (simp add: field_simps)

lemma eval_mero_uhp_inverse [simp]:
  assumes "Im z > 0"
  shows   "eval_mero_uhp (inverse f) z = inverse (eval_mero_uhp f z)"
proof (cases "is_pole (eval_mero_uhp f) z")
  case True
  hence [simp]: "eval_mero_uhp f z = 0"
    using assms(1) eval_mero_uhp_pole by blast
  have "filterlim (\<lambda>w. inverse (eval_mero_uhp f w)) (at 0) (at z)"
    unfolding filterlim_inverse_at_iff using True by (simp add: is_pole_def)
  hence *: "(\<lambda>w. inverse (eval_mero_uhp f w)) \<midarrow>z\<rightarrow> 0"
    using filterlim_at by blast
  have "eval_mero_uhp (inverse f) z = remove_sings (\<lambda>w. inverse (eval_mero_uhp f w)) z"
    unfolding inverse_mero_uhp_def
    by (intro eval_mero_uhp_mero_uhp_eq meromorphic_intros assms) auto
  also have "\<dots> = 0"
    using * by blast
  finally show ?thesis
    by simp
next
  case no_pole: False
  show ?thesis
  proof (cases "eval_mero_uhp f z = 0")
    case False
    show ?thesis
      using assms False no_pole
      unfolding inverse_mero_uhp_def
      by (subst eval_mero_uhp_mero_uhp) (force intro!: meromorphic_intros analytic_intros)+
  next
    case True
    show ?thesis
    proof (cases "f = 0")
      case True
      have "mero_uhp (\<lambda>z. inverse (eval_mero_uhp 0 z)) = mero_uhp (\<lambda>_. 0)"
        by (rule mero_uhp_cong_weak) auto
      also have "\<dots> = 0"
        by (simp add: zero_mero_uhp_def const_mero_uhp_def)
      finally have "inverse f = 0" using True
        unfolding inverse_mero_uhp_def by simp
      thus ?thesis
        using assms True by auto
    next
      case False
      have "filterlim (eval_mero_uhp f) (at 0) (at z)"
      proof (rule filterlim_atI)
        have "eval_mero_uhp f analytic_on {z}"
          using assms eval_mero_uhp_analytic no_pole by blast
        have "eval_mero_uhp f \<midarrow>z\<rightarrow> eval_mero_uhp f z"
          by (rule isContD analytic_at_imp_isCont)+ fact
        with True show "eval_mero_uhp f \<midarrow>z\<rightarrow> 0"
          by simp
      next
        show "\<forall>\<^sub>F x in at z. eval_mero_uhp f x \<noteq> 0"
          using False assms(1) eventually_neq_eval_mero_uhp zero_mero_uhp_def by metis
      qed
      hence pole: "is_pole (\<lambda>z. inverse (eval_mero_uhp f z)) z"
        unfolding is_pole_def by (rule filterlim_compose[OF filterlim_inverse_at_infinity])
      have "eval_mero_uhp (inverse f) z = remove_sings (\<lambda>z. inverse (eval_mero_uhp f z)) z"
        unfolding inverse_mero_uhp_def
        by (rule eval_mero_uhp_mero_uhp_eq) (auto intro!: meromorphic_intros \<open>Im z > 0\<close>)
      also have "\<dots> = 0"
        using pole by (rule remove_sings_at_pole)
      finally show ?thesis
        by (simp add: True)
    qed
  qed
qed

instance proof
  show "inverse (0 :: mero_uhp) = 0"
    by (mero_uhp_rel (nosimp)) simp
  show "inverse f * f = (1 :: mero_uhp)" if "f \<noteq> 0" for f
  proof -
    let ?f = "eval_mero_uhp f"
    have "mero_uhp_rel (inverse f * f) (\<lambda>z. inverse (?f z) * ?f z)"
      by mero_uhp_rel
    also have "eventually (\<lambda>z. ?f z \<noteq> 0) (cosparse {z. Im z > 0})"
      using \<open>f \<noteq> 0\<close> eventually_neq_eval_mero_uhp unfolding zero_mero_uhp_def
      by (subst eventually_cosparse_open_eq[OF open_halfspace_Im_gt]) auto
    hence "mero_uhp_rel (\<lambda>z. inverse (?f z) * ?f z) (\<lambda>_. 1)"
      unfolding mero_uhp_rel_def by eventually_elim auto
    also have "mero_uhp_rel (\<lambda>_. 1) (eval_mero_uhp 1)"
      by mero_uhp_rel
    finally show ?thesis
      by (rule mero_uhp_rel_imp_eq_mero_uhp)
  qed
  show "f div g = f * inverse g" for f g :: mero_uhp
    by (simp add: divide_mero_uhp_def)
  show "inj (of_nat :: nat \<Rightarrow> mero_uhp)"
    by (rule injI) (simp add: of_nat_mero_uhp)
qed

end

lemma eval_mero_uhp_divide [simp]:
  assumes "Im z > 0" "\<not>is_pole (eval_mero_uhp f) z" "\<not>isolated_zero (eval_mero_uhp g) z"
  shows   "eval_mero_uhp (f / g) z = eval_mero_uhp f z / eval_mero_uhp g z"
proof -
  have "is_pole (eval_mero_uhp (inverse g)) z \<longleftrightarrow> is_pole (\<lambda>z. inverse (eval_mero_uhp g z)) z"
  proof (rule is_pole_cong)
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
      by (intro eventually_at_in_open') (use assms(1) in \<open>auto simp: open_halfspace_Im_gt\<close>)
    thus "\<forall>\<^sub>F x in at z. eval_mero_uhp (inverse g) x = inverse (eval_mero_uhp g x)"
      by eventually_elim auto
  qed auto
  with assms(3) have *: "\<not>is_pole (eval_mero_uhp (inverse g)) z"
    by (simp add: is_pole_inverse_iff)

  have "eval_mero_uhp (f / g) z = eval_mero_uhp (f * inverse g) z"
    by (simp add: field_simps)
  also have "\<dots> = eval_mero_uhp f z * eval_mero_uhp (inverse g) z"
    by (subst eval_mero_uhp_mult) (use assms * in auto)
  also have "\<dots> = eval_mero_uhp f z / eval_mero_uhp g z"
    by (subst eval_mero_uhp_inverse) (use assms in \<open>auto simp: field_simps\<close>)
  finally show ?thesis .
qed

interpretation const_mero_uhp: comm_ring_hom const_mero_uhp
  by standard mero_uhp_rel+

interpretation const_mero_uhp: field_char_0_hom const_mero_uhp
  by standard

lemma mero_uhp_rel_power_int [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (f powi n)) (\<lambda>z. eval_mero_uhp f z powi n)"
  by (cases "n \<ge> 0") (simp_all add: power_int_def, mero_uhp_rel+)


instantiation mero_uhp :: real_field
begin

definition scaleR_mero_uhp :: "real \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp"
  where "scaleR_mero_uhp x f = const_mero_uhp x * f"

instance 
  by standard
     (auto simp: algebra_simps scaleR_mero_uhp_def const_mero_uhp.hom_mult const_mero_uhp.hom_add)

end

lemma of_real_mero_uhp: "of_real x = const_mero_uhp (of_real x)"
  by (simp add: of_real_def scaleR_mero_uhp_def)

lemma mero_uhp_rel_of_real [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (of_real x)) (\<lambda>_. of_real x)"
  unfolding of_real_mero_uhp by mero_uhp_rel

lemma of_rat_mero_uhp: "of_rat x = const_mero_uhp (of_rat x)"
  using of_real_mero_uhp[of "of_rat x"] 
  by (cases x) (auto simp: of_rat_rat)


text \<open>
  Pre-modular forms are a complex vector space:
\<close>
interpretation mero_uhp: vector_space "\<lambda>(x::complex) y. const_mero_uhp x * y"
  by standard (auto simp: algebra_simps const_mero_uhp.hom_mult const_mero_uhp.hom_add)


definition inv_image_mero_uhp :: "mero_uhp \<Rightarrow> complex \<Rightarrow> complex set" where
  "inv_image_mero_uhp f c = {z\<in>\<R>\<^sub>\<Gamma>'. \<not>is_pole f z \<and> eval_mero_uhp f z = c}"

abbreviation zeros_mero_uhp :: "mero_uhp \<Rightarrow> complex set" where
  "zeros_mero_uhp f \<equiv> inv_image_mero_uhp f 0"

definition poles_mero_uhp :: "mero_uhp \<Rightarrow> complex set" where
  "poles_mero_uhp f = {z\<in>\<R>\<^sub>\<Gamma>'. is_pole f z}"
lemma inv_image_mero_uhp_conv_zeros:
  "inv_image_mero_uhp f c = zeros_mero_uhp (f - const_mero_uhp c)"
proof -
  have is_pole_iff: "is_pole (eval_mero_uhp (f - const_mero_uhp c)) z \<longleftrightarrow> is_pole f z" for z
  proof (cases "Im z > 0")
    case True
    have "mero_uhp_rel (eval_mero_uhp (f - const_mero_uhp c)) (\<lambda>z. f z - c)"
      by mero_uhp_rel
    hence "is_pole (eval_mero_uhp (f - const_mero_uhp c)) z \<longleftrightarrow> is_pole (\<lambda>z. f z + (-c)) z"
      unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
      by (intro is_pole_cong) (use True in auto)
    also have "\<dots> \<longleftrightarrow> is_pole f z"
      by (rule is_pole_plus_const_iff [symmetric])
    finally show ?thesis .
  qed (auto simp: not_is_pole_eval_mero_uhp_outside)

  have "z \<in> inv_image_mero_uhp f c \<longleftrightarrow> z \<in> zeros_mero_uhp (f - const_mero_uhp c)" for z
    unfolding inv_image_mero_uhp_def mem_Collect_eq
    by (intro conj_cong refl arg_cong[of _ _ Not])
       (auto simp: in_std_fund_region'_iff is_pole_iff)
  thus ?thesis
    by blast
qed


definition is_const_mero_uhp :: "mero_uhp \<Rightarrow> bool"
  where "is_const_mero_uhp f \<longleftrightarrow> f \<in> range const_mero_uhp"

lemma is_const_mero_uhp_const_mero_uhp [simp, intro]: "is_const_mero_uhp (const_mero_uhp c)"
  by (auto simp: is_const_mero_uhp_def)

lemma is_const_mero_uhp_0 [simp, intro]: "is_const_mero_uhp 0"
  by (auto simp: is_const_mero_uhp_def)

lemma is_const_mero_uhp_1 [simp, intro]: "is_const_mero_uhp 1"
  by (auto simp: is_const_mero_uhp_def)

lemma is_const_mero_uhp_of_nat [simp, intro]: "is_const_mero_uhp (of_nat n)"
  unfolding is_const_mero_uhp_def using of_nat_mero_uhp by blast

lemma is_const_mero_uhp_of_int [simp, intro]: "is_const_mero_uhp (of_int n)"
  unfolding is_const_mero_uhp_def using of_int_mero_uhp by blast

lemma is_const_mero_uhp_of_real [simp, intro]: "is_const_mero_uhp (of_real x)"
  unfolding is_const_mero_uhp_def using of_real_mero_uhp by blast

lemma is_const_mero_uhp_numeral [simp, intro]: "is_const_mero_uhp (numeral n)"
  unfolding is_const_mero_uhp_def using numeral_mero_uhp by blast

lemma is_const_mero_uhp_add [intro]:
  assumes "is_const_mero_uhp f" "is_const_mero_uhp g"
  shows   "is_const_mero_uhp (f + g)"
proof -
  from assms obtain cf cg where fg: "f = const_mero_uhp cf" "g = const_mero_uhp cg"
    by (auto simp: is_const_mero_uhp_def)
  have "is_const_mero_uhp (const_mero_uhp (cf + cg))"
    by auto
  thus ?thesis
    unfolding hom_distribs fg .
qed

lemma is_const_mero_uhp_mult [intro]:
  assumes "is_const_mero_uhp f" "is_const_mero_uhp g"
  shows   "is_const_mero_uhp (f * g)"
proof -
  from assms obtain cf cg where fg: "f = const_mero_uhp cf" "g = const_mero_uhp cg"
    by (auto simp: is_const_mero_uhp_def)
  have "is_const_mero_uhp (const_mero_uhp (cf * cg))"
    by auto
  thus ?thesis
    unfolding hom_distribs fg .
qed

lemma is_const_mero_uhp_uminus [intro]:
  assumes "is_const_mero_uhp f"
  shows   "is_const_mero_uhp (-f)"
proof -
  from assms obtain cf where fg: "f = const_mero_uhp cf"
    by (auto simp: is_const_mero_uhp_def)
  have "is_const_mero_uhp (const_mero_uhp (-cf))"
    by auto
  thus ?thesis
    unfolding hom_distribs fg .
qed

lemma is_const_mero_uhp_power_int [intro]:
  assumes "is_const_mero_uhp f"
  shows   "is_const_mero_uhp (f powi n)"
proof -
  from assms obtain cf where fg: "f = const_mero_uhp cf"
    by (auto simp: is_const_mero_uhp_def)
  have "is_const_mero_uhp (const_mero_uhp (cf powi n))"
    by auto
  thus ?thesis
    unfolding hom_distribs fg .
qed

lemma is_const_mero_uhp_power [intro]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (f ^ n)"
  using is_const_mero_uhp_power_int[of f "int n"] by simp

lemma is_const_mero_uhp_inverse [intro]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (inverse f)"
  using is_const_mero_uhp_power_int[of f "-1"] by simp

lemma is_const_mero_uhp_diff [intro]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f - g)"
  using is_const_mero_uhp_add[OF _ is_const_mero_uhp_uminus[of g], of f] by simp

lemma is_const_mero_uhp_divide [intro]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f / g)"
  using is_const_mero_uhp_mult[OF _ is_const_mero_uhp_inverse[of g], of f]
  by (simp add: field_simps)

lemma is_const_mero_uhp_minus_iff [simp]: "is_const_mero_uhp (-f) = is_const_mero_uhp f"
  by (metis const_mero_uhp.hom_uminus imageE is_const_mero_uhp_const_mero_uhp is_const_mero_uhp_def more_arith_simps(10))

lemma is_const_mero_uhp_add_absorb1 [simp]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (f + g) \<longleftrightarrow> is_const_mero_uhp g"
  by (metis add_diff_cancel_left' add_uminus_conv_diff const_mero_uhp.hom_add image_iff is_const_mero_uhp_const_mero_uhp is_const_mero_uhp_def)

lemma is_const_mero_uhp_add_absorb2 [simp]:
  "is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f + g) \<longleftrightarrow> is_const_mero_uhp f"
  using is_const_mero_uhp_add_absorb1[of g f] by (simp only: add.commute)

lemma is_const_mero_uhp_diff_absorb1 [simp]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (f - g) \<longleftrightarrow> is_const_mero_uhp g"
  using is_const_mero_uhp_add_absorb1[of f "-g"] by (simp del: is_const_mero_uhp_add_absorb1)

lemma is_const_mero_uhp_diff_absorb2 [simp]:
  "is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f - g) \<longleftrightarrow> is_const_mero_uhp f"
  using is_const_mero_uhp_add_absorb1[of "-g" f] by (simp del: is_const_mero_uhp_add_absorb1)


lemma is_pole_mero_uhp_power_iff [simp]:
  "is_pole (eval_mero_uhp (f ^ n)) z \<longleftrightarrow> Im z > 0 \<and> is_pole f z \<and> n > 0"
proof (cases "Im z > 0")
  case z: True
  have "mero_uhp_rel (f ^ n) (\<lambda>z. f z ^ n)"
    by mero_uhp_rel
  hence "is_pole (eval_mero_uhp (f ^ n)) z \<longleftrightarrow> is_pole (\<lambda>z. f z ^ n) z"
    using z unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
    by (intro is_pole_cong) auto
  also have "\<dots> \<longleftrightarrow> is_pole f z \<and> n > 0"
    by (rule is_pole_power_iff) (auto intro!: meromorphic_intros z)
  finally show ?thesis using z by auto
qed (simp_all add: not_is_pole_eval_mero_uhp_outside)   
    
lemma eval_mero_uhp_power [simp]:
  assumes z: "Im z > 0"
  shows  "eval_mero_uhp (f ^ n) z = eval_mero_uhp f z ^ n"
proof (cases "is_pole f z")
  case False
  show ?thesis
    by (rule mero_uhp_rel_imp_eval_mero_uhp_eq, mero_uhp_rel)
       (use z False in \<open>auto intro!: analytic_intros\<close>)
next
  case True
  thus ?thesis
    using z by (cases "n = 0") (auto simp: eval_mero_uhp_pole)
qed


lemma constant_on_cong [cong]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> A = B \<Longrightarrow> f constant_on A \<longleftrightarrow> g constant_on B"
  unfolding constant_on_def by (intro ex_cong1 ball_cong) auto

lemma constant_on_const [intro]: "(\<lambda>_. c) constant_on A"
  by (auto simp: constant_on_def)

lemma is_const_eval_const_mero_uhp:
  assumes "is_const_mero_uhp f" "A \<subseteq> {z. Im z > 0}"
  shows   "eval_mero_uhp f constant_on A"
proof -
  from assms(1) obtain c where [simp]: "f = const_mero_uhp c"
    by (auto simp: is_const_mero_uhp_def)
  have "eval_mero_uhp f constant_on A \<longleftrightarrow> (\<lambda>_. c) constant_on A"
    by (intro constant_on_cong refl) (use assms(2) in auto)
  thus ?thesis
    by auto
qed

lemma not_constant_on_eval_mero_uhp:
  assumes "\<not>is_const_mero_uhp f" "\<not>A sparse_in {z. Im z > 0}"
  shows   "\<not>eval_mero_uhp f constant_on A"
proof
  assume "eval_mero_uhp f constant_on A"
  then obtain c where c: "eval_mero_uhp f z = c" if "z \<in> A" for z
    by (auto simp: constant_on_def)
  have "(\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z = c) \<or> (\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z \<noteq> c)"
    by (intro meromorphic_imp_constant_or_avoid meromorphic_intros
              open_halfspace_Im_gt connected_halfspace_Im_gt) auto
  moreover have "\<not>(\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z \<noteq> c)"
    using assms(2) c sparse_in_subset2 unfolding frequently_def eventually_cosparse by blast
  ultimately have "(\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z = c)"
    by blast
  moreover have "(\<forall>\<^sub>\<approx>z | 0 < Im z. z \<in> {z. Im z > 0})"
    by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
  ultimately have "(\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z)"
    by eventually_elim auto
  hence "f = const_mero_uhp c"
    using mero_uhp_eqI by blast
  thus False
    using assms(1) by auto
qed

lemma constant_on_eval_mero_uhp_iff:
  assumes "\<not>A sparse_in {z. Im z > 0}" "A \<subseteq> {z. Im z > 0}"
  shows   "eval_mero_uhp f constant_on A \<longleftrightarrow> is_const_mero_uhp f"
  using not_constant_on_eval_mero_uhp is_const_eval_const_mero_uhp assms by blast

lemma meromorphic_on_imp_sparse_poles:
  assumes "f meromorphic_on A"
  shows   "{z. is_pole f z} sparse_in A"
proof (rule sparse_in_subset2)
  show "{z. \<not>f analytic_on {z}} sparse_in A"
    by (rule meromorphic_on_imp_sparse_singularities) fact
qed (auto dest: analytic_at_imp_no_pole)

lemma is_pole_inverse_iff:
  fixes f :: "'a::{real_normed_div_algebra, division_ring} \<Rightarrow> 'a"
  shows "is_pole (\<lambda>z. inverse (f z)) z \<longleftrightarrow> filterlim f (at 0) (at z)"
proof
  assume *: "filterlim f (at 0) (at z)"
  show "is_pole (\<lambda>z. inverse (f z)) z"
    using filterlim_compose[OF filterlim_inverse_at_infinity *] by (simp add: is_pole_def)
next
  assume "is_pole (\<lambda>z. inverse (f z)) z"
  hence "filterlim (\<lambda>z. inverse (inverse (f z))) (at 0) (at z)"
    unfolding is_pole_def 
    using filterlim_inverse_at_iff[of "\<lambda>z. inverse (f z)" "at z"] by simp
  also have "(\<lambda>z. inverse (inverse (f z))) = f"
    by auto
  finally show "filterlim f (at 0) (at z)" .
qed

lemma filterlim_at_conv_at_0:
  fixes c :: "'a::real_normed_vector"
  shows "filterlim f (at c) F \<longleftrightarrow> filterlim (\<lambda>x. f x - c) (at 0) F"
proof
  assume *: "filterlim f (at c) F"
  have "filterlim (\<lambda>x. x - c) (at 0) (at c)"
    by (simp add: at_to_0' filterlim_filtermap filterlim_ident)
  from this and * show "filterlim (\<lambda>x. f x - c) (at 0) F"
    by (rule filterlim_compose)
next
  assume *: "filterlim (\<lambda>x. f x - c) (at 0) F"
  have "at 0 = filtermap (\<lambda>x. x - c) (at c)"
    by (simp add: at_to_0' filtermap_filtermap)
  hence "filterlim (\<lambda>x. x + c) (at c) (at 0)"
    by (simp add: filterlim_filtermap filterlim_ident)
  from this and * have "filterlim (\<lambda>x. f x - c + c) (at c) F"
    by (rule filterlim_compose)
  thus "filterlim f (at c) F"
    by simp
qed

lemma filterlim_at_conv_at_0':
  fixes c :: "'a::real_normed_vector"
  assumes "NO_MATCH 0 c"
  shows "filterlim f (at c) F \<longleftrightarrow> filterlim (\<lambda>x. f x - c) (at 0) F"
  by (rule filterlim_at_conv_at_0)

abbreviation upper_half_plane ("\<H>") where "\<H> \<equiv> {z. Im z > 0}"

lemma eval_mero_uhp_avoid:
  assumes "f \<noteq> const_mero_uhp c"
  shows   "\<forall>\<^sub>\<approx>z\<in>\<H>. f z \<noteq> c"
proof -
  have "(\<forall>\<^sub>\<approx>z\<in>\<H>. f z = c) \<or> (\<forall>\<^sub>\<approx>z\<in>\<H>. f z \<noteq> c)"
    by (intro meromorphic_imp_constant_or_avoid meromorphic_intros
              open_halfspace_Im_gt connected_halfspace_Im_gt) auto
  thus ?thesis
  proof
    assume "\<forall>\<^sub>\<approx>z\<in>\<H>. f z = c"
    moreover have "(\<forall>\<^sub>\<approx>z | 0 < Im z. z \<in> {z. Im z > 0})"
      by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
    ultimately have "(\<forall>\<^sub>\<approx>z | 0 < Im z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z)"
      by eventually_elim auto
    hence "f = const_mero_uhp c"
      using mero_uhp_eqI by blast
    hence False
      using assms(1) by auto
    thus ?thesis ..
  qed auto
qed

lemma eval_mero_uhp_avoid_0:
  assumes "f \<noteq> 0"
  shows   "eventually (\<lambda>z. eval_mero_uhp f z \<noteq> 0) (cosparse {z. Im z > 0})"
  using eval_mero_uhp_avoid[of f 0] assms by simp

lemma poles_mero_uhp_const_mero_uhp [simp]: "is_const_mero_uhp f \<Longrightarrow> poles_mero_uhp f = {}"
  by (auto simp: is_const_mero_uhp_def poles_mero_uhp_def in_std_fund_region'_iff)

lemma eventually_eval_mero_uhp_neq_iff:
  assumes "Im z > 0"
  shows   "eventually (\<lambda>z. eval_mero_uhp f z \<noteq> c) (at z) \<longleftrightarrow> f \<noteq> const_mero_uhp c"
proof
  assume "eventually (\<lambda>z. eval_mero_uhp f z \<noteq> c) (at z)"
  moreover have "eventually (\<lambda>w. w \<in> {w. Im w > 0}) (at z)"
    using assms by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
  ultimately have "eventually (\<lambda>z. False) (at z)" if "f = const_mero_uhp c"
    by eventually_elim (use that in auto)
  thus "f \<noteq> const_mero_uhp c"
    by auto
next
  assume "f \<noteq> const_mero_uhp c"
  thus "eventually (\<lambda>z. eval_mero_uhp f z \<noteq> c) (at z)"
    using assms by (simp add: eventually_neq_eval_mero_uhp)
qed

lemma analytic_at_mero_uhp_iff:
  assumes "Im z > 0"
  shows   "eval_mero_uhp f analytic_on {z} \<longleftrightarrow> \<not>is_pole (eval_mero_uhp f) z"
  using assms analytic_at_imp_no_pole eval_mero_uhp_analytic by blast

lemma has_laurent_expansion_imp_subdegree_nonneg:
  assumes "f has_laurent_expansion F" "f \<midarrow>0\<rightarrow> c"
  shows   "fls_subdegree F \<ge> 0"
  using assms has_laurent_expansion_imp_filterlim_infinity_0 not_tendsto_and_filterlim_at_infinity
  by force

lemma nicely_meromorphic_at_tendsto_imp_analytic_at:
  assumes "f nicely_meromorphic_on {z}" "f \<midarrow>z\<rightarrow> c"
  shows   "f analytic_on {z}"
  using assms(1)
  by (rule nicely_meromorphic_on_imp_analytic_at)
     (use assms(2) not_tendsto_and_filterlim_at_infinity[of "at z" f c] in \<open>auto simp: is_pole_def\<close>)

lemma tendsto_eval_mero_uhp_iff:
  assumes z: "Im z > 0"
  shows   "eval_mero_uhp f \<midarrow>z\<rightarrow> c \<longleftrightarrow> \<not>is_pole (eval_mero_uhp f) z \<and> f z = c"
proof (intro iffI conjI)
  assume *: "eval_mero_uhp f \<midarrow>z\<rightarrow> c"
  have ana: "eval_mero_uhp f analytic_on {z}"
    by (rule nicely_meromorphic_at_tendsto_imp_analytic_at[OF _ *])
       (auto intro!: eval_mero_uhp_nicely_meromorphic z)
  thus "\<not>is_pole (eval_mero_uhp f) z"
    using z by (simp add: analytic_at_mero_uhp_iff)
  from ana have lim: "f \<midarrow>z\<rightarrow> f z"
    by (intro isContD analytic_at_imp_isCont)
  show "f z = c"
    using tendsto_unique[OF _ lim *] by simp
next
  assume *: "\<not>is_pole (eval_mero_uhp f) z \<and> f z = c"
  hence "f analytic_on {z}"
    using z by (simp add: analytic_at_mero_uhp_iff)
  hence "f \<midarrow>z\<rightarrow> f z"
    by (intro isContD analytic_at_imp_isCont)
  with * show "f \<midarrow>z\<rightarrow> c"
    by auto
qed

lemma is_pole_inverse_mero_uhp_iff:
  assumes z: "Im z > 0"
  shows   "is_pole (eval_mero_uhp (inverse f)) z \<longleftrightarrow> f \<noteq> 0 \<and> \<not>is_pole f z \<and> eval_mero_uhp f z = 0"
proof -
  have "mero_uhp_rel (eval_mero_uhp (inverse f)) (\<lambda>z. inverse (eval_mero_uhp f z))"
    by mero_uhp_rel
  with z have "eventually (\<lambda>z. eval_mero_uhp (inverse f) z = inverse (eval_mero_uhp f z)) (at z)"
    by (simp add: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
  hence "is_pole (eval_mero_uhp (inverse f)) z \<longleftrightarrow> is_pole (\<lambda>z. inverse (eval_mero_uhp f z)) z"
    by (rule is_pole_cong) auto
  also have "\<dots> \<longleftrightarrow> filterlim (eval_mero_uhp f) (at 0) (at z)"
    by (rule is_pole_inverse_iff)
  also have "\<dots> \<longleftrightarrow> eventually (\<lambda>z. f z \<noteq> 0) (at z) \<and> f \<midarrow>z\<rightarrow> 0"
    by (auto simp: filterlim_at)
  also have "eventually (\<lambda>z. f z \<noteq> 0) (at z) \<longleftrightarrow> f \<noteq> 0"
    using eventually_eval_mero_uhp_neq_iff[of z f 0] z by simp
  also have "f \<midarrow>z\<rightarrow> 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
    using z by (subst tendsto_eval_mero_uhp_iff) auto
  finally show ?thesis .
qed

lemma poles_mero_uhp_inverse:
  assumes "f \<noteq> 0"
  shows   "poles_mero_uhp (inverse f) = zeros_mero_uhp f"
  using assms
  by (auto simp: poles_mero_uhp_def inv_image_mero_uhp_def in_std_fund_region'_iff
                 is_pole_inverse_mero_uhp_iff)

lemma zeros_mero_uhp_inverse:
  assumes "f \<noteq> 0"
  shows   "zeros_mero_uhp (inverse f) = poles_mero_uhp f"
  using assms by (subst poles_mero_uhp_inverse [symmetric]) auto

lemma is_pole_cong':
  assumes "eventually (\<lambda>x. f x = g x) (cosparse A)" "x \<in> A" "open A"
  shows   "is_pole f x \<longleftrightarrow> is_pole g x"
  by (rule is_pole_cong) (use assms in \<open>auto simp: eventually_cosparse_open_eq\<close>)

(*TODO: can this be turned into a lift_definition so that the transfer package 
  can be setup? Here, we might need to show nicely meromorphicity is invariant
  under modular group transformation. -- Wenda*)
definition compose_modgrp_mero_uhp :: "mero_uhp \<Rightarrow> modgrp \<Rightarrow> mero_uhp" where
  "compose_modgrp_mero_uhp f h = mero_uhp (\<lambda>z. f (apply_modgrp h z))"

lemma mero_uhp_rel_compose_modgrp [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (compose_modgrp_mero_uhp f h)) (\<lambda>z. eval_mero_uhp f (apply_modgrp h z))"
  unfolding compose_modgrp_mero_uhp_def by mero_uhp_rel auto

lemma compose_modgrp_mero_uhp_uminus_right [simp]:
  "compose_modgrp_mero_uhp f (-h) = compose_modgrp_mero_uhp f h"
  by mero_uhp_rel auto

lemma eval_compose_modgrp_mero_uhp [simp]:
  "eval_mero_uhp (compose_modgrp_mero_uhp f h) z = eval_mero_uhp f (apply_modgrp h z)"
proof (cases "Im z > 0")
  case z: True
  show ?thesis
  unfolding compose_modgrp_mero_uhp_def
  proof (subst eval_mero_uhp_mero_uhp_eq)
    show "remove_sings (\<lambda>z. eval_mero_uhp f (apply_modgrp h z)) z =
            eval_mero_uhp f (apply_modgrp h z)"
    proof (cases "is_pole f (apply_modgrp h z)")
      case False
      thus ?thesis using z
        by (intro remove_sings_at_analytic analytic_intros) auto
    next
      case True
      hence "filterlim f at_infinity (at (apply_modgrp h z))"
        by (simp add: is_pole_def)
      also have "at (apply_modgrp h z) = filtermap (apply_modgrp h) (at z)"
        using z by (subst filtermap_at_apply_modgrp) auto
      finally have "is_pole (\<lambda>z. f (apply_modgrp h z)) z"
        by (simp add: is_pole_def filterlim_filtermap)
      hence "remove_sings (\<lambda>z. eval_mero_uhp f (apply_modgrp h z)) z = 0"
        by (intro remove_sings_at_pole)
      with True show ?thesis
        by (simp add: eval_mero_uhp_pole)
    qed
  qed (auto intro!: meromorphic_intros analytic_intros z)
qed (auto simp: eval_mero_uhp_outside)

lemma compose_modgrp_mero_uhp_const [simp]:
  "compose_modgrp_mero_uhp (const_mero_uhp c) h = const_mero_uhp c"
  by (rule mero_uhp_eqI_weak) auto

lemma compose_modgrp_mero_uhp_1 [simp]:
  "compose_modgrp_mero_uhp f 1 = f"
  by (rule mero_uhp_eqI_weak) auto

lemma mero_uhp_rel_cong_compose_modgrp [mero_uhp_rel_cong]:
  assumes "mero_uhp_rel f g"
  shows   "mero_uhp_rel (\<lambda>z. f (apply_modgrp h z)) (\<lambda>z. g (apply_modgrp h z))"
  unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
proof safe
  fix z assume z: "Im z > 0"
  from assms z have "eventually (\<lambda>z. f z = g z) (at (apply_modgrp h z))"
    by (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt])
  also have "at (apply_modgrp h z) = filtermap (apply_modgrp h) (at z)"
    by (metis Im_pole_modgrp filtermap_at_apply_modgrp less_irrefl z)
  finally show "eventually (\<lambda>z. f (apply_modgrp h z) = g (apply_modgrp h z)) (at z)"
    by (simp add: eventually_filtermap)
qed

interpretation compose_modgrp_mero_uhp: field_char_0_hom "\<lambda>f. compose_modgrp_mero_uhp f h"
proof (unfold_locales, goal_cases)
  show "compose_modgrp_mero_uhp 0 h = 0" "compose_modgrp_mero_uhp 1 h = 1"
    by (rule mero_uhp_eqI_weak; simp; fail)+
qed mero_uhp_rel+

lemma compose_modgrp_mero_uhp_mult_right:
  "compose_modgrp_mero_uhp f (g * h) = compose_modgrp_mero_uhp (compose_modgrp_mero_uhp f g) h"
  by (mero_uhp_rel, rule mero_uhp_relI_weak, subst apply_modgrp_mult) auto


definition automorphy_factor_mero_uhp :: "modgrp \<Rightarrow> mero_uhp" where
  "automorphy_factor_mero_uhp h = mero_uhp (automorphy_factor h)"

lemma mero_uhp_rel_automorphy_factor [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (automorphy_factor_mero_uhp h)) (\<lambda>z. automorphy_factor h z)"
  unfolding automorphy_factor_mero_uhp_def by mero_uhp_rel

lemma automorphy_factor_mero_uhp_uminus [simp]:
  "automorphy_factor_mero_uhp (-h) = -automorphy_factor_mero_uhp h"
  by mero_uhp_rel (auto simp: automorphy_factor_uminus [abs_def])

lemma eval_automorphy_factor_mero_uhp [simp]:
  "Im z > 0 \<Longrightarrow> eval_mero_uhp (automorphy_factor_mero_uhp h) z = automorphy_factor h z"
  unfolding automorphy_factor_mero_uhp_def
  by (subst eval_mero_uhp_mero_uhp) (auto intro!: meromorphic_intros analytic_intros)

lemma automorphy_factor_mero_uhp_1 [simp]: "automorphy_factor_mero_uhp 1 = 1"
  by (rule mero_uhp_eqI_weak) auto

lemma automorphy_factor_mero_uhp_shift [simp]: "automorphy_factor_mero_uhp (shift_modgrp n) = 1"
  by (rule mero_uhp_eqI_weak) simp_all

lemma automorphy_factor_mero_uhp_T [simp]: "automorphy_factor_mero_uhp T_modgrp = 1"
  by (rule mero_uhp_eqI_weak) simp_all

lemma automorphy_factor_mero_uhp_neq_0 [simp]: "automorphy_factor_mero_uhp h \<noteq> 0"
proof
  assume *: "automorphy_factor_mero_uhp h = 0"
  have "eval_mero_uhp (automorphy_factor_mero_uhp h) \<i> = 0"
    by (simp only: *) auto
  thus False
    by simp
qed

lemma deriv_mero_uhp_automorphy_factor [simp]:
  "deriv_mero_uhp (automorphy_factor_mero_uhp h) = of_int (modgrp_c h)"
proof -
  have "mero_uhp_rel (deriv_mero_uhp (automorphy_factor_mero_uhp h)) (deriv (automorphy_factor h))"
    by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (eval_mero_uhp (of_int (modgrp_c h)))"
  proof (rule mero_uhp_relI_weak)
    fix z assume z: "Im z > 0"
    from z have "(automorphy_factor h has_field_derivative eval_mero_uhp (of_int (modgrp_c h)) z) (at z)"
      by (auto intro!: derivative_eq_intros simp: of_int_mero_uhp)
    thus "deriv (automorphy_factor h) z = eval_mero_uhp (of_int (modgrp_c h)) z"
      by (rule DERIV_imp_deriv)
  qed
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed

lemma automorphy_factor_mero_uhp_mult:
  "automorphy_factor_mero_uhp (g * h) = 
     compose_modgrp_mero_uhp (automorphy_factor_mero_uhp g) h * automorphy_factor_mero_uhp h"
proof -
  have "mero_uhp_rel (automorphy_factor_mero_uhp (g * h)) (automorphy_factor (g * h))"
    by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. automorphy_factor g (apply_modgrp h z) * automorphy_factor h z)"
    by (rule mero_uhp_relI_weak, subst automorphy_factor_mult) auto
  also have "mero_uhp_rel \<dots> 
               (compose_modgrp_mero_uhp (automorphy_factor_mero_uhp g) h * automorphy_factor_mero_uhp h)"
    by mero_uhp_rel
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed


definition slash_mero_uhp :: "int \<Rightarrow> modgrp \<Rightarrow> mero_uhp \<Rightarrow>  mero_uhp" where
  "slash_mero_uhp k g f = automorphy_factor_mero_uhp g powi (-k) * compose_modgrp_mero_uhp f g"

lemma mero_uhp_rel_slash [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (slash_mero_uhp k g f))
     (\<lambda>z. automorphy_factor g z powi (-k) * eval_mero_uhp f (apply_modgrp g z))"
  unfolding slash_mero_uhp_def by mero_uhp_rel

lemma eval_slash_mero_uhp:
  assumes "Im z > 0" "\<not>is_pole (eval_mero_uhp f) (apply_modgrp h z)"
  shows "eval_mero_uhp (slash_mero_uhp k h f) z =
           automorphy_factor h z powi (-k) * eval_mero_uhp f (apply_modgrp h z)"
proof -
  have "mero_uhp_rel (slash_mero_uhp k h f)
          (\<lambda>z. automorphy_factor h z powi (-k) * eval_mero_uhp f (apply_modgrp h z))"
    by mero_uhp_rel
  thus ?thesis
    by (rule mero_uhp_rel_imp_eval_mero_uhp_eq) (use assms in \<open>auto intro!: analytic_intros\<close>)
qed

lemma slash_mero_uhp_eq_0_iff [simp]: "slash_mero_uhp k g f = 0 \<longleftrightarrow> f = 0"
  by (auto simp: slash_mero_uhp_def)

lemma slash_mero_uhp_const [simp]: "slash_mero_uhp 0 h (const_mero_uhp c) = const_mero_uhp c"
  and slash_mero_uhp_1_right [simp]: "slash_mero_uhp 0 h 1 = 1"
  and slash_mero_uhp_0 [simp]: "slash_mero_uhp k h 0 = 0"
  by (simp_all add: slash_mero_uhp_def)

lemma slash_mero_uhp_uminus [simp]: "even k \<Longrightarrow> slash_mero_uhp k (-h) f = slash_mero_uhp k h f"
  by (auto simp: slash_mero_uhp_def)

lemma slash_mero_uhp_1 [simp]: "slash_mero_uhp k 1 f = f"
  unfolding slash_mero_uhp_def by simp

lemma slash_mero_uhp_mult:
  "slash_mero_uhp k (g * h) f = slash_mero_uhp k h (slash_mero_uhp k g f)" (is "?lhs = ?rhs")
proof -
  have "mero_uhp_rel ?lhs (\<lambda>z. automorphy_factor (g * h) z powi (-k) * eval_mero_uhp f (apply_modgrp (g * h) z))"
    unfolding slash_mero_uhp_def by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. automorphy_factor h z powi (-k) * 
                (automorphy_factor g (apply_modgrp h z) powi (-k) * 
                 eval_mero_uhp f (apply_modgrp (g * h) z)))"
    by (rule mero_uhp_relI_weak, subst automorphy_factor_mult) 
       (auto simp: complex_is_Real_iff mult_ac power_int_mult_distrib)
  also have "mero_uhp_rel \<dots> (\<lambda>z. automorphy_factor h z powi (-k) *
                                  (automorphy_factor g (apply_modgrp h z) powi (-k) * 
                                   eval_mero_uhp f (apply_modgrp g (apply_modgrp h z))))"
    by (rule mero_uhp_relI_weak, subst apply_modgrp_mult) (auto simp: complex_is_Real_iff mult_ac)
  also have "mero_uhp_rel \<dots> ?rhs"
    unfolding slash_mero_uhp_def by mero_uhp_rel
  finally show ?thesis
    using mero_uhp_rel_imp_eq_mero_uhp by blast
qed

interpretation slash_mero_uhp: ab_group_add_hom "\<lambda>f. slash_mero_uhp k h f"
  by unfold_locales (auto simp: slash_mero_uhp_def hom_distribs)

lemma slash_mero_uhp_mult_right:
  "slash_mero_uhp k h f * slash_mero_uhp l h g = slash_mero_uhp (k + l) h (f * g)"
  by (simp add: slash_mero_uhp_def power_int_diff field_simps power_int_minus hom_distribs)

lemma slash_mero_uhp_divide:
  "slash_mero_uhp k h f / slash_mero_uhp l h g = slash_mero_uhp (k - l) h (f / g)"
  by (simp add: slash_mero_uhp_def power_int_diff field_simps power_int_minus hom_distribs)

lemma slash_mero_uhp_power_int:
  "slash_mero_uhp k h f powi n = slash_mero_uhp (n * k) h (f powi n)"
  by (simp add: slash_mero_uhp_def power_int_mult power_int_divide_distrib 
                power_int_minus hom_distribs field_simps)

lemma slash_mero_uhp_power:
  "slash_mero_uhp k h f ^ n = slash_mero_uhp (n * k) h (f ^ n)"
  using slash_mero_uhp_power_int[of k h f "int n"] by simp

lemma slash_mero_uhp_inverse:
  "inverse (slash_mero_uhp k h f) = slash_mero_uhp (-k) h (inverse f)"
  using slash_mero_uhp_power_int[of k h f "-1"] by simp

lemma slash_mero_uhp_cmult_left [simp]:
  "slash_mero_uhp k h (const_mero_uhp c * f) = const_mero_uhp c * slash_mero_uhp k h f"
  by (simp add: slash_mero_uhp_def algebra_simps hom_distribs)

lemma slash_mero_uhp_cmult_right [simp]:
  "slash_mero_uhp k h (f * const_mero_uhp c) = slash_mero_uhp k h f * const_mero_uhp c"
  by (simp add: slash_mero_uhp_def algebra_simps hom_distribs)

lemma slash_mero_uhp_T: 
  "slash_mero_uhp k T_modgrp f = compose_modgrp_mero_uhp f T_modgrp"
  by (simp add: slash_mero_uhp_def automorphy_factor_mero_uhp_shift)



lemma zorder_mero_uhp_neg_iff [simp]:
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (eval_mero_uhp f) z < 0 \<longleftrightarrow> is_pole f z"
proof (cases "is_pole f z")
  case True
  thus ?thesis using assms
    by (auto intro!: isolated_pole_imp_neg_zorder meromorphic_on_isolated_singularity meromorphic_intros)
next
  case False
  have "\<exists>\<^sub>F z in at z. eval_mero_uhp f z \<noteq> 0"
    using assms False by (simp add: eventually_eval_mero_uhp_neq_iff eventually_frequently)
  hence "zorder (eval_mero_uhp f) z \<ge> 0"
    using False assms by (intro zorder_ge_0 analytic_intros) auto
  thus ?thesis
    using False by auto
qed

lemma zorder_mero_uhp_nonneg_iff [simp]:
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (eval_mero_uhp f) z \<ge> 0 \<longleftrightarrow> \<not>is_pole f z"
  using zorder_mero_uhp_neg_iff[OF assms] by linarith

lemma zorder_mero_uhp_pos_iff [simp]:
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (eval_mero_uhp f) z > 0 \<longleftrightarrow> \<not>is_pole f z \<and> eval_mero_uhp f z = 0"
proof (cases "is_pole f z")
  case False
  thus ?thesis
  proof (subst zorder_pos_iff')
    show "\<exists>\<^sub>F z in at z. eval_mero_uhp f z \<noteq> 0"
      using assms False by (simp add: eventually_eval_mero_uhp_neq_iff eventually_frequently)
  qed (use assms in \<open>auto intro!: analytic_intros\<close>)
next
  case True
  hence "zorder (eval_mero_uhp f) z < 0"
    using assms by simp
  with True show ?thesis
    by auto
qed

lemma zorder_mero_uhp_nonpos_iff [simp]:
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (eval_mero_uhp f) z \<le> 0 \<longleftrightarrow> is_pole f z \<or> eval_mero_uhp f z \<noteq> 0"
  using zorder_mero_uhp_pos_iff[OF assms] by linarith

lemma zorder_mero_uhp_eq_0_iff [simp]:
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (eval_mero_uhp f) z = 0 \<longleftrightarrow> \<not>is_pole f z \<and> eval_mero_uhp f z \<noteq> 0"
  using assms by (metis linorder_cases zorder_mero_uhp_neg_iff zorder_mero_uhp_pos_iff)

lemma zorder_const_mero_uhp [simp]:
  assumes "is_const_mero_uhp f" "f \<noteq> 0" "Im z > 0"
  shows   "zorder f z = 0"
  using assms by (auto simp: is_const_mero_uhp_def)

lemma zorder_mult_mero_uhp:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "Im z > 0"
  shows   "zorder (f * g) z = zorder f z + zorder g z"
proof -
  have "mero_uhp_rel (f * g) (\<lambda>z. f z * g z)"
    by mero_uhp_rel
  hence "zorder (f * g) z = zorder (\<lambda>z. f z * g z) z" using assms
    by (intro zorder_cong)
       (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt mero_uhp_rel_def)
  also have "\<dots> = zorder f z + zorder g z"
  proof (rule zorder_mult)
    show " \<exists>\<^sub>F z in at z. eval_mero_uhp f z \<noteq> 0" " \<exists>\<^sub>F z in at z. eval_mero_uhp g z \<noteq> 0"
      using assms
      by (metis at_neq_bot eventually_eval_mero_uhp_neq_iff eventually_frequently zero_mero_uhp_def)+
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_cmult_mero_uhp [simp]:
  fixes f :: mero_uhp
  assumes [simp]: "c \<noteq> 0"
  shows   "zorder (const_mero_uhp c * f) z = zorder f z"
proof -
  have "zorder (const_mero_uhp c * f) z = zorder (\<lambda>z. c * f z) z"
    by (intro zorder_cong) auto
  also have "\<dots> = zorder f z"
    using assms zorder_cmult by blast
  finally show ?thesis .
qed

lemma zorder_cmult_mero_uhp' [simp]:
  fixes f :: mero_uhp
  assumes [simp]: "c \<noteq> 0"
  shows   "zorder (f * const_mero_uhp c) z = zorder f z"
  by (subst mult.commute) simp

lemma zorder_uminus_mero_uhp [simp]:
  fixes f :: mero_uhp
  shows "zorder (-f) z = zorder f z"
  using zorder_cmult_mero_uhp[of "-1" f z] by (simp del: zorder_cmult_mero_uhp)

lemma zorder_power_mero_uhp [simp]:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (f ^ n) z = int n * zorder f z"
  using assms by (induction n) (simp_all add: zorder_mult_mero_uhp algebra_simps)

lemma zorder_inverse_mero_uhp [simp]:
  fixes f :: mero_uhp
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (inverse f) z = -zorder f z"
proof -
  have "zorder (f * inverse f) z = zorder f z + zorder (inverse f) z"
    using assms by (subst zorder_mult_mero_uhp) auto
  also have "f * inverse f = 1"
    using assms by auto
  finally show ?thesis using assms
    by (simp add: add_eq_0_iff)
qed

lemma zorder_power_int_mero_uhp [simp]:
  fixes f :: mero_uhp
  assumes "f \<noteq> 0" "Im z > 0"
  shows   "zorder (f powi n) z = n * zorder f z"
  using assms by (auto simp: power_int_def)

lemma zorder_divide_mero_uhp:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "Im z > 0"
  shows   "zorder (f / g) z = zorder f z - zorder g z"
proof -
  have "zorder (f * inverse g) z = zorder f z - zorder g z"
    using assms by (subst zorder_mult_mero_uhp) auto
  thus ?thesis
    by (simp add: field_simps)
qed

lemma zorder_prod_mero_uhp:
  fixes f :: "'a \<Rightarrow> mero_uhp"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"  "Im z > 0"
  shows   "zorder (\<Prod>x\<in>A. f x) z = (\<Sum>x\<in>A. zorder (f x) z)"
  using assms by (induction A rule: infinite_finite_induct) (auto simp: zorder_mult_mero_uhp)

lemma zorder_mero_uhp_add_ge:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "f + g \<noteq> 0" "zorder f z \<ge> c" "zorder g z \<ge> c" "Im z > 0"
  shows   "zorder (f + g) z \<ge> c"
proof -
  note avoid = eventually_cosparse_imp_eventually_at[OF eval_mero_uhp_avoid_0]
  have rel: "mero_uhp_rel (f + g) (\<lambda>z. f z + g z)"
    by mero_uhp_rel
  have "\<forall>\<^sub>F z in at z. eval_mero_uhp (f + g) z \<noteq> 0"
    using assms by (intro avoid) auto
  moreover have ev1: "eventually (\<lambda>z. eval_mero_uhp (f + g) z = eval_mero_uhp f z + eval_mero_uhp g z) (at z)"
    using rel \<open>Im z > 0\<close>
    unfolding mero_uhp_rel_def by (intro eventually_cosparse_imp_eventually_at) auto
  ultimately have ev2: "eventually (\<lambda>w. eval_mero_uhp f w + eval_mero_uhp g w \<noteq> 0) (at z)"
    by eventually_elim auto

  hence "zorder (f + g) z = zorder (\<lambda>z. f z + g z) z"
    using ev1 by (intro zorder_cong) auto
  also have "\<dots> \<ge> c" using assms ev2
    by (intro zorder_add_ge meromorphic_intros eventually_frequently analytic_intros avoid) auto
  finally show ?thesis .
qed

lemma zorder_mero_uhp_diff_ge:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "f \<noteq> g" "zorder f z \<ge> c" "zorder g z \<ge> c" "Im z > 0"
  shows   "zorder (f - g) z \<ge> c"
  using zorder_mero_uhp_add_ge[of f "-g"] assms by simp

lemma zorder_mero_uhp_add1:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "zorder f z < zorder g z" "Im z > 0"
  shows   "zorder (f + g) z = zorder f z"
proof -
  have "mero_uhp_rel (f + g) (\<lambda>z. f z + g z)"
    by mero_uhp_rel
  hence "zorder (f + g) z = zorder (\<lambda>z. f z + g z) z"
    unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
    using assms by (intro zorder_cong) auto
  also have "\<dots> = zorder f z" using assms
    by (intro zorder_add1)
       (auto intro!: meromorphic_intros eventually_frequently 
                     eventually_cosparse_imp_eventually_at[OF eval_mero_uhp_avoid_0])
  finally show ?thesis .
qed

lemma zorder_mero_uhp_add2:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "zorder f z > zorder g z" "Im z > 0"
  shows   "zorder (f + g) z = zorder g z"
  by (subst add.commute, subst zorder_mero_uhp_add1) (use assms in auto)

lemma zorder_mero_uhp_diff1:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "zorder f z < zorder g z" "Im z > 0"
  shows   "zorder (f - g) z = zorder f z"
  using zorder_mero_uhp_add1[of f "-g"] assms by simp

lemma zorder_mero_uhp_diff2:
  fixes f g :: mero_uhp
  assumes "f \<noteq> 0" "g \<noteq> 0" "zorder f z > zorder g z" "Im z > 0"
  shows   "zorder (f - g) z = zorder g z"
  using zorder_mero_uhp_add2[of f "-g"] assms by simp

lemma filtermap_apply_modgrp_cosparse_uhp:
  "filtermap (apply_modgrp h) (cosparse {z. Im z > 0}) = cosparse {z. Im z > 0}"
proof -
  note [simp] = eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
  have [simp]: "apply_modgrp h (apply_modgrp (inverse h) z) = z" if "Im z > 0" for z h
    using that by (metis Im_pole_modgrp apply_modgrp_inverse_eqI less_irrefl modgrp.inverse_inverse)
  show ?thesis
  proof (rule filter_eqI, safe)
    fix P :: "complex \<Rightarrow> bool"
    assume *: "eventually P (filtermap (apply_modgrp h) (cosparse {z. Im z > 0}))"
    {
      fix z assume z: "Im z > 0"
      have "eventually P (filtermap (apply_modgrp h) (at z))"
        using * z by (auto simp: eventually_filtermap)
      hence "eventually P (at (apply_modgrp h z))"
        using z by (subst (asm) filtermap_at_apply_modgrp) auto
    } note ** = this
    have "eventually P (at z)" if "Im z > 0" for z
      using **[of "apply_modgrp (inverse h) z"] that by auto
    thus "eventually P (cosparse {z. Im z > 0})"
      by auto
  next
    fix P :: "complex \<Rightarrow> bool"
    assume *: "eventually P (cosparse {z. 0 < Im z})"
    {
      fix z assume z: "Im z > 0"
      have "eventually P (at z)"
        using * z by (auto simp: eventually_filtermap)
    } note ** = this
    have "eventually P (filtermap (apply_modgrp h) (at z))" if "Im z > 0" for z
      using **[of "apply_modgrp h z"] by (subst filtermap_at_apply_modgrp) (use that in auto)
    thus "eventually P (filtermap (apply_modgrp h) (cosparse {z. Im z > 0}))"
      by (auto simp: eventually_filtermap)
  qed
qed

lemma eventually_cosparse_uhp_apply_modgrp_iff:
  "eventually (\<lambda>z. P (apply_modgrp h z)) (cosparse {z. Im z > 0}) \<longleftrightarrow>
   eventually P (cosparse {z. Im z > 0})"
  using filtermap_apply_modgrp_cosparse_uhp[of h] eventually_filtermap by metis

lemma deriv_mero_uhp_compose_modgrp:
  "deriv_mero_uhp (compose_modgrp_mero_uhp f h) =
     compose_modgrp_mero_uhp (deriv_mero_uhp f) h / automorphy_factor_mero_uhp h ^ 2"
proof -
  have "mero_uhp_rel (deriv_mero_uhp (compose_modgrp_mero_uhp f h))
          (deriv (\<lambda>z. f (apply_modgrp h z)))"
    by mero_uhp_rel
  also {
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
      by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
    moreover have "eventually (\<lambda>z. \<not>is_pole f (apply_modgrp h z)) (cosparse {z. Im z > 0})"
      by (subst eventually_cosparse_uhp_apply_modgrp_iff)
         (metis eval_mero_uhp_nicely_meromorphic meromorphic_on_imp_not_pole_cosparse nicely_meromorphic_on_def order.refl)
    ultimately have "mero_uhp_rel (deriv (\<lambda>z. f (apply_modgrp h z)))
                       (\<lambda>z. deriv_mero_uhp f (apply_modgrp h z) / automorphy_factor h z ^ 2)"
      unfolding mero_uhp_rel_def
      by eventually_elim
         (auto intro!: DERIV_imp_deriv derivative_eq_intros simp: automorphy_factor_def field_simps)
  }
  also have "mero_uhp_rel ((\<lambda>z. deriv_mero_uhp f (apply_modgrp h z) / automorphy_factor h z ^ 2))
               (compose_modgrp_mero_uhp (deriv_mero_uhp f) h / automorphy_factor_mero_uhp h ^ 2)"
    by mero_uhp_rel
  finally show ?thesis
    using mero_uhp_rel_imp_eq_mero_uhp by blast
qed

lemma mero_uhp_rel_deriv_mero_uhp_compose_modgrp [mero_uhp_rel_intros]:
  "mero_uhp_rel (deriv_mero_uhp (compose_modgrp_mero_uhp f h))
     (compose_modgrp_mero_uhp (deriv_mero_uhp f) h / automorphy_factor_mero_uhp h ^ 2)"
  by (subst deriv_mero_uhp_compose_modgrp) auto

lemma eventually_not_is_pole_eval_mero_uhp:
  "eventually (\<lambda>z. \<not>is_pole (eval_mero_uhp f) z) (cosparse {z. Im z > 0})"
  by (intro meromorphic_on_imp_not_pole_cosparse meromorphic_intros) auto

lemma is_pole_plus_analytic_mero_uhp_iff1:
  fixes f g :: mero_uhp
  assumes "\<not>is_pole g z"
  shows   "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole f z"
proof (cases "Im z > 0")
  case True
  have "mero_uhp_rel (f + g) (\<lambda>z. f z + g z)"
    by mero_uhp_rel
  hence "eventually (\<lambda>z. eval_mero_uhp (f + g) z = f z + g z) (at z)"
    using True unfolding mero_uhp_rel_def by (intro eventually_cosparse_imp_eventually_at) auto
  hence "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole (\<lambda>z. f z + g z) z"
    by (intro is_pole_cong refl)
  also have "\<dots> \<longleftrightarrow> is_pole f z"
    by (intro is_pole_plus_analytic_iff1 analytic_intros) (use True assms in auto)
  finally show ?thesis .
qed (auto simp: not_is_pole_eval_mero_uhp_outside)

lemma is_pole_plus_analytic_mero_uhp_iff2:
  fixes f g :: mero_uhp
  assumes "\<not>is_pole f z"
  shows   "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole g z"
  by (subst add.commute, rule is_pole_plus_analytic_mero_uhp_iff1) fact

lemma not_is_pole_const_mero_uhp [simp]:
  assumes "is_const_mero_uhp f"
  shows   "\<not>is_pole f z"
proof (cases "Im z > 0")
  case True
  thus ?thesis using assms
    by (auto simp: is_const_mero_uhp_def) 
qed (auto simp: not_is_pole_eval_mero_uhp_outside)

lemma deriv_mero_uhp_const [simp]: "deriv_mero_uhp (const_mero_uhp c) = 0"
proof -
  have "mero_uhp_rel (deriv_mero_uhp (const_mero_uhp c)) (deriv (\<lambda>_. c))"
    by mero_uhp_rel
  also have "\<dots> = (\<lambda>z. eval_mero_uhp 0 z)"
    by simp
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed

lemma deriv_mero_uhp_0 [simp]: "deriv_mero_uhp 0 = 0"
  using deriv_mero_uhp_const[of 0] by (simp del: deriv_mero_uhp_const)

lemma deriv_mero_uhp_1 [simp]: "deriv_mero_uhp 1 = 0"
  using deriv_mero_uhp_const[of 1] by (simp del: deriv_mero_uhp_const)

lemma deriv_mero_uhp_power_int: 
  "deriv_mero_uhp (f powi n) = of_int n * deriv_mero_uhp f * f powi (n-1)"
proof (cases "f = 0")
  case False
  note * = eventually_not_is_pole_eval_mero_uhp
  have "mero_uhp_rel (deriv_mero_uhp (f powi n)) (deriv (\<lambda>z. f z powi n))"
    by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. of_int n * deriv_mero_uhp f z * f z powi (n-1))"
  proof -
    have "eventually (\<lambda>z. f z \<noteq> 0) (cosparse {z. Im z > 0})"
      by (rule eval_mero_uhp_avoid_0) (use False in auto)
    moreover have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
      by (rule eventually_in_cosparse) (auto simp: open_halfspace_Im_gt)
    ultimately have "eventually (\<lambda>z. deriv (\<lambda>z. f z powi n) z = 
                       of_int n * deriv_mero_uhp f z * f z powi (n-1)) (cosparse {z. Im z > 0})"
      using *[of f]
    proof eventually_elim
      case (elim z)
      show "deriv (\<lambda>z. f z powi n) z = of_int n * deriv_mero_uhp f z * f z powi (n-1)"
        by (rule DERIV_imp_deriv)
           (use elim in \<open>auto intro!: derivative_eq_intros simp: analytic_at_mero_uhp_iff\<close>)
    qed
    thus ?thesis
      by (auto simp: mero_uhp_rel_def)
  qed
  also have "mero_uhp_rel \<dots> (of_int n * deriv_mero_uhp f * f powi (n-1))"
    by mero_uhp_rel
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed (auto simp: power_int_0_left_if)

lemma deriv_mero_uhp_add [simp]: "deriv_mero_uhp (f + g) = deriv_mero_uhp f + deriv_mero_uhp g"
proof -
  note * = eventually_not_is_pole_eval_mero_uhp

  have "mero_uhp_rel (deriv_mero_uhp (f + g)) (\<lambda>z. deriv (\<lambda>z. f z + g z) z)"
    by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. deriv_mero_uhp f z + deriv_mero_uhp g z)"
  proof -
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
      by (rule eventually_in_cosparse) (auto simp: open_halfspace_Im_gt)
    hence "eventually (\<lambda>z. deriv (\<lambda>z. f z + g z) z = 
                       deriv_mero_uhp f z + deriv_mero_uhp g z) (cosparse {z. Im z > 0})"
      using *[of f] *[of g]
    proof eventually_elim
      case (elim z)
      show ?case
        by (rule DERIV_imp_deriv)
           (use elim in \<open>auto intro!: derivative_eq_intros simp: analytic_at_mero_uhp_iff\<close>)
    qed
    thus ?thesis
      by (auto simp: mero_uhp_rel_def)
  qed
  also have "mero_uhp_rel \<dots> (deriv_mero_uhp f + deriv_mero_uhp g)"
    by mero_uhp_rel
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed

lemma deriv_mero_uhp_mult: 
  "deriv_mero_uhp (f * g) = deriv_mero_uhp f * g + f * deriv_mero_uhp g"
proof -
  note * = eventually_not_is_pole_eval_mero_uhp

  have "mero_uhp_rel (deriv_mero_uhp (f * g)) (\<lambda>z. deriv (\<lambda>z. f z * g z) z)"
    by mero_uhp_rel
  also have "mero_uhp_rel \<dots> (\<lambda>z. deriv_mero_uhp f z * g z + f z * deriv_mero_uhp g z)"
  proof -
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
      by (rule eventually_in_cosparse) (auto simp: open_halfspace_Im_gt)
    hence "eventually (\<lambda>z. deriv (\<lambda>z. f z * g z) z = 
                       deriv_mero_uhp f z * g z + f z * deriv_mero_uhp g z) (cosparse {z. Im z > 0})"
      using *[of f] *[of g]
    proof eventually_elim
      case (elim z)
      show ?case
        by (rule DERIV_imp_deriv)
           (use elim in \<open>auto intro!: derivative_eq_intros simp: analytic_at_mero_uhp_iff\<close>)
    qed
    thus ?thesis
      by (auto simp: mero_uhp_rel_def)
  qed
  also have "mero_uhp_rel \<dots> (deriv_mero_uhp f * g + f * deriv_mero_uhp g)"
    by mero_uhp_rel
  finally show ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed

lemma deriv_mero_uhp_minus [simp]: 
  "deriv_mero_uhp (-f) = -deriv_mero_uhp f"
proof -
  have "deriv_mero_uhp (const_mero_uhp (-1) * f) = -deriv_mero_uhp f"
    by (subst deriv_mero_uhp_mult)  auto
  thus ?thesis
    by simp
qed

lemma deriv_mero_uhp_diff [simp]:
  "deriv_mero_uhp (f - g) = deriv_mero_uhp f - deriv_mero_uhp g"
proof -
  have "deriv_mero_uhp (f + (-g)) = deriv_mero_uhp f - deriv_mero_uhp g"
    by (subst deriv_mero_uhp_add) auto
  thus ?thesis
    by simp
qed

lemma deriv_mero_uhp_power [simp]: 
  "deriv_mero_uhp (f ^ n) = of_nat n * deriv_mero_uhp f * f ^ (n - 1)"
  using deriv_mero_uhp_power_int[of f "int n"] by (cases n) (auto simp: power_int_add)

lemma deriv_mero_uhp_inverse: 
  "deriv_mero_uhp (inverse f) = -deriv_mero_uhp f / f ^ 2"
  using deriv_mero_uhp_power_int[of f "-1"] by (auto simp: power_int_minus field_simps)

lemma deriv_mero_uhp_divide: 
  "deriv_mero_uhp (f / g) = (g * deriv_mero_uhp f - f * deriv_mero_uhp g) / g ^ 2"
proof (cases "g = 0")
  case [simp]: False
  have "deriv_mero_uhp (f * inverse g) = (g * deriv_mero_uhp f - f * deriv_mero_uhp g) / g ^ 2"
    by (subst deriv_mero_uhp_mult, subst deriv_mero_uhp_inverse)
       (auto simp: deriv_mero_uhp_inverse diff_divide_distrib power2_eq_square 
             simp flip: divide_inverse)
  thus ?thesis
    by (simp flip: divide_inverse)
qed auto

lemma deriv_mero_uhp_sum: "deriv_mero_uhp (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. deriv_mero_uhp (f x))"
  by (induction A rule: infinite_finite_induct) simp_all

lemma deriv_mero_uhp_poly:
  "deriv_mero_uhp (poly p f) = 
     poly (pderiv p) f * deriv_mero_uhp f + poly (map_poly deriv_mero_uhp p) f"
  by (induction p) (simp_all add: deriv_mero_uhp_mult pderiv_pCons algebra_simps map_poly_pCons)

lemma constant_on_extend_mero_uhp_rel:
  assumes "mero_uhp_rel (eval_mero_uhp f) g" "g constant_on A" 
  assumes "open A" "A \<noteq> {}" "A \<subseteq> {z. Im z > 0}"
  shows   "is_const_mero_uhp f"
proof -
  from assms obtain c where c: "\<And>z. z \<in> A \<Longrightarrow> g z = c"
    by (auto simp: constant_on_def)
  from assms obtain z0 where z0: "z0 \<in> A"
    by auto
  have "eventually (\<lambda>z. z \<in> A) (at z0)"
    using assms z0 by (intro eventually_at_in_open') auto
  moreover have "eventually (\<lambda>z. f z = g z) (at z0)"
    using assms z0 unfolding mero_uhp_rel_def
    by (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt)
  ultimately have "eventually (\<lambda>z. f z = c) (at z0)"
    by eventually_elim (use c in auto)
  hence freq: "frequently (\<lambda>z. f z = c) (at z0)"
    by (intro eventually_frequently) auto

  have "f z = c" if "Im z > 0" for z
  proof (rule frequently_eq_meromorphic_imp_constant[where f = "eval_mero_uhp f"])
    show "open {z. Im z > 0}" "connected {z. Im z > 0}" "z0 \<in> {z. Im z > 0}"
      using z0 assms by (auto intro: open_halfspace_Im_gt connected_halfspace_Im_gt)
  qed (use assms that freq in \<open>auto intro!: eval_mero_uhp_nicely_meromorphic\<close>)
  hence "f = const_mero_uhp c"
    by (intro mero_uhp_eqI_weak) auto
  thus ?thesis
    by auto
qed


definition holo_uhp :: "mero_uhp \<Rightarrow> bool" where
  "holo_uhp f \<longleftrightarrow> (\<forall>z. \<not>is_pole f z)"

lemma holo_uhp_mero_uhp_rel_transfer:
  assumes "mero_uhp_rel (eval_mero_uhp f) g"
  assumes "g analytic_on {z. Im z > 0}"
  shows   "holo_uhp f"
  unfolding holo_uhp_def
proof
  fix z :: complex
  show "\<not>is_pole f z"
  proof (cases "Im z > 0")
    case True
    have "\<not>is_pole g z"
      using True assms(2) by (metis analytic_at_imp_no_pole analytic_on_analytic_at mem_Collect_eq)
    moreover have "is_pole f z \<longleftrightarrow> is_pole g z"
      using assms(1) True
      unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
      by (intro is_pole_cong) (auto elim!: eventually_mono)
    ultimately show "\<not>is_pole f z"
      by blast
  qed (simp add: not_is_pole_eval_mero_uhp_outside)
qed

lemma holo_uhp_0 [intro, simp]: "holo_uhp 0"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (eval_mero_uhp 0) (\<lambda>_. 0)"
    by mero_uhp_rel
qed auto

lemma holo_uhp_1 [intro, simp]: "holo_uhp 1"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (eval_mero_uhp 1) (\<lambda>_. 1)"
    by mero_uhp_rel
qed auto

lemma holo_uhp_const [intro, simp]: "holo_uhp (const_mero_uhp c)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (const_mero_uhp c) (\<lambda>_. c)"
    by mero_uhp_rel
qed auto

lemma holo_uhp_of_nat [intro, simp]: "holo_uhp (of_nat n)"
  unfolding of_nat_mero_uhp by simp

lemma holo_uhp_of_int [intro, simp]: "holo_uhp (of_int n)"
  unfolding of_int_mero_uhp by simp

lemma holo_uhp_add:
  assumes "holo_uhp f" "holo_uhp g"
  shows   "holo_uhp (f + g)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (f + g) (\<lambda>x. f x + g x)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_diff:
  assumes "holo_uhp f" "holo_uhp g"
  shows   "holo_uhp (f - g)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (f - g) (\<lambda>x. f x - g x)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_uminus:
  assumes "holo_uhp f"
  shows   "holo_uhp (-f)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (-f) (\<lambda>x. -f x)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_mult:
  assumes "holo_uhp f" "holo_uhp g"
  shows   "holo_uhp (f * g)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (f * g) (\<lambda>x. f x * g x)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_power:
  assumes "holo_uhp f"
  shows   "holo_uhp (f ^ n)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (f ^ n) (\<lambda>x. f x ^ n)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_inverse:
  assumes "holo_uhp f" "\<And>z. Im z > 0 \<Longrightarrow> f z \<noteq> 0"
  shows   "holo_uhp (inverse f)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (inverse f) (\<lambda>x. inverse (f x))"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_divide:
  assumes "holo_uhp f" "holo_uhp g" "\<And>z. Im z > 0 \<Longrightarrow> g z \<noteq> 0"
  shows   "holo_uhp (f / g)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (f / g) (\<lambda>x. f x / g x)"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_power_int:
  assumes "holo_uhp f" "n \<ge> 0 \<or> (\<forall>z. Im z > 0 \<longrightarrow> f z \<noteq> 0)"
  shows   "holo_uhp (f powi n)"
  unfolding power_int_def using assms(2) 
  by (auto split: if_splits intro!: holo_uhp_inverse holo_uhp_power assms(1))

lemma holo_uhp_sum:
  "(\<And>x. x \<in> A \<Longrightarrow> holo_uhp (f x)) \<Longrightarrow> holo_uhp (\<Sum>x\<in>A. f x)"
  by (induction A rule: infinite_finite_induct) (auto intro!: holo_uhp_add)

lemma holo_uhp_deriv:
  assumes "holo_uhp f"
  shows   "holo_uhp (deriv_mero_uhp f)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (deriv_mero_uhp f) (deriv (eval_mero_uhp f))"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_automorphy_factor: "holo_uhp (automorphy_factor_mero_uhp h)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (automorphy_factor_mero_uhp h) (automorphy_factor h)"
    by mero_uhp_rel
qed (auto intro!: analytic_intros simp: holo_uhp_def)

lemma holo_uhp_compose_mero_uhp_modgrp:
  assumes "holo_uhp f"
  shows   "holo_uhp (compose_modgrp_mero_uhp f h)"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel (compose_modgrp_mero_uhp f h) (\<lambda>z. f (apply_modgrp h z))"
    by mero_uhp_rel
qed (use assms in \<open>auto intro!: analytic_intros simp: holo_uhp_def\<close>)

lemma holo_uhp_slash:
  assumes "holo_uhp f"
  shows   "holo_uhp (slash_mero_uhp weight h f)"
  unfolding slash_mero_uhp_def
  by (intro holo_uhp_mult holo_uhp_power_int holo_uhp_automorphy_factor 
            holo_uhp_compose_mero_uhp_modgrp assms) auto

end