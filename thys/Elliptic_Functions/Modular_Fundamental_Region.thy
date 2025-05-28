section \<open>Fundamental regions of the modular group\<close>
theory Modular_Fundamental_Region
  imports Modular_Group Complex_Lattices "HOL-Library.Real_Mod"
begin

subsection \<open>Definition\<close>

text \<open>
  A fundamental region of a subgroup of the modular group is an open subset of the upper half of
  the complex plane that contains at most one representative of every equivalence class
  and whose closure contains at least one representative of every equivalence class.
\<close>
locale fundamental_region = modgrp_subgroup +
  fixes R :: "complex set"
  assumes "open": "open R"
  assumes subset: "R \<subseteq> {z. Im z > 0}"
  assumes unique: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> rel x y \<Longrightarrow> x = y"
  assumes equiv_in_closure: "\<And>x. Im x > 0 \<Longrightarrow> \<exists>y\<in>closure R. rel x y "
begin

text \<open>The uniqueness property can be extended to the closure of \<open>R\<close>:\<close>
lemma unique':
  assumes "x \<in> R" "y \<in> closure R" "rel x y" "Im y > 0"
  shows   "x = y"
proof (cases "y \<in> R")
  case False
  show ?thesis
  proof (rule ccontr)
    assume xy: "x \<noteq> y"
    from assms have "rel y x"
      by (simp add: rel_commutes)
    then obtain f where f: "x = apply_modgrp f y" "f \<in> G"
      unfolding rel_def by blast
  
    have "continuous_on {z. Im z > 0} (apply_modgrp f)"
      by (intro continuous_intros) auto
    hence "isCont (apply_modgrp f) y"
      using open_halfspace_Im_gt[of 0] assms continuous_on_eq_continuous_at by blast
    hence lim: "apply_modgrp f \<midarrow>y\<rightarrow> x"
      using f by (simp add: isCont_def)

    define \<epsilon> where "\<epsilon> = dist x y / 2"
    have \<epsilon>: "\<epsilon> > 0"
      using xy by (auto simp: \<epsilon>_def)

    have "eventually (\<lambda>w. w \<in> ball x \<epsilon> \<inter> R) (nhds x)"
      by (intro eventually_nhds_in_open) (use assms \<epsilon> "open" in auto)
    from this and lim have "eventually (\<lambda>z. apply_modgrp f z \<in> ball x \<epsilon> \<inter> R) (at y)"
      by (rule eventually_compose_filterlim)
    moreover have "eventually (\<lambda>z. z \<in> ball y \<epsilon>) (nhds y)"
      using assms \<epsilon> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>z. z \<in> ball y \<epsilon>) (at y)"
      unfolding eventually_at_filter by eventually_elim auto
    ultimately have "eventually (\<lambda>z. z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) (at y)"
      by eventually_elim auto
    moreover have "y islimpt R"
      using \<open>y \<in> closure R\<close> \<open>y \<notin> R\<close> by (auto simp: closure_def)
    hence "frequently (\<lambda>z. z \<in> R) (at y)"
      using islimpt_conv_frequently_at by blast
    ultimately have "frequently (\<lambda>z.
                        (z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) \<and> z \<in> R) (at y)"
      by (intro frequently_eventually_conj)
    hence "frequently (\<lambda>z. False) (at y)"
    proof (rule frequently_elim1)
      fix z assume z: "(z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) \<and> z \<in> R"
      have "ball y \<epsilon> \<inter> ball x \<epsilon> = {}"
        by (intro disjoint_ballI) (auto simp: \<epsilon>_def dist_commute)
      with z have "apply_modgrp f z \<noteq> z"
        by auto
      with z f subset show False
        using unique[of z "apply_modgrp f z"] by auto
    qed
    thus False
      by simp
  qed
qed (use assms unique in auto)

lemma
  pole_modgrp_not_in_region [simp]: "pole_modgrp f \<notin> R" and
  pole_image_modgrp_not_in_region [simp]: "pole_image_modgrp f \<notin> R"
  using subset by force+


end


subsection \<open>The standard fundamental region\<close>

text \<open>
  The standard fundamental region \<open>\<R>\<^sub>\<Gamma>\<close> consists of all the points \<open>z\<close> in the upper half plane
  with \<open>|z| > 1\<close> and $|\text{Re}(z)| < \frac{1}{2}$.
\<close>
definition std_fund_region :: "complex set" ("\<R>\<^sub>\<Gamma>") where
  "\<R>\<^sub>\<Gamma> = -cball 0 1 \<inter> Re -` {-1/2<..<1/2} \<inter> {z. Im z > 0}"

text \<open>
  The following version of \<open>\<R>\<^sub>\<Gamma>\<close> is what Apostol refers to as the closure of \<open>\<R>\<^sub>\<Gamma>\<close>, but it is
  actually only part of the closure: since each point at the border of the fundamental region
  is equivalent to its mirror image w.r.t.\ the \<open>Im(z) = 0\<close> axis, we only want one of these copies
  to be in \<open>\<R>\<^sub>\<Gamma>'\<close>, and we choose the left one.

  So \<open>\<R>\<^sub>\<Gamma>'\<close> is actually \<open>\<R>\<^sub>\<Gamma>\<close> plus all the points on the left border plus all points on the
  left half of the semicircle.
\<close>
definition std_fund_region' :: "complex set" ("\<R>\<^sub>\<Gamma>''") where
  "\<R>\<^sub>\<Gamma>' = \<R>\<^sub>\<Gamma> \<union> (-ball 0 1 \<inter> Re -` {-1/2..0} \<inter> {z. Im z > 0})"

lemma std_fund_region_altdef:
  "\<R>\<^sub>\<Gamma> = {z. norm z > 1 \<and> norm (z + cnj z) < 1 \<and> Im z > 0}"
  by (auto simp: std_fund_region_def complex_add_cnj)

lemma in_std_fund_region_iff:
  "z \<in> \<R>\<^sub>\<Gamma> \<longleftrightarrow> norm z > 1 \<and> Re z \<in> {-1/2<..<1/2} \<and> Im z > 0"
  by (auto simp: std_fund_region_def field_simps)

lemma in_std_fund_region'_iff:
  "z \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> Im z > 0 \<and> ((norm z > 1 \<and> Re z \<in> {-1/2..<1/2}) \<or> (norm z = 1 \<and> Re z \<in> {-1/2..0}))"
  by (auto simp: std_fund_region'_def std_fund_region_def field_simps)

lemma open_std_fund_region [simp, intro]: "open \<R>\<^sub>\<Gamma>"
  unfolding std_fund_region_def
  by (intro open_Int open_vimage continuous_intros open_halfspace_Im_gt) auto

lemma Im_std_fund_region: "z \<in> \<R>\<^sub>\<Gamma> \<Longrightarrow> Im z > 0"
  by (auto simp: std_fund_region_def)


text \<open>
  We now show that the closure of the standard fundamental region contains exactly those points \<open>z\<close>
  with \<open>|z| \<ge> 1\<close> and $|\text{Re}(z)| \leq \frac{1}{2}$.
\<close>
context
  fixes S S' :: "(real \<times> real) set" and T :: "complex set"
  fixes f :: "real \<times> real \<Rightarrow> complex" and g :: "complex \<Rightarrow> real \<times> real"
  defines "f \<equiv> (\<lambda>(x,y). Complex x (y + sqrt (1 - x ^ 2)))"
  defines "g \<equiv> (\<lambda>z. (Re z, Im z - sqrt (1 - Re z ^ 2)))"
  defines "S \<equiv> ({-1/2<..<1/2} \<times> {0<..})"
  defines "S' \<equiv> ({-1/2..1/2} \<times> {0..})"
  defines "T \<equiv> {z. norm z \<ge> 1 \<and> Re z \<in> {-1/2..1/2} \<and> Im z \<ge> 0}"
begin

lemma image_subset_std_fund_region: "f ` S \<subseteq> \<R>\<^sub>\<Gamma>"
  unfolding subset_iff in_std_fund_region_iff S_def
proof safe
  fix a b :: real
  assume ab: "a \<in> {-1/2<..<1/2}" "b > 0"
  have "\<bar>a\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using ab by (intro power_mono) auto
  hence "a ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "a ^ 2 \<le> 1"
    by simp

  show "Im (f (a, b)) > 0"
    using ab \<open>a ^ 2 \<le> 1 / 4\<close> by (auto simp: f_def intro: add_pos_nonneg)

  show "Re (f (a, b)) \<in> {-1/2<..<1/2}"
    using ab by (simp add: f_def)

  have "1 ^ 2 = a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2"
    using \<open>a ^ 2 \<le> 1 / 4\<close> by (simp add: power2_eq_square algebra_simps)
  also have "a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2 < a\<^sup>2 + (b + sqrt (1 - a\<^sup>2)) ^ 2"
    using ab \<open>a ^ 2 \<le> 1\<close> by (intro add_strict_left_mono power2_mono power2_strict_mono) auto
  also have "\<dots> = norm (f (a, b)) ^ 2"
    by (simp add: f_def norm_complex_def)
  finally show "norm (f (a, b)) > 1"
    by (rule power2_less_imp_less) auto
qed

lemma image_std_fund_region_subset: "g ` \<R>\<^sub>\<Gamma> \<subseteq> S"
  unfolding subset_iff g_def S_def
proof safe
  fix z :: complex
  assume "z \<in> \<R>\<^sub>\<Gamma>"
  hence z: "norm z > 1" "Re z \<in> {-1/2<..<1/2}" "Im z > 0"
    by (auto simp: in_std_fund_region_iff)

  have "\<bar>Re z\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using z by (intro power_mono) auto
  hence "Re z ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "Re z ^ 2 \<le> 1"
    by simp

  from z show "Re z \<in> {- 1 / 2<..<1 / 2}"
    by auto

  have "sqrt (1 - Re z ^ 2) ^ 2 = 1 - Re z ^ 2"
    using \<open>Re z ^ 2 \<le> 1\<close> by simp
  also have "\<dots> < Im z ^ 2"
    using z by (simp add: norm_complex_def algebra_simps)
  finally have "sqrt (1 - Re z ^ 2) < Im z"
    by (rule power2_less_imp_less) (use z in auto)
  thus "Im z - sqrt (1 - Re z ^ 2) > 0"
    by simp
qed

lemma std_fund_region_map_inverses: "f (g x) = x" "g (f y) = y"
  by (simp_all add: f_def g_def case_prod_unfold)

lemma bij_betw_std_fund_region1: "bij_betw f S \<R>\<^sub>\<Gamma>"
  using image_std_fund_region_subset image_subset_std_fund_region
  by (intro bij_betwI[of _ _ _ g]) (auto simp: std_fund_region_map_inverses)

lemma bij_betw_std_fund_region2: "bij_betw g \<R>\<^sub>\<Gamma> S"
  using image_std_fund_region_subset image_subset_std_fund_region
  by (intro bij_betwI[of _ _ _ f]) (auto simp: std_fund_region_map_inverses)

lemma image_subset_std_fund_region': "f ` S' \<subseteq> T"
  unfolding subset_iff S'_def T_def
proof safe
  fix a b :: real
  assume ab: "a \<in> {-1/2..1/2}" "b \<ge> 0"
  have "\<bar>a\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using ab by (intro power_mono) auto
  hence "a ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "a ^ 2 \<le> 1"
    by simp

  show "Im (f (a, b)) \<ge> 0"
    using ab \<open>a ^ 2 \<le> 1 / 4\<close> by (auto simp: f_def intro: add_pos_nonneg)

  show "Re (f (a, b)) \<in> {-1/2..1/2}"
    using ab by (simp add: f_def)

  have "1 ^ 2 = a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2"
    using \<open>a ^ 2 \<le> 1 / 4\<close> by (simp add: power2_eq_square algebra_simps)
  also have "a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2 \<le> a\<^sup>2 + (b + sqrt (1 - a\<^sup>2)) ^ 2"
    using ab \<open>a ^ 2 \<le> 1\<close> by (intro add_left_mono power2_mono power2_strict_mono) auto
  also have "\<dots> = norm (f (a, b)) ^ 2"
    by (simp add: f_def norm_complex_def)
  finally show "norm (f (a, b)) \<ge> 1"
    by (rule power2_le_imp_le) auto
qed

lemma image_std_fund_region_subset': "g ` T \<subseteq> S'"
  unfolding subset_iff g_def S'_def
proof safe
  fix z :: complex
  assume "z \<in> T"
  hence z: "norm z \<ge> 1" "Re z \<in> {-1/2..1/2}" "Im z \<ge> 0"
    by (auto simp: T_def)

  have "\<bar>Re z\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using z by (intro power_mono) auto
  hence "Re z ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "Re z ^ 2 \<le> 1"
    by simp

  from z show "Re z \<in> {-1/2..1/2}"
    by auto

  have "sqrt (1 - Re z ^ 2) ^ 2 = 1 - Re z ^ 2"
    using \<open>Re z ^ 2 \<le> 1\<close> by simp
  also have "\<dots> \<le> Im z ^ 2"
    using z by (simp add: norm_complex_def algebra_simps)
  finally have "sqrt (1 - Re z ^ 2) \<le> Im z"
    by (rule power2_le_imp_le) (use z in auto)
  thus "Im z - sqrt (1 - Re z ^ 2) \<ge> 0"
    by simp
qed

lemma bij_betw_std_fund_region1': "bij_betw f S' T"
  using image_std_fund_region_subset' image_subset_std_fund_region'
  by (intro bij_betwI[of _ _ _ g]) (auto simp: std_fund_region_map_inverses)

lemma bij_betw_std_fund_region2': "bij_betw g T S'"
  using image_std_fund_region_subset' image_subset_std_fund_region'
  by (intro bij_betwI[of _ _ _ f]) (auto simp: std_fund_region_map_inverses)

lemma closure_std_fund_region: "closure \<R>\<^sub>\<Gamma> = T"
proof -
  have homeo: "homeomorphism S \<R>\<^sub>\<Gamma> f g"
    using image_std_fund_region_subset image_subset_std_fund_region
    by (intro homeomorphismI)
       (auto simp: g_def f_def case_prod_unfold intro!: continuous_intros)

  have "closure \<R>\<^sub>\<Gamma> = closure (f ` S)"
    using bij_betw_std_fund_region1 by (simp add: bij_betw_def)
  also have "\<dots> = f ` closure S"
    using bij_betw_std_fund_region1 homeo
  proof (rule closure_bij_homeomorphic_image_eq)
    show "continuous_on UNIV f" "continuous_on UNIV g"
      by (auto simp: f_def g_def case_prod_unfold intro!: continuous_intros)
  qed (auto simp: std_fund_region_map_inverses)
  also have "closure S = {-1 / 2..1 / 2} \<times> {0..}"
    by (simp add: S_def closure_Times)
  also have "\<dots> = S'"
    by (simp add: S'_def)
  also have "f ` S' = T"
    using bij_betw_std_fund_region1' by (simp add: bij_betw_def)
  finally show ?thesis .
qed

lemma in_closure_std_fund_region_iff:
  "x \<in> closure \<R>\<^sub>\<Gamma> \<longleftrightarrow> norm x \<ge> 1 \<and> Re x \<in> {-1/2..1/2} \<and> Im x \<ge> 0"
  by (simp add: closure_std_fund_region T_def)

lemma frontier_std_fund_region:
  "frontier \<R>\<^sub>\<Gamma> =
     {z. norm z \<ge> 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> = 1 / 2} \<union>
     {z. norm z = 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> \<le> 1 / 2}" (is "_ = ?rhs")
proof -
  have [simp]: "x ^ 2 \<ge> 1 \<longleftrightarrow> x \<ge> 1 \<or> x \<le> -1" for x :: real
    using abs_le_square_iff[of 1 x] by auto
  have "frontier \<R>\<^sub>\<Gamma> = closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>"
    unfolding frontier_def by (subst interior_open) simp_all
  also have "\<dots> = ?rhs"
    unfolding closure_std_fund_region unfolding std_fund_region_def
    by (auto simp: cmod_def T_def)
  finally show ?thesis .
qed

lemma std_fund_region'_subset_closure: "\<R>\<^sub>\<Gamma>' \<subseteq> closure \<R>\<^sub>\<Gamma>"
  by (auto simp: in_std_fund_region'_iff in_closure_std_fund_region_iff)

lemma std_fund_region'_superset: "\<R>\<^sub>\<Gamma> \<subseteq> \<R>\<^sub>\<Gamma>'"
  by (auto simp: in_std_fund_region'_iff in_std_fund_region_iff)

lemma in_std_fund_region'_not_on_frontier_iff:
  assumes "z \<notin> frontier \<R>\<^sub>\<Gamma>"
  shows   "z \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>"
proof
  assume "z \<in> \<R>\<^sub>\<Gamma>'"
  hence "z \<in> closure \<R>\<^sub>\<Gamma>"
    using std_fund_region'_subset_closure by blast
  thus "z \<in> \<R>\<^sub>\<Gamma>"
    using assms by (auto simp: frontier_def interior_open)
qed (use std_fund_region'_superset in auto)

lemma simply_connected_std_fund_region: "simply_connected \<R>\<^sub>\<Gamma>"
proof (rule simply_connected_retraction_gen)
  show "simply_connected S"
    unfolding S_def by (intro convex_imp_simply_connected convex_Times) auto
  show "continuous_on S f"
    unfolding f_def S_def case_prod_unfold by (intro continuous_intros)
  show "continuous_on \<R>\<^sub>\<Gamma> g"
    unfolding g_def case_prod_unfold by (intro continuous_intros)
  show "f ` S = \<R>\<^sub>\<Gamma>"
    using bij_betw_std_fund_region1 by (simp add: bij_betw_def)
  show "g \<in> \<R>\<^sub>\<Gamma> \<rightarrow> S"
    using bij_betw_std_fund_region2 bij_betw_imp_funcset by blast
  show "f (g x) = x" for x
    by (simp add: f_def g_def)
qed

lemma simply_connected_closure_std_fund_region: "simply_connected (closure \<R>\<^sub>\<Gamma>)"
proof (rule simply_connected_retraction_gen)
  show "simply_connected S'"
    unfolding S'_def by (intro convex_imp_simply_connected convex_Times) auto
  show "continuous_on S' f"
    unfolding f_def S'_def case_prod_unfold by (intro continuous_intros)
  show "continuous_on (closure \<R>\<^sub>\<Gamma>) g"
    unfolding g_def case_prod_unfold by (intro continuous_intros)
  show "f ` S' = closure \<R>\<^sub>\<Gamma>"
    using bij_betw_std_fund_region1' by (simp add: bij_betw_def closure_std_fund_region)
  show "g \<in> closure \<R>\<^sub>\<Gamma> \<rightarrow> S'"
    using bij_betw_std_fund_region2' bij_betw_imp_funcset closure_std_fund_region by blast
  show "f (g x) = x" for x
    by (simp add: f_def g_def)
qed

lemma std_fund_region'_subset: "\<R>\<^sub>\<Gamma>' \<subseteq> closure \<R>\<^sub>\<Gamma>"
  unfolding std_fund_region'_def closure_std_fund_region T_def unfolding std_fund_region_def
  by auto

lemma closure_std_fund_region_Im_pos: "closure \<R>\<^sub>\<Gamma> \<subseteq> {z. Im z > 0}"
  unfolding closure_std_fund_region
  by (auto intro!: neq_le_trans simp: norm_complex_def field_simps power2_ge_1_iff T_def)

lemma closure_std_fund_region_Im_ge: "closure \<R>\<^sub>\<Gamma> \<subseteq> {z. Im z \<ge> sqrt 3 / 2}"
proof
  fix z assume "z \<in> closure \<R>\<^sub>\<Gamma>"
  hence *: "norm z \<ge> 1" "\<bar>Re z\<bar> \<le> 1 / 2" "Im z \<ge> 0"
    by (auto simp: closure_std_fund_region T_def)
  have "1 \<le> norm z ^ 2"
    using * by simp
  also have "norm z ^ 2 \<le> (1 / 2) ^ 2 + Im z ^ 2"
    unfolding cmod_power2 by (intro add_right_mono power2_mono) (use * in auto)
  finally have "Im z ^ 2 \<ge> (sqrt 3 / 2) ^ 2"
    by (simp add: power2_eq_square)
  hence "Im z \<ge> sqrt 3 / 2"
    by (subst (asm) abs_le_square_iff [symmetric]) (use * in auto)
  thus "z \<in> {z. Im z \<ge> sqrt 3 / 2}"
    by simp
qed  

lemma std_fund_region'_minus_std_fund_region:
  "\<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma> =
      {z. norm z = 1 \<and> Im z > 0 \<and> Re z \<in> {-1/2..0}} \<union> {z. Re z = -1 / 2 \<and> Im z \<ge> sqrt 3 / 2}"
  (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> ?lhs"
  from z have "Im z \<ge> sqrt 3 / 2"
    using closure_std_fund_region_Im_ge std_fund_region'_subset by auto
  thus "z \<in> ?rhs" using z
    by (auto simp: std_fund_region'_def std_fund_region_def not_less)
next
  fix z assume z: "z \<in> ?rhs"
  have "sqrt 3 / 2 > 0"
    by simp
  have "Im z > 0"
    using z less_le_trans[OF \<open>sqrt 3 / 2 > 0\<close>, of "Im z"] by auto
  moreover have "norm z \<ge> 1"
    using z
  proof
    assume "z \<in> {z. Re z = - 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
    hence "norm z ^ 2 \<ge> (-1/2) ^ 2 + (sqrt 3 / 2) ^ 2"
      unfolding cmod_power2 by (intro add_mono power2_mono) auto
    also have "(-1/2) ^ 2 + (sqrt 3 / 2) ^ 2 = 1"
      by (simp add: field_simps power2_eq_square)
    finally show "norm z \<ge> 1"
      by (simp add: power2_nonneg_ge_1_iff)
  qed auto
  ultimately show "z \<in> ?lhs" using z
    by (auto simp: std_fund_region'_def std_fund_region_def)
qed

lemma closure_std_fund_region_minus_std_fund_region':
  "closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>' =
      {z. norm z = 1 \<and> Im z > 0 \<and> Re z \<in> {0<..1/2}} \<union> {z. Re z = 1 / 2 \<and> Im z \<ge> sqrt 3 / 2}"
  (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>'"
  have "norm z \<ge> 1"
    using z by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  from z have "Im z > 0" "Im z \<ge> sqrt 3 / 2"
    using closure_std_fund_region_Im_pos closure_std_fund_region_Im_ge by blast+
  thus "z \<in> ?rhs" using z
    by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
next
  fix z assume "z \<in> ?rhs"
  thus "z \<in> ?lhs"
  proof
    assume "z \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> Re z \<in> {0<..1 / 2}}"
    thus "z \<in> ?lhs"
      by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  next
    assume z: "z \<in> {z. Re z = 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
    have "0 < sqrt 3 / 2"
      by simp
    also have "\<dots> \<le> Im z"
      using z by auto
    finally have "Im z > 0" .
    have "norm z ^ 2 \<ge> (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
      unfolding cmod_power2 by (intro add_mono power2_mono) (use z in auto)
    also have "(1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2 = 1"
      by (simp add: power2_eq_square)
    finally have "norm z \<ge> 1"
      by (simp add: power2_nonneg_ge_1_iff)
    from this and \<open>Im z > 0\<close> and z show "z \<in> ?lhs"
      by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  qed  
qed

lemma cis_in_std_fund_region'_iff:
  assumes "\<phi> \<in> {0..pi}"
  shows   "cis \<phi> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> \<phi> \<in> {pi/2..2*pi/3}"
proof
  assume \<phi>: "\<phi> \<in> {pi/2..2*pi/3}"
  have "\<phi> > 0"
    by (rule less_le_trans[of _ "pi / 2"]) (use \<phi> in auto)
  moreover have "\<phi> < pi"
    by (rule le_less_trans[of _ "2 * pi / 3"]) (use \<phi> in auto)
  ultimately have "sin \<phi> > 0"
    by (intro sin_gt_zero) auto
  moreover have "cos \<phi> \<ge> cos (2 * pi / 3)"
    using \<phi> by (intro cos_monotone_0_pi_le) auto
  moreover have "cos \<phi> \<le> cos (pi / 2)"
    using \<phi> by (intro cos_monotone_0_pi_le) auto
  ultimately show "cis \<phi> \<in> \<R>\<^sub>\<Gamma>'"
    by (auto simp: in_std_fund_region'_iff cos_120)
next
  assume "cis \<phi> \<in> \<R>\<^sub>\<Gamma>'"
  hence *: "cos \<phi> \<ge> cos (2 * pi / 3)" "cos \<phi> \<le> cos (pi / 2)"
    by (auto simp: in_std_fund_region'_iff cos_120)
  have "\<phi> \<le> 2 * pi / 3"
    using *(1) assms by (subst (asm) cos_mono_le_eq) auto
  moreover have "\<phi> \<ge> pi / 2"
    using *(2) assms by (subst (asm) cos_mono_le_eq) auto
  ultimately show "\<phi> \<in> {pi/2..2*pi/3}"
    by auto
qed

lemma imag_axis_in_std_fund_region'_iff: "y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> y \<ge> 1"
  by (auto simp: in_std_fund_region'_iff)

lemma vertical_left_in_std_fund_region'_iff:
  "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> y \<ge> sqrt 3 / 2"
proof
  assume y: "y \<ge> sqrt 3 / 2"
  have "1 = (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> (1 / 2) ^ 2 + y ^ 2"
    using y by (intro add_mono power2_mono) auto
  also have "\<dots> = norm (y *\<^sub>R \<i> - 1 / 2) ^ 2"
    unfolding cmod_power2 by simp
  finally have "norm (y *\<^sub>R \<i> - 1 / 2) \<ge> 1"
    by (simp add: power2_nonneg_ge_1_iff)
  moreover have "y > 0"
    by (rule less_le_trans[OF _ y]) auto
  ultimately show "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>'"
    using y by (auto simp: in_std_fund_region'_iff)
next
  assume *: "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>'"
  hence "y > 0"
    by (auto simp: in_std_fund_region'_iff)
  from * have "1 \<le> norm (y *\<^sub>R \<i> - 1 / 2)"
    by (auto simp: in_std_fund_region'_iff)
  hence "1 \<le> norm (y *\<^sub>R \<i> - 1 / 2) ^ 2"
    by (simp add: power2_nonneg_ge_1_iff)
  also have "\<dots> = (1 / 2) ^ 2 + y ^ 2"
    unfolding cmod_power2 by simp
  finally have "y ^ 2 \<ge> (sqrt 3 / 2) ^ 2"
    by (simp add: algebra_simps power2_eq_square)
  hence "y \<ge> sqrt 3 / 2"
    by (rule power2_le_imp_le) (use \<open>y > 0\<close> in auto)
  thus "y \<ge> sqrt 3 / 2" using *
    by (auto simp: in_std_fund_region'_iff)
qed

lemma std_fund_region'_border_aux1:
  "{z. norm z = 1 \<and> 0 < Im z \<and> Re z \<in> {-1/2..0}} = cis ` {pi / 2..2 / 3 * pi}"
proof safe
  fix z :: complex assume z: "norm z = 1" "Im z > 0" "Re z \<in> {-1/2..0}"
  show "z \<in> cis ` {pi/2..2/3*pi}"
  proof (rule rev_image_eqI)
    from z have [simp]: "z \<noteq> 0"
      by auto
    have [simp]: "Arg z \<ge> 0"
      using z by (auto simp: Arg_less_0)
    have z_eq: "cis (Arg z) = z"
      using z by (auto simp: cis_Arg complex_sgn_def)
    thus "z = cis (Arg z)"
      by simp
    have "Re (cis (Arg z)) \<ge> -1/2"
      using z by (subst z_eq) auto
    hence "cos (Arg z) \<ge> cos (2/3*pi)"
      by (simp add: cos_120 cos_120')
    hence "Arg z \<le> 2 / 3 * pi"
      using Arg_le_pi by (subst (asm) cos_mono_le_eq) auto
    moreover have "Re (cis (Arg z)) \<le> 0"
      using z by (subst z_eq) auto
    hence "cos (Arg z) \<le> cos (pi / 2)"
      by simp
    hence "Arg z \<ge> pi / 2"
      using Arg_le_pi by (subst (asm) cos_mono_le_eq) auto
    ultimately show "Arg z \<in> {pi/2..2/3*pi}"
      by simp
  qed
next
  fix t :: real assume t: "t \<in> {pi/2..2/3*pi}"
  have "t > 0"
    by (rule less_le_trans[of _ "pi/2"]) (use t in auto)
  have "t < pi"
    by (rule le_less_trans[of _ "2/3*pi"]) (use t in auto)
  have "sin t > 0"
    using \<open>t > 0\<close> \<open>t < pi\<close> by (intro sin_gt_zero) auto
  moreover have "cos t \<le> cos (pi / 2)"
    using t \<open>t < pi\<close> by (intro cos_monotone_0_pi_le) auto
  moreover have "cos t \<ge> cos (2*pi/3)"
    using t by (intro cos_monotone_0_pi_le) auto
  ultimately show "norm (cis t) = 1" "Im (cis t) > 0" "Re (cis t) \<in> {-1/2..0}"
    by (auto simp: cos_120 cos_120')
qed

lemma std_fund_region'_border_aux2:
  "{z. Re z = - 1 / 2 \<and> sqrt 3 / 2 \<le> Im z} = (\<lambda>x. - 1 / 2 + x *\<^sub>R \<i>) ` {sqrt 3 / 2..}"
  by (auto simp: complex_eq_iff)

lemma compact_std_fund_region:
  assumes "B > 1"
  shows "compact (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
  unfolding compact_eq_bounded_closed
proof
  show "closed (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
    by (intro closed_Int closed_halfspace_Im_le) auto
next
  show "bounded (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
  proof -
    have "closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B} \<subseteq> cbox (-1/2) (1/2 + \<i> * B)"
      by (auto simp: in_closure_std_fund_region_iff in_cbox_complex_iff)
    moreover have "bounded (cbox (-1/2) (1/2 + \<i> * B))"
      by simp
    ultimately show ?thesis
      using bounded_subset by blast
  qed
qed

end


subsection \<open>Proving that the standard region is fundamental\<close>

lemma norm_open_segment_less:
  fixes x y z :: "'a :: euclidean_space"
  assumes "norm x \<le> norm y" "z \<in> open_segment x y"
  shows   "norm z < norm y"
  using assms
  by (metis (no_types, opaque_lifting) diff_zero dist_decreases_open_segment
         dist_norm norm_minus_commute order_less_le_trans)


text \<open>Lemma 1\<close>
lemma (in complex_lattice) std_fund_region_fundamental_lemma1:
  obtains \<omega>1' \<omega>2' :: complex and a b c d :: int
  where "\<bar>a * d - b * c\<bar> = 1"
        "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
        "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
        "Im (\<omega>2' / \<omega>1') \<noteq> 0"
        "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
proof -
  have "\<Lambda>\<^sup>* \<subseteq> \<Lambda>" "\<Lambda>\<^sup>* \<noteq> {}"
    by auto
  then obtain \<omega>1' where \<omega>1': "\<omega>1' \<in> \<Lambda>\<^sup>*" "\<And>y. y \<in> \<Lambda>\<^sup>* \<Longrightarrow> norm \<omega>1' \<le> norm y"
    using shortest_lattice_vector_exists by blast

  define X where "X = {y. y \<in> \<Lambda>\<^sup>* \<and> y / \<omega>1' \<notin> \<real>}"
  have "X \<subseteq> \<Lambda>"
    by (auto simp: X_def lattice0_def)
  moreover have  "X \<noteq> {}"
    using noncollinear_lattice_point_exists[of \<omega>1'] \<omega>1'(1) unfolding X_def by force
  ultimately obtain \<omega>2' where \<omega>2': "\<omega>2' \<in> X" "\<And>z. z \<in> X \<Longrightarrow> norm \<omega>2' \<le> norm z"
    using shortest_lattice_vector_exists by blast

  have [simp]: "\<omega>1' \<noteq> 0" "\<omega>2' \<noteq> 0"
    using \<omega>1' \<omega>2' by (auto simp: lattice0_def X_def)
  have noncollinear: "\<omega>2' / \<omega>1' \<notin> \<real>"
    using \<omega>2' by (auto simp: X_def)
  hence fundpair': "fundpair (\<omega>1', \<omega>2')"
    unfolding fundpair_def prod.case by simp
  have Im_nz: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
    using noncollinear by (auto simp: complex_is_Real_iff)

  have "norm \<omega>1' \<le> norm \<omega>2'"
    by (intro \<omega>1') (use \<omega>2' in \<open>auto simp: X_def\<close>)

  have triangle: "z \<notin> \<Lambda>" if z: "z \<in> convex hull {0, \<omega>1', \<omega>2'}" "z \<notin> {0, \<omega>1', \<omega>2'}" for z
  proof
    assume "z \<in> \<Lambda>"
    hence "z \<in> \<Lambda>\<^sup>*"
      using z by (auto simp: lattice0_def)
    from that obtain a b where ab: "a \<ge> 0" "b \<ge> 0" "a + b \<le> 1" "z = a *\<^sub>R \<omega>1' + b *\<^sub>R \<omega>2'"
      unfolding convex_hull_3_alt by (auto simp: scaleR_conv_of_real)

    have "norm z \<le> norm (a *\<^sub>R \<omega>1') + norm (b *\<^sub>R \<omega>2')"
      unfolding ab using norm_triangle_ineq by blast
    also have "\<dots> = a * norm \<omega>1' + b * norm \<omega>2'"
      using ab by simp
    finally have norm_z_le: "norm z \<le> a * norm \<omega>1' + b * norm \<omega>2'" .

    also have "\<dots> \<le> a * norm \<omega>2' + b * norm \<omega>2'"
      using ab \<open>norm \<omega>1' \<le> norm \<omega>2'\<close> by (intro add_mono mult_left_mono) auto
    also have "\<dots> = (a + b) * norm \<omega>2'"
      by (simp add: algebra_simps)
    finally have norm_z_le': "norm z \<le> (a + b) * norm \<omega>2'" .

    have "z / \<omega>1' \<notin> \<real>"
    proof
      assume real: "z / \<omega>1' \<in> \<real>"
      show False
      proof (cases "b = 0")
        case False
        hence "\<omega>2' / \<omega>1' = (z / \<omega>1' - of_real a) / of_real b"
          by (simp add: ab field_simps scaleR_conv_of_real)
        also have "\<dots> \<in> \<real>"
          using real by (auto intro: Reals_divide Reals_diff)
        finally show False
          using noncollinear by contradiction
      next
        case True
        hence "z = a *\<^sub>R \<omega>1'"
          using ab by simp
        from this and z have "a \<noteq> 1"
          by auto
        hence "a < 1"
          using ab by simp
        have "norm z = a * norm \<omega>1'"
          using \<open>z = a *\<^sub>R \<omega>1'\<close> \<open>a \<ge> 0\<close> by simp
        also have "\<dots> < 1 * norm \<omega>1'"
          using \<open>a < 1\<close> by (intro mult_strict_right_mono) auto
        finally have "norm z < norm \<omega>1'"
          by simp
        moreover have "norm z \<ge> norm \<omega>1'"
          by (intro \<omega>1') (use z \<open>z \<in> \<Lambda>\<^sup>*\<close> in auto)
        ultimately show False
          by simp
      qed
    qed
    hence "z \<in> X"
      using \<open>z \<in> \<Lambda>\<^sup>*\<close> by (auto simp: X_def)
    hence "norm z \<ge> norm \<omega>2'"
      by (intro \<omega>2')

    moreover have "norm z \<le> norm \<omega>2'"
    proof -
      have "norm z \<le> (a + b) * norm \<omega>2'"
        by (rule norm_z_le')
      also have "\<dots> \<le> 1 * norm \<omega>2'"
        using ab by (intro mult_right_mono) auto
      finally show "norm z \<le> norm \<omega>2'"
        by simp
    qed

    ultimately have norm_z: "norm z = norm \<omega>2'"
      by linarith

    have "\<not>(a + b < 1)"
    proof
      assume *: "a + b < 1"
      have "norm z \<le> (a + b) * norm \<omega>2'"
        by (rule norm_z_le')
      also have "\<dots> < 1 * norm \<omega>2'"
        by (intro mult_strict_right_mono *) auto
      finally show False
        using norm_z by simp
    qed
    with ab have b_eq: "b = 1 - a"
      by linarith

    have "norm z < norm \<omega>2'"
    proof (rule norm_open_segment_less)
      have "a \<noteq> 0" "a \<noteq> 1"
        using z ab by (auto simp: b_eq)
      hence "\<exists>u. u > 0 \<and> u < 1 \<and> z = (1 - u) *\<^sub>R \<omega>1' + u *\<^sub>R \<omega>2'"
        using ab by (intro exI[of _ b]) (auto simp: b_eq)
      thus "z \<in> open_segment \<omega>1' \<omega>2'"
        using z ab noncollinear unfolding in_segment by auto
    next
      show "norm \<omega>1' \<le> norm \<omega>2'"
        by fact
    qed
    with norm_z show False
      by simp
  qed
  hence "convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda> \<subseteq> {0, \<omega>1', \<omega>2'}"
    by blast
  moreover have "{0, \<omega>1', \<omega>2'} \<subseteq> convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda>"
    using \<omega>1' \<omega>2' by (auto intro: hull_inc simp: X_def)
  ultimately have "convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda> = {0, \<omega>1', \<omega>2'}"
    by blast
  
  hence "equiv_fundpair (\<omega>1, \<omega>2) (\<omega>1', \<omega>2')"
    using fundpair' \<omega>1' \<omega>2' by (subst equiv_fundpair_iff_triangle) (auto simp: X_def)
  then obtain a b c d :: int where
    det: "\<bar>a * d - b * c\<bar> = 1" and
    abcd: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
    using fundpair fundpair' by (subst (asm) equiv_fundpair_iff) auto

  have *: "norm (\<omega>1' + of_int n * \<omega>2') \<ge> norm \<omega>2'" if n: "n \<noteq> 0" for n
  proof (rule \<omega>2')
    define z where "z = \<omega>1' + of_int n * \<omega>2'"
    have "z \<in> \<Lambda>"
      unfolding z_def using \<omega>1'(1) \<omega>2'(1) by (auto intro!: lattice_intros simp: X_def)
    moreover have "z / \<omega>1' \<notin> \<real>"
    proof
      assume "z / \<omega>1' \<in> \<real>"
      hence "(z / \<omega>1' - 1) / of_int n \<in> \<real>"
        by auto
      also have "(z / \<omega>1' - 1) / of_int n = \<omega>2' / \<omega>1'"
        using n by (simp add: field_simps z_def)
      finally show False
        using noncollinear by contradiction
    qed
    moreover from this have "z \<noteq> 0"
      by auto
    ultimately show "z \<in> X"
      by (auto simp: X_def lattice0_def)
  qed
  have norms: "norm (\<omega>1' + \<omega>2') \<ge> norm \<omega>2'" "norm (\<omega>1' - \<omega>2') \<ge> norm \<omega>2'"
    using *[of 1] and *[of "-1"] by simp_all

  show ?thesis
    using det norms abcd noncollinear \<open>norm \<omega>1' \<le> norm \<omega>2'\<close>
    by (intro that[of a d b c \<omega>2' \<omega>1']) (simp_all add: complex_is_Real_iff)
qed

lemma (in complex_lattice) std_fund_region_fundamental_lemma2:
  obtains \<omega>1' \<omega>2' :: complex and a b c d :: int
  where "a * d - b * c = 1"
        "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
        "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
        "Im (\<omega>2' / \<omega>1') \<noteq> 0"
        "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
proof -
  obtain \<omega>1' \<omega>2' a b c d
    where abcd: "\<bar>a * d - b * c\<bar> = 1"
      and eq: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      and nz: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
      and norms: "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
    using std_fund_region_fundamental_lemma1 .

  show ?thesis
  proof (cases "a * d - b * c = 1")
    case True
    thus ?thesis
      by (intro that[of a d b c \<omega>2' \<omega>1'] eq nz norms)
  next
    case False
    show ?thesis
    proof (intro that[of a "-d" b "-c" \<omega>2' "-\<omega>1'"])
      from False have "a * d - b * c = -1"
        using abcd by linarith
      thus "a * (-d) - b * (-c) = 1"
        by simp
    next
      show "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
           "-\<omega>1' = of_int (- c) * \<omega>2 + of_int (- d) * \<omega>1"
        using eq by (simp_all add: algebra_simps)
    qed (use norms nz in \<open>auto simp: norm_minus_commute add.commute\<close>)
  qed
qed

text \<open>Theorem 2.2\<close>
lemma std_fund_region_fundamental_aux1:
  assumes "Im \<tau>' > 0"
  obtains \<tau> where "Im \<tau> > 0" "\<tau> \<sim>\<^sub>\<Gamma> \<tau>'" "norm \<tau> \<ge> 1" "norm (\<tau> + 1) \<ge> norm \<tau>" "norm (\<tau> - 1) \<ge> norm \<tau>"
proof -
  interpret std_complex_lattice \<tau>'
    using assms by unfold_locales (auto simp: complex_is_Real_iff)
  obtain \<omega>1 \<omega>2 a b c d
    where abcd: "a * d - b * c = 1"
      and eq: "\<omega>2 = of_int a * \<tau>' + of_int b * 1" "\<omega>1 = of_int c * \<tau>' + of_int d * 1"
      and nz: "Im (\<omega>2 / \<omega>1) \<noteq> 0"
      and norms: "norm \<omega>1 \<le> norm \<omega>2" "norm \<omega>2 \<le> norm (\<omega>1 + \<omega>2)" "norm \<omega>2 \<le> norm (\<omega>1 - \<omega>2)"
    using std_fund_region_fundamental_lemma2 .
  from nz have [simp]: "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0"
    by auto

  interpret unimodular_moebius_transform a b c d
    by unfold_locales fact

  define \<tau> where "\<tau> = \<omega>2 / \<omega>1"
  have \<tau>_eq: "\<tau> = \<phi> \<tau>'"
    by (simp add: moebius_def \<tau>_def eq add_ac \<phi>_def)

  show ?thesis
  proof (rule that[of \<tau>])
    show "Im \<tau> > 0"
      using assms \<tau>_eq by (simp add: Im_transform_pos)
  next
    show "norm \<tau> \<ge> 1" "norm (\<tau> + 1) \<ge> norm \<tau>" "norm (\<tau> - 1) \<ge> norm \<tau>"
      using norms by (simp_all add: \<tau>_def norm_divide field_simps norm_minus_commute)
  next
    have "\<tau> = apply_modgrp as_modgrp \<tau>'"
      using \<tau>_eq by (simp add: \<phi>_as_modgrp)
    thus "\<tau> \<sim>\<^sub>\<Gamma> \<tau>'" using \<open>Im \<tau>' > 0\<close>
      by auto
  qed
qed

lemma std_fund_region_fundamental_aux2:
  assumes "norm (z + 1) \<ge> norm z" "norm (z - 1) \<ge> norm z"
  shows   "Re z \<in> {-1/2..1/2}"
proof -
  have "0 \<le> norm (z + 1) ^ 2 - norm z ^ 2"
    using assms by simp
  also have "\<dots> = (Re z + 1)\<^sup>2 - (Re z)\<^sup>2"
    unfolding norm_complex_def by simp
  also have "\<dots> = 1 + 2 * Re z"
    by (simp add: algebra_simps power2_eq_square)
  finally have "Re z \<ge> -1/2"
    by simp

  have "0 \<le> norm (z - 1) ^ 2 - norm z ^ 2"
    using assms by simp
  also have "\<dots> = (Re z - 1)\<^sup>2 - (Re z)\<^sup>2"
    unfolding norm_complex_def by simp
  also have "\<dots> = 1 - 2 * Re z"
    by (simp add: algebra_simps power2_eq_square)
  finally have "Re z \<le> 1/2"
    by simp

  with \<open>Re z \<ge> -1/2\<close> show ?thesis
    by simp
qed

lemma std_fund_region_fundamental_aux3:
  fixes x y :: complex
  assumes xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>"
  assumes f: "y = apply_modgrp f x"
  defines "c \<equiv> modgrp_c f"
  defines "d \<equiv> modgrp_d f"
  assumes c: "c \<noteq> 0"
  shows   "Im y < Im x"
proof -
  have ineq1: "norm (c * x + d) ^ 2 > c ^ 2 - \<bar>c * d\<bar> + d ^ 2"
  proof -
    have "of_int \<bar>c\<bar> * 1 < of_int \<bar>c\<bar> * norm x"
      using xy c by (intro mult_strict_left_mono) (auto simp: std_fund_region_def)
    hence "of_int c ^ 2 < (of_int c * norm x) ^ 2"
      by (intro power2_strict_mono) auto
    also have "\<dots> - \<bar>c * d\<bar> * 1 + d ^ 2 \<le>
          (of_int c * norm x) ^ 2 - \<bar>c * d\<bar> * (2 * \<bar>Re x\<bar>) + d ^ 2"
      using xy unfolding of_int_add of_int_mult of_int_power of_int_diff
      by (intro add_mono diff_mono mult_left_mono) (auto simp: std_fund_region_def)
    also have "\<dots> = c ^ 2 * norm x ^ 2 - \<bar>2 * c * d * Re x\<bar> + d ^ 2"
      by (simp add: power_mult_distrib abs_mult)
    also have "\<dots> \<le> c ^ 2 * norm x ^ 2 + 2 * c * d * Re x + d ^ 2"
      by linarith
    also have "\<dots> = norm (c * x + d) ^ 2"
      unfolding cmod_power2 by (simp add: algebra_simps power2_eq_square)
    finally show "norm (c * x + d) ^ 2 > c ^ 2 - \<bar>c * d\<bar> + d ^ 2" 
      by simp
  qed

  have "Im y = Im x / norm (c * x + d) ^ 2"
    using f by (simp add: modgrp.Im_transform c_def d_def)

  also have "norm (c * x + d) ^ 2 > 1"
  proof (cases "d = 0")
    case [simp]: True
    have "0 < c ^ 2"
      using c by simp
    hence "1 \<le> real_of_int (c ^ 2) * 1"
      by linarith
    also have "\<dots> < of_int (c ^ 2) * norm x ^ 2"
      using xy c by (intro mult_strict_left_mono) (auto simp: std_fund_region_def)
    also have "\<dots> = norm (c * x + d) ^ 2"
      by (simp add: norm_mult power_mult_distrib)
    finally show ?thesis .
  next
    case False
    have "0 < \<bar>c * d\<bar>"
      using c False by auto
    hence "1 \<le> \<bar>c * d\<bar>"
      by linarith
    also have "\<dots> \<le> \<bar>c * d\<bar> + (\<bar>c\<bar> - \<bar>d\<bar>) ^ 2"
      by simp
    also have "\<dots> = c ^ 2 - \<bar>c * d\<bar> + d ^ 2"
      by (simp add: algebra_simps power2_eq_square abs_mult)
    finally have "1 \<le> real_of_int (c ^ 2 - \<bar>c * d\<bar> + d ^ 2)"
      by linarith
    also have "\<dots> < norm (c * x + d) ^ 2"
      using ineq1 False by simp
    finally show ?thesis .
  qed

  hence "Im x / norm (c * x + d) ^ 2 < Im x / 1"
    using xy by (intro divide_strict_left_mono) (auto simp: std_fund_region_def)
  finally show ?thesis
    by simp
qed

lemma std_fund_region_fundamental_aux4:
  fixes x y :: complex
  assumes xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>"
  assumes f: "y = apply_modgrp f x"
  shows   "f = 1"
proof -
  define a where "a = modgrp_a f"
  define b where "b = modgrp_b f"
  define c where "c = modgrp_c f"
  define d where "d = modgrp_d f"

  have c: "c = 0"
  proof (rule ccontr)
    assume c: "c \<noteq> 0"
    have "Im y < Im x" using xy f c
      by (intro std_fund_region_fundamental_aux3[where f = f]) (auto simp: c_def)
    moreover have "Im y > Im x"
    proof (rule std_fund_region_fundamental_aux3[where f = "inverse f"])
      have "Im x > 0"
        using xy by (auto simp: std_fund_region_def)
      hence "x \<noteq> pole_modgrp f"
        using pole_modgrp_in_Reals[of f, where ?'a = complex]
        by (auto simp: complex_is_Real_iff)
      with f have "apply_modgrp (inverse f) y = x"
        by (intro apply_modgrp_inverse_eqI) auto
      thus "x = apply_modgrp (inverse f) y" ..
    next
      have "is_singular_modgrp f"
        using c by (simp add: is_singular_modgrp_altdef c_def)
      hence "is_singular_modgrp (inverse f)"
        by simp
      thus "modgrp_c (inverse f) \<noteq> 0"
        unfolding is_singular_modgrp_altdef by simp      
    qed (use xy c in \<open>auto simp: c_def\<close>)
    ultimately show False
      by simp
  qed

  define n where "n = sgn a * b"
  from c have "\<not>is_singular_modgrp f"
    by (auto simp: is_singular_modgrp_altdef c_def)
  hence f_eq: "f = shift_modgrp n"
    using not_is_singular_modgrpD[of f] by (simp add: n_def a_def b_def)
  from xy f have "n = 0"
    by (auto simp: std_fund_region_def f_eq)
  thus "f = 1"
    by (simp add: f_eq)
qed

text \<open>Theorem 2.3\<close>
interpretation std_fund_region: fundamental_region UNIV std_fund_region
proof
  show "std_fund_region \<subseteq> {z. Im z > 0}"
    using Im_std_fund_region by blast
next
  fix x y :: complex
  assume xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>" "x \<sim>\<^sub>\<Gamma> y"
  then obtain f where f: "y = apply_modgrp f x"
    by (auto simp: modular_group.rel_def)
  with xy have "f = 1"
    using std_fund_region_fundamental_aux4 by blast
  with f xy show "x = y"
    by simp
next
  fix x :: complex
  assume x: "Im x > 0"
  obtain y where y: "Im y > 0" "y \<sim>\<^sub>\<Gamma> x"
    "norm y \<ge> 1" "norm (y + 1) \<ge> norm y" "norm (y - 1) \<ge> norm y"
    using std_fund_region_fundamental_aux1[OF x] by blast
  from y have "Re y \<in> {-1/2..1/2}"
    by (intro std_fund_region_fundamental_aux2)
  with y show "\<exists>y\<in>closure std_fund_region. x \<sim>\<^sub>\<Gamma> y"
    using x unfolding closure_std_fund_region by (auto simp: modular_group.rel_commutes)
qed auto

theorem std_fund_region_no_fixed_point:
  assumes "z \<in> \<R>\<^sub>\<Gamma>"
  assumes "apply_modgrp f z = z"
  shows   "f = 1"
  using std_fund_region_fundamental_aux4[of z "apply_modgrp f z" f] assms by auto

lemma std_fund_region_no_fixed_point':
  assumes "z \<in> \<R>\<^sub>\<Gamma>"
  assumes "apply_modgrp f z = apply_modgrp g z"
  shows   "f = g"
proof -
  have z: "Im z > 0"
    using assms by (auto simp: in_std_fund_region_iff)
  have "apply_modgrp (inverse f) (apply_modgrp g z) = apply_modgrp (inverse f) (apply_modgrp f z)"
    by (simp only: assms(2))
  also have "\<dots> = z"
    using z by (intro apply_modgrp_inverse_eqI) auto
  also have "apply_modgrp (inverse f) (apply_modgrp g z) = apply_modgrp (inverse f * g) z"
    by (rule apply_modgrp_mult [symmetric]) (use z in auto)
  finally have "inverse f * g = 1"
    using assms by (intro std_fund_region_no_fixed_point) auto
  thus ?thesis
    by (metis modgrp.left_cancel modgrp.left_inverse)
qed

lemma equiv_point_in_std_fund_region':
  assumes "Im z > 0"
  obtains z' where "z \<sim>\<^sub>\<Gamma> z'" "z' \<in> \<R>\<^sub>\<Gamma>'"
proof -
  obtain z1 where z1: "z \<sim>\<^sub>\<Gamma> z1" "z1 \<in> closure \<R>\<^sub>\<Gamma>"
    using std_fund_region.equiv_in_closure assms by blast
  show ?thesis
  proof (cases "z1 \<in> \<R>\<^sub>\<Gamma>'")
    case True
    thus ?thesis
      using z1 by (intro that[of z1]) auto
  next
    case False
    hence "z1 \<in> closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>'"
      using z1 by blast
    thus ?thesis
      unfolding closure_std_fund_region_minus_std_fund_region'
    proof
      assume z1': "z1 \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> Re z \<in> {0<..1 / 2}}"
      define z2 where "z2 = apply_modgrp S_modgrp z1"
      show ?thesis
      proof (rule that [of z2])
        show "z \<sim>\<^sub>\<Gamma> z2"
          unfolding z2_def using z1
          by (subst modular_group.rel_apply_modgrp_right_iff) auto
        have "-cnj z1 \<in> \<R>\<^sub>\<Gamma>'"
          using z1' by (auto simp: z2_def in_std_fund_region'_iff)
        also have "-cnj z1 = z2"
          using z1' by (auto simp: z2_def divide_conv_cnj)
        finally show "z2 \<in> \<R>\<^sub>\<Gamma>'" .
      qed
    next
      assume z1': "z1 \<in> {z. Re z = 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
      define z2 where "z2 = apply_modgrp (shift_modgrp (-1)) z1"
      show ?thesis
      proof (rule that [of z2])
        show "z \<sim>\<^sub>\<Gamma> z2"
          unfolding z2_def using z1
          by (subst modular_group.rel_apply_modgrp_right_iff) auto
        have "-cnj z1 \<in> \<R>\<^sub>\<Gamma>'"
          using z1' z1 by (auto simp: z2_def in_std_fund_region'_iff in_closure_std_fund_region_iff)
        also have "-cnj z1 = z2"
          using z1' by (auto simp: z2_def complex_eq_iff)
        finally show "z2 \<in> \<R>\<^sub>\<Gamma>'" .
      qed
    qed
  qed
qed


text \<open>
  The image of the fundamental region under a unimodular transformation is again a
  fundamental region.
\<close>
locale std_fund_region_image =
  fixes f :: modgrp and R :: "complex set"
  defines "R \<equiv> apply_modgrp f ` \<R>\<^sub>\<Gamma>"
begin

lemma R_altdef: "R = {z. Im z > 0} \<inter> apply_modgrp (inverse f) -` \<R>\<^sub>\<Gamma>"
  unfolding R_def
proof safe
  fix z assume z: "z \<in> \<R>\<^sub>\<Gamma>"
  thus "Im (apply_modgrp f z) > 0"
    by (auto simp: Im_std_fund_region)
  have "apply_modgrp (inverse f) (apply_modgrp f z) \<in> \<R>\<^sub>\<Gamma>"
    by (subst apply_modgrp_mult [symmetric]) (use z in auto)
  thus "apply_modgrp f z \<in> apply_modgrp (inverse f) -` \<R>\<^sub>\<Gamma>"
    by (auto simp flip: apply_modgrp_mult)
next
  fix z assume z: "apply_modgrp (inverse f) z \<in> \<R>\<^sub>\<Gamma>" "Im z > 0"
  have "z = apply_modgrp f (apply_modgrp (inverse f) z)"
    by (subst apply_modgrp_mult [symmetric]) (use z(2) in auto)
  with z show "z \<in> apply_modgrp f ` \<R>\<^sub>\<Gamma>"
    by blast
qed

lemma R_altdef': "R = apply_modgrp (inverse f) -` \<R>\<^sub>\<Gamma>"
  unfolding R_altdef by (auto simp: in_std_fund_region_iff)

sublocale fundamental_region UNIV R
proof
  show "open R"
    unfolding R_altdef 
    by (intro continuous_open_preimage continuous_intros) (auto simp: open_halfspace_Im_gt )
  show "R \<subseteq> {z. 0 < Im z}"
    unfolding R_altdef by auto
  show "x = y" if "x \<in> R" "y \<in> R" "x \<sim>\<^sub>\<Gamma> y" for x y
    using that unfolding R_def by (auto dest: std_fund_region.unique)
  show "\<exists>y\<in>closure R. x \<sim>\<^sub>\<Gamma> y" if "Im x > 0" for x
  proof -
    define x' where "x' = apply_modgrp (inverse f) x"
    have x': "Im x' > 0"
      using that by (simp add: x'_def)
    then obtain y where y: "y \<in> closure \<R>\<^sub>\<Gamma>" "x' \<sim>\<^sub>\<Gamma> y"
      using std_fund_region.equiv_in_closure[of x'] by blast
    define y' where "y' = apply_modgrp f y"
    have "y islimpt \<R>\<^sub>\<Gamma>"
      using y by (meson islimpt_closure_open limpt_of_closure open_std_fund_region)
    then obtain h :: "nat \<Rightarrow> complex" where h: "\<And>n. h n \<in> \<R>\<^sub>\<Gamma> - {y}" "h \<longlonglongrightarrow> y"
      unfolding islimpt_sequential by blast
    have "(apply_modgrp f \<circ> h) n \<in> R - {y'}" for n
    proof -
      have Ims: "Im y > 0" "Im (h n) > 0"
        using y h(1)[of n] by (auto simp: in_std_fund_region_iff)
      have "apply_modgrp f (h n) \<in> R" "h n \<noteq> y"
        using h(1)[of n] by (auto simp: R_def)
      moreover have "apply_modgrp f (h n) \<noteq> y'"
        unfolding y'_def using y \<open>h n \<noteq> y\<close> Ims by (subst apply_modgrp_eq_iff) auto
      ultimately show ?thesis
        by auto
    qed
    moreover have "(apply_modgrp f \<circ> h) \<longlonglongrightarrow> y'"
      unfolding y'_def using y by (auto intro!: tendsto_compose_at[OF h(2)] tendsto_eq_intros)+
    ultimately have "y' islimpt R"
      unfolding islimpt_sequential by blast
    hence "y' \<in> closure R"
      by (simp add: closure_def)
 
    moreover have "x \<sim>\<^sub>\<Gamma> y'"
      using x' that y unfolding y'_def x'_def
      by (auto simp: modular_group.rel_commutes)
    ultimately show ?thesis
      by blast
  qed
qed

end



subsection \<open>The corner point of the standard fundamental region\<close>

text \<open>
  The point $\rho = \exp(2/3\pi) = -\frac{1}{2} + \frac{\sqrt{3}}{2} i$ is the left corner
  of the standard fundamental region, and its reflection on the imaginary axis (which is the
  same as its image under $z \mapsto -1/z$) forms the right corner.
\<close>
definition modfun_rho ("\<^bold>\<rho>") where
  "\<^bold>\<rho> = cis (2 / 3 * pi)"

lemma modfun_rho_altdef: "\<^bold>\<rho> = -1 / 2 + sqrt 3 / 2 * \<i>"
  by (simp add: complex_eq_iff modfun_rho_def Re_exp Im_exp sin_120 cos_120)

lemma Re_modfun_rho [simp]: "Re \<^bold>\<rho> = -1 / 2"
  and Im_modfun_rho [simp]: "Im \<^bold>\<rho> = sqrt 3 / 2"
  by (simp_all add: modfun_rho_altdef)

lemma norm_modfun_rho [simp]: "norm \<^bold>\<rho> = 1"
  by (simp add: modfun_rho_def)

lemma modfun_rho_plus_1_eq: "\<^bold>\<rho> + 1 = exp (pi / 3 * \<i>)"
  by (simp add: modfun_rho_altdef complex_eq_iff Re_exp Im_exp sin_60 cos_60)

lemma norm_modfun_rho_plus_1 [simp]: "norm (\<^bold>\<rho> + 1) = 1"
  by (simp add: modfun_rho_plus_1_eq)

lemma cnj_modfun_rho: "cnj \<^bold>\<rho> = -\<^bold>\<rho> - 1"
  and cnj_modfun_rho_plus1: "cnj (\<^bold>\<rho> + 1) = -\<^bold>\<rho>"
  by (auto simp: complex_eq_iff)

lemma modfun_rho_cube: "\<^bold>\<rho> ^ 3 = 1"
  by (simp add: modfun_rho_def Complex.DeMoivre)

lemma modfun_rho_power_mod3_reduce: "\<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (n mod 3)"
proof -
  have "\<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (3 * (n div 3) + (n mod 3))"
    by simp
  also have "\<dots> = (\<^bold>\<rho> ^ 3) ^ (n div 3) * \<^bold>\<rho> ^ (n mod 3)"
    by (subst power_add) (simp add: power_mult)
  also have "\<dots> = \<^bold>\<rho> ^ (n mod 3)"
    by (simp add: modfun_rho_cube)
  finally show ?thesis .
qed

lemma modfun_rho_power_mod3_reduce': "n \<ge> 3 \<Longrightarrow> \<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (n mod 3)"
  by (rule modfun_rho_power_mod3_reduce)

lemmas [simp] = modfun_rho_power_mod3_reduce' [of "numeral num" for num]

lemma modfun_rho_square: "\<^bold>\<rho> ^ 2 = -\<^bold>\<rho> - 1"
  by (simp add: modfun_rho_altdef power2_eq_square field_simps flip: of_real_mult)

lemma modfun_rho_not_real [simp]: "\<^bold>\<rho> \<notin> \<real>"
  by (simp add: modfun_rho_altdef complex_is_Real_iff)

lemma modfun_rho_nonzero [simp]: "\<^bold>\<rho> \<noteq> 0"
  by (simp add: modfun_rho_def)

lemma modfun_rho_not_one [simp]: "\<^bold>\<rho> \<noteq> 1"
  by (simp add: complex_eq_iff modfun_rho_altdef)

lemma i_neq_modfun_rho [simp]: "\<i> \<noteq> \<^bold>\<rho>"
  and i_neq_modfun_rho_plus1 [simp]: "\<i> \<noteq> \<^bold>\<rho> + 1"
  and modfun_rho_neg_i [simp]: "\<^bold>\<rho> \<noteq> \<i>"
  and modfun_rho_plus1_neg_i [simp]: "\<^bold>\<rho> + 1 \<noteq> \<i>"
  by (auto simp: complex_eq_iff)

lemma i_in_closure_std_fund_region [intro, simp]: "\<i> \<in> closure \<R>\<^sub>\<Gamma>"
  and i_in_std_fund_region' [intro, simp]: "\<i> \<in> \<R>\<^sub>\<Gamma>'"
  and modfun_rho_in_closure_std_fund_region [intro, simp]: "\<^bold>\<rho> \<in> closure \<R>\<^sub>\<Gamma>"
  and modfun_rho_in_std_fund_region' [intro, simp]: "\<^bold>\<rho> \<in> \<R>\<^sub>\<Gamma>'"
  and modfun_rho_plus_1_notin_closure_std_fund_region [intro, simp]: "\<^bold>\<rho> + 1 \<in> closure \<R>\<^sub>\<Gamma>"
  and modfun_rho_plus_1_notin_std_fund_region' [intro, simp]: "\<^bold>\<rho> + 1 \<notin> \<R>\<^sub>\<Gamma>'"
  by (simp_all add: closure_std_fund_region std_fund_region'_def in_std_fund_region_iff)

lemma modfun_rho_power_eq_1_iff: "\<^bold>\<rho> ^ n = 1 \<longleftrightarrow> 3 dvd n"
proof -
  have "\<^bold>\<rho> ^ n = 1 \<longleftrightarrow> (\<exists>k. real n = 3 * real_of_int k)"
    by (simp add: modfun_rho_def Complex.DeMoivre cis_eq_1_iff)
  also have "(\<lambda>k. real n = 3 * real_of_int k) = (\<lambda>k. int n = 3 * k)"
    by (rule ext) linarith
  also have "(\<exists>k. int n = 3 * k) \<longleftrightarrow> 3 dvd n"
    by presburger
  finally show ?thesis .
qed


subsection \<open>Fundamental regions for congruence subgroups\<close>

context hecke_prime_subgroup
begin

definition std_fund_region_cong ("\<R>") where
  "\<R> = \<R>\<^sub>\<Gamma> \<union> (\<Union>k\<in>{0..<p}. (\<lambda>z. -1 / (z + of_int k)) ` \<R>\<^sub>\<Gamma>)"

lemma std_fund_region_cong_altdef: 
  "\<R> = \<R>\<^sub>\<Gamma> \<union> (\<Union>k\<in>{0..<p}. apply_modgrp (S_shift_modgrp k) ` \<R>\<^sub>\<Gamma>)"
proof -
  have "apply_modgrp (S_shift_modgrp k) ` \<R>\<^sub>\<Gamma> = (\<lambda>z. -1 / (z + of_int k)) ` \<R>\<^sub>\<Gamma>" for k
    unfolding S_shift_modgrp_def
    by (intro image_cong refl, subst apply_modgrp_mult) auto
  thus ?thesis
    by (simp add: std_fund_region_cong_def)
qed

lemma closure_UN_finite: "finite A \<Longrightarrow> closure (\<Union>A) = (\<Union>X\<in>A. closure X)"
  by (induction A rule: finite_induct) auto

(* Theorem 4.2 *)
sublocale std_region: fundamental_region \<Gamma>' \<R>
proof
  show "open \<R>"
    unfolding std_fund_region_cong_altdef
    by (intro open_Un open_UN ballI open_std_fund_region apply_modgrp_open_map) auto
next
  show "\<R> \<subseteq> {z. Im z > 0}"
    by (auto simp: std_fund_region_cong_altdef in_std_fund_region_iff)
next
  fix x assume "Im x > 0"
  then obtain y where y: "y \<in> closure \<R>\<^sub>\<Gamma>" "x \<sim>\<^sub>\<Gamma> y"
    using std_fund_region.equiv_in_closure by blast
  then obtain f where f: "y = apply_modgrp f x" "Im y > 0"
    by (auto simp: modular_group.rel_def)
  obtain g h where gh: "g \<in> \<Gamma>'" "h = 1 \<or> (\<exists>k\<in>{0..<p}. h = S_shift_modgrp k)" "inverse f = g * h"
    using modgrp_decompose'[of "inverse f"] .
  have inverse_g_eq: "inverse g = h * f"
    using gh(3) by (metis modgrp.assoc modgrp.inverse_unique modgrp.left_inverse)

  show "\<exists>y\<in>closure \<R>. rel x y"
    using gh(2)
  proof safe
    assume "h = 1"
    thus ?thesis using y f gh
      by (auto simp: std_fund_region_cong_altdef intro!: bexI[of _ y])
  next
    fix k assume k: "k \<in> {0..<p}" "h = S_shift_modgrp k"
    have "apply_modgrp h y \<in> apply_modgrp h ` closure \<R>\<^sub>\<Gamma>"
      using y by blast
    also have "\<dots> \<subseteq> closure (apply_modgrp h ` \<R>\<^sub>\<Gamma>)"
      by (intro continuous_image_closure_subset[of "{z. Im z > 0}"])
         (auto intro!: continuous_intros closure_std_fund_region_Im_pos)
    also have "apply_modgrp h y = apply_modgrp (inverse g) x"
      unfolding inverse_g_eq using \<open>Im x > 0\<close> f by (subst apply_modgrp_mult) auto
    finally have "apply_modgrp (inverse g) x \<in> closure (apply_modgrp h ` \<R>\<^sub>\<Gamma>)" .
    moreover have "rel x (apply_modgrp (inverse g) x)"
      using \<open>Im x > 0\<close> gh by auto
    ultimately show ?thesis
      unfolding std_fund_region_cong_altdef using k by (auto simp: closure_UN_finite)
  qed
next
  fix x y assume xy: "x \<in> \<R>" "y \<in> \<R>" "rel x y"
  define ST where "ST = (\<lambda>k. apply_modgrp (S_shift_modgrp k) :: complex \<Rightarrow> complex)"

  have 1: False
    if xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>" "rel x (ST k y)" and k: "k \<in> {0..<p}" for x y k
  proof -
    have "x \<sim>\<^sub>\<Gamma> ST k y"
      using xy(3) by (rule rel_imp_rel)
    hence "x \<sim>\<^sub>\<Gamma> y"
      by (auto simp: ST_def)
    hence [simp]: "x = y"
      using xy(1,2) std_fund_region.unique by blast
    with xy(3) have "rel (ST k x) x"
      by (simp add: rel_commutes)
    then obtain f where f: "f \<in> \<Gamma>'" "apply_modgrp f (ST k x) = x" "Im x > 0"
      unfolding rel_def by blast
    hence "apply_modgrp (f * S_shift_modgrp k) x = x"
      by (subst apply_modgrp_mult) (auto simp: ST_def)
    hence "f * S_shift_modgrp k = 1"
      using xy by (intro std_fund_region_no_fixed_point) auto
    hence "f = inverse (S_shift_modgrp k)"
      by (metis modgrp.inverse_inverse modgrp.inverse_unique)
    moreover have "modgrp_c (inverse (S_shift_modgrp k)) = 1"
      by (simp add: S_shift_modgrp_def S_modgrp_code shift_modgrp_code inverse_modgrp_code
                    times_modgrp_code modgrp_c_code)
    moreover have "\<not>p dvd 1"
      using p_prime using not_prime_unit by blast
    ultimately show False
      using \<open>f \<in> \<Gamma>'\<close> unfolding subgrp_def modgrps_cong_altdef by auto
  qed 

  have "x \<in> \<R>\<^sub>\<Gamma> \<union> (\<Union>k\<in>{0..<p}. ST k ` \<R>\<^sub>\<Gamma>)" "y \<in> \<R>\<^sub>\<Gamma> \<union> (\<Union>k\<in>{0..<p}. ST k ` \<R>\<^sub>\<Gamma>)"
    using xy unfolding ST_def std_fund_region_cong_altdef by blast+
  thus "x = y"
  proof safe
    assume "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>"
    thus "x = y" 
      using \<open>rel x y\<close> rel_imp_rel std_fund_region.unique by blast
  next
    fix k y'
    assume "x \<in> \<R>\<^sub>\<Gamma>" "k \<in> {0..<p}" "y' \<in> \<R>\<^sub>\<Gamma>" "y = ST k y'"
    thus "x = ST k y'"
      using 1[of x y' k] \<open>rel x y\<close> by auto
  next
    fix k x'
    assume "x' \<in> \<R>\<^sub>\<Gamma>" "k \<in> {0..<p}" "y \<in> \<R>\<^sub>\<Gamma>" "x = ST k x'"
    thus "ST k x' = y"
      using 1[of y x' k] \<open>rel x y\<close> by (auto simp: rel_commutes)
  next
    fix x' y' :: complex and k1 k2 :: int
    assume xy': "x' \<in> \<R>\<^sub>\<Gamma>" "y' \<in> \<R>\<^sub>\<Gamma>" "x = ST k1 x'" "y = ST k2 y'"
    assume k12: "k1 \<in> {0..<p}" "k2 \<in> {0..<p}"
    have x': "Im x' > 0"
      using xy' by (auto simp: in_std_fund_region_iff)
    have "ST k1 x' \<sim>\<^sub>\<Gamma> ST k2 y'"
      using xy xy' by (intro rel_imp_rel) auto
    hence "x' \<sim>\<^sub>\<Gamma> y'"
      by (auto simp: ST_def)
    hence [simp]: "x' = y'"
      using xy' by (intro std_fund_region.unique)
    have "rel (ST k1 x') (ST k2 x')"
      using xy xy' by simp
    then obtain f where f: "f \<in> \<Gamma>'" "apply_modgrp f (ST k1 x') = ST k2 y'"
      unfolding rel_def by auto
    note \<open>apply_modgrp f (ST k1 x') = ST k2 y'\<close>
    also have "apply_modgrp f (ST k1 x') = apply_modgrp (f * S_shift_modgrp k1) x'"
      unfolding ST_def using x' by (subst apply_modgrp_mult) auto
    finally have "f * S_shift_modgrp k1 = S_shift_modgrp k2"
      unfolding ST_def using xy' by (intro std_fund_region_no_fixed_point'[of x']) auto
    hence "f = S_shift_modgrp k2 * inverse (S_shift_modgrp k1)"
      by (metis modgrp.right_inverse modgrp.right_neutral mult.assoc)
    also have "\<dots> = S_modgrp * shift_modgrp (k2 - k1) * S_modgrp"
      using shift_modgrp_add[of k2 "-k1"]
      by (simp add: S_shift_modgrp_def modgrp.inverse_distrib_swap modgrp.assoc
               flip: shift_modgrp_minus)
    finally have "f = S_modgrp * shift_modgrp (k2 - k1) * S_modgrp" .
    moreover have "modgrp_c (S_modgrp * shift_modgrp (k2 - k1) * S_modgrp) = \<bar>k2 - k1\<bar>"
      by (simp add: S_modgrp_code shift_modgrp_code times_modgrp_code modgrp_c_code)
    moreover have "p dvd modgrp_c f"
      using f by (auto simp: subgrp_def modgrps_cong_altdef)
    ultimately have "p dvd \<bar>k2 - k1\<bar>"
      by simp
    moreover from k12 have "\<bar>k2 - k1\<bar> < p"
      by auto
    ultimately have "k1 = k2"
      using zdvd_not_zless[of "\<bar>k2 - k1\<bar>" p] by (cases "k1 = k2") auto
    thus "ST k1 x' = ST k2 y'"
      by simp
  qed
qed

end



bundle modfun_region_notation
begin
notation std_fund_region ("\<R>\<^sub>\<Gamma>")
notation modfun_rho ("\<^bold>\<rho>")
end

unbundle no modfun_region_notation

end