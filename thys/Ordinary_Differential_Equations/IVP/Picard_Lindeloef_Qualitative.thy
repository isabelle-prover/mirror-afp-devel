theory Picard_Lindeloef_Qualitative
imports Initial_Value_Problem
begin

subsection \<open>Picard-Lindelöf On Open Domains \label{sec:qpl}\<close>

subsubsection \<open>Local Solution with local Lipschitz \label{sec:qpl-lipschitz}\<close>

lemma cube_in_cball:
  fixes x y :: "'a::euclidean_space"
  assumes "r > 0"
  assumes "\<And>i. i\<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> r / sqrt(DIM('a))"
  shows "y \<in> cball x r"
  unfolding mem_cball euclidean_dist_l2[of x y] setL2_def
proof -
  have "(\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> (\<Sum>(i::'a)\<in>Basis. (r / sqrt(DIM('a)))\<^sup>2)"
  proof (intro setsum_mono)
    fix i :: 'a
    assume "i \<in> Basis"
    thus "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 \<le> (r / sqrt(DIM('a)))\<^sup>2"
      using assms
      by (auto intro: sqrt_le_rsquare)
  qed
  moreover
  have "... \<le> r\<^sup>2"
    using assms by (simp add: power_divide)
  ultimately
  show "sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> r"
    using assms by (auto intro!: real_le_lsqrt setsum_nonneg)
qed

lemma cbox_in_cball':
  fixes x::"'a::euclidean_space"
  assumes "0 < r"
  shows "\<exists>b > 0. b \<le> r \<and> (\<exists>B. B = (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> (\<forall>y \<in> cbox (x - B) (x + B). y \<in> cball x r))"
proof (rule, safe)
  have "r / sqrt (real DIM('a)) \<le> r / 1"
    using assms DIM_positive by (intro divide_left_mono) auto
  thus "r / sqrt (real DIM('a)) \<le> r" by simp
next
  let ?B = "\<Sum>i\<in>Basis. (r / sqrt (real DIM('a))) *\<^sub>R i"
  show "\<exists>B. B = ?B \<and> (\<forall>y \<in> cbox (x - B) (x + B). y \<in> cball x r)"
  proof (rule, safe)
    fix y::'a
    assume "y \<in> cbox (x - ?B) (x + ?B)"
    hence bounds:
      "\<And>i. i \<in> Basis \<Longrightarrow> (x - ?B) \<bullet> i \<le> y \<bullet> i"
      "\<And>i. i \<in> Basis \<Longrightarrow> y \<bullet> i \<le> (x + ?B) \<bullet> i"
      by (auto simp: mem_box)
    show "y \<in> cball x r"
    proof (intro cube_in_cball)
      fix i :: 'a
      assume "i\<in> Basis"
      with bounds
      have bounds_comp:
        "x \<bullet> i - r / sqrt (real DIM('a)) \<le> y \<bullet> i"
        "y \<bullet> i \<le> x \<bullet> i + r / sqrt (real DIM('a))"
        by (auto simp: algebra_simps)
      thus "dist (x \<bullet> i) (y \<bullet> i) \<le> r / sqrt (real DIM('a))"
        unfolding dist_real_def by simp
    qed (auto simp add: assms)
  qed (rule)
qed (auto simp: assms DIM_positive)

locale ivp_open = ivp +
  assumes openT: "open T"
  assumes openX: "open X"

lemma Pair1_in_Basis: "i \<in> Basis \<Longrightarrow> (i, 0) \<in> Basis"
 and Pair2_in_Basis: "i \<in> Basis \<Longrightarrow> (0, i) \<in> Basis"
  by (auto simp: Basis_prod_def)

lemma Basis_prodD:
  assumes "(i, j) \<in> Basis"
  shows "i \<in> Basis \<and> j = 0 \<or> i = 0 \<and> j \<in> Basis"
  using assms
  by (auto simp: Basis_prod_def)

lemma cball_Pair_split_subset: "cball (a, b) c \<subseteq> cball a c \<times> cball b c"
  apply (auto simp: dist_prod_def)
   apply (metis dual_order.trans le_real_sqrt_sumsq power2_eq_square)
  by (metis add.commute dual_order.trans le_real_sqrt_sumsq power2_eq_square)

lemma cball_times_subset: "cball a (c/2) \<times> cball b (c/2) \<subseteq> cball (a, b) c"
proof -
  {
    fix a' b'
    have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) \<le> dist a a' + dist b b'"
      by (rule real_le_lsqrt) (auto simp: power2_eq_square algebra_simps)
    also assume "a' \<in> cball a (c / 2)"
    then have "dist a a' \<le> c / 2" by simp
    also assume "b' \<in> cball b (c / 2)"
    then have "dist b b' \<le> c / 2" by simp
    finally have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) \<le> c"
      by simp
  } thus ?thesis by (auto simp: dist_prod_def)
qed

lemma eventually_bound_pairE:
  assumes "isCont f (t0, x0)"
  obtains B where
    "B \<ge> 1"
    "eventually (\<lambda>e. \<forall>x \<in> cball t0 e \<times> cball x0 e. norm (f x) \<le> B) (at_right 0)"
proof -
  from assms[simplified isCont_def, THEN tendstoD, OF zero_less_one]
  obtain d::real where d: "d > 0"
    "\<And>x. x \<noteq> (t0, x0) \<Longrightarrow> dist x (t0, x0) < d \<Longrightarrow> dist (f x) (f (t0, x0)) < 1"
    by (auto simp: eventually_at)
  have bound: "norm (f (t, x)) \<le> norm (f (t0, x0)) + 1"
    if "t \<in> cball t0 (d/3)" "x \<in> cball x0 (d/3)" for t x
  proof -
    from that have "norm (f (t, x) - f (t0, x0)) < 1"
      using \<open>0 < d\<close>
      unfolding dist_norm[symmetric]
      apply (cases "(t, x) = (t0, x0)", force)
      by (rule d) (auto simp: dist_commute dist_prod_def
        intro!: le_less_trans[OF sqrt_sum_squares_le_sum_abs])
    then show ?thesis
      by norm
  qed
  have "norm (f (t0, x0)) + 1 \<ge> 1"
    "eventually (\<lambda>e. \<forall>x \<in> cball t0 e \<times> cball x0 e.
      norm (f x) \<le> norm (f (t0, x0)) + 1) (at_right 0)"
    using d(1) bound
    by (auto simp: eventually_at dist_real_def intro!: exI[where x="d/3"])
  thus ?thesis ..
qed

lemma
  eventually_in_cballs:
  assumes "d > 0" "c > 0"
  shows "eventually (\<lambda>e. cball t0 (c * e) \<times> (cball x0 e) \<subseteq> cball (t0, x0) d) (at_right 0)"
  using assms
  by (auto simp: eventually_at dist_real_def field_simps dist_prod_def
    intro!: exI[where x="min d (d / c) / 3"]
    order_trans[OF sqrt_sum_squares_le_sum_abs])

lemma cball_eq_sing':
  fixes x :: "'a::{metric_space,perfect_space}"
  shows "cball x e = {y} \<longleftrightarrow> e = 0 \<and> x = y"
  using cball_eq_sing[of x e]
  apply (cases "x = y", force)
  by (metis cball_empty centre_in_cball insert_not_empty not_le singletonD)

locale unique_on_open = ivp_open + continuous_rhs T X f +
  assumes local_lipschitz: "local_lipschitz T X (\<lambda>t x. f (t, x))"
begin

lemma eventually_lipschitz:
  assumes "t \<in> T" "x \<in> X" "c > 0"
  obtains L where
    "eventually (\<lambda>u. \<forall>t' \<in> cball t (c * u) \<inter> T.
      lipschitz (cball x u \<inter> X) (\<lambda>y. f (t', y)) L) (at_right 0)"
proof -
  from local_lipschitzE[OF local_lipschitz, OF \<open>t \<in> T\<close> \<open>x \<in> X\<close>]
  obtain u L where
    "u > 0"
    "\<And>t'. t' \<in> cball t u \<inter> T \<Longrightarrow> lipschitz (cball x u \<inter> X) (\<lambda>y. f (t', y)) L"
    by auto
  hence "eventually (\<lambda>u. \<forall>t' \<in> cball t (c * u) \<inter> T.
      lipschitz (cball x u \<inter> X) (\<lambda>y. f (t', y)) L) (at_right 0)"
    using \<open>u > 0\<close> \<open>c > 0\<close>
    by (auto simp: dist_real_def eventually_at divide_simps algebra_simps
      intro!: exI[where x="min u (u / c)"]
      intro: lipschitz_subset[where D="cball x u \<inter> X"])
  thus ?thesis ..
qed

lemma eventually_unique_solution:
  obtains B L t
  where "t > 0" "eventually (\<lambda>e. e > 0 \<and> cball t0 (t * e) \<subseteq> T \<and> cball x0 e \<subseteq> X \<and>
      (unique_on_cylinder (i\<lparr>ivp_T:=cball t0 (t * e), ivp_X:=cball x0 e\<rparr>) (t * e) e B L (cball x0 e)))
    (at_right 0)"
proof -
  from open_Times[OF openT openX] have "open (T \<times> X)" .
  from at_within_open[OF _ this] iv_defined
  have "isCont f (t0, x0)"
    using continuous by (auto simp: continuous_on_eq_continuous_within)
  from eventually_bound_pairE[OF this]
  obtain B where B:
    "1 \<le> B" "\<forall>\<^sub>F e in at_right 0. \<forall>x\<in>cball t0 e \<times> cball x0 e. norm (f x) \<le> B"
    .
  moreover

  def t \<equiv> "inverse B"
  have te: "\<And>e. e > 0 \<Longrightarrow> t * e > 0"
    using \<open>1 \<le> B\<close> by (auto simp: t_def field_simps)
  have t_pos: "t > 0"
    using \<open>1 \<le> B\<close> by (auto simp: t_def)

  from B(2) obtain dB where "0 < dB" "0 < dB / 2"
    and dB: "\<And>d t x. d > 0 \<Longrightarrow> d < dB \<Longrightarrow> t\<in>cball t0 d \<Longrightarrow> x\<in>cball x0 d \<Longrightarrow>
      norm (f (t, x)) \<le> B"
    by (auto simp: eventually_at dist_real_def)
  hence dB': "\<And>t x. (t, x) \<in> cball (t0, x0) (dB / 2) \<Longrightarrow> norm (f (t, x)) \<le> B"
    using cball_Pair_split_subset[of t0 x0 "dB / 2"]
    by (auto simp: eventually_at dist_real_def
      simp del: mem_cball
      intro!: dB[where d="dB/2"])
  from eventually_in_cballs[OF \<open>0 < dB/2\<close> t_pos, of t0 x0]
  have "eventually
     (\<lambda>e. \<forall>x\<in>cball t0 (t * e) \<times> cball x0 e. norm (f x) \<le> B)
     (at_right 0)"
    unfolding eventually_at_filter
    by eventually_elim (auto intro!: dB')
  moreover

  from eventually_lipschitz[OF iv_defined t_pos ] obtain L where
    "eventually (\<lambda>u. \<forall>t'\<in>cball t0 (t * u) \<inter> T.
      lipschitz (cball x0 u \<inter> X) (\<lambda>y. f (t', y)) L) (at_right 0)"
    .
  moreover
  have "eventually (\<lambda>e. cball t0 (t * e) \<subseteq> T) (at_right 0)"
    using eventually_open_cball[OF openT iv_defined(1)]
    by (subst eventually_filtermap[symmetric, where f="op * t"])
      (simp add: filtermap_times_real t_pos)
  moreover
  have "eventually (\<lambda>e. cball x0 e \<subseteq> X) (at_right 0)"
    using openX iv_defined(2)
    by (rule eventually_open_cball)
  ultimately have "eventually (\<lambda>e. e > 0 \<and> cball t0 (t * e) \<subseteq> T \<and> cball x0 e \<subseteq> X \<and>
      (unique_on_cylinder (i\<lparr>ivp_T:=cball t0 (t * e), ivp_X:=(cball x0 e)\<rparr>) (t * e) e B L (cball x0 e)))
    (at_right 0)"
    unfolding eventually_at_filter
  proof eventually_elim
    case (elim e)
    thus ?case
    proof safe
      fix X' assume *: "cball x0 e \<subseteq> X'"
      assume e: "0 < e"
      assume L: "\<forall>t'\<in>cball t0 (t * e) \<inter> T.
        lipschitz (cball x0 e \<inter> X) (\<lambda>y. f (t', y)) L"
      assume B: "\<forall>x\<in>cball t0 e \<times> cball x0 e. norm (f x) \<le> B"
      assume B': "\<forall>x\<in>cball t0 (t * e) \<times> cball x0 e. norm (f x) \<le> B"
      assume T: "cball t0 (t * e) \<subseteq> T"
      assume X: "cball x0 e \<subseteq> X"
      have "t0 \<in> cball t0 (t * e) \<inter> T" using T
        by (force simp: e t_pos intro!: mult_nonneg_nonneg less_imp_le)
      hence L': "lipschitz (cball x0 e \<inter> X) (\<lambda>y. f (t0, y)) L" using L
        by simp
      hence "L \<ge> 0"
        by (rule lipschitz_nonneg)
      from T X have subset: "cball t0 (t * e) \<times> cball x0 e \<subseteq> T \<times> X" by auto
      let ?i = "(i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>)"
      interpret i: cylinder ?i "t * e" e using \<open>e > 0\<close> T te[OF \<open>e > 0\<close>]
        by unfold_locales (auto simp: cball_def dist_real_def)
      interpret i: continuous_rhs i.T i.X i.f
        using continuous_on_subset[OF continuous subset]
        by unfold_locales auto
      interpret i: solution_in_cylinder ?i "t * e" e B
        using B'
        by unfold_locales (auto simp: t_def cball_def dist_real_def inverse_eq_divide)
      show "unique_on_cylinder ?i (t * e) e B L (cball x0 e)"
        using L \<open>L \<ge> 0\<close> te T X
        by unfold_locales
          (auto simp: cball_def dist_real_def abs_real_def
            dest!: bspec
            intro: lipschitz_subset)
    qed
  qed
  with t_pos show ?thesis ..
qed

lemma exists_unique_solution_abstracted:
  shows "\<exists>e>0. \<exists>u>0. cball t0 e \<subseteq> T \<and> cball x0 u \<subseteq> X \<and>
    (\<forall>X. cball x0 u \<subseteq> X \<longrightarrow> unique_solution (i\<lparr>ivp_T:=cball t0 e, ivp_X:=X\<rparr>))"
proof -
  from eventually_unique_solution obtain B L t
  where *: "0 < t"
    "\<forall>\<^sub>F e in at_right 0. 0 < e \<and> cball t0 (t * e) \<subseteq> T \<and> cball x0 e \<subseteq> X \<and>
       unique_on_cylinder (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>)
        (t * e) e B L (cball x0 e)" .
  from eventually_happens[OF *(2)]
  obtain e where e: "0 < e"
        "cball t0 (t * e) \<subseteq> T"
        "cball x0 e \<subseteq> X"
        "unique_on_cylinder (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>)
          (t * e) e B L (cball x0 e)"
    by auto
  then
  interpret uc:
    unique_on_cylinder "i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>"
      "t * e" e B L "cball x0 e"
    by simp
  have cylinder_le: "B * \<bar>s - t0\<bar> \<le> e" if "s \<in> cball t0 (t * e)" for s
  proof -
    from that have "abs (s - t0) \<le> abs (t * e)"
      by (auto simp: cball_def dist_real_def)
    hence "B * \<bar>s - t0\<bar> \<le> B * abs (t * e)"
      using * e uc.B_nonneg
      by (intro mult_left_mono)
        (auto simp: cball_def dist_real_def abs_real_def algebra_simps)
    also have "abs (t * e) = t * e"
      using * e by simp
    also note uc.e_bounded
    finally show ?thesis
      using uc.B_nonneg e
      by (cases "B = 0") (auto)
  qed
  show ?thesis
    apply (rule exI[where x="t * e"])
    apply (rule conjI)
    subgoal using *(1) e by simp
    subgoal
    proof (safe intro!: exI[where x=e] e)
      fix X' assume "cball x0 e \<subseteq> X'"
      then interpret us:
        unique_on_superset_domain
          "i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>" X'
        apply unfold_locales
        subgoal by simp
        subgoal
          using e *(1)
          by (auto simp: dist_real_def abs_real_def closed_segment_real; fail)
        subgoal
          using uc.e_bounded uc.B_nonneg
          by (intro set_rev_mp[OF uc.solves_in_cone])
             (auto intro!: has_vector_derivative_continuous_on subset_cball uc.solves_in_cone
               open_closed_segment cylinder_le
               has_vector_derivative_within_subset[OF _ open_closed_segment_subset])
        done
      have "unique_solution
          (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e, ivp_X := X'\<rparr>)" ..
      thus "unique_solution (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := X'\<rparr>)"
        by simp
    qed
    done
qed

lemma
  eventually_less_at_right:
  fixes a b::real shows
  "b > a \<Longrightarrow> eventually (\<lambda>e. e < b) (at_right a)"
  by (auto simp: eventually_at_le dist_real_def intro!: exI[where x="(b - a)/2"])

lemma exists_unique_solution_legacy:
  assumes "t0 < t_max"
  shows "\<exists>t1\<in>{t0<..t_max}. \<exists>u>0. {t0..t1} \<subseteq> T \<and> cball x0 u \<subseteq> X \<and>
    (\<forall>X. cball x0 u \<subseteq> X \<longrightarrow> unique_solution (i\<lparr>ivp_T:={t0..t1}, ivp_X:=X\<rparr>))"
proof -
  from eventually_unique_solution obtain B L t
  where *: "0 < t"
    "\<forall>\<^sub>F e in at_right 0. 0 < e \<and> cball t0 (t * e) \<subseteq> T \<and> cball x0 e \<subseteq> X \<and>
       unique_on_cylinder (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>)
        (t * e) e B L (cball x0 e)" .
  have "eventually (\<lambda>e. e < t_max - t0) (at_right 0)"
    using assms by (simp add: eventually_less_at_right)
  hence less: "eventually (\<lambda>e. t * e < t_max - t0) (at_right 0)"
    apply (subst eventually_filtermap[symmetric, where f="op * t"])
    apply (subst filtermap_times_real[OF *(1)])
    apply assumption
    done
  from eventually_conj[OF *(2) less, THEN eventually_happens]
  obtain e where e: "0 < e" "cball t0 (t * e) \<subseteq> T" "cball x0 e \<subseteq> X"
    "unique_on_cylinder (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>)
      (t * e) e B L (cball x0 e)" "t0 + t * e < t_max"
    by auto
  then interpret uc:
    unique_on_cylinder
      "i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e\<rparr>"
      "t * e" e B L "cball x0 e"
    by simp
  have "unique_solution (i\<lparr>ivp_T := cball t0 (t * e), ivp_X := cball x0 e, ivp_T := {uc.t0 .. uc.t0 + t * e}\<rparr>)"
    (is "unique_solution ?i")
    ..
  also have "?i = (i\<lparr>ivp_T := {t0 .. t0 + t * e}, ivp_X := cball x0 e\<rparr>)"
    (is "_ = ?j")
    by simp
  finally interpret up: unique_solution ?j .
  have cylinder_le: "B * (s - t0) \<le> e" if "s \<in> cball t0 (t * e)" for s
  proof -
    have "s - t0 \<le> abs (s - t0)" by simp
    also
    from that have "abs (s - t0) \<le> abs (t * e )"
      by (auto simp: cball_def dist_real_def)
    hence "B * \<bar>s - t0\<bar> \<le> B * abs (t * e)"
      using * e uc.B_nonneg
      by (intro mult_left_mono)
        (auto simp: cball_def dist_real_def abs_real_def algebra_simps)
    also have "abs (t * e) = t * e"
      using * e by simp
    also note uc.e_bounded
    finally show ?thesis
      using uc.B_nonneg e
      by (cases "B = 0") (auto)
  qed
  show ?thesis
    apply (rule bexI[where x="t0 + t * e"])
    subgoal
    proof (safe intro!: exI[where x=e] e)
      fix x assume "x \<in> {t0 .. t0 + t * e}" then show "x \<in> T"
        using *(1) e
        by (simp add: subset_iff dist_real_def)
    next
      fix X' assume "cball x0 e \<subseteq> X'"
      then interpret us: unique_on_superset_domain
          "i\<lparr>ivp_T := {t0 .. t0 + t * e}, ivp_X := cball x0 e\<rparr>" X'
        apply unfold_locales
          apply (simp; fail)
         using e *(1)
         apply (auto simp: dist_real_def abs_real_def closed_segment_real; fail)[1]
        apply (simp del: mem_cball)
        apply (rule set_rev_mp)
         apply (rule uc.solves_in_cone)
        using uc.e_bounded uc.B_nonneg cylinder_le
        by (auto
          intro!: has_vector_derivative_continuous_on subset_cball
            has_vector_derivative_within_subset[OF _ open_closed_segment_subset]
            open_closed_segment cylinder_le
          simp: dist_real_def)
      have "unique_solution
        (i\<lparr>ivp_T := {t0 .. t0 + (t * e)}, ivp_X := cball x0 e, ivp_X := X'\<rparr>)" ..
      thus "unique_solution (i\<lparr>ivp_T := {t0 .. t0 + (t * e)}, ivp_X := X'\<rparr>)"
        by simp
    qed
    subgoal using e by (auto simp add: dist_real_def cball_def abs_real_def \<open>t > 0\<close>)
    done
qed

lemma exists_unique_solution_legacy':
  assumes "t0 < t_max"
  shows "\<exists>t1\<in>{t0<..t_max}. {t0..t1} \<subseteq> T \<and> unique_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>)"
proof-
  from exists_unique_solution_legacy[OF assms]
  obtain t1 u where *: "t1\<in>{t0<..t_max}" "u > 0"
    "{t0..t1} \<subseteq> T" "cball x0 u \<subseteq> X" "(\<forall>X. cball x0 u \<subseteq> X \<longrightarrow> unique_solution (i\<lparr>ivp_T := {t0..t1}, ivp_X := X\<rparr>))"
    by auto
  show ?thesis
    using *(1-4) *(5)[rule_format, OF \<open>cball x0 u \<subseteq> X\<close>]
    by (auto intro!: bexI[where x=t1])
qed

subsubsection \<open>Global maximal solution with local Lipschitz \label{sec:qpl-global-solution}\<close>

definition PHI where
  "PHI = {(x, t1). t0 < t1 \<and> {t0..t1} \<subseteq> T \<and> ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) x}"

lemma PHI_notempty: "PHI \<noteq> {}"
proof -
  from exists_unique_solution_legacy[where t_max="t0+1"]
  obtain t1 a where
    "\<And>X. cball x0 a \<subseteq> X \<Longrightarrow> unique_solution (i\<lparr>ivp_T:={t0..t1}, ivp_X:=X\<rparr>)"
    "t0 < t1" "{t0..t1} \<subseteq> T" "cball x0 a \<subseteq> X"
    by force
  from this(1)[OF this(4)] interpret i: unique_solution "i\<lparr>ivp_T:={t0..t1}\<rparr>"
    by auto
  from i.is_solution_solution \<open>t0<t1\<close> \<open>{t0..t1} \<subseteq> T\<close>
  have "(i.solution, t1) \<in> PHI"
    by (simp add: PHI_def)
  thus ?thesis by auto
qed

lemma positive_existence_interval:
  assumes E: "\<forall>(x, t1) \<in> PHI. \<forall>(y, U) \<in> PHI. \<forall>t \<in> {t0..t1} \<inter> {t0..U}. x t = y t"
  defines "J \<equiv> \<Union>(x, t1)\<in>PHI. {t0..t1}"
  defines "j \<equiv> i\<lparr>ivp_T:=J\<rparr>"
  defines "M \<equiv> (SUP xt : PHI. ereal (snd xt))"
  shows "unique_solution j"
    "\<And>x t1 t. (x, t1) \<in> PHI \<Longrightarrow> t \<in> {t0..t1} \<Longrightarrow> x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t"
    "J = real_of_ereal ` {ereal t0..<M}"
    "t0 \<in> J"
proof -
  from PHI_def have PHI: "PHI = {xT. t0 < snd xT \<and> {t0..snd xT} \<subseteq> T \<and>
    ivp.is_solution (i\<lparr>ivp_T:={t0..snd xT}\<rparr>) (fst xT)}"
    by auto
  from PHI_notempty obtain a b where "(a, b) \<in> PHI" by auto
  hence "t0 \<le> b" by (simp add: PHI_def)
  thus "t0 \<in> J"
    using \<open>(a, b) \<in> PHI\<close>
    by (auto simp: J_def intro!: bexI[where x="(a, b)"])
  have sol_eq: "x t = y t"
    if "ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) x"
      "ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) y"
      "t \<in> {t0..t1}" "t0<t1" "{t0..t1} \<subseteq> T"
    for x y t t1
  proof -
    from that have "(x, t1) \<in> PHI" "(y, t1) \<in> PHI"
      by (auto simp: PHI)
    with that show ?thesis using E by force
  qed
  from E have E: "\<forall>xT \<in> PHI. \<forall>yU \<in> PHI. \<forall>t \<in> {t0..snd xT} \<inter> {t0..snd yU}.
    (fst xT) t = (fst yU) t" by force
  have J: "(\<Union>(x, t1)\<in>PHI. {t0..t1}) = (\<Union>xT\<in>PHI. {t0..snd xT})"
    by auto
  with j_def J_def have j_def': "j = i\<lparr>ivp_T:=\<Union>xT\<in>PHI. {t0..snd xT}\<rparr>" by simp
  have "J \<subseteq> T" unfolding J_def j_def PHI_def by auto
  have "\<exists>x. \<forall>t \<in> J. \<forall>yT \<in> PHI. t \<le> snd yT \<longrightarrow> x t = fst yT t"
  proof (intro bchoice, safe)
    fix x
    assume xI: "x \<in> J"
    hence "\<exists>s\<in>PHI. x \<le> snd s" unfolding J_def PHI_def by auto
    then obtain ya where ya: "ya \<in> PHI" "x \<le> snd ya" by auto
    with E[simplified Ball_def, THEN spec, THEN mp, OF ya(1)]
    have E':"\<forall>zb\<in>PHI. x \<in> {t0..snd ya} \<inter> {t0..snd zb} \<longrightarrow> fst ya x = fst zb x"
      by (simp add: Ball_def)
    show "\<exists>y. \<forall>za\<in>PHI. x \<le> snd za \<longrightarrow> y = fst za x"
    proof (rule, rule, rule)
      fix zb
      assume zb: "zb \<in> PHI" "x \<le> snd zb"
      with E'[simplified Ball_def, THEN spec, THEN mp, OF \<open>zb \<in> PHI\<close>]
      have "x \<in> {t0..snd ya} \<inter> {t0..snd zb} \<longrightarrow> fst ya x = fst zb x" by (simp add: Ball_def)
      thus "fst ya x = fst zb x" using xI ya zb J_def PHI_def by auto
    qed
  qed
  then obtain y where y: "\<forall>t\<in>J. \<forall>yT\<in>PHI. t \<le> snd yT \<longrightarrow> y t = fst yT t"
    by auto
  hence equal: "\<forall>s\<in>PHI. \<forall>t \<in> {t0..snd s}. y t = fst s t" using J_def PHI_def
    by simp
  have continuable: "\<exists>s\<in>PHI. x < snd s" if "x \<in> J" for x
  proof -
    obtain s where s: "s \<in> PHI" "x \<le> snd s" using \<open>x \<in> J\<close>
      by (force simp add: PHI_def J_def)
    def i1 \<equiv> "i\<lparr>ivp_T:={t0..snd s}\<rparr>"
    interpret i1: ivp i1
      using s iv_defined \<open>x \<in> J\<close>
      by unfold_locales (auto simp: PHI_def J_def i1_def)
    from \<open>s \<in> PHI\<close> have "t0 < snd s" by (simp add: PHI)
    from \<open>s \<in> PHI\<close> have "{t0..snd s} \<subseteq> T" by (simp add: PHI)
    from \<open>s \<in> PHI\<close> have "i1.is_solution (fst s)" by (simp add: PHI i1_def)
    then interpret i1: unique_solution i1
    proof (intro i1.unique_solutionI, simp)
      fix y t
      assume "i1.is_solution y"
      assume "t \<in> i1.T"
      hence "t \<in> {t0..snd s}" by (simp add: i1_def)
      with sol_eq \<open>i1.is_solution (fst s)\<close> \<open>i1.is_solution y\<close>
        \<open>t0 < snd s\<close> \<open>{t0..snd s} \<subseteq> T\<close>
      show "y t = fst s t" by (simp add: i1_def)
    qed
    show ?thesis
    proof (cases "x = snd s")
      assume "x = snd s"
      def i2' \<equiv> "i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s)\<rparr>"
      interpret i2': unique_on_open i2'
        using iv_defined \<open>x \<in> J\<close> continuous openT openX local_lipschitz
          i1.is_solutionD(3)[OF \<open>i1.is_solution (fst s)\<close>] \<open>s \<in> PHI\<close>
        by unfold_locales (auto simp: PHI i1_def i2'_def)
      from i2'.exists_unique_solution_legacy[where t_max = "snd s + 1"]
      obtain t1 u where t1u: "t1 > snd s" "{snd s..t1} \<subseteq> T" "0 < u"
        "cball (fst s (snd s)) u \<subseteq> ivp_X i2'"
        "\<And>X. cball (fst s (snd s)) u \<subseteq> X \<Longrightarrow>
          unique_solution
            (i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s), ivp_T:={snd s..t1},
              ivp_X := X\<rparr>)"
         by (auto simp: i2'_def)
      def i2 \<equiv> "i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s), ivp_T:={snd s..t1}\<rparr>"
      interpret i2: unique_solution i2 using t1u(5)[OF t1u(4)]
        by (simp add: i2_def i2'_def)
      def ic \<equiv> "i\<lparr>ivp_T:={t0..t1}\<rparr>"
      interpret ic: ivp_on_interval ic t1
        using iv_defined \<open>t1 > snd s\<close> \<open>snd s > t0\<close>
        by unfold_locales (auto simp: ic_def)
      interpret ic: connected_unique_solutions ic i1 i2 "snd s"
        using i1.unique_solution[OF \<open>i1.is_solution (fst s)\<close>]
          \<open>snd s > t0\<close> \<open>t1 > snd s\<close>
          i1.is_solution_solution
          i2.is_solution_solution
          i1.is_solutionD[OF i1.is_solution_solution]
          i2.is_solutionD[OF i2.is_solution_solution]
        by unfold_locales (auto simp: i1_def i2_def ic_def)
      have "(ic.solution, t1) \<in> PHI"
        using \<open>t0 < snd s\<close> \<open>{t0..snd s} \<subseteq> T\<close> t1u(1-4) ic.is_solution_solution
        by (force simp add: PHI ic_def)
      thus ?thesis using \<open>x = snd s\<close>  \<open>snd s < t1\<close> by force
    qed (insert s, force)
  qed

  have inJ: "x \<in> J" if "(a, b) \<in> PHI" "t0 \<le> x" "x \<le> b" for x a b
    using that by (force simp: PHI_def J_def)
  show "J = real_of_ereal ` {t0..<M}"
    unfolding J_def M_def
    by safe
     (auto simp: ereal_le_real_iff real_le_ereal_iff less_SUP_iff
       intro!: image_eqI[where x="ereal x" for x] continuable inJ bexI[where x="(a, b)" for a b])

  interpret j: ivp j
    using iv_defined PHI_notempty
    by (unfold_locales, auto simp: j_def J_def PHI_def) force
  have "j.is_solution y"
  proof (intro j.is_solutionI)
    from PHI_notempty have "\<exists>ya. ya \<in> PHI" unfolding ex_in_conv .
    then obtain ya where ya: "ya \<in> PHI" ..
    then interpret iya: ivp "i\<lparr>ivp_T:={t0..(snd ya)}\<rparr>"
      using iv_defined by unfold_locales (auto simp: PHI)
    from ya have "iya.is_solution (fst ya)" by (simp add: PHI)
    from ya equal have "y t0 = fst ya t0" by (auto simp: PHI)
    thus "y j.t0 = j.x0"
      using iv_defined iya.iv_defined
      using iya.is_solutionD(1)[OF \<open>iya.is_solution (fst ya)\<close>]
      by (auto simp: j_def)
  next
    fix x
    assume "x \<in> j.T"
    hence "x \<in> J" by (simp add: j_def)
    note continuable[OF this]
    then obtain ya where ya: "ya \<in> PHI" "x < snd ya" ..
    then interpret iya: ivp "i\<lparr>ivp_T:={t0..snd ya}\<rparr>"
      using iv_defined by unfold_locales (auto simp: PHI)
    from ya have "iya.is_solution (fst ya)" by (simp add: PHI)
    from iya.is_solutionD(2)[OF this]
    have deriv:
      "(fst ya has_vector_derivative f (x, fst ya x)) (at x within {t0..snd ya})"
      using \<open>x \<in> j.T\<close> J_def ya by (auto simp add: j_def)
    moreover
    from \<open>x \<in> j.T\<close> ya have "x\<in>{t0..<snd ya}" by (auto simp add: J_def j_def)
    with equal ya have y_eq_x: "y x = fst ya x" by simp
    ultimately
    show "(y has_vector_derivative j.f (x, y x)) (at x within j.T)"
      apply (simp (no_asm) add: j_def J_def)
      unfolding J
      unfolding has_vector_derivative_def
      unfolding has_derivative_within'
    proof safe
      fix e::real
      assume "e > 0" "\<forall>e>0. \<exists>d>0. \<forall>x'\<in>{t0..snd ya}.
        0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
        norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / norm (x' - x)
        < e"
      then obtain d where d: "d > 0"
        "\<And>x'. x'\<in>{t0..snd ya} \<Longrightarrow> x' \<noteq> x \<Longrightarrow> \<bar>x' - x\<bar> < d \<Longrightarrow>
        norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e"
        by auto
      show "\<exists>d>0. \<forall>x'\<in>\<Union>s\<in>PHI. {t0..snd s}.
        0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
        norm (y x' - y x - (x' - x) *\<^sub>R f (x, y x)) / norm (x' - x) < e"
      proof (rule, rule)
        show "Min {d, snd ya - x} > 0" using d ya by simp
      next
        have "\<forall>a\<in>PHI. \<forall>x'\<in>{t0..snd a}.
          x' \<noteq> x \<and> \<bar>x' - x\<bar> < Min {d, snd ya - x} \<longrightarrow>
          norm (y x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e"
        proof (rule, rule, rule)
          fix t and x'
          assume A: "t \<in> PHI"
            "x' \<in> {t0..snd t}"
            "x' \<noteq> x \<and> \<bar>x' - x\<bar> < Min {d, snd ya - x}"
          with d
          have "x' \<noteq> x \<and> \<bar>x' - x\<bar> < d \<longrightarrow>
            norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e"
            by auto
          moreover
          from A have "x' \<noteq> x \<and> \<bar>x' - x\<bar> < d" by simp
          moreover
          from A have "x'\<in>{t0..snd ya}" by auto
          with A have "y x' = fst ya x'" using equal ya by fast
          ultimately show
            "norm (y x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e"
            by simp
        qed
        thus "\<forall>x'\<in>\<Union>s\<in>PHI. {t0..snd s}.
          0 < norm (x' - x) \<and> norm (x' - x) < Min {d, snd ya - x} \<longrightarrow>
          norm (y x' - y x - (x' - x) *\<^sub>R f (x, y x)) / norm (x' - x) < e"
          using y_eq_x by simp
      qed
    qed simp
    from iya.is_solutionD(3)[OF \<open>iya.is_solution (fst ya)\<close>]
    have "fst ya x \<in> X"
      using \<open>x \<in> j.T\<close> ya by (auto simp: PHI_def j_def J_def)
    moreover
    from \<open>x \<in> j.T\<close> ya have "x\<in>{t0..snd ya}" by (auto simp: PHI_def j_def J_def)
    with equal ya have y_eq_x: "y x = fst ya x" by simp
    ultimately
    show "y x \<in> j.X" by (auto simp: j_def J_def)
  qed
  thus "unique_solution j"
  proof (rule j.unique_solutionI)
    fix x t
    assume "t \<in> j.T"
    hence "t \<in> J" by (simp add: j_def)
    note continuable[OF this]
    then obtain x' t1 where x't1: "(x', t1) \<in> PHI" "t < t1" "{t0..t1} \<subseteq> T"
      by (auto simp: PHI)
    then interpret ix': ivp "i\<lparr>ivp_T:={t0..t1}\<rparr>"
      using iv_defined by unfold_locales (auto simp: PHI)
    have"t0 \<le> t" using \<open>t \<in> J\<close> unfolding J_def by auto
    from x't1 have "ix'.is_solution x'" by (simp add: PHI)
    assume "j.is_solution x"
    hence "ix'.is_solution x"
      using x't1 \<open>t \<in> J\<close> \<open>{t0..t1} \<subseteq> T\<close>
      by (intro j.solution_on_subset[where T'="{t0..t1}", simplified j_def,
        simplified]) (auto simp: J_def j_def)
    from equal x't1 \<open>t\<in>j.T\<close> have "y t = x' t" by (auto simp: j_def J_def)
    thus "x t = y t"
      using sol_eq[OF \<open>ix'.is_solution x'\<close> \<open>ix'.is_solution x\<close>] \<open>t < t1\<close> \<open>t \<in> j.T\<close>
      \<open>{t0..t1} \<subseteq> T\<close>
      by (auto simp: j_def J_def)
  qed
  then interpret j: unique_solution j by simp
  fix x t1 t
  assume "(x, t1) \<in> PHI" "t \<in> {t0..t1}"
  then interpret i': ivp "i\<lparr>ivp_T := {t0..t1}\<rparr>" using iv_defined
    by unfold_locales auto
  from \<open>(x, t1) \<in> PHI\<close> have x: "i'.is_solution x" "t0 < t1" "{t0..t1} \<subseteq> T"
    by (auto simp add: PHI_def)
  have "i'.is_solution j.solution"
    apply (rule j.solution_on_subset[simplified j_def, simplified])
    using x \<open>(x, t1) \<in> PHI\<close> j.is_solution_solution
    by (auto simp: j_def J_def)
  from sol_eq[OF x(1) this \<open>t \<in> {t0..t1}\<close> \<open>t0 < t1\<close> \<open>{t0..t1} \<subseteq> T\<close>]
  show "x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t" by (simp add: j_def)
qed

lemma E:
  shows "\<forall>(x, t1)\<in>PHI. \<forall>(y, t2)\<in>PHI. \<forall>t\<in>{t0..t1} \<inter> {t0..t2}. x t = y t"
proof safe
  fix a b
  fix y z
  fix t
  assume "(y, a) \<in> PHI" "(z, b) \<in> PHI"
  hence bounds: "t0 < a" "t0 < b"
    and subsets: "{t0..a} \<subseteq> T" "{t0..b} \<subseteq> T"
    and y_sol: "ivp.is_solution (i\<lparr>ivp_T := {t0..a}\<rparr>) y"
    and z_sol: "ivp.is_solution (i\<lparr>ivp_T := {t0..b}\<rparr>) z"
    unfolding PHI_def by auto
  assume "t \<in> {t0..a}" "t \<in> {t0..b}"
  interpret i1: ivp "i\<lparr>ivp_T := {t0..a}\<rparr>"
    using bounds iv_defined by unfold_locales auto
  interpret i2: ivp "i\<lparr>ivp_T := {t0..b}\<rparr>"
    using bounds iv_defined by unfold_locales auto
  have "\<forall>t \<in> {t0..a} \<inter> {t0..b}. y t = z t"
  proof (rule ccontr)
    assume "\<not> (\<forall>x\<in>{t0..a} \<inter> {t0..b}. y x = z x)"
    hence "\<exists>x\<in>{t0..min a b}. y x \<noteq> z x" by simp
    then obtain x1 where x1: "x1 \<in> {t0..min a b}" "y x1 \<noteq> z x1" ..

    from i1.solution_continuous_on[OF y_sol]
    have "continuous_on {t0..x1} y" by (rule continuous_on_subset) (insert x1, simp)
    moreover
    from i2.solution_continuous_on[OF z_sol]
    have "continuous_on {t0..x1} z" by (rule continuous_on_subset) (insert x1, simp)
    ultimately have "continuous_on {t0..x1} (\<lambda>x. norm (y x - z x))"
      by (auto intro: continuous_intros)
    moreover
    have "closed {t0..x1}" by simp
    ultimately
    have "closed {t \<in> {t0..x1}. norm (y t - z t) = 0}"
      by (rule continuous_closed_preimage_constant)
    moreover
    have "t0 \<in> {t \<in> {t0..x1}. norm (y t - z t) = 0}"
      using x1 i1.is_solutionD[OF y_sol] i2.is_solutionD[OF z_sol]
      by simp
    then have "{t \<in> {t0..x1}. norm (y t - z t) = 0} \<noteq> {}" by blast
    ultimately
    have "\<exists>m\<in>{t \<in> {t0..x1}. norm (y t - z t) = 0}.
      \<forall>y\<in>{t \<in> {t0..x1}. norm (y t - z t) = 0}. dist x1 m \<le> dist x1 y"
      by (rule distance_attains_inf) auto
    then guess x_max .. note max = this
    have "z x_max = y x_max" using max by simp
    have "x_max \<in> {t0..min a b}" "x_max \<in> T"
      using x1 z_sol y_sol max subsets by auto
    with x1 i1.is_solutionD[OF y_sol] have "y x_max \<in> X"
      by (simp add: is_solution_def)
    with max have "z x_max \<in> X" by simp
    def i3' \<equiv> "i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max\<rparr>"
    interpret i3': unique_on_open i3'
      using iv_defined continuous openT openX local_lipschitz
        i1.is_solutionD(3)[OF y_sol] \<open>x_max \<in> T\<close> \<open>y x_max \<in> X\<close>
      by unfold_locales (auto simp: PHI_def i3'_def)
    have "x_max < x1" using x1 max by auto
    with i3'.exists_unique_solution_legacy'[where t_max = x1]
    obtain t1 where t1: "t1 \<in>{x_max<..x1}" "{x_max..t1} \<subseteq> T" "unique_solution
      (i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max, ivp_T:={x_max..t1}\<rparr>)"
      by (auto simp: i3'_def)
    def i3 \<equiv> "i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max, ivp_T:={x_max..t1}\<rparr>"
    from t1 interpret i3: unique_solution i3
      by (simp add: i3_def)
    have "x_max \<in> {x_max..t1}" using t1 by simp
    have "i3.is_solution y" unfolding i3_def
      using \<open>y x_max \<in> X\<close> \<open>x_max \<in> {t0..min a b}\<close> y_sol t1 x1(1)
        i1.restriction_of_solution by auto
    have "i3.is_solution z" unfolding i3_def
      using \<open>z x_max \<in> X\<close> \<open>x_max \<in> {t0..min a b}\<close> z_sol t1 x1(1)
        i2.restriction_of_solution
      by (auto simp: \<open>z x_max = y x_max\<close>[symmetric])
    let ?m = "(x_max + t1) / 2"
    have xm1: "?m \<in> {t0..t1}" using max \<open>x_max \<in> {x_max..t1}\<close> by simp
    have xm2: "?m \<in> {x_max..t1}" using max \<open>x_max \<in> {x_max..t1}\<close> by simp
    from i3.unique_solution[OF \<open>i3.is_solution y\<close>, of ?m]
      i3.unique_solution[OF \<open>i3.is_solution z\<close>, of ?m]
      \<open>x_max \<in> {x_max..t1}\<close>
    have eq: "y ?m = z ?m"
      by (simp add: i3_def)
    hence "?m \<in> {t \<in> {t0..x1}. norm (y t - z t) = 0}" using max x1 t1 by simp
    with max have "dist x1 x_max \<le> dist x1 ?m" by auto
    moreover have "dist x1 x_max = x1 - x_max"
      unfolding dist_real_def using x1 max by simp
    moreover
    have "x_max \<le> x1" using max by simp
    hence "?m \<le> x1" using max x1 t1 by simp
    hence "dist x1 ?m = x1 - ?m"
      using x1 max by (auto intro!: abs_of_nonneg simp add: dist_real_def)
    ultimately
    show False using max x1 t1 by simp
  qed
  thus "y t = z t" using \<open>t \<in> {t0..a}\<close> \<open>t \<in> {t0..b}\<close> by simp
qed

lemma global_solution:
  obtains J::"real set" and M::ereal where
  "J = real_of_ereal ` {t0 ..< M}"
  "\<And>x. x \<in> J \<Longrightarrow> t0 \<le> x"
  "J \<subseteq> T"
  "is_interval J"
  "t0 \<in> J"
  "unique_solution (i\<lparr>ivp_T:=J\<rparr>)"
  "\<And>K x. K \<subseteq> T \<Longrightarrow> is_interval K \<Longrightarrow> t0 \<in> K \<Longrightarrow> (\<And>x. x \<in> K \<Longrightarrow> t0 \<le> x) \<Longrightarrow>
    ivp.is_solution (i\<lparr>ivp_T:=K\<rparr>) x \<Longrightarrow>
    K \<subseteq> J \<and> (\<forall>t\<in>K. x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t)"
proof -
  def M \<equiv> "SUP xt : PHI. ereal (snd xt)"
  def J \<equiv> "(\<Union>(x, t1)\<in>PHI. {t0..t1})"
  show ?thesis
  proof
    show "J = real_of_ereal ` {ereal t0 ..< M}"
      using positive_existence_interval[OF E]
      by (simp add: J_def M_def)
    show "J \<subseteq> T"
      by (auto simp: PHI_def J_def)
    show "is_interval J"
      unfolding is_interval_def J_def PHI_def
      by auto (metis order.trans)+
    show "t0 \<in> J" using PHI_notempty
      by (force simp add: PHI_def J_def)
  next
    fix x assume "x \<in> J" thus "t0 \<le> x"
      by (auto simp add: J_def PHI_def)
  next
    show "unique_solution (i\<lparr>ivp_T := J\<rparr>)"
      using positive_existence_interval[OF E] by (simp add: J_def)
    then interpret j: unique_solution "i\<lparr>ivp_T := J\<rparr>" by simp
    fix K z
    assume "K \<subseteq> T"
    def y \<equiv> "ivp.solution (i\<lparr>ivp_T := J\<rparr>)"
    assume interval: "is_interval K"
    assume Inf: "t0 \<in> K" "\<And>x. x \<in> K \<Longrightarrow> t0 \<le> x"
    assume z_sol: "ivp.is_solution (i\<lparr>ivp_T := K\<rparr>) z"
    then interpret k: has_solution "i\<lparr>ivp_T := K\<rparr>"
      using iv_defined Inf
      by unfold_locales auto
    have "\<forall>x \<in> K. x \<in> J \<and> z x = y x"
    proof (rule, cases, safe)
      fix xM
      def k1 \<equiv> "i\<lparr>ivp_T:={t0..xM}\<rparr>"
      assume xM_in: "xM \<in> K"
      assume "t0 < xM"
      then interpret k1: ivp k1 using iv_defined
        by unfold_locales (auto simp: k1_def)
      have subset: "{t0..xM} \<subseteq> K"
      proof
        fix t
        assume "t \<in> {t0..xM}"
        moreover
        from Inf(1) xM_in interval have "(\<forall>i\<in>Basis.
          t0 \<bullet> i \<le> t \<bullet> i \<and> t \<bullet> i \<le> xM \<bullet> i) \<longrightarrow>
          t \<in> K" unfolding is_interval_def by blast
        hence "t \<in> {t0..xM} \<longrightarrow> t \<in> K" by simp
        ultimately show "t \<in> K" by simp
      qed
      have "k1.is_solution z"
        using k.solution_on_subset z_sol subset \<open>t0 < xM\<close> by (simp add: k1_def)
      then interpret k1: has_solution k1 by unfold_locales auto
      interpret k2': unique_on_open "i\<lparr>ivp_t0:=xM, ivp_x0:=z xM\<rparr>"
        using \<open>t0 < xM\<close> k1.is_solutionD[OF \<open>k1.is_solution z\<close>]
          local_lipschitz openT openX continuous \<open>K \<subseteq> T\<close> \<open>xM \<in> K\<close>
        by unfold_locales (auto simp: k1_def)
      from k2'.exists_unique_solution_legacy'[where t_max = "xM + 1", simplified]
      obtain t1 where t1: "t1 \<in> {xM<..xM+1}" "{xM..t1} \<subseteq> T"
        "unique_solution (i\<lparr>ivp_t0 := xM, ivp_x0 := z xM, ivp_T := {xM..t1}\<rparr>)"
        by auto
      def k2\<equiv>"i\<lparr>ivp_t0 := xM, ivp_x0 := z xM, ivp_T := {xM..t1}\<rparr>"
      from t1 interpret k2: unique_solution k2 by (simp add: k2_def)
      def kc \<equiv> "i\<lparr>ivp_T:={t0..t1}\<rparr>"
      interpret kc: connected_solutions kc k1 k2 z
        using k1.is_solution_solution k2.is_solution_solution iv_defined
          \<open>k1.is_solution z\<close> \<open>t0<xM\<close> t1 k1.is_solutionD[OF \<open>k1.is_solution z\<close>]
          k2.is_solutionD[OF k2.is_solution_solution]
        by unfold_locales (auto simp: k1_def k2_def kc_def)
      have "{t0..t1} \<subseteq> T"
      proof -
        have "{t0..t1} = {t0..xM} \<union> {xM..t1}" using t1 \<open>t0 < xM\<close> by auto
        thus ?thesis using \<open>{t0..xM} \<subseteq> K\<close> \<open>{xM..t1} \<subseteq> T\<close> \<open>K \<subseteq> T\<close> by simp
      qed
      hence concrete_sol: "(kc.connection, t1) \<in> PHI"
        using \<open>t0<xM\<close> t1 \<open>{t0..xM} \<subseteq> K\<close> \<open>K \<subseteq> T\<close> kc.is_solution_connection
        by (auto simp add: PHI_def kc_def)
      moreover have "xM \<in> {t0..<snd (kc.connection, t1)}"
        using \<open>t0<xM\<close> t1 by simp
      ultimately
      show "xM \<in> J" by (force simp: PHI_def J_def)
      have "xM \<in> {t0..t1}" using t1 \<open>t0 < xM\<close> by simp
      from positive_existence_interval[OF E] J_def y_def concrete_sol this
      show "z xM = y xM"
        by (simp add: kc.connection_def[abs_def]) (simp add: k1_def)
    next
      fix x
      assume "x \<in> K" "\<not> t0 < x"
      hence "x = t0" using Inf(2)[OF \<open>x\<in>K\<close>] by simp
      thus "x \<in> J" using PHI_notempty by (force simp: J_def PHI_def)
      from j.solution_t0 k.is_solutionD[OF z_sol]
      show "z x = y x" by (simp add: y_def \<open>x = t0\<close>)
    qed
    thus "K \<subseteq> J \<and> (\<forall>t\<in>K. z t = ivp.solution (i\<lparr>ivp_T := J\<rparr>) t)"
      by (auto simp: y_def)
  qed
qed

definition
  "maximal_existence_interval J =
    (J \<subseteq> T \<and>
     is_interval J \<and>
     t0 \<in> J \<and>
     open J \<and>
     unique_solution (i\<lparr>ivp_T:=J\<rparr>) \<and>
     (\<forall>K x. K \<subseteq> T \<longrightarrow> is_interval K \<longrightarrow> t0 \<in> K \<longrightarrow> ivp.is_solution (i\<lparr>ivp_T:=K\<rparr>) x \<longrightarrow>
     K \<subseteq> J \<and> (\<forall>t \<in> K. x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t)))"

lemma maximal_existence_intervalE:
  obtains M0 M1::ereal and J where
  "J = real_of_ereal ` {M0 <..< M1}"
  "maximal_existence_interval J"
proof -
  from global_solution obtain J M where J:
    "J = real_of_ereal ` {ereal t0 ..< M}"
    "\<And>x. x \<in> J \<Longrightarrow> t0 \<le> x"
    "J \<subseteq> T"
    "is_interval J"
    "t0 \<in> J"
    "unique_solution (i\<lparr>ivp_T:=J\<rparr>)"
    "\<And>K x. K \<subseteq> T \<Longrightarrow> is_interval K \<Longrightarrow> t0 \<in> K \<Longrightarrow> (\<And>x. x \<in> K \<Longrightarrow> t0 \<le> x) \<Longrightarrow>
      ivp.is_solution (i\<lparr>ivp_T:=K\<rparr>) x \<Longrightarrow>
      K \<subseteq> J \<and> (\<forall>t\<in>K. x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t)"
      by blast
  from openT iv_defined(1) obtain dt where dt: "dt > 0" "ball t0 dt \<subseteq> T"
    by (rule openE)
  hence subs: "{t0..} \<inter> ball t0 dt \<subseteq> T"
    by auto
  have is_ivl: "is_interval ({t0..} \<inter> ball t0 dt)"
    by (intro is_interval_inter is_interval_ci is_interval_ball_real)
  have t0_in: "t0 \<in> {t0..} \<inter> ball t0 dt" using dt by auto

  let ?mirror = "\<lambda>t. 2 * t0 - t"
  let ?nT = "?mirror ` T"
  let ?ni = "i\<lparr>ivp_T:=?nT, ivp_f:=(\<lambda>(t, x). - f (?mirror t, x))\<rparr>"
  have "continuous_on (op - (2 * t0) ` T \<times> X) (uminus o f o (\<lambda>(t, x). (2*t0 - t, x)))"
    using dt
    by (intro continuous_intros)
      (auto intro!: continuous_intros continuous_on_subset[OF continuous]
        simp: split_beta dist_real_def)
  then
  interpret neg: unique_on_open ?ni
    using local_lipschitz
    by unfold_locales
      (auto simp: openX open_neg_translation openT iv_defined split_beta
        local_lipschitz_uminus continuous_on_op_minus image_image
        intro: local_lipschitz_compose1)
  from neg.global_solution obtain J' M' where J':
    "J' = real_of_ereal ` {ereal (ivp_t0 ?ni) ..< M'}"
    "(\<And>x. x \<in> J' \<Longrightarrow> ivp_t0 ?ni \<le> x)"
    "J' \<subseteq> ivp_T ?ni"
    "is_interval J'"
    "ivp_t0 ?ni \<in> J'"
    "unique_solution (?ni\<lparr>ivp_T := J'\<rparr>)"
    "(\<And>K x. K \<subseteq> ivp_T ?ni \<Longrightarrow> is_interval K \<Longrightarrow> ivp_t0 ?ni \<in> K \<Longrightarrow>
      (\<And>x. x \<in> K \<Longrightarrow> ivp_t0 ?ni \<le> x) \<Longrightarrow>
      ivp.is_solution (?ni\<lparr>ivp_T := K\<rparr>) x \<Longrightarrow>
      K \<subseteq> J' \<and> (\<forall>t\<in>K. x t = ivp.solution (?ni\<lparr>ivp_T := J'\<rparr>) t))"
    by blast
  interpret neg_unique: unique_solution "?ni\<lparr>ivp_T := J'\<rparr>"
    by fact
  let ?mJ' = "?mirror ` J'"
  let ?mi = "i\<lparr>ivp_T := ?mJ'\<rparr>"
  interpret mi: ivp ?mi
    using J'(5) iv_defined
    by unfold_locales auto
  interpret mi: has_solution ?mi
  proof
    show "\<exists>x. mi.is_solution x"
      by (rule exI)
        (rule neg_unique.mirror_solution[simplified,
              OF neg_unique.is_solution_solution[simplified]])
  qed
  interpret mi: unique_solution ?mi
  proof
    fix x t assume misol: "mi.is_solution x" and t: "t \<in> mi.T"
    have [simp]: "op - (2 * t0) ` ?mJ' = J'" by force
    from mi.mirror_solution[OF misol]
    have "neg_unique.is_solution (x o ?mirror)"
      by simp
    from neg_unique.unique_solution[OF this]
    have "\<And>t. t \<in> J' \<Longrightarrow> (x o ?mirror) t = neg_unique.solution t"
      by auto
    moreover
    from mi.mirror_solution[OF mi.is_solution_solution, simplified]
    have "neg_unique.is_solution (mi.solution o ?mirror)"
      by simp
    from neg_unique.unique_solution[OF this, simplified]
    have "\<And>t. t \<in> J' \<Longrightarrow> (mi.solution o ?mirror) t = neg_unique.solution t"
      by auto
    ultimately
    have "\<And>t. t \<in> J' \<Longrightarrow> (x o ?mirror) t = (mi.solution o ?mirror) t"
      by simp
    thus "x t = mi.solution t" using t
      by auto
  qed
  let ?J = "J \<union> ?mJ'"
  show ?thesis
  proof
    have t0_in: "t0 \<in> J \<inter> op - (2 * t0) ` J'"
      using \<open>t0 \<in> J\<close> J'(5)
      by auto
    from t0_in have "t0 < M'" "t0 < M"
      by (auto simp: J(1) J'(1))
    have "J \<union> ?mJ' =
      real_of_ereal ` {ereal t0..<M} \<union> op - (2 * t0) ` real_of_ereal ` {ereal t0..<M'}"
      unfolding J(1) J'(1) split image_Un
      by simp
    also
    have right_ivl: "real_of_ereal ` {ereal t0..<M} = (if M = \<infinity> then {t0..} else {t0..<real_of_ereal M})"
    proof -
      have "{ereal t0..<M} = {ereal t0} \<union> {ereal t0 <..< M}"
        using \<open>t0 \<in> J\<close> J'(5) J(1) by auto
      also have "real_of_ereal ` \<dots> = (if M = \<infinity> then {t0 ..} else {t0 ..<real_of_ereal M})"
        using \<open>t0 < M\<close>
        by (cases M) (auto simp add: real_atLeastGreaterThan_eq)
      finally show ?thesis
        by (simp add: J)
    qed
    also
    have left_ivl: "op - (2 * t0) ` real_of_ereal ` {ereal t0..<M'} =
      (if M' = \<infinity> then {..t0} else {2 * t0 - real_of_ereal M'<..t0})"
    proof -
      have "{ereal t0..<M'} = {ereal t0} \<union> {ereal t0<..<M'}"
        using J'(1, 5)  by auto
      also have "real_of_ereal ` \<dots> = (if M' = \<infinity> then {t0 ..} else {t0 ..<real_of_ereal M'})"
        using \<open>t0 < M'\<close>
        by (cases M') (auto simp add: real_atLeastGreaterThan_eq)
      also have "op - (2 * t0) ` \<dots> =
        (if M' = \<infinity> then {.. t0} else {2 * t0 - real_of_ereal M' <.. t0})"
        by simp
      finally show ?thesis .
    qed
    also have
      "(if M = \<infinity> then {t0..} else {t0..<real_of_ereal M}) \<union>
       (if M' = \<infinity> then {..t0} else {2 * t0 - real_of_ereal M'<..t0}) =
        real_of_ereal ` {2 * t0 - M' <..< M}"
      using \<open>t0 < M\<close> \<open>t0 < M'\<close>
      by (cases M; cases M') (auto simp add: real_atLeastGreaterThan_eq)
    finally show ivl: "J \<union> ?mJ' = real_of_ereal ` {2 * t0 - M' <..< M}" .
    show "maximal_existence_interval (J \<union> op - (2 * t0) ` J')"
      unfolding maximal_existence_interval_def
    proof (intro conjI allI impI)
      show "?J \<subseteq> T" "t0 \<in> ?J"
        using J(3,5) J'(3,5) by auto
      show "is_interval (J \<union> op - (2 * t0) ` J')"
        using J(4) J'(4) t0_in
        by (auto intro!: is_real_interval_union)
      show "open (J \<union> ?mJ')"
        unfolding ivl
        by (auto intro!: open_real_image)
      interpret pi: unique_solution "i\<lparr>ivp_T:=J\<rparr>"
        by fact
      have t0_less_M: "M \<noteq> \<infinity> \<Longrightarrow> t0 < real_of_ereal M"
        using J(1) \<open>t0 \<in> J\<close> right_ivl
        by auto
      have "closure (real_of_ereal ` {ereal t0..<M}) = (if M = \<infinity> then {t0..} else {t0 .. real_of_ereal M})"
        by (simp add: t0_less_M right_ivl)
      moreover
      have "t0 \<in> J'" using J' by auto
      have *: "?mJ' = (if M' = \<infinity> then {..t0} else {2 * t0 - real_of_ereal M'<..t0})"
        by (simp add: J' left_ivl)
      have "M' \<noteq> \<infinity> \<Longrightarrow> 2 * t0 - real_of_ereal M' < t0"
        using J'(1) \<open>t0 \<in> J'\<close> \<open>t0 < M'\<close>
        by (cases M'; simp)
      hence "closure ?mJ' = (if M' = \<infinity> then {..t0} else {2 * t0 - real_of_ereal M'..t0})"
        by (simp add: *)
      ultimately have clos: "\<And>x. x \<in> closure J \<Longrightarrow> x \<in> closure ?mJ' \<Longrightarrow> x = t0"
        unfolding J(1) by (auto simp: split_ifs)
      have JJ': "\<And>x. 2 * t0 - x \<in> J \<Longrightarrow> x \<in> J' \<Longrightarrow> x = t0"
        using J(1) J'(1)
        apply (auto simp: algebra_simps)
        apply (rename_tac x y)
        apply (case_tac x; case_tac y; simp)
        done
      interpret glob: connected_unique_solutions "i\<lparr>ivp_T := J \<union> ?mJ'\<rparr>" "i\<lparr>ivp_T:=J\<rparr>" "?mi" t0
        using \<open>t0 \<in> J\<close> \<open>ivp_t0 ?ni \<in> J'\<close> pi.is_solutionD[OF pi.is_solution_solution] pi.iv_defined
          mi.is_solutionD[OF mi.is_solution_solution]
        by unfold_locales (auto simp: dest!: clos JJ')
      show "unique_solution (i\<lparr>ivp_T := J \<union> ?mJ'\<rparr>)"
        by unfold_locales
      fix K x
      assume K: "K \<subseteq> T" "is_interval K" "t0 \<in> K"
      assume K_sol: "ivp.is_solution (i\<lparr>ivp_T := K\<rparr>) x"
      have mJ': "is_interval ?mJ'" "t0 \<in> ?mJ'"
        using t0_in
        by (auto simp add: J'(4))
      from K have Kp: "K \<inter> {t0..} \<subseteq> T"  "is_interval (K \<inter> {t0..})"
        "t0 \<in> (K \<inter> {t0..})" "\<And>x. x \<in> K \<inter> {t0..} \<Longrightarrow> t0 \<le> x"
        by (auto simp: is_interval_ci is_interval_ic intro!: is_interval_inter J)
      have "ivp (i\<lparr>ivp_T := K\<rparr>)"
        by unfold_locales (auto simp: K iv_defined)
      then have "ivp.is_solution (i\<lparr>ivp_T := K, ivp_T := K \<inter> {t0..}\<rparr>) x"
        by (rule ivp.solution_on_subset) (auto intro!: K_sol K J)
      hence Kp_sol: "ivp.is_solution (i\<lparr>ivp_T := K \<inter> {t0..}\<rparr>) x"
        by simp
      from J(7)[OF Kp Kp_sol]
      have Kp_subset_unique:
        "K \<inter> {t0..} \<subseteq> J"
        "(\<forall>t\<in>K \<inter> {t0..}. x t = ivp.solution (i\<lparr>ivp_T := J\<rparr>) t)"
        by auto

      let ?mKp = "?mirror ` K \<inter> {t0..}"
      have Km: "?mKp \<subseteq> ?mirror ` T" "is_interval (?mirror ` K \<inter> {t0..})"
        "t0 \<in> ?mKp" "\<And>x. x \<in> ?mKp \<Longrightarrow> t0 \<le> x"
        using K
        by (auto simp: is_interval_ci
          intro!: is_interval_inter K)
      let ?mKi = "i\<lparr>ivp_f := \<lambda>(t, x). - f (2 * t0 - t, x), ivp_T := op - (2 * t0) ` K \<inter> {t0..}\<rparr>"
      interpret mKi: ivp ?mKi
        using K by unfold_locales (auto simp: iv_defined)
      interpret Ki: ivp "i\<lparr>ivp_T := K\<rparr>"
        by unfold_locales (auto simp: K iv_defined)
      from Ki.mirror_solution[OF K_sol]
      have **:
        "ivp.is_solution
          (i\<lparr>ivp_f := \<lambda>(t, x). - f (?mirror t, x), ivp_T := ?mirror ` K\<rparr>)
          (x \<circ> ?mirror)"
        by simp
      have "ivp (i\<lparr>ivp_f := \<lambda>(t, x). - f (2 * t0 - t, x), ivp_T := op - (2 * t0) ` K\<rparr>)"
        using K **
        by unfold_locales (auto simp: iv_defined)
      then have
        "ivp.is_solution
          (i\<lparr>ivp_f := \<lambda>(t, x). - f (?mirror t, x), ivp_T := ?mirror ` K, ivp_T := ?mirror ` K \<inter> {t0..}\<rparr>)
          (x \<circ> ?mirror)"
        apply (rule ivp.solution_on_subset)
        using K **
        by auto
      hence "mKi.is_solution (x o ?mirror)"
        by simp
      from J'(7)[simplified, OF Km this]
      have Km_unique': "op - (2 * t0) ` K \<inter> {t0..} \<subseteq> J'"
        "(\<forall>t\<in>op - (2 * t0) ` K \<inter> {t0..}.
          (x \<circ> op - (2 * t0)) t =
            ivp.solution (i\<lparr>ivp_f := \<lambda>(t, x). - f (2 * t0 - t, x), ivp_T := J'\<rparr>) t)"
        by auto
      hence Km_subset: "K \<inter> {..t0} \<subseteq> ?mJ'"
        by (auto simp: J' intro!: image_eqI[where x="2 * t0 - x" for x])
      have Km_unique: "(\<forall>t\<in>K \<inter> {..t0}. x t = ivp.solution (i\<lparr>ivp_T := ?mJ'\<rparr>) t)"
      proof safe
        fix t assume "t \<in> K" assume "t \<le> t0"
        {
          fix t' assume t': "t' \<in> ?mirror ` K \<inter> {t0..}"
          hence "(x o ?mirror) t' =
              ivp.solution
                (i\<lparr>ivp_f := \<lambda>(t, x). - f (2 * t0 - t, x), ivp_T := J'\<rparr>)
                t'"
            using Km_unique' by auto
          moreover
          have mmid: "\<And>X. ?mirror ` (?mirror ` X \<inter> {t0..}) = X \<inter> {..t0}"
            by force
          have "ivp.is_solution (i\<lparr>ivp_T := K \<inter> {..t0}\<rparr>) mi.solution"
            by (rule mi.solution_on_subset') (auto intro!: K Km_subset)
          then have "ivp.is_solution ?mKi
             (ivp.solution (i\<lparr>ivp_T := op - (2 * t0) ` J'\<rparr>) \<circ> op - (2 * t0))"
             by (intro mKi.solution_mirror) (auto simp: o_def mmid)
          from J'(7)[simplified, OF Km this] t'
          have "(ivp.solution (i\<lparr>ivp_T := ?mJ'\<rparr>) o ?mirror) t' =
              ivp.solution (i\<lparr>ivp_f := \<lambda>(t, x). - f (2 * t0 - t, x), ivp_T := J'\<rparr>) t'"
            by auto
          ultimately
          have "(x o ?mirror) t' = (ivp.solution (i\<lparr>ivp_T := ?mJ'\<rparr>) o ?mirror) t'"
            by simp
        }
        with \<open>t \<in> K\<close> \<open>t \<le> t0\<close>
        show "x t = ivp.solution (i\<lparr>ivp_T := op - (2 * t0) ` J'\<rparr>) t" by force
      qed
      have "{t0..} \<union> {..t0} = UNIV" by auto
      with Kp_subset_unique Km_subset have K_subset: "K \<subseteq> J \<union> op - (2 * t0) ` J'"
        by auto
      moreover
      have "(\<forall>t\<in>K. x t = ivp.solution (i\<lparr>ivp_T := J \<union> op - (2 * t0) ` J'\<rparr>) t)"
      proof safe
        fix t
        assume "t \<in> K"
        {
          assume "t \<in> J"
          with \<open>t \<in> K\<close>
          have "x t = ivp.solution (i\<lparr>ivp_T := J\<rparr>) t"
            by (metis Int_Collect J(2) Kp_subset_unique(2) atLeast_def)
        } moreover {
          assume "t \<notin> J"
          with \<open>t \<in> K\<close> K_subset have "x t = ivp.solution (i\<lparr>ivp_T := op - (2 * t0) ` J'\<rparr>) t"
            by (intro Km_unique[rule_format])
              (auto simp: glob.connection_def * split: if_split_asm)
        } ultimately
        show "x t = ivp.solution (i\<lparr>ivp_T := J \<union> op - (2 * t0) ` J'\<rparr>) t"
          using \<open>t \<in> K\<close> K_subset
          by (subst glob.connection_eq_solution[symmetric])
            (auto simp add: glob.connection_def)
      qed
      ultimately show "K \<subseteq> J \<union> ?mJ'" "(\<forall>t\<in>K. x t = ivp.solution (i\<lparr>ivp_T := J \<union> ?mJ'\<rparr>) t)"
        by auto
    qed
  qed
qed

end

end
