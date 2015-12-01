theory Picard_Lindeloef_Qualitative
imports Initial_Value_Problem
begin

subsection {* Picard-Lindeloef On Open Domains *}
text{*\label{sec:qpl}*}

subsubsection {* Local Solution with local Lipschitz *}
text{*\label{sec:qpl-lipschitz}*}

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

lemma cube_in_cball':
  fixes x::"'a::ordered_euclidean_space"
  assumes "0 < r"
  shows "\<exists>b > 0. b \<le> r \<and> (\<exists>B. B = (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> (\<forall>y \<in> {x - B..x + B}. y \<in> cball x r))"
proof (rule, safe)
  have "r / sqrt (real DIM('a)) \<le> r / 1"
    using assms DIM_positive by (intro divide_left_mono) auto
  thus "r / sqrt (real DIM('a)) \<le> r" by simp
next
  let ?B = "\<Sum>i\<in>Basis. (r / sqrt (real DIM('a))) *\<^sub>R i"
  show "\<exists>B. B = ?B \<and> (\<forall>y \<in> {x - B..x + B}. y \<in> cball x r)"
  proof (rule, safe)
    fix y::'a
    assume "y \<in> {x - ?B..x + ?B}"
    hence bounds: "x - ?B \<le> y" "y \<le> x + ?B"
      by auto
    show "y \<in> cball x r"
    proof (intro cube_in_cball)
      fix i :: 'a
      assume "i\<in> Basis"
      with bounds[simplified eucl_le[where y = y] eucl_le[where x = y]]
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

locale local_lipschitz = ivp +
  assumes lipschitz: "\<forall>t\<in>T. \<forall>x\<in>X. \<exists>u>0. \<exists>L\<ge>0. \<forall>t'\<in>cball t u \<inter> I.
    lipschitz (cball x u \<inter> X) (\<lambda>y. f (t', y)) L"

locale unique_on_open = ivp_open + local_lipschitz + continuous T X f
begin

lemma exists_unique_solution:
  assumes "t0 < t_max"
  shows "\<exists>t1\<in>{t0<..t_max}. {t0..t1} \<subseteq> T \<and> unique_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>)"
proof -
  from lipschitz have "\<exists>u > 0. \<exists>L \<ge> 0. \<forall>t\<in>cball t0 u \<inter> T. \<forall>x\<in>cball x0 u \<inter> X.
    \<forall>y\<in>cball x0 u \<inter> X. dist (f (t, x)) (f (t, y)) \<le> L * dist x y"
    using iv_defined by (simp add: lipschitz_def)
  then guess u .. note u = this
  from this[THEN conjunct2] guess L .. note L = this
  from open_Times[OF openT openX] have "open (T \<times> X)" .
  from this[THEN open_contains_cball_eq] iv_defined
  have "\<exists>e>0. cball (t0, x0) e \<subseteq> (T\<times>X)" by auto
  then guess v .. note v = this
  let ?C = "\<lambda>c. \<Sum>i\<in>Basis. c *\<^sub>R i"
  have "0 < Min {u, v, 1/(L+1)}" using u v L by simp
  hence
    "\<exists>b > 0. b \<le> Min {u, v, 1 / (2*(L+1))} \<and> (\<exists>B. B = ?C b \<and> (\<forall>p \<in> {(t0, x0) - B..(t0, x0) + B}. p \<in> cball (t0, x0) (Min {u, v, 1 / (2 *(L+1))})))"
    by (intro cube_in_cball') simp_all
  then guess a .. note a = this
  from this[THEN conjunct2, THEN conjunct2] guess A .. note A = this
  have inclusion: "\<forall>(t, x) \<in> {(t0, x0 - ?C a)..(t0 + a, x0 + ?C a)}. (t, x) \<in> cball (t0, x0) u \<inter> (T\<times>X)"
  proof (rule, rule)
    fix tx
    fix t x
    assume "tx \<in> {(t0, x0 - ?C a)..(t0 + a, x0 + ?C a)}" "tx = (t, x)"
    hence "(t, x) \<in> {(t0, x0) - A..(t0, x0) + A}"
      using A a
      by (auto simp add: fst_setsum snd_setsum setsum_Basis_prod_eq less_eq_prod_def)
    with A v show "(t, x)\<in>cball (t0, x0) u \<inter> (T\<times>X)" using iv_defined
      by force
  qed
  hence subset: "{(t0, x0 - ?C a)..(t0 + a, x0 + ?C a)} \<subseteq> cball (t0, x0) u \<inter> (T\<times>X)" by auto
  def R \<equiv> "{(t0, x0 - ?C a)..(t0 + a, x0 + ?C a)}"
  have "(t0, x0) \<in> R" using a by (auto simp: R_def intro!: setsum_nonneg scaleR_nonneg_nonneg)
  have "R \<subseteq> T\<times>X" using subset by (simp add: R_def)
  have "bounded (f ` R)"
    using continuous_on_subset[where t="R"] `R\<subseteq>T\<times>X` continuous
    by (auto intro: compact_Times compact_interval compact_imp_bounded
      compact_continuous_image simp add: R_def)
  then obtain B where f_bounded: "\<And>x t. (t, x) \<in> R \<Longrightarrow> norm (f (t, x)) \<le> B"
    by (auto simp add: bounded_iff)
  have "0 \<le> norm (f (t0, x0))" using norm_ge_zero[of "f (t0, x0)"] by simp
  also have "... \<le> B" using f_bounded[OF `(t0, x0) \<in> R`] .
  finally have "0 \<le> B" .
  obtain a' where a': "a' > 0" "a' < a / (B+1)" "a' < a"
  proof
    from `B\<ge>0`
    show "0 < min (a / (B + 2)) (a/2)" using a by simp
    show "min (a / (B + 2)) (a/2) < a / (B + 1)"
      using a `0\<le>B`
      by (auto intro!: divide_strict_left_mono simp add: min_less_iff_disj)
    show "min (a / (B + 2)) (a / 2) < a" using a by auto
  qed
      --{* new initial value problem *}
  def j \<equiv> "(i\<lparr>ivp_T := {t0..min (t0 + a') t_max}, ivp_X := {x0 - ?C a..x0 + ?C a}\<rparr>)"
  have "ivp_T j \<times> ivp_X j \<subseteq>R" using a' by (auto simp add: j_def R_def)
  with `R \<subseteq> T\<times>X` have "ivp_T j \<times> ivp_X j \<subseteq> T\<times>X" by simp
  with continuous have "continuous_on (ivp_T j \<times> ivp_X j) f"
    by (rule continuous_on_subset)
  moreover
  {
    fix t x y
    assume "t \<in> {t0..t0 + a}" "x \<in> {x0 - ?C a..x0 + ?C a}"
      "y \<in> {x0 - ?C a..x0 + ?C a}"
    with inclusion have "(t, x) \<in> cball (t0, x0) u \<inter> (T\<times>X)"
      "(t, y) \<in> cball (t0, x0) u \<inter> (T\<times>X)"
      by auto
    hence "t\<in>cball t0 u \<inter> T" "x\<in>cball x0 u \<inter> X" "y\<in>cball x0 u \<inter> X"
      by (auto simp: dist_Pair_Pair intro: order.trans
        real_sqrt_sum_squares_ge1 real_sqrt_sum_squares_ge2)
    with L have "dist (f (t, x)) (f (t, y)) \<le> L * dist x y" by auto
  }
  moreover
  from f_bounded have "\<And>x t. (t, x) \<in> R \<Longrightarrow> norm (f (t, x)) \<le> B + 1"
    by (metis add_increasing2 zero_le_one)
  ultimately
  interpret ivp_r: unique_on_rectangle j "min (t0 + a') t_max" a "B+1" L "ivp_X j"
    using a' a L `B\<ge>0` `t0 < t_max`
    by unfold_locales (auto simp: algebra_simps scaleR_setsum_right setsum_nonneg scaleR_nonneg_nonneg
      j_def eucl_le[of x0] eucl_le[where y=x0] R_def lipschitz_def)

  have "ivp_X j \<subseteq> X"
  proof safe
    fix x assume "x \<in> ivp_X j"
    hence "(t0, x) \<in> ivp_T j\<times>ivp_X j" using ivp_r.iv_defined
      by (simp add: j_def)
    thus "x \<in> X" using `ivp_T j \<times> ivp_X j \<subseteq> T\<times>X` by auto
  qed
  interpret ivp': ivp "i\<lparr>ivp_T:={t0..min (t0+a') t_max}\<rparr>"
    using a' iv_defined `t0 < t_max` by unfold_locales auto
  have "{t0..min (t0+a') t_max} \<subseteq> T"
  proof
    fix t
    assume "t \<in> {t0..min (t0+a') t_max}"
    hence "(t, x0) \<in> cball (t0, x0) v" using v a' a
      by (auto simp: cball_def dist_Pair_Pair dist_real_def)
    with v show "t \<in> T" by auto
  qed
  show ?thesis
    using a' ivp_r.is_solution_solution ivp_r.unique_solution
      ivp_r.is_solution_eq_is_solution_on_supersetdomain[OF `ivp_X j \<subseteq> X`]
      `{t0..min (t0+a') t_max} \<subseteq> T` `t0 < t_max`
    by (safe intro!: bexI[where x="min (t0 + a') t_max"] ivp'.unique_solutionI) (auto simp: j_def)
qed

subsubsection {* Global maximal solution with local Lipschitz*}
text{*\label{sec:qpl-global-solution}*}

definition PHI where
  "PHI = {(x, t1). t0 < t1 \<and> {t0..t1} \<subseteq> T \<and> ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) x}"

lemma PHI_notempty: "PHI \<noteq> {}"
proof -
  from exists_unique_solution[where t_max="t0+1"]
  obtain t1 where "unique_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>)"
    "t0 < t1" "{t0..t1} \<subseteq> T"
    by force
  then interpret i: unique_solution "i\<lparr>ivp_T:={t0..t1}\<rparr>" by simp
  from i.is_solution_solution `t0<t1` `{t0..t1} \<subseteq> T` have "(i.solution, t1) \<in> PHI"
    by (simp add: PHI_def)
  thus ?thesis by auto
qed

lemma maximal_existence_interval:
  assumes E: "\<forall>(x, t1) \<in> PHI. \<forall>(y, U) \<in> PHI. \<forall>t \<in> {t0..t1} \<inter> {t0..U}. x t = y t"
  defines "J \<equiv> \<Union>(x, t1)\<in>PHI. {t0..t1}"
  defines "j \<equiv> i\<lparr>ivp_T:=J\<rparr>"
  shows "unique_solution j"
  "\<And>x t1 t. (x, t1) \<in> PHI \<Longrightarrow> t \<in> {t0..t1} \<Longrightarrow> x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t"
proof -
  from PHI_def have PHI: "PHI = {xT. t0 < snd xT \<and> {t0..snd xT} \<subseteq> T \<and>
    ivp.is_solution (i\<lparr>ivp_T:={t0..snd xT}\<rparr>) (fst xT)}"
    by auto
  {
    fix x y t t1
    assume
      "ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) x"
      "ivp.is_solution (i\<lparr>ivp_T:={t0..t1}\<rparr>) y"
      "t \<in> {t0..t1}" "t0<t1" "{t0..t1} \<subseteq> T"
    moreover
    hence "(x, t1) \<in> PHI" "(y, t1) \<in> PHI"
      by (auto simp: PHI)
    ultimately have "x t = y t" using E by force
  } note sol_eq = this
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
    then guess ya .. note ya = this
    with E[simplified Ball_def, THEN spec, THEN mp, OF ya(1)]
    have E':"\<forall>zb\<in>PHI. x \<in> {t0..snd ya} \<inter> {t0..snd zb} \<longrightarrow> fst ya x = fst zb x" by (simp add: Ball_def)
    show "\<exists>y. \<forall>za\<in>PHI. x \<le> snd za \<longrightarrow> y = fst za x"
    proof (rule, rule, rule)
      fix zb
      assume zb: "zb \<in> PHI" "x \<le> snd zb"
      with E'[simplified Ball_def, THEN spec, THEN mp, OF `zb \<in> PHI`]
      have "x \<in> {t0..snd ya} \<inter> {t0..snd zb} \<longrightarrow> fst ya x = fst zb x" by (simp add: Ball_def)
      thus "fst ya x = fst zb x" using xI ya zb J_def PHI_def by auto
    qed
  qed
  then guess y .. note y = this
  hence equal: "\<forall>s\<in>PHI. \<forall>t \<in> {t0..snd s}. y t = fst s t" using J_def PHI_def
    by simp
  {
    fix x
    assume "x \<in> J"
    have "\<exists>s\<in>PHI. x < snd s"
    proof -
      obtain s where s: "s \<in> PHI" "x \<le> snd s" using `x \<in> J`
        by (force simp add: PHI_def J_def)
      def i1 \<equiv> "i\<lparr>ivp_T:={t0..snd s}\<rparr>"
      interpret i1: ivp i1
        using s iv_defined `x \<in> J`
        by unfold_locales (auto simp: PHI_def J_def i1_def)
      from `s \<in> PHI` have "t0 < snd s" by (simp add: PHI)
      from `s \<in> PHI` have "{t0..snd s} \<subseteq> T" by (simp add: PHI)
      from `s \<in> PHI` have "i1.is_solution (fst s)" by (simp add: PHI i1_def)
      then interpret i1: unique_solution i1
      proof (intro i1.unique_solutionI, simp)
        fix y t
        assume "i1.is_solution y"
        assume "t \<in> i1.T"
        hence "t \<in> {t0..snd s}" by (simp add: i1_def)
        with sol_eq `i1.is_solution (fst s)` `i1.is_solution y`
          `t0 < snd s` `{t0..snd s} \<subseteq> T`
        show "y t = fst s t" by (simp add: i1_def)
      qed
      show ?thesis
      proof (cases "x = snd s")
        assume "x = snd s"
        def i2' \<equiv> "i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s)\<rparr>"
        interpret i2': unique_on_open i2'
          using iv_defined `x \<in> J` continuous openT openX lipschitz
            i1.is_solutionD(3)[OF `i1.is_solution (fst s)`] `s \<in> PHI`
          by unfold_locales (auto simp: PHI i1_def i2'_def)
        from i2'.exists_unique_solution[where t_max = "snd s + 1"]
        obtain t1 where t1: "t1 > snd s" "{snd s..t1} \<subseteq> T" "unique_solution
          (i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s), ivp_T:={snd s..t1}\<rparr>)"
          by (auto simp: i2'_def)
        def i2 \<equiv> "i\<lparr>ivp_t0:=snd s, ivp_x0:=fst s (snd s), ivp_T:={snd s..t1}\<rparr>"
        interpret i2: unique_solution i2 using t1
          by (simp add: i2_def i2'_def)
        def ic \<equiv> "i\<lparr>ivp_T:={t0..t1}\<rparr>"
        interpret ic: ivp_on_interval ic t1
          using iv_defined `t1 > snd s` `snd s > t0`
          by unfold_locales (auto simp: ic_def)
        interpret ic: connected_unique_solutions ic i1 i2 "snd s" t1
          using i1.unique_solution[OF `i1.is_solution (fst s)`]
            `snd s > t0` `t1 > snd s`
            i1.is_solution_solution
          by unfold_locales (auto simp: i1_def i2_def ic_def)
        have "(ic.solution, t1) \<in> PHI"
          using `t0 < snd s` `{t0..snd s} \<subseteq> T` t1 ic.is_solution_solution
          by (force simp add: PHI ic_def)
        thus ?thesis using `x = snd s`  `snd s < t1` by force
      qed (insert s, force)
    qed
  } note continuable=this

  interpret j: ivp j
    using iv_defined PHI_notempty
    by (unfold_locales, auto simp: j_def J_def PHI_def) force
  have "j.is_solution y"
  proof (intro j.is_solutionI)
    from PHI_notempty have "\<exists>ya. ya \<in> PHI" unfolding ex_in_conv .
    then guess ya .. note ya = this
    then interpret iya: ivp "i\<lparr>ivp_T:={t0..(snd ya)}\<rparr>"
      using iv_defined by unfold_locales (auto simp: PHI)
    from ya have "iya.is_solution (fst ya)" by (simp add: PHI)
    from ya equal have "y t0 = fst ya t0" by (auto simp: PHI)
    thus "y j.t0 = j.x0"
      using iv_defined iya.iv_defined
      using iya.is_solutionD(1)[OF `iya.is_solution (fst ya)`]
      by (auto simp: j_def)
  next
    fix x
    assume "x \<in> j.T"
    hence "x \<in> J" by (simp add: j_def)
    note continuable[OF this]
    then guess ya .. note ya = this
    then interpret iya: ivp "i\<lparr>ivp_T:={t0..snd ya}\<rparr>"
      using iv_defined by unfold_locales (auto simp: PHI)
    from ya have "iya.is_solution (fst ya)" by (simp add: PHI)
    from iya.is_solutionD(2)[OF this]
    have deriv: "(fst ya has_vector_derivative f (x, fst ya x)) (at x within {t0..snd ya})"
      using `x \<in> j.T` J_def ya by (auto simp add: j_def)
    moreover
    from `x \<in> j.T` ya have "x\<in>{t0..<snd ya}" by (auto simp add: J_def j_def)
    with equal ya have y_eq_x: "y x = fst ya x" by simp
    ultimately
    show "(y has_vector_derivative j.f (x, y x)) (at x within j.T)"
      apply (simp (no_asm) add: j_def J_def)
      unfolding J
      unfolding has_vector_derivative_def
      unfolding has_derivative_within'
    proof (safe)
      fix e::real
      assume "e > 0" "\<forall>e>0. \<exists>d>0. \<forall>x'\<in>{t0..snd ya}.
        0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
        norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / norm (x' - x)
        < e"
      hence "\<exists>d>0. \<forall>x'\<in>{t0..snd ya}.
        x' \<noteq> x \<and> \<bar>x' - x\<bar> < d \<longrightarrow>
        norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e" by auto
      then guess d .. note d = this
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
            norm (fst ya x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e" by auto
          moreover
          from A have "x' \<noteq> x \<and> \<bar>x' - x\<bar> < d" by simp
          moreover
          from A have "x'\<in>{t0..snd ya}" by auto
          with A have "y x' = fst ya x'" using equal ya by fast
          ultimately show
            "norm (y x' - fst ya x - (x' - x) *\<^sub>R f (x, fst ya x)) / \<bar>x' - x\<bar> < e" by simp
        qed
        thus "\<forall>x'\<in>\<Union>s\<in>PHI. {t0..snd s}.
          0 < norm (x' - x) \<and> norm (x' - x) < Min {d, snd ya - x} \<longrightarrow>
          norm (y x' - y x - (x' - x) *\<^sub>R f (x, y x)) / norm (x' - x) < e" using y_eq_x by simp
      qed
    qed simp
    from iya.is_solutionD(3)[OF `iya.is_solution (fst ya)`]
    have "fst ya x \<in> X"
      using `x \<in> j.T` ya by (auto simp: PHI_def j_def J_def)
    moreover
    from `x \<in> j.T` ya have "x\<in>{t0..snd ya}" by (auto simp: PHI_def j_def J_def)
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
    have"t0 \<le> t" using `t \<in> J` unfolding J_def by auto
    from x't1 have "ix'.is_solution x'" by (simp add: PHI)
    assume "j.is_solution x"
    hence "ix'.is_solution x"
      using x't1 `t \<in> J` `{t0..t1} \<subseteq> T`
      by (intro j.solution_on_subset[where T'="{t0..t1}", simplified j_def,
        simplified]) (auto simp: J_def j_def)
    from equal x't1 `t\<in>j.T` have "y t = x' t" by (auto simp: j_def J_def)
    thus "x t = y t"
      using sol_eq[OF `ix'.is_solution x'` `ix'.is_solution x`] `t < t1` `t \<in> j.T`
      `{t0..t1} \<subseteq> T`
      by (auto simp: j_def J_def)
  qed
  then interpret j: unique_solution j by simp
  fix x t1 t
  assume "(x, t1) \<in> PHI" "t \<in> {t0..t1}"
  then interpret i': ivp "i\<lparr>ivp_T := {t0..t1}\<rparr>" using iv_defined
    by unfold_locales auto
  from `(x, t1) \<in> PHI` have x: "i'.is_solution x" "t0 < t1" "{t0..t1} \<subseteq> T"
    by (auto simp add: PHI_def)
  have "i'.is_solution j.solution"
    apply (rule j.solution_on_subset[simplified j_def, simplified])
    using x `(x, t1) \<in> PHI` j.is_solution_solution
    by (auto simp: j_def J_def)
  from sol_eq[OF x(1) this `t \<in> {t0..t1}` `t0 < t1` `{t0..t1} \<subseteq> T`]
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
    then guess x1 .. note x1 = this

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
    ultimately
    have "\<exists>m\<in>{t \<in> {t0..x1}. norm (y t - z t) = 0}.
      \<forall>y\<in>{t \<in> {t0..x1}. norm (y t - z t) = 0}.
      dist x1 m \<le> dist x1 y"
      by (intro distance_attains_inf) (auto intro!: distance_attains_inf
        simp: ex_in_conv[symmetric])
    then guess x_max .. note max = this
    have "z x_max = y x_max" using max by simp
    have "x_max \<in> {t0..min a b}" "x_max \<in> T"
      using x1 z_sol y_sol max subsets by auto
    with x1 i1.is_solutionD[OF y_sol] have "y x_max \<in> X"
      by (simp add: is_solution_def)
    with max have "z x_max \<in> X" by simp
    def i3' \<equiv> "i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max\<rparr>"
    interpret i3': unique_on_open i3'
      using iv_defined continuous openT openX lipschitz
        i1.is_solutionD(3)[OF y_sol] `x_max \<in> T` `y x_max \<in> X`
      by unfold_locales (auto simp: PHI_def i3'_def)
    have "x_max < x1" using x1 max by auto
    with i3'.exists_unique_solution[where t_max = x1]
    obtain t1 where t1: "t1 \<in>{x_max<..x1}" "{x_max..t1} \<subseteq> T" "unique_solution
      (i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max, ivp_T:={x_max..t1}\<rparr>)"
      by (auto simp: i3'_def)
    def i3 \<equiv> "i\<lparr>ivp_t0:=x_max, ivp_x0:=y x_max, ivp_T:={x_max..t1}\<rparr>"
    from t1 interpret i3: unique_solution i3
      by (simp add: i3_def)
    have "x_max \<in> {x_max..t1}" using t1 by simp
    have "i3.is_solution y" unfolding i3_def
      using `y x_max \<in> X` `x_max \<in> {t0..min a b}` y_sol t1 x1(1)
        i1.restriction_of_solution by auto
    have "i3.is_solution z" unfolding i3_def
      using `z x_max \<in> X` `x_max \<in> {t0..min a b}` z_sol t1 x1(1)
        i2.restriction_of_solution
      by (auto simp: `z x_max = y x_max`[symmetric])
    let ?m = "(x_max + t1) / 2"
    have xm1: "?m \<in> {t0..t1}" using max `x_max \<in> {x_max..t1}` by simp
    have xm2: "?m \<in> {x_max..t1}" using max `x_max \<in> {x_max..t1}` by simp
    from i3.unique_solution[OF `i3.is_solution y`, of ?m]
      i3.unique_solution[OF `i3.is_solution z`, of ?m]
      `x_max \<in> {x_max..t1}`
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
  thus "y t = z t" using `t \<in> {t0..a}` `t \<in> {t0..b}` by simp
qed

lemma global_solution:
  obtains J where
  "is_interval J"
  "t0 \<in> J"
  "\<And>x. x \<in> J \<Longrightarrow> t0 \<le> x"
  "unique_solution (i\<lparr>ivp_T:=J\<rparr>)"
  "\<And>K x. K \<subseteq> T \<Longrightarrow> is_interval K \<Longrightarrow> t0 \<in> K \<Longrightarrow> (\<And>x. x \<in> K \<Longrightarrow> t0 \<le> x) \<Longrightarrow>
    ivp.is_solution (i\<lparr>ivp_T:=K\<rparr>) x \<Longrightarrow>
    K \<subseteq> J \<and> (\<forall>t\<in>K. x t = ivp.solution (i\<lparr>ivp_T:=J\<rparr>) t)"
proof -
  def J \<equiv> "(\<Union>(x, t1)\<in>PHI. {t0..t1})"
  show ?thesis
  proof
    show "is_interval J"
      unfolding is_interval_def J_def PHI_def
      by auto (metis (full_types) xt1(6))+
    show "t0 \<in> J" using PHI_notempty
      by (force simp add: PHI_def J_def)
  next
    fix x assume "x \<in> J" thus "t0 \<le> x"
      by (auto simp add: J_def PHI_def)
  next
    show "unique_solution (i\<lparr>ivp_T := J\<rparr>)"
      using maximal_existence_interval[OF E] by (simp add: J_def)
    then interpret j: unique_solution "i\<lparr>ivp_T := J\<rparr>" by simp
    fix K z
    assume "K \<subseteq> T"
    def y \<equiv> "ivp.solution (i\<lparr>ivp_T := J\<rparr>)"
    assume interval: "is_interval K"
    assume Inf: "t0 \<in> K" "\<And>x. x \<in> K \<Longrightarrow> t0 \<le> x"
    assume z_sol: "ivp.is_solution (i\<lparr>ivp_T := K\<rparr>) z"
    then interpret k: has_solution "i\<lparr>ivp_T := K\<rparr>"
      apply unfold_locales
      using iv_defined Inf
      by auto
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
        using k.solution_on_subset z_sol subset `t0 < xM` by (simp add: k1_def)
      then interpret k1: has_solution k1 by unfold_locales auto
      interpret k2': unique_on_open "i\<lparr>ivp_t0:=xM, ivp_x0:=z xM\<rparr>"
        using `t0 < xM` k1.is_solutionD[OF `k1.is_solution z`]
          lipschitz openT openX continuous `K \<subseteq> T` `xM \<in> K`
        by unfold_locales (auto simp: k1_def)
      from k2'.exists_unique_solution[where t_max = "xM + 1", simplified]
      obtain t1 where t1: "t1 \<in> {xM<..xM+1}" "{xM..t1} \<subseteq> T"
        "unique_solution (i\<lparr>ivp_t0 := xM, ivp_x0 := z xM, ivp_T := {xM..t1}\<rparr>)"
        by auto
      def k2\<equiv>"i\<lparr>ivp_t0 := xM, ivp_x0 := z xM, ivp_T := {xM..t1}\<rparr>"
      from t1 interpret k2: unique_solution k2 by (simp add: k2_def)
      def kc \<equiv> "i\<lparr>ivp_T:={t0..t1}\<rparr>"
      interpret kc: connected_solutions kc k1 k2 xM t1 z
        using k1.is_solution_solution iv_defined `k1.is_solution z` `t0<xM` t1
        by unfold_locales (auto simp: k1_def k2_def kc_def)
      have "{t0..t1} \<subseteq> T"
      proof -
        have "{t0..t1} = {t0..xM} \<union> {xM..t1}" using t1 `t0 < xM` by auto
        thus ?thesis using `{t0..xM} \<subseteq> K` `{xM..t1} \<subseteq> T` `K \<subseteq> T` by simp
      qed
      hence concrete_sol: "(kc.connection, t1) \<in> PHI"
        using `t0<xM` t1 `{t0..xM} \<subseteq> K` `K \<subseteq> T` kc.is_solution_connection
        by (auto simp add: PHI_def kc_def)
      moreover have "xM \<in> {t0..<snd (kc.connection, t1)}" using `t0<xM` t1 by simp
      ultimately
      show "xM \<in> J" by (force simp: PHI_def J_def)
      have "xM \<in> {t0..t1}" using t1 `t0 < xM` by simp
      from maximal_existence_interval[OF E] J_def y_def concrete_sol this
      show "z xM = y xM" by (simp add: kc.connection_def)
    next
      fix x
      assume "x \<in> K" "\<not> t0 < x"
      hence "x = t0" using Inf(2)[OF `x\<in>K`] by simp
      thus "x \<in> J" using PHI_notempty by (force simp: J_def PHI_def)
      from j.solution_t0 k.is_solutionD[OF z_sol]
      show "z x = y x" by (simp add: y_def `x = t0`)
    qed
    thus "K \<subseteq> J \<and> (\<forall>t\<in>K. z t = ivp.solution (i\<lparr>ivp_T := J\<rparr>) t)"
      by (auto simp: y_def)
  qed
qed

end

end
