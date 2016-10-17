section\<open>Initial Value Problems\<close>
theory Initial_Value_Problem
imports "../ODE_Auxiliarities"
begin

lemma closed_segment_translation_zero: "z \<in> {z + a--z + b} \<longleftrightarrow> 0 \<in> {a -- b}"
  by (metis add.right_neutral closed_segment_translation_eq)

lemma closed_segment_subset_interval: "is_interval T \<Longrightarrow> a \<in> T \<Longrightarrow> b \<in> T \<Longrightarrow> closed_segment a b \<subseteq> T"
  by (rule closed_segment_subset) (auto intro!: closed_segment_subset is_interval_convex)

definition half_open_segment::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--<_})")
  where "half_open_segment a b = {a -- b} - {b}"

lemma half_open_segment_real:
  fixes a b::real
  shows "{a --< b} = (if a \<le> b then {a ..< b} else {b <.. a})"
  by (auto simp: half_open_segment_def closed_segment_real)

lemma closure_half_open_segment:
  fixes a b::real
  shows "closure {a --< b} = (if a = b then {} else {a -- b})"
  unfolding closed_segment_real if_distrib half_open_segment_real
  unfolding cond_application_beta
  by simp

lemma half_open_segment_subset[intro, simp]:
  "{t0--<t1} \<subseteq> {t0 -- t1}"
  "x \<in> {t0--<t1} \<Longrightarrow> x \<in> {t0 -- t1}"
  by (auto simp: half_open_segment_def)

lemma half_open_segment_closed_segmentI:
  "t \<in> {t0 -- t1} \<Longrightarrow> t \<noteq> t1 \<Longrightarrow> t \<in> {t0 --< t1}"
  by (auto simp: half_open_segment_def)

lemma islimpt_half_open_segment:
  fixes t0 t1 s::real
  assumes "t0 \<noteq> t1" "s \<in> {t0--t1}"
  shows "s islimpt {t0--<t1}"
proof -
  have "s islimpt {t0..<t1}" if "t0 \<le> s" "s \<le> t1" for s
  proof -
    have *: "{t0..<t1} - {s} = {t0..<s} \<union> {s<..<t1}"
      using that by auto
    show ?thesis
      using that \<open>t0 \<noteq> t1\<close> *
      by (cases "t0 = s") (auto simp: islimpt_in_closure)
  qed
  moreover have "s islimpt {t1<..t0}" if "t1 \<le> s" "s \<le> t0" for s
  proof -
    have *: "{t1<..t0} - {s} = {t1<..<s} \<union> {s<..t0}"
      using that by auto
    show ?thesis
      using that \<open>t0 \<noteq> t1\<close> *
      by (cases "t0 = s") (auto simp: islimpt_in_closure)
  qed
  ultimately show ?thesis using assms
    by (auto simp: half_open_segment_real closed_segment_real)
qed

lemma
  mem_half_open_segment_eventually_in_closed_segment:
  fixes t::real
  assumes "t \<in> {t0--<t1'}"
  shows "\<forall>\<^sub>F t1' in at t1' within {t0--<t1'}. t \<in> {t0--t1'}"
  unfolding half_open_segment_real
proof (split if_split, safe)
  assume le: "t0 \<le> t1'"
  with assms have t: "t0 \<le> t" "t < t1'"
    by (auto simp: half_open_segment_real)
  then have "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t0 \<le> t"
    by simp
  moreover
  from tendsto_ident_at \<open>t < t1'\<close>
  have "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t < t1'"
    by (rule order_tendstoD)
  ultimately show "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t \<in> {t0--t1'}"
    by eventually_elim (auto simp add: closed_segment_real)
next
  assume le: "\<not> t0 \<le> t1'"
  with assms have t: "t \<le> t0" "t1' < t"
    by (auto simp: half_open_segment_real)
  then have "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t \<le> t0"
    by simp
  moreover
  from tendsto_ident_at \<open>t1' < t\<close>
  have "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t1' < t"
    by (rule order_tendstoD)
  ultimately show "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t \<in> {t0--t1'}"
    by eventually_elim (auto simp add: closed_segment_real)
qed

lemma closed_segment_half_open_segment_subsetI:
  fixes x::real shows "x \<in> {t0--<t1} \<Longrightarrow> {t0--x} \<subseteq> {t0--<t1}"
  by (auto simp: half_open_segment_real closed_segment_real split: if_split_asm)

lemma dist_component_le:
  fixes x y::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  using assms
  by (auto simp: euclidean_dist_l2[of x y] intro: member_le_setL2)

lemma sum_inner_Basis_one: "i \<in> Basis \<Longrightarrow> (\<Sum>x\<in>Basis. x \<bullet> i) = 1"
  by (subst sum.mono_neutral_right[where S="{i}"])
    (auto simp: inner_not_same_Basis)

lemma cball_in_cbox:
  fixes y::"'a::euclidean_space"
  shows "cball y r \<subseteq> cbox (y - r *\<^sub>R One) (y + r *\<^sub>R One)"
  unfolding scaleR_sum_right interval_cbox cbox_def
proof safe
  fix x i::'a assume "i \<in> Basis" "x \<in> cball y r"
  with dist_component_le[OF \<open>i \<in> Basis\<close>, of y x]
  have "dist (y \<bullet> i) (x \<bullet> i) \<le> r" by (simp add: mem_cball)
  thus "(y - sum (op *\<^sub>R r) Basis) \<bullet> i \<le> x \<bullet> i"
    "x \<bullet> i \<le> (y + sum (op *\<^sub>R r) Basis) \<bullet> i"
    by (auto simp add: inner_diff_left inner_add_left inner_sum_left
      sum_distrib_left[symmetric] sum_inner_Basis_one \<open>i\<in>Basis\<close> dist_real_def)
qed

lemma centered_cbox_in_cball:
  shows "cbox (- r *\<^sub>R One) (r *\<^sub>R One::'a::euclidean_space) \<subseteq>
    cball 0 (sqrt(DIM('a)) * r)"
proof
  fix x::'a
  have "norm x \<le> sqrt(DIM('a)) * infnorm x"
  by (rule norm_le_infnorm)
  also
  assume "x \<in> cbox (- r *\<^sub>R One) (r *\<^sub>R One)"
  hence "infnorm x \<le> r"
    by (auto simp: infnorm_def mem_box intro!: cSup_least)
  finally show "x \<in> cball 0 (sqrt(DIM('a)) * r)"
    by (auto simp: dist_norm mult_left_mono mem_cball)
qed


subsection \<open>Lipschitz continuity\<close>\<comment>\<open>TODO: move to \<open>Analysis\<close>?!\<close>
text\<open>\label{sec:lipschitz}\<close>

definition lipschitz
  where "lipschitz t f L \<longleftrightarrow> (0 \<le> L \<and> (\<forall>x \<in> t. \<forall>y\<in>t. dist (f x) (f y) \<le> L * dist x y))"

lemma lipschitzI:
  assumes "\<And>x y. x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> dist (f x) (f y) \<le> L * dist x y"
  assumes "0 \<le> L"
  shows "lipschitz t f L"
using assms unfolding lipschitz_def by auto

lemma lipschitzD:
  assumes "lipschitz t f L"
  assumes "x \<in> t" "y \<in> t"
  shows "dist (f x) (f y) \<le> L * dist x y"
using assms unfolding lipschitz_def by auto

lemma lipschitz_nonneg:
  assumes "lipschitz t f L"
  shows "0 \<le> L"
using assms unfolding lipschitz_def by auto

lemma lipschitz_mono:
  assumes "lipschitz D f M"
  assumes "D' \<subseteq> D" "M \<le> L"
  shows "lipschitz D' f L"
proof (rule lipschitzI)
  from lipschitz_nonneg[OF assms(1)] \<open>M \<le> L\<close> show "0 \<le> L" by simp
  fix x y assume "x \<in> D'" "y \<in> D'"
  then have "x \<in> D" "y \<in> D" using \<open>D' \<subseteq> D\<close> by auto
  from lipschitzD[OF assms(1) this] have "dist (f x) (f y) \<le> M * dist x y" .
  also have "\<dots> \<le> L * dist x y"
    by (auto intro!: mult_right_mono \<open>M \<le> L\<close>)
  finally show "dist (f x) (f y) \<le> L * dist x y" .
qed

lemma lipschitz_subset:
  assumes "lipschitz D f L"
  assumes "D' \<subseteq> D"
  shows "lipschitz D' f L"
  using lipschitz_mono[OF assms order_refl] .

lemma lipschitz_imp_continuous:
  assumes "lipschitz X f L"
  assumes "x \<in> X"
  shows "continuous (at x within X) f"
  unfolding continuous_within_eps_delta
proof safe
  fix e::real
  assume "0 < e"
  show "\<exists>d>0. \<forall>x'\<in>X. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
  proof (cases "L > 0")
    case True
    thus ?thesis
      using \<open>0 < e\<close> using assms
      by (force intro!: exI[where x="e / L"] divide_pos_pos
        dest!: lipschitzD simp: field_simps)
  next
    case False
    thus ?thesis
    proof (safe intro!: exI[where x="1"] zero_less_one)
      fix x' assume "x' \<in> X"
      note lipschitzD[OF assms(1) \<open>x' \<in> X\<close> \<open>x \<in> X\<close>]
      also have "L * dist x' x \<le> 0"
        using False by (auto simp: not_less mult_nonpos_nonneg)
      also note \<open>0 < e\<close>
      finally show "dist (f x') (f x) < e" .
    qed
  qed
qed

lemma lipschitz_imp_continuous_on:
  assumes "lipschitz t f L"
  shows "continuous_on t f"
  using lipschitz_imp_continuous[OF assms]
  by (metis continuous_on_eq_continuous_within)

lemma lipschitz_norm_leI:
  assumes "lipschitz t f L"
  assumes "x \<in> t" "y \<in> t"
  shows "norm (f x - f y) \<le> L * norm (x - y)"
  using lipschitzD[OF assms]
  by (simp add: dist_norm)

lemma lipschitz_uminus:
  fixes f::"_ \<Rightarrow> 'b::real_normed_vector"
  shows "lipschitz t (\<lambda>x. - f x) L \<longleftrightarrow> lipschitz t f L"
  by (auto intro!: lipschitzI intro: lipschitz_nonneg dest: lipschitzD
    simp: dist_minus)

lemma lipschitz_uminus':
  fixes f::"_ \<Rightarrow> 'b::real_normed_vector"
  shows "lipschitz t (- f) L \<longleftrightarrow> lipschitz t f L"
  by (auto intro!: lipschitzI intro: lipschitz_nonneg dest: lipschitzD
    simp: dist_minus)

lemma nonneg_lipschitz:
  assumes "lipschitz X f L"
  shows "lipschitz X f (abs L)"
  using assms lipschitz_nonneg by fastforce

lemma pos_lipschitz:
  assumes "lipschitz X f L"
  shows "lipschitz X f (abs L + 1)"
  using assms
proof (auto simp: lipschitz_def, goal_cases)
  case (1 x y)
  hence "dist (f x) (f y) \<le> L * dist x y"
    by auto
  also have "\<dots> \<le> (abs L + 1) * dist x y"
    by (rule mult_right_mono) auto
  finally show ?case by (simp add: lipschitz_nonneg[OF assms])
qed

lemma lipschitz_uniformly_continuous_on:
  assumes "lipschitz X f L"
  shows "uniformly_continuous_on X f"
  unfolding uniformly_continuous_on_def
proof safe
  fix e::real
  assume "0 < e"
  define L' where "L' \<equiv> L + 1"
  have "L' > 0" using lipschitz_nonneg[OF assms] by (simp add: L'_def)
  from assms have l: "lipschitz X f L'"
    by (rule lipschitz_mono) (auto simp: L'_def)
  show "\<exists>d>0. \<forall>x\<in>X. \<forall>x'\<in>X. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
    using lipschitzD[OF l] \<open>L' > 0\<close> \<open>0 < e\<close>
    by (force intro!: exI[where x="e/L'"] simp: field_simps)
qed

lemma bounded_derivative_imp_lipschitz:
  assumes "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative f' x) (at x within X)"
  assumes convex: "convex X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> onorm (f' x) \<le> C" "0 \<le> C"
  shows "lipschitz X f C"
proof (rule lipschitzI)
  show "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> dist (f x) (f y) \<le> C * dist x y"
    by (auto intro!: assms differentiable_bound[unfolded dist_norm[symmetric], OF convex])
qed fact

lemma bounded_vderiv_on_imp_lipschitz:
  assumes "(f has_vderiv_on f') X"
  assumes convex: "convex X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> norm (f' x) \<le> C" "0 \<le> C"
  shows "lipschitz X f C"
  using assms
  by (auto simp: has_vderiv_on_def has_vector_derivative_def onorm_scaleR_left onorm_id
    intro!: bounded_derivative_imp_lipschitz[where f' = "\<lambda>x d. d *\<^sub>R f' x"])


subsection \<open>Local Lipschitz continuity (uniformly for a family of functions)\<close>

text \<open>TODO: distinguish local Lipschitz continuity and uniform local Lipschitz continuity\<close>

definition local_lipschitz::
  "'a::metric_space set \<Rightarrow> 'b::metric_space set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c::metric_space) \<Rightarrow> bool"
  where
  "local_lipschitz T X f \<equiv> \<forall>x \<in> X. \<forall>t \<in> T. \<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> T.
    lipschitz (cball x u \<inter> X) (f t) L"

lemma local_lipschitzI:
  assumes "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> \<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> T. lipschitz (cball x u \<inter> X) (f t) L"
  shows "local_lipschitz T X f"
  using assms
  unfolding local_lipschitz_def
  by auto

lemma local_lipschitzE:
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes "t \<in> T" "x \<in> X"
  obtains u L where "u > 0" "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> lipschitz (cball x u \<inter> X) (f s) L"
  using assms local_lipschitz local_lipschitz_def
  by metis

lemma local_lipschitz_continuous_on:
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes "t \<in> T"
  shows "continuous_on X (f t)"
  unfolding continuous_on_def
proof safe
  fix x assume "x \<in> X"
  from local_lipschitzE[OF local_lipschitz \<open>t \<in> T\<close> \<open>x \<in> X\<close>] obtain u L
    where "0 < u"
    and L: "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> lipschitz (cball x u \<inter> X) (f s) L"
    by metis
  have "x \<in> ball x u" using \<open>0 < u\<close> by simp
  from lipschitz_imp_continuous_on[OF L]
  have tendsto: "(f t \<longlongrightarrow> f t x) (at x within cball x u \<inter> X)"
    using \<open>0 < u\<close> \<open>x \<in> X\<close> \<open>t \<in> T\<close>
    by (auto simp: continuous_on_def)
  then show "(f t \<longlongrightarrow> f t x) (at x within X)"
    using \<open>x \<in> ball x u\<close>
    by (rule tendsto_within_nhd) (auto simp: ball_subset_cball)
qed

lemma
  local_lipschitz_compose1:
  assumes ll: "local_lipschitz (g ` T) X (\<lambda>t. f t)"
  assumes g: "continuous_on T g"
  shows "local_lipschitz T X (\<lambda>t. f (g t))"
proof (rule local_lipschitzI)
  fix t x
  assume "t \<in> T" "x \<in> X"
  then have "g t \<in> g ` T" by simp
  from local_lipschitzE[OF assms(1) this \<open>x \<in> X\<close>]
  obtain u L where "0 < u" and l: "(\<And>s. s \<in> cball (g t) u \<inter> g ` T \<Longrightarrow> lipschitz (cball x u \<inter> X) (f s) L)"
    by auto
  from g[unfolded continuous_on_eq_continuous_within, rule_format, OF \<open>t \<in> T\<close>,
    unfolded continuous_within_eps_delta, rule_format, OF \<open>0 < u\<close>]
  obtain d where d: "d>0" "\<And>x'. x'\<in>T \<Longrightarrow> dist x' t < d \<Longrightarrow> dist (g x') (g t) < u"
    by (auto)
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. lipschitz (cball x u \<inter> X) (f (g t)) L"
    using d \<open>0 < u\<close>
    by (fastforce intro: exI[where x="(min d u)/2"] exI[where x=L]
      intro!: less_imp_le[OF d(2)] lipschitz_subset[OF l] simp: dist_commute mem_ball mem_cball)
qed

context
  fixes T::"'a::metric_space set" and X f
  assumes local_lipschitz: "local_lipschitz T X f"
begin

lemma continuous_on_TimesI:
  assumes y: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  shows "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
  unfolding continuous_on_iff
proof (safe, simp)
  fix a b and e::real
  assume H: "a \<in> T" "b \<in> X" "0 < e"
  hence "0 < e/2" by simp
  from y[unfolded continuous_on_iff, OF \<open>b \<in> X\<close>, rule_format, OF \<open>a \<in> T\<close> \<open>0 < e/2\<close>]
  obtain d where d: "d > 0" "\<And>t. t \<in> T \<Longrightarrow> dist t a < d \<Longrightarrow> dist (f t b) (f a b) < e/2"
    by auto

  from \<open>a : T\<close> \<open>b \<in> X\<close>
  obtain u L where u: "0 < u"
    and L: "\<And>t. t \<in> cball a u \<inter> T \<Longrightarrow> lipschitz (cball b u \<inter> X) (f t) L"
    by (erule local_lipschitzE[OF local_lipschitz])

  have "a \<in> cball a u \<inter> T" by (auto simp: \<open>0 < u\<close> \<open>a \<in> T\<close> less_imp_le)
  from lipschitz_nonneg[OF L[OF \<open>a \<in> cball _ _ \<inter> _\<close>]] have "0 \<le> L" .

  let ?d = "Min {d, u, (e/2/(L + 1))}"
  show "\<exists>d>0. \<forall>x\<in>T. \<forall>y\<in>X. dist (x, y) (a, b) < d \<longrightarrow> dist (f x y) (f a b) < e"
  proof (rule exI[where x = ?d], safe)
    show "0 < ?d"
      using \<open>0 \<le> L\<close> \<open>0 < u\<close> \<open>0 < e\<close> \<open>0 < d\<close>
      by (auto intro!: divide_pos_pos )
    fix x y
    assume "x \<in> T" "y \<in> X"
    assume dist_less: "dist (x, y) (a, b) < ?d"
    have "dist y b \<le> dist (x, y) (a, b)"
      using dist_snd_le[of "(x, y)" "(a, b)"]
      by auto
    also
    note dist_less
    also
    {
      note calculation
      also have "?d \<le> u" by simp
      finally have "dist y b < u" .
    }
    have "?d \<le> e/2/(L + 1)" by simp
    also have "(L + 1) * \<dots> \<le> e / 2"
      using \<open>0 < e\<close> \<open>L \<ge> 0\<close>
      by (auto simp: divide_simps)
    finally have le1: "(L + 1) * dist y b < e / 2" using \<open>L \<ge> 0\<close> by simp

    have "dist x a \<le> dist (x, y) (a, b)"
      using dist_fst_le[of "(x, y)" "(a, b)"]
      by auto
    also note dist_less
    finally have "dist x a < ?d" .
    also have "?d \<le> d" by simp
    finally have "dist x a < d" .
    note \<open>dist x a < ?d\<close>
    also have "?d \<le> u" by simp
    finally have "dist x a < u" .
    then have "x \<in> cball a u \<inter> T"
      using \<open>x \<in> T\<close>
      by (auto simp: dist_commute mem_cball)
    have "dist (f x y) (f a b) \<le> dist (f x y) (f x b) + dist (f x b) (f a b)"
      by (rule dist_triangle)
    also have "dist (f x y) (f x b) \<le> (abs L + 1) * dist y b"
      apply (rule lipschitzD[OF pos_lipschitz[OF L]])
      subgoal by fact
      subgoal
        using \<open>y \<in> X\<close> \<open>dist y b < u\<close>
        by (simp add: dist_commute mem_cball)
      subgoal
        using \<open>0 < u\<close> \<open>b \<in> X\<close>
        by (simp add: )
      done
    also have "(abs L + 1) * dist y b \<le> e / 2"
      using le1 \<open>0 \<le> L\<close> by simp
    also have "dist (f x b) (f a b) < e / 2"
      by (rule d; fact)
    also have "e / 2 + e / 2 = e" by simp
    finally show "dist (f x y) (f a b) < e" by simp
  qed
qed

lemma local_lipschitz_on_compact_implies_lipschitz:
  assumes "compact X" "compact T"
  assumes cont: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  obtains L where "\<And>t. t \<in> T \<Longrightarrow> lipschitz X (f t) L"
proof -
  {
    assume *: "\<And>n::nat. \<not>(\<forall>t\<in>T. lipschitz X (f t) n)"
    {
      fix n::nat
      from *[of n] have "\<exists>x y t. t \<in> T \<and> x \<in> X \<and> y \<in> X \<and> dist (f t y) (f t x) > n * dist y x"
        by (force simp: lipschitz_def)
    } then obtain t and x y::"nat \<Rightarrow> 'b" where xy: "\<And>n. x n \<in> X" "\<And>n. y n \<in> X"
      and t: "\<And>n. t n \<in> T"
      and d: "\<And>n. dist (f (t n) (y n)) (f (t n) (x n)) > n * dist (y n) (x n)"
      by metis
    from xy assms obtain lx rx where lx': "lx \<in> X" "subseq rx" "(x o rx) \<longlonglongrightarrow> lx"
      by (metis compact_def)
    with xy have "\<And>n. (y o rx) n \<in> X" by auto
    with assms obtain ly ry where ly': "ly \<in> X" "subseq ry" "((y o rx) o ry) \<longlonglongrightarrow> ly"
      by (metis compact_def)
    with t have "\<And>n. ((t o rx) o ry) n \<in> T" by simp
    with assms obtain lt rt where lt': "lt \<in> T" "subseq rt" "(((t o rx) o ry) o rt) \<longlonglongrightarrow> lt"
      by (metis compact_def)
    from lx' ly'
    have lx: "(x o (rx o ry o rt)) \<longlonglongrightarrow> lx" (is "?x \<longlonglongrightarrow> _")
      and ly: "(y o (rx o ry o rt)) \<longlonglongrightarrow> ly" (is "?y \<longlonglongrightarrow> _")
      and lt: "(t o (rx o ry o rt)) \<longlonglongrightarrow> lt" (is "?t \<longlonglongrightarrow> _")
      subgoal by (simp add: LIMSEQ_subseq_LIMSEQ o_assoc lt'(2))
      subgoal by (simp add: LIMSEQ_subseq_LIMSEQ ly'(3) o_assoc lt'(2))
      subgoal by (simp add: o_assoc lt'(3))
      done
    hence "(\<lambda>n. dist (?y n) (?x n)) \<longlonglongrightarrow> dist ly lx"
      by (metis tendsto_dist)
    moreover
    let ?S = "(\<lambda>(t, x). f t x) ` (T \<times> X)"
    have "eventually (\<lambda>n::nat. n > 0) sequentially"
      by (metis eventually_at_top_dense)
    hence "eventually (\<lambda>n. norm (dist (?y n) (?x n)) \<le> norm (\<bar>diameter ?S\<bar> / n) * 1) sequentially"
    proof eventually_elim
      case (elim n)
      have "0 < rx (ry (rt n))" using \<open>0 < n\<close>
        by (metis dual_order.strict_trans1 lt'(2) lx'(2) ly'(2) seq_suble)
      have compact: "compact ?S"
        by (auto intro!: compact_continuous_image continuous_on_subset[OF continuous_on_TimesI]
          compact_Times \<open>compact X\<close> \<open>compact T\<close> cont)
      have "norm (dist (?y n) (?x n)) = dist (?y n) (?x n)" by simp
      also
      from this elim d[of "rx (ry (rt n))"]
      have "\<dots> < dist (f (?t n) (?y n)) (f (?t n) (?x n)) / rx (ry (rt (n)))"
        using lx'(2) ly'(2) lt'(2) \<open>0 < rx _\<close>
        by (auto simp add: divide_simps algebra_simps subseq_def)
      also have "\<dots> \<le> diameter ?S / n"
        by (force intro!: \<open>0 < n\<close> subseq_def xy diameter_bounded_bound frac_le
          compact_imp_bounded compact t
          intro: le_trans[OF seq_suble[OF lt'(2)]]
            le_trans[OF seq_suble[OF ly'(2)]]
            le_trans[OF seq_suble[OF lx'(2)]])
      also have "\<dots> \<le> abs (diameter ?S) / n"
        by (auto intro!: divide_right_mono)
      finally show ?case by simp
    qed
    with _ have "(\<lambda>n. dist (?y n) (?x n)) \<longlonglongrightarrow> 0"
      by (rule tendsto_0_le)
        (metis tendsto_divide_0[OF tendsto_const] filterlim_at_top_imp_at_infinity
          filterlim_real_sequentially)
    ultimately have "lx = ly"
      using LIMSEQ_unique by fastforce
    with assms lx' have "lx \<in> X" by auto
    from \<open>lt \<in> T\<close> this obtain u L where L: "u > 0" "\<And>t. t \<in> cball lt u \<inter> T \<Longrightarrow> lipschitz (cball lx u \<inter> X) (f t) L"
      by (erule local_lipschitzE[OF local_lipschitz])
    hence "L \<ge> 0" by (force intro!: lipschitz_nonneg \<open>lt \<in> T\<close>)

    from L lt ly lx \<open>lx = ly\<close>
    have
      "eventually (\<lambda>n. ?t n \<in> ball lt u) sequentially"
      "eventually (\<lambda>n. ?y n \<in> ball lx u) sequentially"
      "eventually (\<lambda>n. ?x n \<in> ball lx u) sequentially"
      by (auto simp: dist_commute Lim mem_ball)
    moreover have "eventually (\<lambda>n. n > L) sequentially"
      by (metis filterlim_at_top_dense filterlim_real_sequentially)
    ultimately
    have "eventually (\<lambda>_. False) sequentially"
    proof eventually_elim
      case (elim n)
      hence "dist (f (?t n) (?y n)) (f (?t n) (?x n)) \<le> L * dist (?y n) (?x n)"
        using assms xy t
        unfolding dist_norm[symmetric]
        by (intro lipschitzD[OF L(2)]) (auto simp: mem_ball mem_cball)
      also have "\<dots> \<le> n * dist (?y n) (?x n)"
        using elim by (intro mult_right_mono) auto
      also have "\<dots> \<le> rx (ry (rt n)) * dist (?y n) (?x n)"
        by (intro mult_right_mono[OF _ zero_le_dist])
           (meson lt'(2) lx'(2) ly'(2) of_nat_le_iff order_trans seq_suble)
      also have "\<dots> < dist (f (?t n) (?y n)) (f (?t n) (?x n))"
        by (auto intro!: d)
      finally show ?case by simp
    qed
    hence False
      by simp
  } then obtain L where "\<And>t. t \<in> T \<Longrightarrow> lipschitz X (f t) L"
    by metis
  thus ?thesis ..
qed

lemma local_lipschitz_on_subset:
  assumes "S \<subseteq> T" "Y \<subseteq> X"
  shows "local_lipschitz S Y f"
proof (rule local_lipschitzI)
  fix t x assume "t \<in> S" "x \<in> Y"
  then have "t \<in> T" "x \<in> X" using assms by auto
  from local_lipschitzE[OF local_lipschitz, OF this]
  obtain u L where u: "0 < u" and L: "\<And>s. s \<in> cball t u \<inter> T \<Longrightarrow> lipschitz (cball x u \<inter> X) (f s) L"
    by blast
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> S. lipschitz (cball x u \<inter> Y) (f t) L"
    using assms
    by (auto intro: exI[where x=u] exI[where x=L] intro!: u lipschitz_subset[OF _ Int_mono[OF order_refl \<open>Y \<subseteq> X\<close>]] L)
qed

end

lemma local_lipschitz_uminus:
  fixes f::"'a::metric_space \<Rightarrow> 'b::metric_space \<Rightarrow> 'c::real_normed_vector"
  shows "local_lipschitz T X (\<lambda>t x. - f t x) = local_lipschitz T X f"
  by (auto simp: local_lipschitz_def lipschitz_uminus)

lemma lipschitz_PairI:
  assumes f: "lipschitz A f L"
  assumes g: "lipschitz A g M"
  shows "lipschitz A (\<lambda>a. (f a, g a)) (sqrt (L\<^sup>2 + M\<^sup>2))"
proof (rule lipschitzI, goal_cases)
  case (1 x y)
  have "dist (f x, g x) (f y, g y) = sqrt ((dist (f x) (f y))\<^sup>2 + (dist (g x) (g y))\<^sup>2)"
    by (auto simp add: dist_Pair_Pair real_le_lsqrt)
  also have "\<dots> \<le> sqrt ((L * dist x y)\<^sup>2 + (M * dist x y)\<^sup>2)"
    by (auto intro!: real_sqrt_le_mono add_mono power_mono 1 lipschitzD f g)
  also have "\<dots> \<le> sqrt (L\<^sup>2 + M\<^sup>2) * dist x y"
    by (auto simp: power_mult_distrib ring_distribs[symmetric] real_sqrt_mult)
  finally show ?case .
qed simp

lemma local_lipschitz_PairI:
  assumes f: "local_lipschitz A B (\<lambda>a b. f a b)"
  assumes g: "local_lipschitz A B (\<lambda>a b. g a b)"
  shows "local_lipschitz A B (\<lambda>a b. (f a b, g a b))"
proof (rule local_lipschitzI)
  fix t x assume "t \<in> A" "x \<in> B"
  from local_lipschitzE[OF f this] local_lipschitzE[OF g this]
  obtain u L v M where "0 < u" "(\<And>s. s \<in> cball t u \<inter> A \<Longrightarrow> lipschitz (cball x u \<inter> B) (f s) L)"
    "0 < v" "(\<And>s. s \<in> cball t v \<inter> A \<Longrightarrow> lipschitz (cball x v \<inter> B) (g s) M)"
    by metis
  then show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> A. lipschitz (cball x u \<inter> B) (\<lambda>b. (f t b, g t b)) L"
    by (intro exI[where x="min u v"])
      (force intro: lipschitz_subset intro!: lipschitz_PairI simp: mem_cball)
qed

lemma lipschitz_constI: "lipschitz A (\<lambda>x. c) 0"
  by (auto simp: lipschitz_def)

lemma local_lipschitz_constI: "local_lipschitz S T (\<lambda>t x. f t)"
  by (auto simp: intro!: local_lipschitzI lipschitz_constI intro: exI[where x=1])

lemma (in bounded_linear) lipschitz_boundE:
  obtains B where "lipschitz A f B"
proof -
  from nonneg_bounded
  obtain B where B: "B \<ge> 0" "\<And>x. norm (f x) \<le> B * norm x"
    by (auto simp: ac_simps)
  have "lipschitz A f B"
    by (auto intro!: lipschitzI B simp: dist_norm diff[symmetric])
  thus ?thesis ..
qed

lemma (in bounded_linear) local_lipschitzI:
  shows "local_lipschitz A B (\<lambda>_. f)"
proof (rule local_lipschitzI, goal_cases)
  case (1 t x)
  from lipschitz_boundE[of "(cball x 1 \<inter> B)"] obtain C where "lipschitz (cball x 1 \<inter> B) f C" by auto
  then show ?case
    by (auto intro: exI[where x=1])
qed

lemma c1_implies_local_lipschitz:
  fixes T::"real set" and X::"'a::{banach,heine_borel} set"
    and f::"real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f': "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> (f t has_derivative blinfun_apply (f' (t, x))) (at x)"
  assumes cont_f': "continuous_on (T \<times> X) f'"
  assumes "open T"
  assumes "open X"
  shows "local_lipschitz T X f"
proof (rule local_lipschitzI)
  fix t x
  assume "t \<in> T" "x \<in> X"
  from open_contains_cball[THEN iffD1, OF \<open>open X\<close>, rule_format, OF \<open>x \<in> X\<close>]
  obtain u where u: "u > 0" "cball x u \<subseteq> X" by auto
  moreover
  from open_contains_cball[THEN iffD1, OF \<open>open T\<close>, rule_format, OF \<open>t \<in> T\<close>]
  obtain v where v: "v > 0" "cball t v \<subseteq> T" by auto
  ultimately
  have "compact (cball t v \<times> cball x u)" "cball t v \<times> cball x u \<subseteq> T \<times> X"
    by (auto intro!: compact_Times)
  then have "compact (f' ` (cball t v \<times> cball x u))"
    by (auto intro!: compact_continuous_image continuous_on_subset[OF cont_f'])
  then obtain B where B: "B > 0" "\<And>s y. s \<in> cball t v \<Longrightarrow> y \<in> cball x u \<Longrightarrow> norm (f' (s, y)) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_pos simp: mem_ball)

  have lipschitz: "lipschitz (cball x (min u v) \<inter> X) (f s) B" if s: "s \<in> cball t v" for s
  proof -
    note s
    also note \<open>cball t v \<subseteq> T\<close>
    finally
    have deriv: "\<forall>y\<in>cball x u. (f s has_derivative blinfun_apply (f' (s, y))) (at y within cball x u)"
      using \<open>_ \<subseteq> X\<close>
      by (auto intro!: has_derivative_at_within[OF f'])
    have "norm (f s y - f s z) \<le> B * norm (y - z)"
      if "y \<in> cball x u" "z \<in> cball x u"
      for y z
      using s that
      by (intro differentiable_bound[OF convex_cball deriv])
        (auto intro!: B  simp: norm_blinfun.rep_eq[symmetric] mem_cball)
    then show ?thesis
      using \<open>0 < B\<close>
      by (auto intro!: lipschitzI simp: dist_norm mem_cball)
  qed
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. lipschitz (cball x u \<inter> X) (f t) L"
    by (force intro: exI[where x="min u v"] exI[where x=B] intro!: lipschitz simp: u v mem_cball)
qed


subsection \<open>Solutions of IVPs \label{sec:solutions}\<close>

definition
  solves_ode :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool"
  (infix "(solves'_ode)" 50)
where
  "(y solves_ode f) T X \<longleftrightarrow> (y has_vderiv_on (\<lambda>t. f t (y t))) T \<and> y \<in> T \<rightarrow> X"

lemma solves_odeI:
  assumes solves_ode_vderivD: "(y has_vderiv_on (\<lambda>t. f t (y t))) T"
    and solves_ode_domainD: "\<And>t. t \<in> T \<Longrightarrow> y t \<in> X"
  shows "(y solves_ode f) T X"
  using assms
  by (auto simp: solves_ode_def)

lemma solves_odeD:
  assumes "(y solves_ode f) T X"
  shows solves_ode_vderivD: "(y has_vderiv_on (\<lambda>t. f t (y t))) T"
    and solves_ode_domainD: "\<And>t. t \<in> T \<Longrightarrow> y t \<in> X"
  using assms
  by (auto simp: solves_ode_def)

lemma solves_ode_continuous_on: "(y solves_ode f) T X \<Longrightarrow> continuous_on T y"
  by (auto intro!: vderiv_on_continuous_on simp: solves_ode_def)

lemma solves_ode_congI:
  assumes "(x solves_ode f) T X"
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t. t \<in> T \<Longrightarrow> f t (x t) = g t (x t)"
  assumes "T = S" "X = Y"
  shows "(y solves_ode g) S Y"
  using assms
  by (auto simp: solves_ode_def Pi_iff)

lemma solves_ode_cong[cong]:
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t. t \<in> T \<Longrightarrow> f t (x t) = g t (x t)"
  assumes "T = S" "X = Y"
  shows "(x solves_ode f) T X \<longleftrightarrow> (y solves_ode g) S Y"
  using assms
  by (auto simp: solves_ode_def Pi_iff)

lemma solves_ode_on_subset:
  assumes "(x solves_ode f) S Y"
  assumes "T \<subseteq> S" "Y \<subseteq> X"
  shows "(x solves_ode f) T X"
  using assms
  by (auto simp: solves_ode_def has_vderiv_on_subset)

lemma preflect_solution:
  assumes "t0 \<in> T"
  assumes sol: "((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  shows "(x solves_ode f) T X"
proof (rule solves_odeI)
  from solves_odeD[OF sol]
  have xm_deriv: "(x o preflect t0 has_vderiv_on (\<lambda>t. - f (preflect t0 t) (x (preflect t0 t)))) (preflect t0 ` T)"
    and xm_mem: "t \<in> preflect t0 ` T \<Longrightarrow> x (preflect t0 t) \<in> X" for t
    by simp_all
  have "(x o preflect t0 o preflect t0 has_vderiv_on (\<lambda>t. f t (x t))) T"
    apply (rule has_vderiv_on_eq_rhs)
    apply (rule has_vderiv_on_compose)
    apply (rule xm_deriv)
    apply (auto simp: preflect_def intro!: derivative_intros)
    done
  then show "(x has_vderiv_on (\<lambda>t. f t (x t))) T"
    by (simp add: preflect_def)
  show "x t \<in> X" if "t \<in> T" for t
    using that xm_mem[of "preflect t0 t"]
    by (auto simp: preflect_def)
qed

lemma solution_preflect:
  assumes "t0 \<in> T"
  assumes sol: "(x solves_ode f) T X"
  shows "((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  using sol \<open>t0 \<in> T\<close>
  by (simp_all add: preflect_def image_image preflect_solution[of t0])

lemma solution_eq_preflect_solution:
  assumes "t0 \<in> T"
  shows "(x solves_ode f) T X \<longleftrightarrow> ((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  using solution_preflect[OF \<open>t0 \<in> T\<close>] preflect_solution[OF \<open>t0 \<in> T\<close>]
  by blast

lemma shift_autonomous_solution:
  assumes sol: "(x solves_ode f) T X"
  assumes auto: "\<And>s t. s \<in> T \<Longrightarrow> f s (x s) = f t (x s)"
  shows "((\<lambda>t. x (t + t0)) solves_ode f) ((\<lambda>t. t - t0) ` T) X"
  using solves_odeD[OF sol]
  apply (intro solves_odeI)
  apply (rule has_vderiv_on_compose'[of x, THEN has_vderiv_on_eq_rhs])
  apply (auto simp: image_image intro!: auto derivative_intros)
  done

lemma solves_ode_singleton: "y t0 \<in> X \<Longrightarrow> (y solves_ode f) {t0} X"
  by (auto intro!: solves_odeI has_vderiv_on_singleton)

subsubsection\<open>Connecting solutions\<close>
text\<open>\label{sec:combining-solutions}\<close>

lemma connection_solves_ode:
  assumes x: "(x solves_ode f) T X"
  assumes y: "(y solves_ode g) S Y"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_x: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x t = y t"
  assumes conn_f: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> f t (y t) = g t (y t)"
  shows "((\<lambda>t. if t \<in> T then x t else y t) solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (T \<union> S) (X \<union> Y)"
proof (rule solves_odeI)
  from solves_odeD(2)[OF x] solves_odeD(2)[OF y]
  show "t \<in> T \<union> S \<Longrightarrow> (if t \<in> T then x t else y t) \<in> X \<union> Y" for t
    by auto
  show "((\<lambda>t. if t \<in> T then x t else y t) has_vderiv_on (\<lambda>t. (if t \<in> T then f t else g t) (if t \<in> T then x t else y t))) (T \<union> S)"
    apply (rule has_vderiv_on_If[OF refl, THEN has_vderiv_on_eq_rhs])
    unfolding Un_absorb2[OF conn_T] Un_absorb2[OF conn_S]
    apply (rule solves_odeD(1)[OF x])
    apply (rule solves_odeD(1)[OF y])
    apply (simp_all add: conn_T conn_S Un_absorb2 conn_x conn_f)
    done
qed

lemma solves_ode_on_union_closed:
  assumes x: "(x solves_ode f) T X"
  assumes y: "(x solves_ode f) S Y"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  shows "(x solves_ode f) (T \<union> S) (X \<union> Y)"
  using connection_solves_ode[OF assms]
  by simp

lemma
  solves_ode_subset_range:
  assumes x: "(x solves_ode f) T X"
  assumes s: "x ` T \<subseteq> Y"
  shows "(x solves_ode f) T Y"
  using assms
  by (auto intro!: solves_odeI dest!: solves_odeD)


subsection \<open>unique solution with initial value\<close>

definition
  usolves_ode_from :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool"
  ("((_) usolves'_ode (_) from (_))" [10, 10, 10] 10)
  \<comment>\<open>TODO: no idea about mixfix and precedences, check this!\<close>
where
  "(y usolves_ode f from t0) T X \<longleftrightarrow> (y solves_ode f) T X \<and> t0 \<in> T \<and> is_interval T \<and>
    (\<forall>z T'. t0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> T \<and> (z solves_ode f) T' X \<longrightarrow> z t0 = y t0 \<longrightarrow> (\<forall>t \<in> T'. z t = y t))"

text \<open>uniqueness of solution can depend on domain \<open>X\<close>:\<close>

lemma
  "((\<lambda>_. 0::real) usolves_ode (\<lambda>_. sqrt) from 0) {0..} {0}"
    "((\<lambda>t. t\<^sup>2 / 4) solves_ode (\<lambda>_. sqrt)) {0..} {0..}"
    "(\<lambda>t. t\<^sup>2 / 4) 0 = (\<lambda>_. 0::real) 0"
  by (auto intro!: derivative_eq_intros
    simp: has_vderiv_on_def has_vector_derivative_def usolves_ode_from_def solves_ode_def
      is_interval_ci real_sqrt_divide)

text \<open>TODO: show that if solution stays in interior, then domain can be enlarged! (?)\<close>

lemma usolves_odeD:
  assumes "(y usolves_ode f from t0) T X"
  shows "(y solves_ode f) T X"
    and "t0 \<in> T"
    and "is_interval T"
    and "\<And>z T' t. t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow>(z solves_ode f) T' X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = y t"
  using assms
  unfolding usolves_ode_from_def
  by blast+

lemma usolves_ode_rawI:
  assumes "(y solves_ode f) T X" "t0 \<in> T" "is_interval T"
  assumes "\<And>z T' t. t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> (z solves_ode f) T' X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = y t"
  shows "(y usolves_ode f from t0) T X"
  using assms
  unfolding usolves_ode_from_def
  by blast

lemma usolves_odeI:
  assumes "(y solves_ode f) T X" "t0 \<in> T" "is_interval T"
  assumes usol: "\<And>z t. {t0 -- t} \<subseteq> T \<Longrightarrow> (z solves_ode f) {t0 -- t} X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> z t = y t"
  shows "(y usolves_ode f from t0) T X"
proof (rule usolves_ode_rawI; fact?)
  fix z T' t
  assume T': "t0 \<in> T'" "is_interval T'" "T' \<subseteq> T"
    and z: "(z solves_ode f) T' X" and iv: "z t0 = y t0" and t: "t \<in> T'"
  have subset_T': "{t0 -- t} \<subseteq> T'"
    by (rule closed_segment_subset_interval; fact)
  with z have sol_cs: "(z solves_ode f) {t0 -- t} X"
    by (rule solves_ode_on_subset[OF _ _ order_refl])
  from subset_T' have subset_T: "{t0 -- t} \<subseteq> T"
    using \<open>T' \<subseteq> T\<close> by simp
  from usol[OF subset_T sol_cs iv]
  show "z t = y t" by simp
qed

lemma is_interval_singleton[intro,simp]: "is_interval {t0}"
  by (auto simp: is_interval_def intro!: euclidean_eqI[where 'a='a])

lemma usolves_ode_singleton: "x t0 \<in> X \<Longrightarrow> (x usolves_ode f from t0) {t0} X"
  by (auto intro!: usolves_odeI solves_ode_singleton)

lemma usolves_ode_congI:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t y. t \<in> T \<Longrightarrow> y \<in> X \<Longrightarrow> f t y = g t y"\<comment>\<open>TODO: weaken this assumption?!\<close>
  assumes "t0 = s0"
  assumes "T = S"
  assumes "X = Y"
  shows "(y usolves_ode g from s0) S Y"
proof (rule usolves_ode_rawI)
  from assms x have "(y solves_ode f) S Y"
    by (auto simp add: usolves_ode_from_def)
  then show "(y solves_ode g) S Y"
    by (rule solves_ode_congI) (use assms in \<open>auto simp: usolves_ode_from_def dest!: solves_ode_domainD\<close>)
  from assms show "s0 \<in> S" "is_interval S"
    by (auto simp add: usolves_ode_from_def)
next
  fix z T' t
  assume hyps: "s0 \<in> T'" "is_interval T'" "T' \<subseteq> S" "(z solves_ode g) T' Y" "z s0 = y s0" "t \<in> T'"
  from \<open>(z solves_ode g) T' Y\<close>
  have zsol: "(z solves_ode f) T' Y"
    by (rule solves_ode_congI) (use assms hyps in \<open>auto dest!: solves_ode_domainD\<close>)
  have "z t = x t"
    by (rule x[THEN usolves_odeD(4),where T' = T'])
      (use zsol \<open>s0 \<in> T'\<close> \<open>is_interval T'\<close> \<open>T' \<subseteq> S\<close> \<open>T = S\<close> \<open>z s0 = y s0\<close> \<open>t \<in> T'\<close> assms in auto)
  also have "y t = x t" using assms \<open>t \<in> T'\<close> \<open>T' \<subseteq> S\<close> \<open>T = S\<close> by auto
  finally show "z t = y t" by simp
qed


lemma usolves_ode_cong[cong]:
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t y. t \<in> T \<Longrightarrow> y \<in> X \<Longrightarrow> f t y = g t y"\<comment>\<open>TODO: weaken this assumption?!\<close>
  assumes "t0 = s0"
  assumes "T = S"
  assumes "X = Y"
  shows "(x usolves_ode f from t0) T X \<longleftrightarrow> (y usolves_ode g from s0) S Y"
  apply (rule iffI)
  subgoal by (rule usolves_ode_congI[OF _ assms]; assumption)
  subgoal by (metis assms(1) assms(2) assms(3) assms(4) assms(5) usolves_ode_congI)
  done

lemma shift_autonomous_unique_solution:
  assumes usol: "(x usolves_ode f from t0) T X"
  assumes auto: "\<And>s t x. x \<in> X \<Longrightarrow> f s x = f t x"
  shows "((\<lambda>t. x (t + t0 - t1)) usolves_ode f from t1) (op + (t1 - t0) ` T) X"
proof (rule usolves_ode_rawI)
  from usolves_odeD[OF usol]
  have sol: "(x solves_ode f) T X"
    and "t0 \<in> T"
    and "is_interval T"
    and unique: "t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> (z solves_ode f) T' X \<Longrightarrow> z t0 = x t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = x t"
    for z T' t
    by blast+
  have "(\<lambda>t. t + t1 - t0) = op + (t1 - t0)"
    by (auto simp add: algebra_simps)
  with shift_autonomous_solution[OF sol auto, of "t0 - t1"] solves_odeD[OF sol]
  show "((\<lambda>t. x (t + t0 - t1)) solves_ode f) (op + (t1 - t0) ` T) X"
    by (simp add: algebra_simps)
  from \<open>t0 \<in> T\<close> show "t1 \<in> op + (t1 - t0) ` T" by auto
  from \<open>is_interval T\<close>
  show "is_interval (op + (t1 - t0) ` T)"
    by simp
  fix z T' t
  assume z: "(z solves_ode f) T' X"
    and t0': "t1 \<in> T'" "T' \<subseteq> op + (t1 - t0) ` T"
    and shift: "z t1 = x (t1 + t0 - t1)"
    and t: "t \<in> T'"
    and ivl: "is_interval T'"

  let ?z = "(\<lambda>t. z (t + (t1 - t0)))"

  have "(?z solves_ode f) ((\<lambda>t. t - (t1 - t0)) ` T') X"
    apply (rule shift_autonomous_solution[OF z, of "t1 - t0"])
    using solves_odeD[OF z]
    by (auto intro!: auto)
  with _ _ _ have "?z ((t + (t0 - t1))) = x (t + (t0 - t1))"
    apply (rule unique[where z = ?z ])
    using shift t t0' ivl
    by auto
  then show "z t = x (t + t0 - t1)"
    by (simp add: algebra_simps)
qed

lemma three_intervals_lemma:
  fixes a b c::real
  assumes a: "a \<in> A - B"
    and b: "b \<in> B - A"
    and c: "c \<in> A \<inter> B"
    and iA: "is_interval A" and iB: "is_interval B"
    and aI: "a \<in> I"
    and bI: "b \<in> I"
    and iI: "is_interval I"
  shows "c \<in> I"
  apply (rule mem_is_intervalI[OF iI aI bI])
  using iA iB
  apply (auto simp: is_interval_def)
  apply (metis Diff_iff Int_iff a b c le_cases)
  apply (metis Diff_iff Int_iff a b c le_cases)
  done

lemma connection_usolves_ode:
  assumes x: "(x usolves_ode f from tx) T X"
  assumes y: "\<And>t. t \<in> closure S \<inter> closure T \<Longrightarrow> (y usolves_ode g from t) S X"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_t: "t \<in> closure S \<inter> closure T"
  assumes conn_x: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x t = y t"
  assumes conn_f: "\<And>t x. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x \<in> X \<Longrightarrow> f t x = g t x"
  shows "((\<lambda>t. if t \<in> T then x t else y t) usolves_ode (\<lambda>t. if t \<in> T then f t else g t) from tx) (T \<union> S) X"
  apply (rule usolves_ode_rawI)
  apply (subst Un_absorb[of X, symmetric])
  apply (rule connection_solves_ode[OF usolves_odeD(1)[OF x] usolves_odeD(1)[OF y[OF conn_t]] conn_T conn_S conn_x conn_f])
  subgoal by assumption
  subgoal by assumption
  subgoal by assumption
  subgoal by assumption
  subgoal using solves_odeD(2)[OF usolves_odeD(1)[OF x]] conn_T by (auto simp add: conn_x[symmetric])
  subgoal using usolves_odeD(2)[OF x] by auto
  subgoal using usolves_odeD(3)[OF x] usolves_odeD(3)[OF y]
    apply (rule is_real_interval_union)
    using conn_T conn_S conn_t by auto
  subgoal premises prems for z TS' s
  proof -
    from \<open>(z solves_ode _) _ _\<close>
    have "(z solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (T \<inter> TS') X"
      by (rule solves_ode_on_subset) auto
    then have z_f: "(z solves_ode f) (T \<inter> TS') X"
      by (subst solves_ode_cong) auto

    from prems(4)
    have "(z solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (S \<inter> TS') X"
      by (rule solves_ode_on_subset) auto
    then have z_g: "(z solves_ode g) (S \<inter> TS') X"
      apply (rule solves_ode_congI)
      subgoal by simp
      subgoal by clarsimp (meson closure_subset conn_f contra_subsetD prems(4) solves_ode_domainD)
      subgoal by simp
      subgoal by simp
      done
    have "tx \<in> T" using assms using usolves_odeD(2)[OF x] by auto

    have "z tx = x tx" using assms prems
      by (simp add: \<open>tx \<in> T\<close>)

    from usolves_odeD(4)[OF x _ _ _ \<open>(z solves_ode f) _ _\<close>, of s] prems
    have "z s = x s" if "s \<in> T" using that \<open>tx \<in> T\<close> \<open>z tx = x tx\<close>
      by (auto simp: is_interval_inter usolves_odeD(3)[OF x] \<open>is_interval TS'\<close>)

    moreover

    {
      assume "s \<notin> T"
      then have "s \<in> S" using prems assms by auto
      {
        assume "tx \<notin> S"
        then have "tx \<in> T - S" using \<open>tx \<in> T\<close> by simp
        moreover have "s \<in> S - T" using \<open>s \<notin> T\<close> \<open>s \<in> S\<close> by blast
        ultimately have "t \<in> TS'"
          apply (rule three_intervals_lemma)
          subgoal using assms by auto
          subgoal using usolves_odeD(3)[OF x] .
          subgoal using usolves_odeD(3)[OF y[OF conn_t]] .
          subgoal using \<open>tx \<in> TS'\<close> .
          subgoal using \<open>s \<in> TS'\<close> .
          subgoal using \<open>is_interval TS'\<close> .
          done
        with assms have t: "t \<in> closure S \<inter> closure T \<inter> TS'" by simp

        then have "t \<in> S" "t \<in> T" "t \<in> TS'" using assms by auto
        have "z t = x t"
          apply (rule usolves_odeD(4)[OF x _ _ _ z_f, of t])
          using \<open>t \<in> TS'\<close> \<open>t \<in> T\<close> prems assms \<open>tx \<in> T\<close> usolves_odeD(3)[OF x]
          by (auto intro!: is_interval_inter)
        with assms have "z t = y t" using t by auto

        from usolves_odeD(4)[OF y[OF conn_t] _ _ _ z_g, of s] prems
        have "z s = y s" using \<open>s \<notin> T\<close> assms \<open>z t = y t\<close> t \<open>t \<in> S\<close>
          \<open>is_interval TS'\<close> usolves_odeD(3)[OF y[OF conn_t]]
          by (auto simp: is_interval_inter)
      } moreover {
        assume "tx \<in> S"
        with prems closure_subset \<open>tx \<in> T\<close>
        have tx: "tx \<in> closure S \<inter> closure T \<inter> TS'" by force

        then have "tx \<in> S" "tx \<in> T" "tx \<in> TS'" using assms by auto
        have "z tx = x tx"
          apply (rule usolves_odeD(4)[OF x _ _ _ z_f, of tx])
          using \<open>tx \<in> TS'\<close> \<open>tx \<in> T\<close> prems assms \<open>tx \<in> T\<close> usolves_odeD(3)[OF x]
          by (auto intro!: is_interval_inter)
        with assms have "z tx = y tx" using tx by auto

        from usolves_odeD(4)[OF y[where t=tx] _ _ _ z_g, of s] prems
        have "z s = y s" using \<open>s \<notin> T\<close> assms \<open>z tx = y tx\<close> tx \<open>tx \<in> S\<close>
          \<open>is_interval TS'\<close> usolves_odeD(3)[OF y]
          by (auto simp: is_interval_inter)
      } ultimately have "z s = y s" by blast
    }
    ultimately
    show "z s = (if s \<in> T then x s else y s)" by simp
  qed
  done

lemma usolves_ode_union_closed:
  assumes x: "(x usolves_ode f from tx) T X"
  assumes y: "\<And>t. t \<in> closure S \<inter> closure T \<Longrightarrow> (x usolves_ode f from t) S X"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_t: "t \<in> closure S \<inter> closure T"
  shows "(x usolves_ode f from tx) (T \<union> S) X"
  using connection_usolves_ode[OF assms] by simp

lemma usolves_ode_solves_odeI:
  assumes "(x usolves_ode f from tx) T X"
  assumes "(y solves_ode f) T X" "y tx = x tx"
  shows "(y usolves_ode f from tx) T X"
  using assms(1)
  apply (rule usolves_ode_congI)
  subgoal using assms by (metis set_eq_subset usolves_odeD(2) usolves_odeD(3) usolves_odeD(4))
  by auto

lemma usolves_ode_subset_range:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes r: "x ` T \<subseteq> Y" and "Y \<subseteq> X"
  shows "(x usolves_ode f from t0) T Y"
proof (rule usolves_odeI)
  note usolves_odeD[OF x]
  show "(x solves_ode f) T Y" by (rule solves_ode_subset_range; fact)
  show "t0 \<in> T" "is_interval T" by fact+
  fix z t
  assume s: "{t0 -- t} \<subseteq> T" and z: "(z solves_ode f) {t0 -- t} Y" and z0: "z t0 = x t0"
  then have "t0 \<in> {t0 -- t}" "is_interval {t0 -- t}"
    by auto
  moreover note s
  moreover have "(z solves_ode f) {t0--t} X"
    using solves_odeD[OF z] \<open>Y \<subseteq> X\<close>
    by (intro solves_ode_subset_range[OF z]) force
  moreover note z0
  moreover have "t \<in> {t0 -- t}" by simp
  ultimately show "z t = x t"
    by (rule usolves_odeD[OF x])
qed


subsection \<open>ivp on interval\<close>

context
  fixes t0 t1::real and T
  defines "T \<equiv> closed_segment t0 t1"
begin

lemma is_solution_ext_cont:
  "continuous_on T x \<Longrightarrow> (ext_cont x (min t0 t1) (max t0 t1) solves_ode f) T X = (x solves_ode f) T X"
  by (rule solves_ode_cong) (auto simp add: T_def min_def max_def closed_segment_real)

lemma solution_fixed_point:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes x: "(x solves_ode f) T X" and t: "t \<in> T"
  shows "x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) = x t"
proof -
  from solves_odeD(1)[OF x, unfolded T_def]
  have "(x has_vderiv_on (\<lambda>t. f t (x t))) (closed_segment t0 t)"
    by (rule has_vderiv_on_subset) (insert \<open>t \<in> T\<close>, auto simp: closed_segment_real T_def)
  from fundamental_theorem_of_calculus_ivl_integral[OF this]
  have "((\<lambda>t. f t (x t)) has_ivl_integral x t - x t0) t0 t" .
  from this[THEN ivl_integral_unique]
  show ?thesis by simp
qed

lemma solution_fixed_point_left:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes x: "(x solves_ode f) T X" and t: "t \<in> T"
  shows "x t1 - ivl_integral t t1 (\<lambda>t. f t (x t)) = x t"
proof -
  from solves_odeD(1)[OF x, unfolded T_def]
  have "(x has_vderiv_on (\<lambda>t. f t (x t))) (closed_segment t t1)"
    by (rule has_vderiv_on_subset) (insert \<open>t \<in> T\<close>, auto simp: closed_segment_real T_def)
  from fundamental_theorem_of_calculus_ivl_integral[OF this]
  have "((\<lambda>t. f t (x t)) has_ivl_integral x t1 - x t) t t1" .
  from this[THEN ivl_integral_unique]
  show ?thesis by simp
qed

lemma solution_fixed_pointI:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes cont_f: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
  assumes cont_x: "continuous_on T x"
  assumes defined: "\<And>t. t \<in> T \<Longrightarrow> x t \<in> X"
  assumes fp: "\<And>t. t \<in> T \<Longrightarrow> x t = x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))"
  shows "(x solves_ode f) T X"
proof (rule solves_odeI)
  note [continuous_intros] = continuous_on_compose_Pair[OF cont_f]
  have "((\<lambda>t. x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))) has_vderiv_on (\<lambda>t. f t (x t))) T"
    using cont_x defined
    by (auto intro!: derivative_eq_intros ivl_integral_has_vector_derivative
      continuous_intros
      simp: has_vderiv_on_def T_def)
  with fp show "(x has_vderiv_on (\<lambda>t. f t (x t))) T" by simp
qed (simp add: defined)

end

lemma solves_ode_half_open_segment_continuation:
  fixes f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach"
  assumes ode: "(x solves_ode f) {t0 --< t1} X"
  assumes continuous: "continuous_on ({t0 -- t1} \<times> X) (\<lambda>(t, x). f t x)"
  assumes "compact X"
  assumes "t0 \<noteq> t1"
  obtains l where
    "(x \<longlongrightarrow> l) (at t1 within {t0 --< t1})"
    "((\<lambda>t. if t = t1 then l else x t) solves_ode f) {t0 -- t1} X"
proof -
  note [continuous_intros] = continuous_on_compose_Pair[OF continuous]
  have "compact ((\<lambda>(t, x). f t x) ` ({t0 -- t1} \<times> X))"
    by (auto intro!: compact_continuous_image continuous_intros compact_Times \<open>compact X\<close>
      simp: split_beta)
  then obtain B where "B > 0" and B: "\<And>t x. t \<in> {t0 -- t1} \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f t x) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_pos)

  have uc: "uniformly_continuous_on {t0 --< t1} x"
    apply (rule lipschitz_uniformly_continuous_on[where L=B])
    apply (rule bounded_vderiv_on_imp_lipschitz)
    apply (rule solves_odeD[OF ode])
    using solves_odeD(2)[OF ode] \<open>0 < B\<close>
    by (auto simp: closed_segment_real half_open_segment_real subset_iff
      intro!: B split: if_split_asm)

  have "t1 \<in> closure ({t0 --< t1})"
    using closure_half_open_segment[of t0 t1] \<open>t0 \<noteq> t1\<close>
    by simp
  from uniformly_continuous_on_extension_on_closure[OF uc]
  obtain g where uc_g: "uniformly_continuous_on {t0--t1} g"
    and xg: "(\<And>t. t \<in> {t0 --< t1} \<Longrightarrow> x t = g t)"
    using closure_half_open_segment[of t0 t1] \<open>t0 \<noteq> t1\<close>
    by metis

  from uc_g[THEN uniformly_continuous_imp_continuous, unfolded continuous_on_def]
  have "(g \<longlongrightarrow> g t) (at t within {t0--t1})" if "t\<in>{t0--t1}" for t
    using that by auto
  then have g_tendsto: "(g \<longlongrightarrow> g t) (at t within {t0--<t1})" if "t\<in>{t0--t1}" for t
    using that by (auto intro: tendsto_within_subset half_open_segment_subset)
  then have x_tendsto: "(x \<longlongrightarrow> g t) (at t within {t0--<t1})" if "t\<in>{t0--t1}" for t
    using that
    by (subst Lim_cong_within[OF refl refl refl xg]) auto
  then have "(x \<longlongrightarrow> g t1) (at t1 within {t0 --< t1})"
    by auto
  moreover
  have nbot: "at s within {t0--<t1} \<noteq> bot" if "s \<in> {t0--t1}" for s
    using that \<open>t0 \<noteq> t1\<close>
    by (auto simp: trivial_limit_within islimpt_half_open_segment)
  have g_mem: "s \<in> {t0--t1} \<Longrightarrow> g s \<in> X" for s
    apply (rule Lim_in_closed_set[OF compact_imp_closed[OF \<open>compact X\<close>] _ _ x_tendsto])
    using solves_odeD(2)[OF ode] \<open>t0 \<noteq> t1\<close>
    by (auto intro!: simp: eventually_at_filter nbot)
  have "(g solves_ode f) {t0 -- t1} X"
    apply (rule solution_fixed_pointI[OF continuous])
    subgoal by (auto intro!: uc_g uniformly_continuous_imp_continuous)
    subgoal by (rule g_mem)
    subgoal premises prems for s
    proof -
      {
        fix s
        assume s: "s \<in> {t0--<t1}"
        with prems have subs: "{t0--s} \<subseteq> {t0--<t1}"
          by (auto simp: half_open_segment_real closed_segment_real)
        with ode have sol: "(x solves_ode f) ({t0--s}) X"
          by (rule solves_ode_on_subset) (rule order_refl)
        from subs have inner_eq: "t \<in> {t0 -- s} \<Longrightarrow> x t = g t" for t
          by (intro xg) auto
        from solution_fixed_point[OF sol, of s]
        have "g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s = 0"
          using s prems \<open>t0 \<noteq> t1\<close>
          by (auto simp: inner_eq cong: ivl_integral_cong)
      } note fp = this

      from prems have subs: "{t0--s} \<subseteq> {t0--t1}"
        by (auto simp: closed_segment_real)
      have int: "(\<lambda>t. f t (g t)) integrable_on {t0--t1}"
        using prems subs
        by (auto intro!: integrable_continuous_closed_segment continuous_intros g_mem
          uc_g[THEN uniformly_continuous_imp_continuous, THEN continuous_on_subset])
      note ivl_tendsto[tendsto_intros] =
        indefinite_ivl_integral_continuous(1)[OF int, unfolded continuous_on_def, rule_format]

      from subs half_open_segment_subset
      have "((\<lambda>s. g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) \<longlongrightarrow>
        g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) (at s within {t0 --< t1})"
        using subs
        by (auto intro!: tendsto_intros ivl_tendsto[THEN tendsto_within_subset]
          g_tendsto[THEN tendsto_within_subset])
      moreover
      have "((\<lambda>s. g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) \<longlongrightarrow> 0) (at s within {t0 --< t1})"
        apply (subst Lim_cong_within[OF refl refl refl, where g="\<lambda>_. 0"])
        subgoal by (subst fp) auto
        subgoal by simp
        done
      ultimately have "g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s = 0"
        using nbot prems tendsto_unique by blast
      then show "g s = g t0 + ivl_integral t0 s (\<lambda>t. f t (g t))" by simp
    qed
    done
  then have "((\<lambda>t. if t = t1 then g t1 else x t) solves_ode f) {t0--t1} X"
    apply (rule solves_ode_congI)
    using xg \<open>t0 \<noteq> t1\<close>
    by (auto simp: half_open_segment_closed_segmentI)
  ultimately show ?thesis ..
qed


subsection \<open>Picard-Lindeloef on set of functions into closed set\<close>
text\<open>\label{sec:plclosed}\<close>

locale continuous_rhs = fixes T X f
  assumes continuous: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
begin

lemma continuous_rhs_comp[continuous_intros]:
  assumes [continuous_intros]: "continuous_on S g"
  assumes [continuous_intros]: "continuous_on S h"
  assumes "\<And>t. t \<in> S \<Longrightarrow> g t \<in> T"
  assumes "\<And>t. t \<in> S \<Longrightarrow> h t \<in> X"
  shows "continuous_on S (\<lambda>x. f (g x) (h x))"
  using continuous_on_compose_Pair[OF continuous assms(1,2)] assms(3,4)
  by auto

end

locale global_lipschitz =
  fixes T X f and L::real
  assumes lipschitz: "\<And>t. t \<in> T \<Longrightarrow> lipschitz X (\<lambda>x. f t x) L"

locale closed_domain =
  fixes X assumes closed: "closed X"

locale interval = fixes T::"real set"
  assumes interval: "is_interval T"
begin

lemma closed_segment_subset_domain: "t0 \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> closed_segment t0 t \<subseteq> T"
  by (simp add: closed_segment_subset_interval interval)

lemma closed_segment_subset_domainI: "t0 \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> s \<in> closed_segment t0 t \<Longrightarrow> s \<in> T"
  using closed_segment_subset_domain by force

lemma convex[intro, simp]: "convex T"
  and connected[intro, simp]: "connected T"
  by (simp_all add: interval is_interval_connected is_interval_convex )

end

locale nonempty_set = fixes T assumes nonempty_set: "T \<noteq> {}"

locale compact_interval = interval + nonempty_set T +
  assumes compact_time: "compact T"
begin

definition "tmin = Inf T"
definition "tmax = Sup T"

lemma
  shows tmin: "t \<in> T \<Longrightarrow> tmin \<le> t" "tmin \<in> T"
    and tmax: "t \<in> T \<Longrightarrow> t \<le> tmax" "tmax \<in> T"
  using nonempty_set
  by (auto intro!: cInf_lower cSup_upper bounded_imp_bdd_below bounded_imp_bdd_above
    compact_imp_bounded compact_time closed_contains_Inf closed_contains_Sup compact_imp_closed
    simp: tmin_def tmax_def)

lemma tmin_le_tmax[intro, simp]: "tmin \<le> tmax"
  using nonempty_set tmin tmax by auto

lemma T_def: "T = {tmin .. tmax}"
  using closed_segment_subset_interval[OF interval tmin(2) tmax(2)]
  by (auto simp: closed_segment_real subset_iff intro!: tmin tmax)

end

locale self_mapping = interval T for T +
  fixes t0::real and x0 f X
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  assumes self_mapping:
    "\<And>x t. t \<in> T \<Longrightarrow> x t0 = x0 \<Longrightarrow> x \<in> closed_segment t0 t \<rightarrow> X \<Longrightarrow>
      continuous_on (closed_segment t0 t) x \<Longrightarrow> x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> X"
begin

sublocale nonempty_set T using iv_defined by unfold_locales auto

lemma closed_segment_iv_subset_domain: "t \<in> T \<Longrightarrow> closed_segment t0 t \<subseteq> T"
  by (simp add: closed_segment_subset_domain iv_defined)

end

locale unique_on_closed =
  compact_interval T +
  self_mapping T t0 x0 f X +
  continuous_rhs T X f +
  closed_domain X +
  global_lipschitz T X f L for t0::real and T and x0::"'a::banach" and f X L
begin

lemma T_split: "T = {tmin .. t0} \<union> {t0 .. tmax}"
  by (metis T_def atLeastAtMost_iff iv_defined(1) ivl_disj_un_two_touch(4))

lemma L_nonneg: "0 \<le> L"
  by (auto intro!: lipschitz_nonneg[OF lipschitz] iv_defined)

text \<open>Picard Iteration\<close>

definition P_inner where "P_inner x t = x0 + ivl_integral t0 t (\<lambda>t. f  t (x t))"

lemma P_inner_t0[simp]: "P_inner (Rep_bcontfun g) t0 = x0"
  by (simp add: P_inner_def)

definition P::"(real, 'a) bcontfun \<Rightarrow> (real, 'a) bcontfun" where "P x = ext_cont (P_inner x) tmin tmax"

lemma
  continuous_f:
  assumes "y \<in> closed_segment t0 t \<rightarrow> X"
  assumes "continuous_on (closed_segment t0 t) y"
  assumes "t \<in> T"
  shows "continuous_on (closed_segment t0 t) (\<lambda>t. f t (y t))"
  using assms closed_segment_iv_subset_domain[OF \<open>t \<in> T\<close>]
  by (auto intro!: assms continuous_intros)

lemma P_inner_bcontfun:
  assumes "y \<in> T \<rightarrow> X"
  assumes y_cont: "continuous_on T y"
  shows "(\<lambda>x. P_inner y (clamp tmin tmax x)) \<in> bcontfun"
proof -
  have "continuous_on {tmin .. tmax} (\<lambda>x. ivl_integral t0 x (\<lambda>t. f t (y t)))"
    unfolding real_Icc_closed_segment[OF tmin_le_tmax]
    using iv_defined assms T_def
    by (intro indefinite_ivl_integral_continuous_subset integrable_continuous_closed_segment)
      (auto intro!: continuous_intros simp: real_Icc_closed_segment)
  then show ?thesis
    by (auto intro!: clamp_bcontfun continuous_intros simp: P_inner_def)
qed

lemma t0_cs_tmin_tmax: "t0 \<in> {tmin--tmax}" and cs_tmin_tmax_subset: "{tmin--tmax} \<subseteq> T"
  using iv_defined T_def closed_segment_eq_real_ivl
  by auto

lemma P_def':
  assumes "t \<in> T"
  assumes "\<And>t. t \<in> T \<Longrightarrow> Rep_bcontfun fixed_point t \<in> X"
  shows "(P fixed_point) t = x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x))"
  apply (subst P_def)
  apply (subst P_inner_def[abs_def])
  apply (subst ext_cont_cancel)
  subgoal using assms T_def by simp
  subgoal
    using assms iv_defined t0_cs_tmin_tmax cs_tmin_tmax_subset
    by (auto
        intro!: continuous_intros indefinite_ivl_integral_continuous_subset integrable_continuous_closed_segment
        simp: real_Icc_closed_segment )
  subgoal by simp
  done

definition "iter_space = (Abs_bcontfun ` ((T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0}))"

lemma iter_spaceI:
  assumes "(\<And>x. x \<in> T \<Longrightarrow> Rep_bcontfun g x \<in> X)" "g t0 = x0"
  shows "g \<in> iter_space"
  using assms
  by (auto simp: iter_space_def Rep_bcontfun Rep_bcontfun_inverse
      intro!: Rep_bcontfun image_eqI[where x="Rep_bcontfun g"])

lemma iter_spaceD:
  assumes "g \<in> iter_space"
  shows "\<And>x. x \<in> T \<Longrightarrow> g x \<in> X" "g t0 = x0"
  using assms
  by (auto simp add: iter_space_def Abs_bcontfun_inverse)

lemma const_in_subspace: "(\<lambda>_. x0) \<in> (T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0}"
  by (auto intro: const_bcontfun iv_defined)

lemma closed_iter_space: "closed iter_space"
proof -
  have "(T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0} =
    Pi T (\<lambda>i. if i = t0 then {x0} else X) \<inter> bcontfun"
    using iv_defined
    by (force simp: Pi_iff split_ifs)
  thus ?thesis using closed
    by (auto simp add: iter_space_def intro!: closed_Pi_bcontfun)
qed

lemma iter_space_notempty: "iter_space \<noteq> {}"
  using const_in_subspace by (auto simp: iter_space_def)

lemma clamb_in_eq[simp]: fixes a x b::real shows "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> clamp a b x = x"
  by (auto simp: clamp_def)

lemma P_self_mapping:
  assumes in_space: "g \<in> iter_space"
  shows "P g \<in> iter_space"
proof (rule iter_spaceI)
  from iter_spaceD[OF in_space] iv_defined
  show "Rep_bcontfun (P g) t0 = x0"
    by (auto simp: P_def')
  from iter_spaceD[OF in_space] iv_defined
  show "Rep_bcontfun (P g) t \<in> X" if "t \<in> T" for t
    using that closed_segment_iv_subset_domain[OF \<open>t \<in> T\<close>]
    by (auto simp: P_def' intro!: self_mapping)
qed

lemma continuous_on_T: "continuous_on {tmin .. tmax} g \<Longrightarrow> continuous_on T g"
  using T_def by auto

lemma T_closed_segment_subsetI[intro, simp]: "t \<in> {tmin--tmax} \<Longrightarrow> t \<in> T"
  and T_subsetI[intro, simp]: "tmin \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> t \<in> T"
  by (subst T_def, simp add: closed_segment_real)+

lemma t0_mem_closed_segment[intro, simp]: "t0 \<in> {tmin--tmax}"
  using T_def iv_defined
  by (simp add: closed_segment_real)

lemma tmin_le_t0[intro, simp]: "tmin \<le> t0"
  and tmax_ge_t0[intro, simp]: "tmax \<ge> t0"
  using t0_mem_closed_segment
  unfolding closed_segment_real
  by simp_all

lemma ext_cont_solution_fixed_point:
  assumes ode: "(x solves_ode f) T X"
  assumes iv: "x t0 = x0"
  shows "P (ext_cont x tmin tmax) = ext_cont x tmin tmax"
  unfolding P_def
proof (rule ext_cont_cong)
  show "P_inner (Rep_bcontfun (ext_cont x tmin tmax)) t = x t" if "t \<in> cbox tmin tmax" for t
  proof -
    from that have "t \<in> T" using T_def by simp
    then have "{t0--t} \<subseteq> T" by (rule closed_segment_iv_subset_domain)
    with ode have "(x solves_ode f) {t0--t} X"
      by (rule solves_ode_on_subset) simp
    then have "x t = x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))"
      by (rule solution_fixed_point[symmetric]) simp
    also have "ivl_integral t0 t (\<lambda>t. f t (x t)) = ivl_integral t0 t (\<lambda>t. f t ((ext_cont x tmin tmax) t))"
      using \<open>{t0--t} \<subseteq> T\<close> T_def
      by (intro ivl_integral_cong) (auto simp: ext_cont_cancel solves_ode_continuous_on[OF ode])
    finally show ?thesis by (simp add: iv P_inner_def)
  qed
  show "continuous_on (cbox tmin tmax) x" using solves_ode_continuous_on[OF ode] T_def by auto
  then show "continuous_on (cbox tmin tmax) (P_inner (ext_cont x tmin tmax))"
    using solves_odeD(2)[OF ode]
    by (auto simp: P_inner_def real_Icc_closed_segment
      intro!: continuous_intros indefinite_ivl_integral_continuous_subset
        integrable_continuous_closed_segment)
qed auto

lemma
  solution_in_iter_space:
  assumes ode: "(z solves_ode f) T X"
  assumes iv: "z t0 = x0"
  shows "ext_cont z tmin tmax \<in> iter_space" (is "?z \<in> _")
proof -
  from T_def ode have ode: "(z solves_ode f) {tmin -- tmax} X"
    by (simp add: closed_segment_real)
  have "(?z solves_ode f) T X"
    using is_solution_ext_cont[OF solves_ode_continuous_on[OF ode], of f X] ode T_def
    by (auto simp: min_def max_def closed_segment_real)
  then have "\<And>t. t \<in> T \<Longrightarrow> ext_cont z tmin tmax t \<in> X"
    by (auto simp add: solves_ode_def)
  thus "?z \<in> iter_space" using solves_odeD[OF ode] solves_ode_continuous_on[OF ode]
    by (auto simp: iv closed_segment_real min_def max_def
      intro!: iter_spaceI)
qed

end

locale unique_on_bounded_closed = unique_on_closed +
  assumes lipschitz_bound: "\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> abs (s - t) * L < 1"
begin

lemma lipschitz_bound_maxmin: "(tmax - tmin) * L < 1"
  using lipschitz_bound[of tmax tmin]
  by auto

lemma lipschitz_P:
  shows "lipschitz iter_space P ((tmax - tmin) * L)"
proof (rule lipschitzI)
  have "t0 \<in> T" by (simp add: iv_defined)
  thus "0 \<le> (tmax - tmin) * L"
    using T_def
    by (auto intro!: mult_nonneg_nonneg lipschitz lipschitz_nonneg[OF lipschitz]
      iv_defined)
  fix y z
  assume "y \<in> iter_space" and "z \<in> iter_space"
  hence y_defined: "Rep_bcontfun y \<in> (T \<rightarrow> X)"
    and z_defined: "Rep_bcontfun z \<in> (T \<rightarrow> X)"
    by (auto simp: Abs_bcontfun_inverse iter_space_def)
  {
    fix y z::"real\<Rightarrow>'a"
    assume "y \<in> bcontfun" and y_defined: "y \<in> (T \<rightarrow> X)"
    assume "z \<in> bcontfun" and z_defined: "z \<in> (T \<rightarrow> X)"
    from bcontfunE[OF \<open>y \<in> bcontfun\<close>] have y[THEN continuous_on_compose2, continuous_intros]: "continuous_on UNIV y" by auto
    from bcontfunE[OF \<open>z \<in> bcontfun\<close>] have z[THEN continuous_on_compose2, continuous_intros]: "continuous_on UNIV z" by auto
    have defined: "s \<in> T" "y s \<in> X" "z s \<in> X" if "s \<in> closed_segment tmin tmax" for s
      using y_defined z_defined that T_def
      by (auto simp: )    {
      note [intro, simp] = integrable_continuous_closed_segment
      fix t
      assume t_bounds: "t \<in> closed_segment tmin tmax"
      then have cs_subs: "closed_segment t0 t \<subseteq> closed_segment tmin tmax"
        by (auto simp: closed_segment_real)
      then have cs_subs_ext: "\<And>ta. ta \<in> {t0--t} \<Longrightarrow> ta \<in> {tmin--tmax}" by auto

      have "norm (P_inner y t - P_inner z t) =
        norm (ivl_integral t0 t (\<lambda>t. f t (y t) - f t (z t)))"
        by (subst ivl_integral_diff)
          (auto intro!: integrable_continuous_closed_segment continuous_intros defined cs_subs_ext simp: P_inner_def)
      also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. norm (f t (y t) - f t (z t))))"
        by (rule ivl_integral_norm_bound_ivl_integral)
          (auto intro!: ivl_integral_norm_bound_ivl_integral continuous_intros integrable_continuous_closed_segment
            simp: defined cs_subs_ext)
      also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. L * norm (y t - z t)))"
        using lipschitz t_bounds T_def y_defined z_defined cs_subs
        by (intro norm_ivl_integral_le) (auto intro!: continuous_intros integrable_continuous_closed_segment
          simp add: dist_norm lipschitz_def Pi_iff)
      also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. L * norm (Abs_bcontfun y - Abs_bcontfun  z)))"
        using norm_bounded[of "Abs_bcontfun y - Abs_bcontfun z"]
          L_nonneg
        by (intro norm_ivl_integral_le) (auto intro!: continuous_intros mult_left_mono
          simp add: Abs_bcontfun_inverse[OF \<open>y \<in> bcontfun\<close>]
          Abs_bcontfun_inverse[OF \<open>z \<in> bcontfun\<close>])
      also have "... =
        L * abs (t - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds L_nonneg by (simp add: abs_mult)
      also have "... \<le> L * (tmax - tmin) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds zero_le_dist L_nonneg cs_subs tmin_le_t0 tmax_ge_t0
        by (auto intro!: mult_right_mono mult_left_mono simp: closed_segment_real abs_real_def
          simp del: tmin_le_t0 tmax_ge_t0 split: if_split_asm)
      finally
      have "norm (P_inner y t - P_inner z t)
        \<le> L * (tmax - tmin) * norm (Abs_bcontfun y - Abs_bcontfun z)" .
    } note * = this
    have "dist (P (Abs_bcontfun y)) (P (Abs_bcontfun z)) \<le>
      L * (tmax - tmin) * dist (Abs_bcontfun y) (Abs_bcontfun z)"
      unfolding P_def dist_norm ext_cont_def
        Abs_bcontfun_inverse[OF \<open>y \<in> bcontfun\<close>]
        Abs_bcontfun_inverse[OF \<open>z \<in> bcontfun\<close>]
      using T_def iv_defined \<open>y \<in> bcontfun\<close> \<open>z \<in> bcontfun\<close>
        y_defined z_defined
        clamp_in_interval[of "tmin" "tmax"]
      apply (intro norm_bound)
      unfolding Rep_bcontfun_minus
      apply (subst Abs_bcontfun_inverse,
        fastforce simp add: elim!: bcontfunE  intro!: P_inner_bcontfun * intro: continuous_on_subset)
      apply (subst Abs_bcontfun_inverse,
        fastforce simp add: elim!: bcontfunE  intro!: P_inner_bcontfun * intro: continuous_on_subset)
      by (auto intro!: P_inner_bcontfun * elim!: bcontfunE simp: real_Icc_closed_segment
        intro: continuous_on_subset)
  }
  from this[OF Rep_bcontfun y_defined Rep_bcontfun z_defined]
  show "dist (P y) (P z) \<le> (tmax - tmin) * L * dist y z"
    unfolding Rep_bcontfun_inverse by (simp add: field_simps)
qed


lemma fixed_point_unique: "\<exists>!x\<in>iter_space. P x = x"
  using lipschitz lipschitz_bound_maxmin lipschitz_P T_def
      complete_UNIV iv_defined
  by (intro banach_fix)
    (auto
      intro: P_self_mapping split_mult_pos_le
      intro!: closed_iter_space iter_space_notempty mult_nonneg_nonneg
      simp: lipschitz_def complete_eq_closed)

definition fixed_point where
  "fixed_point = (THE x. x \<in> iter_space \<and> P x = x)"

lemma fixed_point':
  "fixed_point \<in> iter_space \<and> P fixed_point = fixed_point"
  unfolding fixed_point_def using fixed_point_unique
  by (rule theI')

lemma fixed_point:
  "fixed_point \<in> iter_space" "P fixed_point = fixed_point"
  using fixed_point' by simp_all

lemma fixed_point_equality': "x \<in> iter_space \<and> P x = x \<Longrightarrow> fixed_point = x"
  unfolding fixed_point_def using fixed_point_unique
  by (rule the1_equality)

lemma fixed_point_equality: "x \<in> iter_space \<Longrightarrow> P x = x \<Longrightarrow> fixed_point = x"
  using fixed_point_equality'[of x] by auto

lemma fixed_point_iv: "fixed_point t0 = x0"
  and fixed_point_domain: "x \<in> T \<Longrightarrow> fixed_point x \<in> X"
  using fixed_point
  by (auto dest: iter_spaceD)

lemma fixed_point_has_vderiv_on: "(fixed_point has_vderiv_on (\<lambda>t. f t (fixed_point t))) T"
proof -
  have "continuous_on {tmin--tmax} (\<lambda>x. f x (fixed_point x))"
    using fixed_point_domain
    by (auto intro!: continuous_intros)
  then have "((\<lambda>u. x0 + ivl_integral t0 u (\<lambda>x. f x (fixed_point x))) has_vderiv_on (\<lambda>t. f t (fixed_point t))) {tmin -- tmax}"
    by (auto intro!: derivative_intros ivl_integral_has_vderiv_on_subset)
  then show ?thesis
  proof (rule has_vderiv_eq)
    fix t
    assume t: "t \<in> {tmin--tmax}"
    have "fixed_point t = P fixed_point t"
      using fixed_point by simp
    also have "\<dots> = x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x))"
      using t fixed_point_domain
      by (auto simp: P_def')
    finally show "x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x)) = fixed_point t" by simp
  qed (insert T_def, auto simp: closed_segment_real)
qed

lemma fixed_point_solution:
  shows "(fixed_point solves_ode f) T X"
  using fixed_point_has_vderiv_on fixed_point_domain
  by (rule solves_odeI)


subsubsection \<open>Unique solution\<close>
text\<open>\label{sec:ivp-ubs}\<close>

lemma solves_ode_equals_fixed_point:
  assumes ode: "(x solves_ode f) T X"
  assumes iv: "x t0 = x0"
  assumes "t \<in> T"
  shows "x t = fixed_point t"
proof -
  have "ext_cont fixed_point tmin tmax t = ext_cont x tmin tmax t"
    by (metis ode ext_cont_solution_fixed_point fixed_point_iv fixed_point_solution
      iv solution_in_iter_space unique_on_bounded_closed.fixed_point_equality'
      unique_on_bounded_closed_axioms)
  then show "x t = fixed_point t"
    using solves_ode_continuous_on[OF ode] solves_ode_continuous_on[OF fixed_point_solution] \<open>t \<in> T\<close> T_def
    by (auto simp: closed_segment_real min_def max_def split: if_split_asm)
qed

lemma solves_ode_on_closed_segment_equals_fixed_point:
  assumes ode: "(x solves_ode f) {t0 -- t1'} X"
  assumes iv: "x t0 = x0"
  assumes subset: "{t0--t1'} \<subseteq> T"
  assumes t_mem: "t \<in> {t0--t1'}"
  shows "x t = fixed_point t"
proof -
  have subsetI: "t \<in> {t0--t1'} \<Longrightarrow> t \<in> T" for t
    using subset by auto
  interpret s: unique_on_bounded_closed t0 "{t0--t1'}" x0 f X L
    apply - apply unfold_locales
    subgoal by (simp add: closed_segment_real is_interval_closed_interval)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal using iv_defined by simp
    subgoal by (intro self_mapping subsetI)
    subgoal by (rule continuous_on_subset[OF continuous]) (auto simp: subsetI )
    subgoal by (rule lipschitz) (auto simp: subsetI)
    subgoal by (auto intro!: subsetI lipschitz_bound)
    done
  have "x t = s.fixed_point t"
    by (rule s.solves_ode_equals_fixed_point; fact)
  moreover
  have "fixed_point t = s.fixed_point t"
    by (intro s.solves_ode_equals_fixed_point solves_ode_on_subset[OF fixed_point_solution] assms
      fixed_point_iv order_refl subset t_mem)
  ultimately show ?thesis by simp
qed

lemma unique_solution:
  assumes ivp1: "(x solves_ode f) T X" "x t0 = x0"
  assumes ivp2: "(y solves_ode f) T X" "y t0 = x0"
  assumes "t \<in> T"
  shows "x t = y t"
  using solves_ode_equals_fixed_point[OF ivp1 \<open>t \<in> T\<close>]
    solves_ode_equals_fixed_point[OF ivp2 \<open>t \<in> T\<close>]
  by simp

lemma fixed_point_usolves_ode: "(fixed_point usolves_ode f from t0) T X"
  apply (rule usolves_odeI[OF fixed_point_solution])
  subgoal by (simp add: iv_defined(1))
  subgoal by (rule interval)
  subgoal
    using fixed_point_iv solves_ode_on_closed_segment_equals_fixed_point
    by auto
  done

end

lemma closed_segment_Un:
  fixes a b c::real
  assumes "b \<in> closed_segment a c"
  shows "closed_segment a b \<union> closed_segment b c = closed_segment a c"
  using assms
  by (auto simp: closed_segment_real)

lemma closed_segment_closed_segment_subset:
  fixes s::real and i::nat
  assumes "s \<in> closed_segment a b"
  assumes "a \<in> closed_segment c d" "b \<in> closed_segment c d"
  shows "s \<in> closed_segment c d"
  using assms
  by (auto simp: closed_segment_real split: if_split_asm)


context unique_on_closed begin

context\<comment>\<open>solution until t1\<close>
  fixes t1::real
  assumes mem_t1: "t1 \<in> T"
begin

lemma subdivide_count_ex: "\<exists>n. L * abs (t1 - t0) / (Suc n) < 1"
  by auto (meson add_strict_increasing less_numeral_extra(1) real_arch_simple)

definition "subdivide_count = (SOME n. L * abs (t1 - t0) / Suc n < 1)"

lemma subdivide_count: "L * abs (t1 - t0) / Suc subdivide_count < 1"
  unfolding subdivide_count_def
  using subdivide_count_ex
  by (rule someI_ex)

lemma subdivide_lipschitz:
  assumes "\<bar>s - t\<bar> \<le> abs (t1 - t0) / Suc subdivide_count"
  shows "\<bar>s - t\<bar> * L < 1"
proof -
  from assms L_nonneg
  have "\<bar>s - t\<bar> * L \<le> abs (t1 - t0) / Suc subdivide_count * L"
    by (rule mult_right_mono)
  also have "\<dots> < 1"
    using subdivide_count
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma subdivide_lipschitz_lemma:
  assumes st: "s \<in> {a -- b}" "t \<in> {a -- b}"
  assumes "abs (b - a) \<le> abs (t1 - t0) / Suc subdivide_count"
  shows "\<bar>s - t\<bar> * L < 1"
  apply (rule subdivide_lipschitz)
  apply (rule order_trans[where y="abs (b - a)"])
  using assms
  by (auto simp: closed_segment_real split: if_splits)

definition "step = (t1 - t0) / Suc subdivide_count"

lemma last_step: "t0 + real (Suc subdivide_count) * step = t1"
  by (auto simp: step_def)

lemma step_in_segment:
  assumes "0 \<le> i" "i \<le> real (Suc subdivide_count)"
  shows "t0 + i * step \<in> closed_segment t0 t1"
  unfolding closed_segment_real step_def
proof (clarsimp, safe)
  assume "t0 \<le> t1"
  then have "(t1 - t0) * i \<le> (t1 - t0) * (1 + subdivide_count)"
    using assms
    by (auto intro!: mult_left_mono)
  then show "t0 + i * (t1 - t0) / (1 + real subdivide_count) \<le> t1"
    by (simp add: field_simps)
next
  assume "\<not>t0 \<le> t1"
  then have "(1 + subdivide_count) * (t0 - t1) \<ge> i * (t0 - t1)"
    using assms
    by (auto intro!: mult_right_mono)
  then show "t1 \<le> t0 + i * (t1 - t0) / (1 + real subdivide_count)"
    by (simp add: field_simps)
  show "i * (t1 - t0) / (1 + real subdivide_count) \<le> 0"
    using \<open>\<not>t0 \<le> t1\<close>
    by (auto simp: divide_simps mult_le_0_iff assms)
qed (auto intro!: divide_nonneg_nonneg mult_nonneg_nonneg assms)

lemma subset_T1:
  fixes s::real and i::nat
  assumes "s \<in> closed_segment t0 (t0 + i * step)"
  assumes "i \<le> Suc subdivide_count"
  shows "s \<in> {t0 -- t1}"
  using closed_segment_closed_segment_subset assms of_nat_le_iff of_nat_0_le_iff step_in_segment
  by blast

lemma subset_T: "{t0 -- t1} \<subseteq> T" and subset_TI: "s \<in> {t0 -- t1} \<Longrightarrow> s \<in> T"
  using closed_segment_iv_subset_domain mem_t1 by blast+

primrec psolution::"nat \<Rightarrow> real \<Rightarrow> 'a" where
  "psolution 0 t = x0"
| "psolution (Suc i) t = unique_on_bounded_closed.fixed_point
    (t0 + real i * step) {t0 + real i * step -- t0 + real (Suc i) * step}
    (psolution i (t0 + real i * step)) f X t"

definition "psolutions t = psolution (LEAST i. t \<in> closed_segment (t0 + real (i - 1) * step) (t0 + real i * step)) t"

lemma psolutions_usolves_until_step:
  assumes i_le: "i \<le> Suc subdivide_count"
  shows "(psolutions usolves_ode f from t0) (closed_segment t0 (t0 + real i * step)) X"
proof cases
  assume "t0 = t1"
  then have "step = 0"
    unfolding step_def by simp
  then show ?thesis by (simp add: psolutions_def iv_defined usolves_ode_singleton)
next
  assume "t0 \<noteq> t1"
  then have "step \<noteq> 0"
    by (simp add: step_def)
  define S where "S \<equiv> \<lambda>i. closed_segment (t0 + real (i - 1) * step) (t0 + real i * step)"
  have solution_eq: "psolutions \<equiv> \<lambda>t. psolution (LEAST i. t \<in> S i) t"
    by (simp add: psolutions_def[abs_def] S_def)
  show ?thesis
    unfolding solution_eq
    using i_le
  proof (induction i)
    case 0 then show ?case by (simp add: iv_defined usolves_ode_singleton S_def)
  next
    case (Suc i)
    let ?sol = "\<lambda>t. psolution (LEAST i. t \<in> S i) t"
    let ?pi = "t0 + real (i - Suc 0) * step" and ?i = "t0 + real i * step" and ?si = "t0 + (1 + real i) * step"
    from Suc have ui: "(?sol usolves_ode f from t0) (closed_segment t0 (t0 + real i * step)) X"
      by simp

    from usolves_odeD(1)[OF Suc.IH] Suc
    have IH_sol: "(?sol solves_ode f) (closed_segment t0 ?i) X"
      by simp

    have Least_eq_t0[simp]: "(LEAST n. t0 \<in> S n) = 0"
      by (rule Least_equality) (auto simp add: S_def)
    have Least_eq[simp]: "(LEAST n. t0 + real i * step \<in> S n) = i" for i
      apply (rule Least_equality)
      subgoal by (simp add: S_def)
      subgoal
        using \<open>step \<noteq> 0\<close>
        by (cases "step \<ge> 0")
          (auto simp add: S_def closed_segment_real zero_le_mult_iff split: if_split_asm)
      done

    have "y = t0 + real i * s"
      if "t0 + (1 + real i) * s \<le> t" "t \<le> y" "y \<le> t0 + real i * s" "t0 \<le> y"
      for y i s t
    proof -
      from that have "(1 + real i) * s \<le> real i * s" "0 \<le> real i * s"
        by arith+
      have "s + (t0 + s * real i) \<le> t \<Longrightarrow> t \<le> y \<Longrightarrow> y \<le> t0 + s * real i \<Longrightarrow> t0 \<le> y \<Longrightarrow> y = t0 + s * real i"
        by (metis add_decreasing2 eq_iff le_add_same_cancel2 linear mult_le_0_iff of_nat_nonneg order.trans)
      then show ?thesis using that
        by (simp add: algebra_simps)
    qed
    then have segment_inter:
      "xa = t0 + real i * step"
      if
      "t \<in> {t0 + real (Suc i - 1) * step--t0 + real (Suc i) * step}"
      "xa \<in> closed_segment (t0 + real i * step) t" "xa \<in> closed_segment t0 (t0 + real i * step)"
      for xa t
      apply (cases "step > 0"; cases "step = 0")
      using that
      by (auto simp: S_def closed_segment_real split: if_split_asm)

    have right_cond: "t0 \<le> t" "t \<le> t1" if "t0 + real i * step \<le> t" "t \<le> t0 + (step + real i * step)" for t
    proof -
      from that have "0 \<le> step" by simp
      with last_step have "t0 \<le> t1"
        by (metis le_add_same_cancel1 of_nat_0_le_iff zero_le_mult_iff)
      from that have "t0 \<le> t - real i * step" by simp
      also have "\<dots> \<le> t" using that by (auto intro!: mult_nonneg_nonneg)
      finally show "t0 \<le> t" .
      have "t \<le> t0 + (real (Suc i) * step)" using that by (simp add: algebra_simps)
      also have "\<dots> \<le> t1"
      proof -
        have "real (Suc i) * (t1 - t0) \<le> real (Suc subdivide_count) * (t1 - t0)"
          using Suc.prems \<open>t0 \<le> t1\<close>
          by (auto intro!: mult_mono)
        then show ?thesis by (simp add: divide_simps algebra_simps step_def)
      qed
      finally show "t \<le> t1" .
    qed
    have left_cond: "t1 \<le> t" "t \<le> t0" if "t0 + (step + real i * step) \<le> t" "t \<le> t0 + real i * step" for t
    proof -
      from that have "step \<le> 0" by simp
      with last_step have "t1 \<le> t0"
        by (metis add_le_same_cancel1 mult_nonneg_nonpos of_nat_0_le_iff)
      from that have "t0 \<ge> t - real i * step" by simp
      also have "t - real i * step \<ge> t" using that by (auto intro!: mult_nonneg_nonpos)
      finally (xtrans) show "t \<le> t0" .
      have "t \<ge> t0 + (real (Suc i) * step)" using that by (simp add: algebra_simps)
      also have " t0 + (real (Suc i) * step) \<ge> t1"
      proof -
        have "real (Suc i) * (t0 - t1) \<le> real (Suc subdivide_count) * (t0 - t1)"
          using Suc.prems \<open>t0 \<ge> t1\<close>
          by (auto intro!: mult_mono)
        then show ?thesis by (simp add: divide_simps algebra_simps step_def)
      qed
      finally (xtrans) show "t1 \<le> t" .
    qed

    interpret l: self_mapping "S (Suc i)" ?i "?sol ?i" f X
    proof unfold_locales
      show "?sol ?i \<in> X"
        using solves_odeD(2)[OF usolves_odeD(1)[OF ui], of "?i"]
        by (simp add: S_def)
      fix x t assume t[unfolded S_def]: "t \<in> S (Suc i)"
        and x: "x ?i = ?sol ?i" "x \<in> closed_segment ?i t \<rightarrow> X"
        and cont: "continuous_on (closed_segment ?i t) x"

      let ?if = "\<lambda>t. if t \<in> closed_segment t0 ?i then ?sol t else x t"
      let ?f = "\<lambda>t. f t (?if t)"
      have sol_mem: "?sol s \<in> X" if "s \<in> closed_segment t0 ?i" for s
        by (auto simp: subset_T1 intro!: solves_odeD[OF IH_sol] that)

      from x(1) have "x ?i + ivl_integral ?i t (\<lambda>t. f t (x t)) = ?sol ?i + ivl_integral ?i t (\<lambda>t. f t (x t))"
        by simp
      also have "?sol ?i = ?sol t0 + ivl_integral t0 ?i (\<lambda>t. f t (?sol t))"
        apply (subst solution_fixed_point)
        apply (rule usolves_odeD[OF ui])
        by simp_all
      also have "ivl_integral t0 ?i (\<lambda>t. f t (?sol t)) = ivl_integral t0 ?i ?f"
        by (simp cong: ivl_integral_cong)
      also
      have psolution_eq: "x (t0 + real i * step) = psolution i (t0 + real i * step) \<Longrightarrow>
        ta \<in> {t0 + real i * step--t} \<Longrightarrow>
        ta \<in> {t0--t0 + real i * step} \<Longrightarrow> psolution (LEAST i. ta \<in> S i) ta = x ta" for ta
        by (subst segment_inter[OF t], assumption, assumption)+ simp
      have "ivl_integral ?i t (\<lambda>t. f t (x t)) = ivl_integral ?i t ?f"
        by (rule ivl_integral_cong) (simp_all add: x psolution_eq)
      also
      from t right_cond(1) have cs: "closed_segment t0 t = closed_segment t0 ?i \<union> closed_segment ?i t"
        by (intro closed_segment_Un[symmetric])
          (auto simp: closed_segment_real algebra_simps mult_le_0_iff split: if_split_asm
            intro!: segment_inter segment_inter[symmetric])
      have cont_if: "continuous_on (closed_segment t0 t) ?if"
        unfolding cs
        using x Suc.prems cont t psolution_eq
        by (auto simp: subset_T1 T_def intro!: continuous_on_cases solves_ode_continuous_on[OF IH_sol])
      have t_mem: "t \<in> closed_segment t0 t1"
        using x Suc.prems t
        apply -
        apply (rule closed_segment_closed_segment_subset, assumption)
        apply (rule step_in_segment, force, force)
        apply (rule step_in_segment, force, force)
        done
      have segment_subset: "ta \<in> {t0 + real i * step--t} \<Longrightarrow> ta \<in> {t0--t1}" for ta
        using x Suc.prems
        apply -
        apply (rule closed_segment_closed_segment_subset, assumption)
        subgoal by (rule step_in_segment; force)
        subgoal by (rule t_mem)
        done
      have cont_f: "continuous_on (closed_segment t0 t) ?f"
        apply (rule continuous_intros)
        apply (rule continuous_intros)
        apply (rule cont_if)
        unfolding cs
        using x Suc.prems
         apply (auto simp: subset_T1 segment_subset intro!: sol_mem subset_TI)
        done
      have "?sol t0 + ivl_integral t0 ?i ?f + ivl_integral ?i t ?f = ?if t0 + ivl_integral t0 t ?f"
        by (auto simp: cs intro!: ivl_integral_combine integrable_continuous_closed_segment
          continuous_on_subset[OF cont_f])
      also have "\<dots> \<in> X"
        apply (rule self_mapping)
        apply (rule subset_TI)
        apply (rule t_mem)
        using x cont_if
        by (auto simp: subset_T1 Pi_iff cs intro!: sol_mem)
      finally
      have "x ?i + ivl_integral ?i t (\<lambda>t. ?f t) \<in> X" .
      also have "ivl_integral ?i t (\<lambda>t. ?f t) = ivl_integral ?i t (\<lambda>t. f t (x t))"
        apply (rule ivl_integral_cong[OF _ refl refl])
        using x
        by (auto simp: segment_inter psolution_eq)
      finally
      show "x ?i + ivl_integral ?i t (\<lambda>t. f t (x t)) \<in> X" .
    qed (auto simp add: S_def closed_segment_real is_interval_closed_interval)
    have "S (Suc i) \<subseteq> T"
      unfolding S_def
      apply (rule subsetI)
      apply (rule subset_TI)
    proof (cases "step = 0")
      case False
      fix x assume x: "x \<in> {t0 + real (Suc i - 1) * step--t0 + real (Suc i) * step}"
      from x have nn: "((x - t0) / step) \<ge> 0"
        using False right_cond(1)[of x] left_cond(2)[of x]
        by (auto simp: closed_segment_real divide_simps algebra_simps split: if_splits)
      have "t1 < t0 \<Longrightarrow> t1 \<le> x" "t1 > t0 \<Longrightarrow> x \<le> t1"
        using x False right_cond(1,2)[of x] left_cond(1,2)[of x]
        by (auto simp: closed_segment_real algebra_simps split: if_splits)
      then have le: "(x - t0) / step \<le> 1 + real subdivide_count"
        unfolding step_def
        by (auto simp: divide_simps)
      have "x = t0 + ((x - t0) / step) * step"
        using False
        by auto
      also have "\<dots> \<in> {t0 -- t1}"
        by (rule step_in_segment) (auto simp: nn le)
      finally show "x \<in> {t0 -- t1}" by simp
    qed simp
    have algebra: "(1 + real i) * (t1 - t0) - real i * (t1 - t0) = t1 - t0"
      by (simp only: algebra_simps)
    interpret l: unique_on_bounded_closed ?i "S (Suc i)" "?sol ?i" f X L
      apply unfold_locales
      subgoal by (auto simp: S_def)
      subgoal using \<open>S (Suc i) \<subseteq> T\<close> by (auto intro!: continuous_intros simp: split_beta')
      subgoal using \<open>S (Suc i) \<subseteq> T\<close> by (auto intro!: lipschitz)
      subgoal by (rule subdivide_lipschitz_lemma) (auto simp add: step_def divide_simps algebra S_def)
      done
    note ui
    moreover
    have mem_SI: "t \<in> closed_segment ?i ?si \<Longrightarrow> t \<in> S (if t = ?i then i else Suc i)" for t
      by (auto simp: S_def)
    have min_S: "(if t = t0 + real i * step then i else Suc i) \<le> y"
      if "t \<in> closed_segment (t0 + real i * step) (t0 + (1 + real i) * step)"
        "t \<in> S y"
      for y t
      apply (cases "t = t0 + real i * step")
      subgoal using that \<open>step \<noteq> 0\<close>
        by (auto simp add: S_def closed_segment_real algebra_simps zero_le_mult_iff split: if_splits )
      subgoal premises ne
      proof (cases)
        assume "step > 0"
        with that have "t0 + real i * step \<le> t" "t \<le> t0 + (1 + real i) * step"
          "t0 + real (y - Suc 0) * step \<le> t" "t \<le> t0 + real y * step"
          by (auto simp: closed_segment_real S_def)
        then have "real i * step < real y * step" using \<open>step > 0\<close> ne
          by arith
        then show ?thesis using \<open>step > 0\<close> that by (auto simp add: closed_segment_real S_def)
      next
        assume "\<not> step > 0" with \<open>step \<noteq> 0\<close> have "step < 0" by simp
        with that have "t0 + (1 + real i) * step \<le> t" "t \<le> t0 + real i * step"
          "t0 + real y * step \<le> t" "t \<le> t0 + real (y - Suc 0) * step" using ne
          by (auto simp: closed_segment_real S_def diff_Suc zero_le_mult_iff split: if_splits nat.splits)
        then have "real y * step < real i * step"
          using \<open>step < 0\<close> ne
          by arith
        then show ?thesis using \<open>step < 0\<close> by (auto simp add: closed_segment_real S_def)
      qed
      done
    have "(?sol usolves_ode f from ?i) (closed_segment ?i ?si) X"
      apply (subst usolves_ode_cong)
      apply (subst Least_equality)
      apply (rule mem_SI) apply assumption
      apply (rule min_S) apply assumption apply assumption
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (subst usolves_ode_cong[where y="psolution (Suc i)"])
      using l.fixed_point_iv[unfolded Least_eq]
      apply (simp add: S_def; fail)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      using l.fixed_point_usolves_ode
      apply -
      apply (simp)
      apply (simp add: S_def)
      done
    moreover have "t \<in> {t0 + real i * step--t0 + (step + real i * step)} \<Longrightarrow>
         t \<in> {t0--t0 + real i * step} \<Longrightarrow> t = t0 + real i * step" for t
      by (subst segment_inter[rotated], assumption, assumption) (auto simp: algebra_simps)
    ultimately
    have "((\<lambda>t. if t \<in> closed_segment t0 ?i then ?sol t else ?sol t)
      usolves_ode
      (\<lambda>t. if t \<in> closed_segment t0 ?i then f t else f t) from t0)
      (closed_segment t0 ?i \<union> closed_segment ?i ?si) X"
      by (intro connection_usolves_ode[where t="?i"]) (auto simp: algebra_simps split: if_split_asm)
    also have "closed_segment t0 ?i \<union> closed_segment ?i ?si = closed_segment t0 ?si"
      apply (rule closed_segment_Un)
      by (cases "step < 0")
        (auto simp: closed_segment_real zero_le_mult_iff mult_le_0_iff
          intro!: mult_right_mono
          split: if_split_asm)
    finally show ?case by simp
  qed
qed

lemma psolutions_usolves_ode: "(psolutions usolves_ode f from t0) {t0 -- t1} X"
proof -
  let ?T = "closed_segment t0 (t0 + real (Suc subdivide_count) * step)"
  have "(psolutions usolves_ode f from t0) ?T X"
    by (rule psolutions_usolves_until_step) simp
  also have "?T = {t0 -- t1}" unfolding last_step ..
  finally show ?thesis .
qed

end

definition "solution t = (if t \<le> t0 then psolutions tmin t else psolutions tmax t)"

lemma solution_eq_left: "tmin \<le> t \<Longrightarrow> t \<le> t0 \<Longrightarrow> solution t = psolutions tmin t"
  by (simp add: solution_def)

lemma solution_eq_right: "t0 \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> solution t = psolutions tmax t"
  by (simp add: solution_def psolutions_def)

lemma solution_usolves_ode: "(solution usolves_ode f from t0) T X"
proof -
  from psolutions_usolves_ode[OF tmin(2)] tmin_le_t0
  have u1: "(psolutions tmin usolves_ode f from t0) {tmin .. t0} X"
    by (auto simp: closed_segment_real split: if_splits)
  from psolutions_usolves_ode[OF tmax(2)] tmin_le_t0
  have u2: "(psolutions tmax usolves_ode f from t0) {t0 .. tmax} X"
    by (auto simp: closed_segment_real split: if_splits)
  have "(solution usolves_ode f from t0) ({tmin .. t0} \<union> {t0 .. tmax}) (X \<union> X)"
    apply (rule usolves_ode_union_closed[where t=t0])
    subgoal by (subst usolves_ode_cong[where y="psolutions tmin"]) (auto simp: solution_eq_left u1)
    subgoal
      using u2
      by (rule usolves_ode_congI) (auto simp: solution_eq_right)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done
  also have "{tmin .. t0} \<union> {t0 .. tmax} = T"
    by (simp add: T_split[symmetric])
  finally show ?thesis by simp
qed

lemma solution_solves_ode: "(solution solves_ode f) T X"
  by (rule usolves_odeD[OF solution_usolves_ode])

lemma solution_iv[simp]: "solution t0 = x0"
  by (auto simp: solution_def psolutions_def)

end


subsection \<open>Picard-Lindeloef for @{term "X = UNIV"}\<close>
text\<open>\label{sec:pl-us}\<close>

locale unique_on_strip =
  compact_interval T +
  continuous_rhs T UNIV f +
  global_lipschitz T UNIV f L
  for t0 and T and f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach" and L +
  assumes iv_time: "t0 \<in> T"
begin

sublocale unique_on_closed t0 T x0 f UNIV L for x0
  by (-, unfold_locales) (auto simp: iv_time)

end


subsection \<open>Picard-Lindeloef on cylindric domain\<close>
text\<open>\label{sec:pl-rect}\<close>

locale solution_in_cylinder =
  continuous_rhs T "cball x0 b" f +
  compact_interval T
  for t0 T x0 b and f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach" +
  fixes X B
  defines "X \<equiv> cball x0 b"
  assumes initial_time_in: "t0 \<in> T"
  assumes norm_f: "\<And>x t. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f t x) \<le> B"
  assumes b_pos: "b \<ge> 0"
  assumes e_bounded: "\<And>t. t \<in> T \<Longrightarrow> dist t t0 \<le> b / B"
begin

lemmas cylinder = X_def

lemma B_nonneg: "B \<ge> 0"
proof -
  have "0 \<le> norm (f t0 x0)" by simp
  also from b_pos norm_f have "... \<le> B" by (simp add: initial_time_in X_def)
  finally show ?thesis by simp
qed

lemma in_bounds_derivativeI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (y s))) (open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi> \<in> closed_segment t0 t \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
proof cases
  assume "b = 0 \<or> B = 0" with assms e_bounded T_def have "t = t0"
    by auto
  thus ?thesis using b_pos init by simp
next
  assume "\<not>(b = 0 \<or> B = 0)"
  hence "b > 0" "B > 0" using B_nonneg b_pos by auto
  show ?thesis
  proof cases
    assume "t0 \<noteq> t"
    then have b_less: "B * abs (t - t0) \<le> b"
      using b_pos e_bounded using \<open>b > 0\<close> \<open>B > 0\<close> \<open>t \<in> T\<close>
      by (auto simp: field_simps initial_time_in dist_real_def abs_real_def closed_segment_real split: if_split_asm)
    define b where  "b \<equiv> B * abs (t - t0)"
    have "b > 0" using \<open>t0 \<noteq> t\<close> by (auto intro!: mult_pos_pos simp: algebra_simps b_def \<open>B > 0\<close>)
    from cont
    have closed: "closed {s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}}"
      by (intro continuous_closed_preimage continuous_intros closed_segment)
    have exceeding: "{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
    proof (rule ccontr)
      assume "\<not>{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
      hence notempty: "{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<noteq> {}"
        and not_max: "{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<noteq> {t}"
        by auto
      obtain s where s_bound: "s \<in> closed_segment t0 t"
        and exceeds: "norm (x s - x t0) \<in> {b..}"
        and min: "\<forall>t2\<in>closed_segment t0 t.
          norm (x t2 - x t0) \<in> {b..} \<longrightarrow> dist t0 s \<le> dist t0 t2"
        by (rule distance_attains_inf[OF closed notempty, of t0]) blast
      have "s \<noteq> t0" using exceeds \<open>b > 0\<close> by auto
      have st: "closed_segment t0 t \<supseteq> open_segment t0 s" using s_bound
        by (auto simp: closed_segment_real open_segment_real)
      from cont have cont: "continuous_on (closed_segment t0 s) x"
        by (rule continuous_on_subset)
          (insert b_pos closed_segment_subset_domain s_bound, auto simp: closed_segment_real)
      have bnd_cont: "continuous_on (closed_segment t0 s) (op * B)"
        and bnd_deriv: "(op * B has_vderiv_on (\<lambda>_. B)) (open_segment t0 s)"
        by (auto intro!: continuous_intros derivative_eq_intros
          simp: has_vector_derivative_def has_vderiv_on_def)
      {
        fix ss assume ss: "ss \<in> open_segment t0 s"
        with st have "ss \<in> closed_segment t0 t" by auto
        have less_b: "norm (x ss - x t0) < b"
        proof (rule ccontr)
          assume "\<not> norm (x ss - x t0) < b"
          hence "norm (x ss - x t0) \<in> {b..}" by auto
          from min[rule_format, OF \<open>ss \<in> closed_segment t0 t\<close> this]
          show False using ss \<open>s \<noteq> t0\<close>
            by (auto simp: dist_real_def open_segment_real split_ifs)
        qed
        have "norm (f ss (y ss)) \<le> B"
          apply (rule norm_f)
          subgoal using ss st closed_segment_subset_domain[OF initial_time_in \<open>t \<in> T\<close>] by auto
          subgoal using ss st b_less less_b
            by (intro y_bounded)
              (auto simp: X_def dist_norm b_def init norm_minus_commute mem_cball)
          done
      } note bnd = this
      have subs: "open_segment t0 s \<subseteq> open_segment t0 t" using s_bound \<open>s \<noteq> t0\<close>
        by (auto simp: closed_segment_real open_segment_real)
      with differentiable_bound_general_open_segment[OF cont bnd_cont has_vderiv_on_subset[OF solves subs]
        bnd_deriv bnd]
      have "norm (x s - x t0) \<le> B * \<bar>s - t0\<bar>"
        by (auto simp: algebra_simps[symmetric] abs_mult B_nonneg)
      also
      have "s \<noteq> t"
        using s_bound exceeds min not_max
        by (auto simp: dist_norm closed_segment_real split_ifs)
      hence "B * \<bar>s - t0\<bar> < \<bar>t - t0\<bar> * B"
        using s_bound \<open>B > 0\<close>
        by (intro le_neq_trans)
          (auto simp: algebra_simps closed_segment_real split_ifs
            intro!: mult_left_mono)
      finally have "norm (x s - x t0) < \<bar>t - t0\<bar> * B" .
      moreover
      {
        have "b \<ge> \<bar>t - t0\<bar> * B" by (simp add: b_def algebra_simps)
        also from exceeds have "norm (x s - x t0) \<ge> b" by simp
        finally have "\<bar>t - t0\<bar> * B \<le> norm (x s - x t0)" .
      }
      ultimately show False by simp
    qed note mvt_result = this
    from cont assms
    have cont_diff: "continuous_on (closed_segment t0 t) (\<lambda>xa. x xa - x t0)"
      by (auto intro!: continuous_intros)
    have "norm (x t - x t0) \<le> b"
    proof (rule ccontr)
      assume H: "\<not> norm (x t - x t0) \<le> b"
      hence "b \<in> closed_segment (norm (x t0 - x t0)) (norm (x t - x t0))"
        using assms T_def \<open>0 < b\<close>
        by (auto simp: closed_segment_real )
      from IVT'_closed_segment_real[OF this continuous_on_norm[OF cont_diff]]
      obtain s where s: "s \<in> closed_segment t0 t" "norm (x s - x t0) = b"
        using \<open>b > 0\<close> by auto
      have "s \<in> {s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}}"
        using s \<open>t \<in> T\<close> by (auto simp: initial_time_in)
      with mvt_result have "s = t" by blast
      hence "s = t" using s \<open>t \<in> T\<close> by (auto simp: initial_time_in)
      with s H show False by simp
    qed
    hence "x t \<in> cball x0 b" using init
      by (auto simp: dist_commute dist_norm[symmetric] mem_cball)
    thus "x t \<in> cball x0 (B * abs (t - t0))" unfolding cylinder b_def .
  qed (simp add: init[symmetric])
qed

lemma in_bounds_derivative_globalI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (y s))) (open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi> \<in> closed_segment t0 t \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> X"
proof -
  from in_bounds_derivativeI[OF assms]
  have "x t \<in> cball x0 (B * abs (t - t0))" .
  moreover have "B * abs (t - t0) \<le> b" using e_bounded b_pos B_nonneg \<open>t \<in> T\<close>
    by (cases "B = 0")
      (auto simp: field_simps initial_time_in dist_real_def abs_real_def closed_segment_real split: if_splits)
  ultimately show ?thesis by (auto simp: cylinder mem_cball)
qed

lemma integral_in_bounds:
  assumes "t \<in> T" "x t0 = x0" "x \<in> {t0 -- t} \<rightarrow> X"
  assumes cont[continuous_intros]: "continuous_on ({t0 -- t}) x"
  shows "x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> X" (is "_ + ?ix t \<in> X")
proof cases
  assume "t = t0"
  thus ?thesis by (auto simp: cylinder b_pos assms)
next
  assume "t \<noteq> t0"
  from closed_segment_subset_domain[OF initial_time_in]
  have cont_f:"continuous_on {t0 -- t} (\<lambda>t. f t (x t))"
    using assms
    by (intro continuous_intros)
      (auto intro: cont continuous_on_subset[OF continuous] simp: cylinder split: if_splits)
  from closed_segment_subset_domain[OF initial_time_in \<open>t \<in> T\<close>]
  have subsets: "s \<in> {t0--t} \<Longrightarrow> s \<in> T" "s \<in> open_segment t0 t \<Longrightarrow> s \<in> {t0--t}" for s
    by (auto simp: closed_segment_real open_segment_real initial_time_in split: if_split_asm)
  show ?thesis
    unfolding \<open>x t0 = _\<close>
    using assms \<open>t \<noteq> t0\<close>
    by (intro in_bounds_derivative_globalI[where y=x and x="\<lambda>t. x0 + ?ix t"])
      (auto simp: initial_time_in subsets cylinder has_vderiv_on_def
        split: if_split_asm
        intro!: cont_f has_vector_derivative_const integrable_continuous_closed_segment
          has_vector_derivative_within_subset[OF ivl_integral_has_vector_derivative]
          has_vector_derivative_add[THEN vector_derivative_eq_rhs]
          continuous_intros indefinite_ivl_integral_continuous)
qed

lemma solves_in_cone:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (x s))) (open_segment t0 t)"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
  using assms
  by (rule in_bounds_derivativeI)

lemma is_solution_in_cone:
  assumes "t \<in> T"
  assumes sol: "(x solves_ode f) (closed_segment t0 t) Y" and iv: "x t0 = x0"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
  using solves_odeD[OF sol] \<open>t \<in> T\<close>
  by (intro solves_in_cone)
    (auto intro!: assms vderiv_on_continuous_on segment_open_subset_closed
      intro: has_vderiv_on_subset simp: initial_time_in)

lemma cone_subset_domain:
  assumes "t \<in> T"
  shows "cball x0 (B * \<bar>t - t0\<bar>) \<subseteq> X"
  using e_bounded[OF assms] B_nonneg b_pos
  unfolding cylinder
  by (intro subset_cball) (auto simp: dist_real_def divide_simps algebra_simps split: if_splits)

lemma is_solution_in_domain:
  assumes "t \<in> T"
  assumes sol: "(x solves_ode f) (closed_segment t0 t) Y" and iv: "x t0 = x0"
  shows "x t \<in> X"
  using is_solution_in_cone[OF assms] cone_subset_domain[OF \<open>t \<in> T\<close>]
  by (rule set_rev_mp)

lemma solves_ode_on_subset_domain:
  assumes sol: "(x solves_ode f) S Y" and iv: "x t0 = x0"
    and ivl: "t0 \<in> S" "is_interval S" "S \<subseteq> T"
  shows "(x solves_ode f) S X"
proof (rule solves_odeI)
  show "(x has_vderiv_on (\<lambda>t. f t (x t))) S" using solves_odeD(1)[OF sol] .
  show "x s \<in> X" if s: "s \<in> S" for s
  proof -
    from s assms have "s \<in> T"
      by auto
    moreover
    have "{t0--s} \<subseteq> S"
      by (rule closed_segment_subset) (auto simp: s assms is_interval_convex)
    with sol have "(x solves_ode f) {t0--s} Y"
      using order_refl
      by (rule solves_ode_on_subset)
    ultimately
    show ?thesis using iv
      by (rule is_solution_in_domain)
  qed
qed

lemma usolves_ode_on_subset:
  assumes x: "(x usolves_ode f from t0) T X" and iv: "x t0 = x0"
  assumes "t0 \<in> S" "is_interval S" "S \<subseteq> T" "X \<subseteq> Y"
  shows "(x usolves_ode f from t0) S Y"
proof (rule usolves_odeI)
  show "(x solves_ode f) S Y" by (rule solves_ode_on_subset[OF usolves_odeD(1)[OF x]]; fact)
  show "t0 \<in> S" "is_interval S" by fact+
  fix z t assume "{t0 -- t} \<subseteq> S" and z: "(z solves_ode f) {t0--t} Y" "z t0 = x t0"
  then have "z t0 = x0" "t0 \<in> {t0--t}" "is_interval {t0--t}" "{t0--t} \<subseteq> T"
    using iv \<open>S \<subseteq> T\<close> by (auto simp: is_interval_convex_1)
  with z(1) have zX: "(z solves_ode f) {t0 -- t} X"
    by (rule solves_ode_on_subset_domain)
  show "z t = x t"
    apply (rule usolves_odeD(4)[OF x _ _ _ zX])
    using \<open>{t0 -- t} \<subseteq> S\<close> \<open>S \<subseteq> T\<close>
    by (auto simp: is_interval_convex_1 \<open>z t0 = x t0\<close>)
qed

lemma usolves_ode_on_superset_domain:
  assumes "(x usolves_ode f from t0) T X" and iv: "x t0 = x0"
  assumes "X \<subseteq> Y"
  shows "(x usolves_ode f from t0) T Y"
  using assms(1,2) usolves_odeD(2,3)[OF assms(1)] order_refl assms(3)
  by (rule usolves_ode_on_subset)

end

locale unique_on_cylinder =
  solution_in_cylinder t0 T x0 b f X B +
  global_lipschitz T X f L
  for t0 T x0 b X f B L
begin

sublocale unique_on_closed t0 T x0 f X L
  apply unfold_locales
  subgoal by (simp add: initial_time_in)
  subgoal by (simp add: X_def b_pos)
  subgoal by (auto intro!: integral_in_bounds simp: initial_time_in)
  subgoal by (auto intro!: continuous_intros simp: split_beta' X_def)
  subgoal by (simp add: X_def)
  done

end

locale derivative_on_prod =
  fixes T X and f::"real \<Rightarrow> 'a::banach \<Rightarrow> 'a" and f':: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow> 'a"
  assumes f': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow> ((\<lambda>(t, x). f t x) has_derivative (f' tx)) (at tx within (T \<times> X))"
begin

lemma f'_comp[derivative_intros]:
  "(g has_derivative g') (at s within S) \<Longrightarrow> (h has_derivative h') (at s within S) \<Longrightarrow>
  s \<in> S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> g x \<in> T) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> h x \<in> X) \<Longrightarrow>
  ((\<lambda>x. f (g x) (h x)) has_derivative (\<lambda>y. f' (g s, h s) (g' y, h' y))) (at s within S)"
  apply (rule has_derivative_in_compose2[OF f' _ _ has_derivative_Pair, unfolded split_beta' fst_conv snd_conv, of g h S s g' h'])
  apply auto
  done

lemma derivative_on_prod_subset:
  assumes "X' \<subseteq> X"
  shows "derivative_on_prod T X' f f'"
  using assms
  by (unfold_locales) (auto intro!: derivative_eq_intros)

end

end
