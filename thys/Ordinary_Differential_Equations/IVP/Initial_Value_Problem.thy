section\<open>Initial Value Problems\<close>
theory Initial_Value_Problem
imports "../ODE_Auxiliarities"
begin

lemma dist_component_le:
  fixes x y::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  using assms
  by (auto simp: euclidean_dist_l2[of x y] intro: member_le_setL2)

lemma setsum_inner_Basis_one: "i \<in> Basis \<Longrightarrow> (\<Sum>x\<in>Basis. x \<bullet> i) = 1"
  by (subst setsum.mono_neutral_right[where S="{i}"])
    (auto simp: inner_not_same_Basis)

lemma cball_in_cbox:
  fixes y::"'a::euclidean_space"
  shows "cball y r \<subseteq> cbox (y - r *\<^sub>R One) (y + r *\<^sub>R One)"
  unfolding scaleR_setsum_right interval_cbox cbox_def
proof safe
  fix x i::'a assume "i \<in> Basis" "x \<in> cball y r"
  with dist_component_le[OF \<open>i \<in> Basis\<close>, of y x]
  have "dist (y \<bullet> i) (x \<bullet> i) \<le> r" by simp
  thus "(y - setsum (op *\<^sub>R r) Basis) \<bullet> i \<le> x \<bullet> i"
    "x \<bullet> i \<le> (y + setsum (op *\<^sub>R r) Basis) \<bullet> i"
    by (auto simp add: inner_diff_left inner_add_left inner_setsum_left
      setsum_right_distrib[symmetric] setsum_inner_Basis_one \<open>i\<in>Basis\<close> dist_real_def)
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
    by (auto simp: dist_norm mult_left_mono)
qed

subsection \<open>Lipschitz continuity \label{sec:lipschitz}\<close>

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

lemma lipschitz_subset:
  assumes "lipschitz D f L"
  assumes "D' \<subseteq> D"
  shows "lipschitz D' f L"
  using lipschitzD[OF assms(1)] lipschitz_nonneg[OF assms(1)] assms(2)
  by (auto intro!: lipschitzI)

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

subsection \<open>Local Lipschitz continuity (uniformly for a family of functions)\<close>

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
    by (rule tendsto_within_nhd) auto
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
      intro!: less_imp_le[OF d(2)] lipschitz_subset[OF l] simp: dist_commute)
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
      by (auto simp: dist_commute)
    have "dist (f x y) (f a b) \<le> dist (f x y) (f x b) + dist (f x b) (f a b)"
      by (rule dist_triangle)
    also have "dist (f x y) (f x b) \<le> (abs L + 1) * dist y b"
      apply (rule lipschitzD[OF pos_lipschitz[OF L]])
      subgoal by fact
      subgoal
        using \<open>y \<in> X\<close> \<open>dist y b < u\<close>
        by (simp add: dist_commute)
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
      apply (simp add: LIMSEQ_subseq_LIMSEQ o_assoc lt'(2))
      apply (simp add: LIMSEQ_subseq_LIMSEQ ly'(3) o_assoc lt'(2))
      by (simp add: o_assoc lt'(3))
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
      with elim d[of "rx (ry (rt n))"]
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
        (metis tendsto_divide_0[OF tendsto_const] filterlim_at_top_imp_at_infinity filterlim_real_sequentially)
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
      by (auto simp: dist_commute Lim)
    moreover have "eventually (\<lambda>n. n > L) sequentially"
      by (metis filterlim_at_top_dense filterlim_real_sequentially)
    ultimately
    have "eventually (\<lambda>_. False) sequentially"
    proof eventually_elim
      case (elim n)
      hence "dist (f (?t n) (?y n)) (f (?t n) (?x n)) \<le> L * dist (?y n) (?x n)"
        using assms xy t
        unfolding dist_norm[symmetric]
        by (intro lipschitzD[OF L(2)]) auto
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
      (force intro: lipschitz_subset intro!: lipschitz_PairI)
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
    by (auto dest!: compact_imp_bounded simp: bounded_pos simp del: mem_cball)

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
        (auto intro!: B  simp: norm_blinfun.rep_eq[symmetric])
    then show ?thesis
      using \<open>0 < B\<close>
      by (auto intro!: lipschitzI simp: dist_norm)
  qed
  show "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. lipschitz (cball x u \<inter> X) (f t) L"
    by (force intro: exI[where x="min u v"] exI[where x=B] intro!: lipschitz simp: u v)
qed


subsection \<open>Solutions of IVPs \label{sec:solutions}\<close>

record 'a ivp =
  ivp_f :: "real \<times> 'a \<Rightarrow> 'a"
  ivp_t0 :: "real"
  ivp_x0 :: "'a"
  ivp_T :: "real set"
  ivp_X :: "'a set"

locale ivp =
  fixes i::"'a::banach ivp"
  assumes iv_defined: "ivp_t0 i \<in> ivp_T i" "ivp_x0 i \<in> ivp_X i"
begin

abbreviation "t0 \<equiv> ivp_t0 i"
abbreviation "x0 \<equiv> ivp_x0 i"
abbreviation "T \<equiv> ivp_T i"
abbreviation "X \<equiv> ivp_X i"
abbreviation "f \<equiv> ivp_f i"

definition is_solution where "is_solution x \<longleftrightarrow>
  x t0 = x0 \<and>
  (\<forall>t\<in>T.
    (x has_vector_derivative f (t, x t))
      (at t within T) \<and>
     x t \<in> X)"

definition "solution = (SOME x. is_solution x)"

lemma is_solutionD:
  assumes "is_solution x"
  shows
  "x t0 = x0"
  "\<And>t. t \<in> T \<Longrightarrow> (x has_vector_derivative f (t, x t)) (at t within T)"
  "\<And>t. t \<in> T \<Longrightarrow> x t \<in> X"
  using assms
  by (auto simp: is_solution_def)

lemma solution_continuous_on[intro, simp]:
  assumes "is_solution x"
  shows "continuous_on T x"
using is_solutionD[OF assms]
by (auto intro!: differentiable_imp_continuous_on
  simp add: differentiable_on_def differentiable_def has_vector_derivative_def)
  blast

lemma is_solutionI[intro]:
  assumes "x t0 = x0"
  assumes "\<And>t. t \<in> T \<Longrightarrow>
    (x has_vector_derivative f (t, x t)) (at t within T)"
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t \<in> X"
  shows "is_solution x"
  using assms
  unfolding is_solution_def by simp

lemma is_solution_cong:
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  shows "is_solution x = is_solution y"
proof -
  { fix t assume "t \<in> T"
    hence "(y has_vector_derivative f (t, y t)) (at t within T) =
      (x has_vector_derivative f (t, y t)) (at t within T)"
      using assms
      by (subst has_vector_derivative_cong) auto }
  thus ?thesis using assms iv_defined by (auto simp: is_solution_def)
qed

lemma solution_on_subset:
  assumes "t0 \<in> T'"
  assumes "T' \<subseteq> T"
  assumes "is_solution x"
  shows "ivp.is_solution (i\<lparr>ivp_T := T'\<rparr>) x"
proof -
  interpret ivp': ivp "i\<lparr>ivp_T := T'\<rparr>" using assms iv_defined
    by unfold_locales simp_all
  show ?thesis
  using assms is_solutionD[OF \<open>is_solution x\<close>]
  by (intro ivp'.is_solutionI) (auto intro:
    has_vector_derivative_within_subset[where s="T"])
qed

lemma solution_on_subset':
  assumes "t0 \<in> ivp_T i'"
  assumes "ivp_T i' \<subseteq> T"
  assumes "is_solution x"
  assumes "i' = i\<lparr>ivp_T:=ivp_T i'\<rparr>"
  shows "ivp.is_solution i' x"
  by (subst assms) (auto intro!: solution_on_subset assms)

lemma is_solution_on_superset_domain:
  assumes "is_solution y"
  assumes "X \<subseteq> X'"
  shows "ivp.is_solution (i \<lparr>ivp_X := X'\<rparr>) y"
proof -
  interpret ivp': ivp "i\<lparr>ivp_X:=X'\<rparr>" using assms iv_defined
    by unfold_locales auto
  show ?thesis
  using assms
  by (auto simp: is_solution_def ivp'.is_solution_def)
qed

lemma restriction_of_solution:
  assumes "t1 \<in> T'"
  assumes "x t1 \<in> X"
  assumes "T' \<subseteq> T"
  assumes x_sol: "is_solution x"
  shows "ivp.is_solution (i\<lparr>ivp_t0:=t1, ivp_x0:=x t1, ivp_T:=T'\<rparr>) x"
proof -
  interpret ivp': ivp "i\<lparr>ivp_t0:=t1, ivp_x0:=x t1, ivp_T:=T'\<rparr>"
    using assms iv_defined is_solutionD[OF x_sol]
    by unfold_locales simp_all
  show ?thesis
    using is_solutionD[OF x_sol] assms
    by (intro ivp'.is_solutionI)
      (auto intro: has_vector_derivative_within_subset[where t=T' and s=T])
qed

lemma mirror_solution:
  defines "mirror \<equiv> \<lambda>t. 2 * t0 - t"
  defines "mi \<equiv> i\<lparr>ivp_f := (\<lambda>(t, x). - f (mirror t, x)), ivp_T := mirror ` T\<rparr>"
  assumes sol: "is_solution x"
  shows "ivp.is_solution mi (x o mirror)"
proof -
  interpret mi: ivp mi
    using iv_defined
    by unfold_locales (auto simp: mi_def mirror_def)
  show ?thesis
    using is_solutionD[OF sol]
  proof (intro mi.is_solutionI)
    fix t
    assume "t \<in> mi.T"
    from is_solutionD[OF sol]
    have *: "\<And>t. t \<in> T \<Longrightarrow>
      (x has_derivative (\<lambda>a. a *\<^sub>R f (t, x t))) (at t within T)"
      by (auto simp: has_vector_derivative_def)
    show "(x o mirror has_vector_derivative mi.f (t, (x o mirror) t))
        (at t within mi.T)"
      using \<open>t \<in> mi.T\<close>
      by (auto simp: mi_def mirror_def has_vector_derivative_def
        intro!: derivative_eq_intros has_derivative_subset[OF *])
  qed (auto simp: mirror_def mi_def)
qed

lemma solution_mirror:
  defines "mirror \<equiv> \<lambda>t. 2 * t0 - t"
  defines "mi \<equiv> i\<lparr>ivp_f := (\<lambda>(t, x). - f (mirror t, x)), ivp_T := mirror ` T\<rparr>"
  assumes misol: "ivp.is_solution mi (x o mirror)"
  shows "is_solution x"
proof -
  interpret mi: ivp mi
    using iv_defined
    by unfold_locales (auto simp: mi_def mirror_def)
  have "op - (2 * t0) ` op - (2 * t0) ` T = T"
    "x o (\<lambda>t. 2 * t0 - t) o (\<lambda>t. 2 * t0 - t) = x"
    by force+
  thus ?thesis
    using mi.mirror_solution[of "x o mirror"] misol
    by (auto simp: mirror_def mi_def)
qed

lemma solution_mirror_eq:
  defines "mirror \<equiv> \<lambda>t. 2 * t0 - t"
  defines "mi \<equiv> i\<lparr>ivp_f := (\<lambda>(t, x). - f (mirror t, x)), ivp_T := mirror ` T\<rparr>"
  shows "is_solution x \<longleftrightarrow> ivp.is_solution mi (x o mirror)"
  using solution_mirror[of x] mirror_solution[of x]
  by (auto simp add: mirror_def mi_def)

lemma shift_autonomous_solution:
  assumes "is_solution y"
  assumes "x = y o (\<lambda>t.(t + ivp_t0 i - ivp_t0 j))"
  assumes "\<And>s t x. ivp_f i (s, x) = ivp_f i (t, x)"
  assumes "ivp_f j = ivp_f i"
  assumes "ivp_x0 j = ivp_x0 i"
  assumes "ivp_X j = ivp_X i"
  assumes "ivp_T j = op + (ivp_t0 j - ivp_t0 i) ` ivp_T i"
  shows "ivp.is_solution j x"
proof -
  interpret j: ivp j
    using iv_defined
    by (unfold_locales) (auto simp: assms)
  have image_collapse:
    "(\<lambda>t. t + t0 - ivp_t0 j) ` op + (ivp_t0 j - t0) ` T = ivp_T i"
    by force
  have deriv_id: "\<And>x F. ((\<lambda>t. t + ivp_t0 i - ivp_t0 j) has_vector_derivative 1) F"
    by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def)
  show ?thesis
    using is_solutionD[OF assms(1)]
    by (intro j.is_solutionI;
      force
        simp: assms image_collapse
        intro: deriv_id vector_diff_chain_within[THEN vector_derivative_eq_rhs])
qed

lemma shift_initial_value:
  assumes "is_solution y"
  assumes "ivp_t0 j \<in> ivp_T j"
  assumes "ivp_f j = ivp_f i"
  assumes "ivp_x0 j = y (ivp_t0 j)"
  assumes "ivp_X j = ivp_X i"
  assumes "ivp_T j \<subseteq> ivp_T i"
  shows "ivp.is_solution j y"
proof -
  interpret j: ivp j
    using iv_defined is_solutionD(3)[OF assms(1)] assms
    by (unfold_locales) auto
  show ?thesis
    using is_solutionD[OF assms(1)] assms
    by (auto intro!: j.is_solutionI
      has_vector_derivative_within_subset[where t="j.T" and s = T])
qed

end

locale has_solution = ivp +
  assumes exists_solution: "\<exists>x. is_solution x"
begin

lemma is_solution_solution[intro, simp]:
  shows "is_solution solution"
  using exists_solution unfolding solution_def by (rule someI_ex)

lemma solution:
  shows solution_t0: "solution t0 = x0"
    and solution_has_deriv: "\<And>t. t \<in> T \<Longrightarrow>
      (solution has_vector_derivative f (t, solution t)) (at t within T)"
    and solution_in_D: "\<And>t. t \<in> T \<Longrightarrow> solution t \<in> X"
  using is_solution_solution unfolding is_solution_def by auto

lemma has_solution_moved:
  assumes "ivp_t0 j \<in> ivp_T j"
  assumes "ivp_x0 j = ivp.solution i (ivp_t0 j)"
  assumes "ivp_X j = ivp_X i"
  assumes "ivp_T j \<subseteq> ivp_T i"
  assumes "ivp_f j = ivp_f i"
  shows "has_solution j"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) has_solution_axioms.intro has_solution_def
    is_solutionD(3) is_solution_solution ivp.intro set_mp shift_initial_value)

end

lemma (in ivp) singleton_has_solutionI:
  assumes "T = {t0}"
  shows "has_solution i"
  by unfold_locales (auto simp: has_vector_derivative_def assms
    intro!: has_derivative_singletonI bounded_linear_scaleR_left
    iv_defined exI[where x="\<lambda>x. x0"])

locale unique_solution = has_solution +
  assumes unique_solution: "\<And>y t. is_solution y \<Longrightarrow> t \<in> T \<Longrightarrow> y t = solution t"
    \<comment>"TODO: stronger uniqueness: assume @{term is_solution} without restriction
      to @{term X} and allow for shorter time intervals"

lemma (in ivp) unique_solutionI:
  assumes "is_solution x"
  assumes "\<And>y t. is_solution y \<Longrightarrow> t \<in> T \<Longrightarrow> y t = x t"
  shows "unique_solution i"
proof
  show "\<exists>x. is_solution x" using assms by blast
  then interpret has_solution by unfold_locales
  fix y t
  assume "is_solution y" "t\<in>T"
  from assms(2)[OF this] assms(2)[OF is_solution_solution \<open>t \<in> T\<close>]
  show "y t = solution t" by simp
qed

lemma (in ivp) singleton_unique_solutionI:
  assumes "T = {t0}"
  shows "unique_solution i"
  by (metis assms has_solution.is_solution_solution is_solutionD(1) singletonD
    singleton_has_solutionI unique_solutionI)

lemma (in unique_solution) shift_autonomous_unique_solution:
  assumes "x = y o (\<lambda>t.(t + ivp_t0 i - ivp_t0 j))"
  assumes "\<And>s t x. ivp_f i (s, x) = ivp_f i (t, x)"
  assumes "ivp_f j = ivp_f i"
  assumes "ivp_x0 j = ivp_x0 i"
  assumes "ivp_X j = ivp_X i"
  assumes "ivp_T j = op + (ivp_t0 j - ivp_t0 i) ` ivp_T i"
  shows "unique_solution j"
proof
  interpret j: ivp j
    using iv_defined
    by unfold_locales (auto simp: assms)
  show "j.t0 \<in> j.T" "j.x0 \<in> j.X" using j.iv_defined by auto
  show "\<exists>x. ivp.is_solution j x"
    by (auto simp: assms
      intro!: exI shift_autonomous_solution[OF is_solution_solution])
  then interpret j: has_solution j by unfold_locales
  fix t y assume t: "t \<in> j.T" and y_sol: "j.is_solution y"
  from t have ts: "t + t0 - j.t0 \<in> T" by (auto simp: assms)
  from y_sol have "is_solution (y o (op + (j.t0 - t0)))"
    by (rule j.shift_autonomous_solution) (force simp: o_def algebra_simps assms)+
  note unique_solution[OF this ts]
  moreover
  from j.is_solution_solution have "is_solution (j.solution o (op + (j.t0 - t0)))"
    by (rule j.shift_autonomous_solution) (force simp: o_def algebra_simps assms)+
  note unique_solution[OF this ts]
  ultimately
  show "y t = j.solution t"
    by simp
qed

locale interval = fixes a b assumes interval_notempty: "a \<le> b"

locale ivp_on_interval = ivp + interval t0 t1 for t1 +
  assumes interval: "T = {t0..t1}"
begin

lemma is_solution_ext_cont:
  assumes "continuous_on T x"
  shows "is_solution (ext_cont x t0 t1) = is_solution x"
  using assms iv_defined interval by (intro is_solution_cong) simp_all

lemma solution_fixed_point:
  assumes x: "is_solution x" and t: "t \<in> T"
  shows "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) = x t"
proof -
  from is_solutionD(2)[OF x] t
  have "\<forall>ta\<in>{t0 .. t}.
      (x has_vector_derivative f (ta, x ta))
      (at ta within {t0..t})"
    by (auto simp: interval intro:
      has_vector_derivative_within_subset[where s=T])
  hence "((\<lambda>t. f (t, x t)) has_integral x t - x t0)
      {t0..t}"
    using t by (auto simp: interval
      intro!: fundamental_theorem_of_calculus)
  from this[THEN integral_unique]
  show "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) = x t"
    by (simp add: is_solutionD[OF x])
qed

end

locale ivp_on_interval_left = ivp + interval t1 t0 for t1 +
  assumes interval: "T = {t1..t0}"
begin

lemma is_solution_ext_cont:
  assumes "continuous_on T x"
  shows "is_solution (ext_cont x t1 t0) = is_solution x"
  using assms iv_defined interval by (intro is_solution_cong) simp_all

lemma solution_fixed_point:
  assumes x: "is_solution x" and t: "t \<in> T"
  shows "x0 - integral {t..t0} (\<lambda>t. f (t, x t)) = x t"
proof -
  from is_solutionD(2)[OF x] t
  have "\<forall>ta\<in>{t..t0}.
      (x has_vector_derivative f (ta, x ta))
      (at ta within {t..t0})"
    by (auto simp: interval intro:
      has_vector_derivative_within_subset[where s=T])
  hence "((\<lambda>t. f (t, x t)) has_integral x t0 - x t)
      {t..t0}"
    using t by (auto simp: interval
      intro!: fundamental_theorem_of_calculus)
  from this[THEN integral_unique]
  show "x0 - integral {t..t0} (\<lambda>t. f (t, x t)) = x t"
    by (simp add: is_solutionD[OF x])
qed

end

sublocale ivp_on_interval \<subseteq> interval t0 t1 by unfold_locales
sublocale ivp_on_interval_left \<subseteq> interval t1 t0 by unfold_locales

subsubsection \<open>Connecting solutions \label{sec:combining-solutions}\<close>

locale connected_solutions =
  i1?: has_solution i1 + i2?: has_solution i2 + i?: ivp i
  for i::"('a::banach) ivp" and i1::"'a ivp"
  and i2::"'a ivp" +
  fixes y
  assumes sol1: "i1.is_solution y"
  assumes iv_on:
    "i.t0 \<notin> i1.T \<Longrightarrow> i2.solution i.t0 = i.x0"
    "i.t0 \<in> i1.T \<Longrightarrow> y i.t0 = i.x0"
  assumes conn_x: "\<And>t. t \<in> i1.T \<inter> i2.T \<Longrightarrow> y t = i2.solution t"
  assumes conn_f: "\<And>t. t \<in> i1.T \<inter> i2.T \<Longrightarrow> i1.f (t, y t) = i2.f (t, y t)"
  assumes conn_T: "closure i1.T \<inter> closure i2.T \<subseteq> i1.T"
    "closure i1.T \<inter> closure i2.T \<subseteq> i2.T"
  assumes f: "f = (\<lambda>(t, x). if t \<in> i1.T then i1.f (t, x) else i2.f (t, x))"
  assumes interval: "T = i1.T \<union> i2.T"
  assumes dom:"X = i1.X" "X = i2.X"
begin

lemma T_subsets:
  shows T1_subset: "i1.T \<subseteq> T"
  and T2_subset: "i2.T \<subseteq> T"
  subgoal by (metis Un_commute Un_upper2 interval)
  subgoal by (metis inf_sup_ord(4) interval)
  done

definition connection where
  "connection t = (if t \<in> i1.T then y t else i2.solution t)"

lemma is_solution_connection: "is_solution connection"
proof standard
  show "connection i.t0 = i.x0" "\<And>t. t \<in> i.T \<Longrightarrow> connection t \<in> i.X"
    by (auto simp: connection_def iv_on connection_def[abs_def]
      has_vector_derivative_def interval
      i2.is_solutionD[OF i2.is_solution_solution, simplified dom(2)[symmetric]]
      i1.is_solutionD[OF sol1, simplified dom(1)[symmetric]])
  fix t
  assume "t \<in> T"
  have FDERIV_y:
    "\<And>t. t \<in> i1.T \<Longrightarrow>
      (y has_derivative (\<lambda>a. a *\<^sub>R i1.f (t, y t)))
      (at t within i1.T)"
    using i1.is_solutionD[OF sol1]
    by (auto simp: has_vector_derivative_def)
  have FDERIV_2:
    "\<And>t. t \<in> i2.T \<Longrightarrow>
      (i2.solution has_derivative (\<lambda>a. a *\<^sub>R i2.f (t, i2.solution t)))
      (at t within i2.T)"
    using i2.is_solutionD[OF i2.is_solution_solution]
    by (auto simp: has_vector_derivative_def)
  show
    "(connection has_vector_derivative i.f (t, connection t)) (at t within i.T)"
    unfolding connection_def[abs_def] interval has_vector_derivative_def
    apply (rule has_derivative_subset[where s="i1.T \<union> i2.T"])
    proof (rule has_derivative_If[where t="i2.T", THEN has_derivative_eq_rhs, OF has_derivative_subset has_derivative_subset])
      from FDERIV_y FDERIV_2
      show "t \<in> i1.T \<union> closure i1.T \<inter> closure i2.T \<Longrightarrow> (y has_derivative (\<lambda>a. a *\<^sub>R i1.f (t, y t))) (at t within i1.T)"
        and "t \<in> i2.T \<union> closure i1.T \<inter> closure i2.T \<Longrightarrow> (i2.solution has_derivative (\<lambda>a. a *\<^sub>R i2.f (t, i2.solution t))) (at t within i2.T)" for t
        using conn_T
        by auto
    qed (insert conn_T conn_f conn_T \<open>t \<in> T\<close>, auto simp: conn_x f interval)
qed

lemma connection_eq_solution2: "t \<in> i2.T \<Longrightarrow> connection t = i2.solution t"
  by (auto simp: connection_def conn_x)

end

sublocale connected_solutions \<subseteq> has_solution using is_solution_connection
  by unfold_locales auto

locale connected_unique_solutions =
  i1?: unique_solution i1 + i2?: unique_solution i2 +
  connected_solutions i i1 i2 "i1.solution"
  for i::"'a::banach ivp" and i1::"'a ivp"
  and i2::"'a ivp" +
  fixes t1::real
  assumes inter_T: "i1.T \<inter> i2.T = {t1}"
  assumes initial_times: "i2.t0 = t1" "i.t0 = i1.t0"
begin

sublocale unique_solution
proof (intro unique_solutionI)
  show "is_solution connection" using is_solution_connection .
  fix y t
  assume "is_solution y" "t \<in> T"
  have "i1.is_solution y"
  proof (intro i1.is_solutionI)
    fix ta
    assume "ta \<in> i1.T"
    hence "ta \<in> T" using T1_subset by auto
    from is_solutionD(2)[OF \<open>is_solution y\<close> this]
    have "(y has_vector_derivative i1.f (ta, y ta)) (at ta within T)"
      using \<open>ta \<in> i1.T\<close> by (simp add: f)
    thus "(y has_vector_derivative i1.f (ta, y ta)) (at ta within i1.T)"
      using T1_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i1.X" using is_solutionD(3)[OF \<open>is_solution y\<close> \<open>ta \<in> T\<close>]
      by (simp add: dom)
  next
    have "connection i1.t0 = i1.solution i1.t0"
      using i1.iv_defined
      by (auto simp: connection_def)
    show "y i1.t0 = i1.x0"
      using is_solutionD(1)[OF \<open>is_solution y\<close>]
      using i1.iv_defined(1) initial_times i1.solution_t0 iv_on(2)
      by auto
  qed
  have "i2.is_solution y"
  proof (intro i2.is_solutionI)
    show "y (i2.t0) = i2.x0"
      by (metis Int_lower1 \<open>ivp.is_solution i1 y\<close> conn_x i1.unique_solution
        i2.solution_t0 initial_times(1) insertI1 inter_T rev_subsetD)
    fix ta
    assume "ta \<in> i2.T"
    hence "ta \<in> T" using T2_subset by auto
    from is_solutionD(2)[OF \<open>is_solution y\<close> this]
    have "(y has_vector_derivative i2.f (ta, y ta)) (at ta within T)"
      using \<open>ta \<in> i2.T\<close> conn_f conn_T
      apply (auto simp: f)
      by (metis (poly_guards_query) \<open>ivp.is_solution i1 y\<close> i1.unique_solution)
    thus "(y has_vector_derivative i2.f (ta, y ta)) (at ta within i2.T)"
      using T2_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i2.X" using is_solutionD(3)[OF \<open>is_solution y\<close> \<open>ta \<in> T\<close>]
      using dom by simp
  qed
  from i1.unique_solution[OF \<open>i1.is_solution y\<close>, of t]
    i2.unique_solution[OF \<open>i2.is_solution y\<close>, of t]
  show "y t = connection t"
    using \<open>t \<in> T\<close>
    by (auto simp: connection_def interval)
qed

lemma connection_eq_solution: "\<And>t. t \<in> T \<Longrightarrow> connection t = solution t"
  by (rule unique_solution is_solution_connection)+

lemma solution1_eq_solution:
  assumes "t \<in> i1.T"
  shows "i1.solution t = solution t"
proof -
  from T1_subset assms have "t \<in> T" by auto
  from connection_eq_solution[OF \<open>t \<in> T\<close>] assms
  show ?thesis
    by (simp add: connection_def)
qed

lemma solution2_eq_solution:
  assumes "t \<in> i2.T"
  shows "i2.solution t = solution t"
proof -
  from T2_subset assms have "t \<in> T" by auto
  from connection_eq_solution[OF \<open>t \<in> T\<close>] assms conn_x i2.solution_t0
  show ?thesis
    by (simp add: connection_def split_ifs)
qed

end

subsection \<open>Picard-Lindelöf on set of functions into closed set \label{sec:plclosed}\<close>

locale continuous_rhs = fixes T X f
  assumes continuous: "continuous_on (T \<times> X) f"

locale global_lipschitz =
  fixes T X f and L::real
  assumes lipschitz: "\<And>t. t\<in>T \<Longrightarrow> lipschitz X (\<lambda>x. f (t, x)) L"

locale closed_domain =
  fixes X assumes closed: "closed X"

locale self_mapping = ivp_on_interval +
  assumes self_mapping:
    "\<And>x t. t \<in> T \<Longrightarrow> x t0 = x0 \<Longrightarrow> x \<in> {t0..t} \<rightarrow> X \<Longrightarrow> continuous_on {t0..t} x \<Longrightarrow>
      x0 + integral {t0..t} (\<lambda>t. f (t, x t)) \<in> X"

locale unique_on_closed = self_mapping + continuous_rhs T X f +
  closed_domain X +
  global_lipschitz T X f L for L
begin

lemma L_nonneg: "0 \<le> L"
  by (auto intro!: lipschitz_nonneg[OF lipschitz] iv_defined)

text \<open>Picard Iteration\<close>

definition P_inner
  where
  "P_inner x t = x0 + integral {t0..t} (\<lambda>t. f (t, x t))"

definition P::"(real, 'a) bcontfun \<Rightarrow> (real, 'a) bcontfun" where
  "P x = ext_cont (P_inner x) t0 t1"

lemma
  continuous_f:
  assumes "y \<in> {t0..t} \<rightarrow> X"
  assumes "continuous_on {t0..t} y"
  assumes "t \<in> T"
  shows "continuous_on {t0..t} (\<lambda>t. f (t, y t))"
  using \<open>y \<in> {t0..t} \<rightarrow> X\<close> assms interval_notempty
  by (intro continuous_Sigma[of _ _ "\<lambda>_. X"])
    (auto simp: interval intro: assms continuous_on_subset continuous)

lemma P_inner_bcontfun:
  assumes "y \<in> T \<rightarrow> X"
  assumes y_cont: "continuous_on T y"
  shows "(\<lambda>x. P_inner y (clamp t0 t1 x)) \<in> bcontfun"
proof -
  show ?thesis using interval iv_defined assms
    by (auto intro!: clamp_bcontfun continuous_intros continuous_f
      indefinite_integral_continuous integrable_continuous_real
      simp: P_def P_inner_def)
qed

definition "iter_space = (Abs_bcontfun ` ((T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0}))"

lemma iter_spaceI:
  "(\<And>x. x \<in> T \<Longrightarrow> Rep_bcontfun g x \<in> X) \<Longrightarrow> g t0 = x0 \<Longrightarrow> g \<in> iter_space"
  by (force simp add: iter_space_def Rep_bcontfun Rep_bcontfun_inverse
    intro!: Rep_bcontfun)

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

lemma P_self_mapping:
  assumes in_space: "g \<in> iter_space"
  shows "P g \<in> iter_space"
proof (rule iter_spaceI)
  have cont: "continuous_on (cbox t0 t1) (P_inner (Rep_bcontfun g))"
    using assms Rep_bcontfun[of g, simplified bcontfun_def]
    by (auto simp: interval iter_space_def Abs_bcontfun_inverse P_inner_def
        interval_notempty
      intro!: continuous_intros indefinite_integral_continuous
        integrable_continuous_real continuous_f)
  from ext_cont_cancel[OF _ cont] assms
  show "Rep_bcontfun (P g) t0 = x0"
     "\<And>t. t \<in> T \<Longrightarrow> Rep_bcontfun (P g) t \<in> X"
    using assms Rep_bcontfun[of g, simplified bcontfun_def]
    by (auto intro!: self_mapping simp: interval interval_notempty P_inner_def
      P_def iter_space_def Abs_bcontfun_inverse)
qed

lemma ext_cont_solution_fixed_point:
  assumes "is_solution x"
  shows "P (ext_cont x t0 t1) = ext_cont x t0 t1"
  unfolding P_def
proof (rule ext_cont_cong)
  show "P_inner (Rep_bcontfun (ext_cont x t0 t1)) t = x t" when "t \<in> {t0..t1}" for t
    unfolding P_inner_def
    using solution_fixed_point solution_continuous_on assms is_solutionD that
    by (subst integral_spike[OF negligible_empty])
       (auto simp: interval P_inner_def integral_spike[OF negligible_empty])
qed (insert iv_defined solution_continuous_on assms is_solutionD,
  auto simp: interval P_inner_def continuous_intros
    indefinite_integral_continuous continuous_f)

lemma
  solution_in_iter_space:
  assumes "is_solution z"
  shows "ext_cont z t0 t1 \<in> iter_space"
proof -
  let ?z = "ext_cont z t0 t1"
  have "is_solution ?z"
    using is_solution_ext_cont interval \<open>is_solution z\<close> solution_continuous_on
    by simp
  hence "\<And>t. t \<in> T \<Longrightarrow> ext_cont z t0 t1 t \<in> X"
    by (auto simp add: is_solution_def)
  thus "?z \<in> iter_space" using is_solutionD[OF \<open>is_solution z\<close>]
    solution_continuous_on[OF \<open>is_solution z\<close>]
    by (auto simp: interval interval_notempty intro!: iter_spaceI)
qed

end

locale unique_on_bounded_closed = unique_on_closed +
  assumes lipschitz_bound: "(t1 - t0) * L < 1"
begin

lemma lipschitz_P:
  shows "lipschitz iter_space P ((t1 - t0) * L)"
proof (rule lipschitzI)
  have "t0 \<in> T" by (simp add: iv_defined)
  thus "0 \<le> (t1 - t0) * L"
    using interval_notempty interval
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
    from bcontfunE[OF \<open>y \<in> bcontfun\<close>] have y: "continuous_on UNIV y" by auto
    from bcontfunE[OF \<open>z \<in> bcontfun\<close>] have z: "continuous_on UNIV z" by auto
    have *: "norm (P_inner y t - P_inner z t)
        \<le> L * (t1 - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
      if t_bounds: "t0 \<le> t" "t \<le> t1" for t
      \<comment>\<open>Instances of \<open>continuous_on_subset\<close>\<close>
    proof -
      have y_cont: "continuous_on {t0..t} (\<lambda>t. y t)" using y
        by (auto intro:continuous_on_subset)
      have "continuous_on {t0..t1} (\<lambda>t. f (t, y t))"
        using continuous interval interval_notempty y strip y_defined
        by (auto intro!:continuous_f intro: continuous_on_subset)
      hence fy_cont[intro, simp]:
        "continuous_on {t0..t} (\<lambda>t. f (t, y t))"
        by (rule continuous_on_subset) (simp add: t_bounds)
      have z_cont: "continuous_on {t0..t} (\<lambda>t. z t)" using z
        by (auto intro:continuous_on_subset)
      have "continuous_on {t0..t1} (\<lambda>t. f (t, z t))"
        by (metis (no_types) UNIV_I continuous continuous_Sigma continuous_on_subset interval subsetI z z_defined)
      hence fz_cont[intro, simp]:
        "continuous_on {t0..t} (\<lambda>t. f (t, z t))"
        by (rule continuous_on_subset) (simp add: t_bounds)

      have "norm (P_inner y t - P_inner z t) =
        norm (integral {t0..t} (\<lambda>t. f (t, y t) - f (t, z t)))"
        using y
        by (auto simp add: integral_diff P_inner_def)
      also have "... \<le> integral {t0..t} (\<lambda>t. norm (f (t, y t) - f (t, z t)))"
        by (auto intro!: integral_norm_bound_integral continuous_intros)
      also have "... \<le> integral {t0..t} (\<lambda>t. L * norm (y t - z t))"
        using y_cont z_cont lipschitz t_bounds interval y_defined z_defined
        by (intro integral_le)
           (auto intro!: continuous_intros simp add: dist_norm lipschitz_def Pi_iff)
      also have "... \<le> integral {t0..t} (\<lambda>t. L *
        norm (Abs_bcontfun y - Abs_bcontfun  z))"
        using norm_bounded[of "Abs_bcontfun y - Abs_bcontfun z"]
          y_cont z_cont L_nonneg
        by (intro integral_le) (auto intro!: continuous_intros mult_left_mono
          simp add: Abs_bcontfun_inverse[OF \<open>y \<in> bcontfun\<close>]
          Abs_bcontfun_inverse[OF \<open>z \<in> bcontfun\<close>])
      also have "... =
        L * (t - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds by simp
      also have "... \<le> L * (t1 - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds zero_le_dist L_nonneg
        by (auto intro!: mult_right_mono mult_left_mono)
      finally show ?thesis .
    qed
    have "dist (P (Abs_bcontfun y)) (P (Abs_bcontfun z)) \<le>
      L * (t1 - t0) * dist (Abs_bcontfun y) (Abs_bcontfun z)"
      unfolding P_def dist_norm ext_cont_def
        Abs_bcontfun_inverse[OF \<open>y \<in> bcontfun\<close>]
        Abs_bcontfun_inverse[OF \<open>z \<in> bcontfun\<close>]
      using interval iv_defined \<open>y \<in> bcontfun\<close> \<open>z \<in> bcontfun\<close>
        y_defined z_defined
        clamp_in_interval[of t0 t1] interval_notempty
      apply (intro norm_bound)
      unfolding Rep_bcontfun_minus
      apply (subst Abs_bcontfun_inverse)
       defer
       apply (subst Abs_bcontfun_inverse)
        defer
      by (auto intro!: P_inner_bcontfun * elim!: bcontfunE
        intro: continuous_on_subset)
  }
  from this[OF Rep_bcontfun y_defined Rep_bcontfun z_defined]
  show "dist (P y) (P z) \<le> (t1 - t0) * L * dist y z"
    unfolding Rep_bcontfun_inverse by (simp add: field_simps)
qed


lemma fixed_point_unique: "\<exists>!x\<in>iter_space. P x = x"
  using lipschitz lipschitz_bound lipschitz_P interval
      complete_UNIV iv_defined
  by (intro banach_fix)
    (auto
      intro: P_self_mapping split_mult_pos_le
      intro!: closed_iter_space iter_space_notempty
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

lemma fixed_point_continuous: "\<And>t. continuous_on I fixed_point"
  using bcontfunE[OF Rep_bcontfun[of fixed_point]]
  by (auto intro: continuous_on_subset)

lemma fixed_point_solution:
  shows "is_solution fixed_point"
proof
  have "fixed_point t0 = P fixed_point t0"
    unfolding fixed_point ..
  also have "... = x0"
    using interval iv_defined continuous fixed_point_continuous fixed_point
    unfolding P_def P_inner_def[abs_def]
    by (subst ext_cont_cancel)
      (auto simp add: iter_space_def Abs_bcontfun_inverse
        intro!: continuous_intros indefinite_integral_continuous
          integrable_continuous_real continuous_f
        intro: continuous_on_subset)
  finally show "fixed_point t0 = x0" .
next
  fix t
  have U: "Rep_bcontfun fixed_point \<in> Pi T (\<lambda>_. X)"
    using fixed_point by (auto simp add: iter_space_def Abs_bcontfun_inverse)
  assume "t \<in> T" hence t_range: "t \<in> {t0..t1}" by (simp add: interval)
  from has_vector_derivative_const
    integral_has_vector_derivative[OF
      continuous_Sigma[OF U continuous fixed_point_continuous,
        simplified interval]
      t_range]
  have "((\<lambda>u. x0 + integral {t0..u}
         (\<lambda>x. f (x, fixed_point x))) has_vector_derivative
   0 + f (t, fixed_point t))
   (at t within {t0..t1})"
    by (rule has_vector_derivative_add)
  hence "((P fixed_point) has_vector_derivative
    f (t, fixed_point t)) (at t within {t0..t1})"
    unfolding P_def P_inner_def[abs_def]
    using t_range
    apply (subst has_vector_derivative_cong)
    apply (simp_all)
    using fixed_point fixed_point_continuous continuous interval
    by (subst ext_cont_cancel)
      (auto simp: iter_space_def Abs_bcontfun_inverse
        intro!: continuous_intros indefinite_integral_continuous
          integrable_continuous_real continuous_f
        intro: continuous_on_subset)
  moreover
  have "fixed_point t \<in> X"
    using fixed_point \<open>t \<in> T\<close> by (auto simp add: iter_space_def Abs_bcontfun_inverse)
  ultimately
  show "(fixed_point has_vector_derivative
      f (t, fixed_point t)) (at t within T)"
    "fixed_point t \<in> X" unfolding fixed_point interval
    by simp_all
qed

end

subsubsection \<open>Existence of solution\<close>

sublocale unique_on_bounded_closed \<subseteq> has_solution
proof
  from fixed_point_solution
  show "\<exists>x. is_solution x" by blast
qed

subsubsection \<open>Unique solution \label{sec:ivp-ubs}\<close>

sublocale unique_on_bounded_closed \<subseteq> unique_solution
proof
  fix z t
  assume "is_solution z"
  with ext_cont_solution_fixed_point \<open>is_solution z\<close> is_solution_solution
    solution_in_iter_space fixed_point_equality
  have "ext_cont solution t0 t1 t = ext_cont z t0 t1 t" by metis
  moreover assume "t \<in> T"
  ultimately
  show "z t = solution t"
    using solution_continuous_on[OF \<open>is_solution z\<close>]
      solution_continuous_on[OF is_solution_solution]
    by (auto simp: interval)
qed

sublocale unique_on_closed \<subseteq> unique_solution
proof (cases "t1 = t0")
  assume "t1 = t0"
  then interpret has_solution
    using is_solution_def interval iv_defined
    by unfold_locales (auto intro!: exI[where x="(\<lambda>t. x0)"]
      simp add: has_vector_derivative_def
      has_derivative_within_alt bounded_linear_scaleR_left)
  show "unique_solution i"
    using \<open>t1=t0\<close> interval solution_t0
    by unfold_locales (simp add: is_solution_def)
next
  assume "t1 \<noteq> t0"
  with interval iv_defined
  have interval: "T = {t0..t1}" "t0 < t1"
    by auto
  obtain n::nat and b where b: "b = (t1 - t0) / (Suc n)" and bL: "L * b < 1"
    by (rule, rule) (auto intro: order_le_less_trans real_nat_ceiling_ge simp del: of_nat_Suc)
  then interpret i': ivp_on_interval i "t0 + (Suc n) * b"
    using interval by unfold_locales simp_all
  from b have "b > 0" using interval iv_defined
    by auto
  hence "b \<ge> 0" by simp
  from interval have "t0 * (real (Suc n) - 1) \<le> t1 * (real (Suc n) - 1)"
    by (cases n) auto
  hence ble: "t0 + b \<le> t1" unfolding b by (auto simp add: field_simps)
  have subsetbase: "t0 + (Suc n) * b \<le> t1" using i'.interval interval by auto

  interpret i': unique_solution "i\<lparr>ivp_T := {t0..t0 + real (Suc n) * b}\<rparr>"
    using subsetbase
  proof (induct n)
    case 0
    then interpret sol: unique_on_bounded_closed "i\<lparr>ivp_T:={t0..t0+b}\<rparr>" "t0 + b"
      using interval iv_defined \<open>b > 0\<close> bL continuous lipschitz closed self_mapping
      by unfold_locales (auto intro: continuous_on_subset simp: ac_simps Pi_iff)
    show ?case by simp unfold_locales
  next
    case (Suc n)
    def nb \<equiv> "real (Suc n) * b"
    def snb \<equiv> "real (Suc (Suc n)) * b"
    note Suc = Suc[simplified nb_def[symmetric] snb_def[symmetric]]
    from \<open>b > 0\<close> nb_def snb_def have nbs_nonneg: "0 < snb" "0 < nb"
      by (simp_all add: zero_less_mult_iff)
    with \<open>b>0\<close> have nb_le_snb: "nb < snb" using nb_def snb_def
      by auto
    have [simp]: "snb - nb = b"
    proof -
      have "snb + - (nb) = b * real (Suc (Suc n)) + - (b * real (Suc n))"
        by (simp add: ac_simps snb_def nb_def)
      thus ?thesis by (simp add: field_simps of_nat_Suc)
    qed
    def i1 \<equiv> "i\<lparr>ivp_T := {t0..t0 + nb}\<rparr>"
    def T1 \<equiv> "t0 + nb"
    interpret ivp1: ivp_on_interval i1 T1
      using iv_defined \<open>nb > 0\<close> by unfold_locales (auto simp: i1_def T1_def)
    interpret ivp1: unique_solution i1
      using nb_le_snb nbs_nonneg Suc continuous lipschitz by (simp add: i1_def)
    interpret ivp1_cl: unique_on_closed i1 "t0 + nb"
      using nb_le_snb nbs_nonneg Suc continuous lipschitz closed self_mapping
      by unfold_locales (auto simp: i1_def interval intro: continuous_on_subset)
    def i2 \<equiv> "i\<lparr>ivp_t0:=t0+nb, ivp_T:={t0 + nb..t0+snb},
      ivp_x0:=ivp1.solution (t0 + nb)\<rparr>"
    def T2 \<equiv> "t0 + snb"
    interpret ivp2: ivp_on_interval i2 T2
      using nbs_nonneg \<open>nb < snb\<close> ivp1.solution_in_D
      by unfold_locales (auto simp: i1_def i2_def T2_def)
    interpret ivp2: self_mapping i2 T2
    proof unfold_locales
      fix x t assume t: "t \<in> ivp2.T"
        and x: "x ivp2.t0 = ivp2.x0" "x \<in> {ivp2.t0 .. t} \<rightarrow> ivp2.X"
        and cont: "continuous_on {ivp2.t0 .. t} x"
      hence "t \<in> T"
        using Suc(2) nbs_nonneg interval
        by (simp add: i2_def)
      let ?un = "(\<lambda>t. if t \<le> nb + t0 then ivp1.solution t else x t)"
      let ?fun = "(\<lambda>t. f (t, ?un t))"
      have decomp: "{t0..t} = {t0..nb + t0} \<union> {nb + t0..t}"
        using interval_notempty t nbs_nonneg
        by (auto simp: i2_def)
      have un_space: "?un \<in> {t0..t} \<rightarrow> X"
        using x ivp1.solution_in_D
        by (auto simp: i1_def i2_def Pi_iff)
      have cont_un: "continuous_on {t0..t} ?un"
        using x cont
          ivp1.solution_continuous_on[OF ivp1.is_solution_solution,
            simplified i1_def]
        unfolding decomp
        by (intro continuous_on_If)
          (auto intro: continuous_on_subset simp: i1_def i2_def ac_simps)
      have cont_fun: "continuous_on {t0..t} ?fun"
        using un_space cont_un \<open>t \<in> T\<close> by (rule continuous_f)
      have "ivp.solution i1 (nb + t0) + integral {nb + t0..t} (\<lambda>xa. f (xa, x xa)) =
        x0 + (integral {t0..nb + t0} (\<lambda>t. f (t, ivp1.solution t)) +
          integral {nb + t0..t} (\<lambda>xa. f (xa, x xa)))"
        using ivp1_cl.solution_fixed_point[OF ivp1.is_solution_solution] nbs_nonneg
          ivp1_cl.P_inner_def
        by (auto simp: i1_def ac_simps)
      also have "integral {t0..nb + t0} (\<lambda>t. f (t, ivp1.solution t)) =
          integral {t0..nb + t0} ?fun"
        by (rule integral_spike[OF negligible_empty]) auto
      also have fun2: "integral {nb + t0..t} (\<lambda>t. f (t, x t)) =
          integral {nb + t0..t} ?fun"
        using x
        by (intro integral_spike[OF negligible_empty])
          (auto simp: i1_def i2_def ac_simps)
      also have "integral {t0..nb + t0} ?fun + integral {nb + t0..t} ?fun =
          integral {t0..t} ?fun"
        using t nbs_nonneg
        by (intro integral_combine)
          (auto simp: i2_def less_imp_le intro!: cont_fun)
      also have "x0 + \<dots> \<in> X"
        using \<open>t \<in> T\<close> \<open>nb > 0\<close> ivp1.is_solutionD[OF ivp1.is_solution_solution]
        by (intro self_mapping[OF _ _ un_space cont_un])
          (auto simp: ivp1.iv_defined i1_def)
      also note fun2[symmetric]
      finally
      show "ivp2.x0 + integral {ivp2.t0 .. t} (\<lambda>t. ivp2.f (t, x t)) \<in> ivp2.X"
        by (simp add: i1_def i2_def ac_simps)
    qed
    interpret ivp2: unique_on_bounded_closed i2 T2
      using bL Suc(2) nbs_nonneg interval continuous lipschitz closed
      by unfold_locales
        (auto intro: continuous_on_subset simp: ac_simps i1_def i2_def T2_def)
    def i \<equiv> "i\<lparr>ivp_T := {t0..t0 + real (Suc (Suc n)) * b}\<rparr>"
    def T \<equiv> "t0 + real (Suc (Suc n)) * b"
    interpret i: ivp i
    proof
      show "ivp_t0 i \<in> ivp_T i" "ivp_x0 i \<in> ivp_X i"
        using ivp1.iv_defined \<open>0 \<le> b\<close>
        by (auto simp: i_def i1_def nb_def intro!: mult_nonneg_nonneg)
    qed
    have *: "ivp_T i1 \<inter> ivp_T i2 = {T1}"
      using nbs_nonneg
      by (auto simp: i1_def i2_def nb_def snb_def max_def min_def T1_def not_le
        mult_less_cancel_right sign_simps
        simp del: of_nat_Suc)
    have nb_le_snb: "t0 + real (Suc n) * b \<le> t0 + real (Suc (Suc n)) * b"
      using \<open>b > 0\<close> by auto
    interpret ivp_c: connected_unique_solutions i i1 i2 T1
      apply unfold_locales
      unfolding *
      using \<open>b > 0\<close> iv_defined ivp1.is_solutionD[OF ivp1.is_solution_solution]
        ivp2.is_solutionD[OF ivp2.is_solution_solution]
        ivp1.is_solution_solution
        ivp2.is_solution_solution
         nbs_nonneg
        add_increasing2[of "real (Suc n) * b" "t0 + real (Suc n) * b"]
      by (auto simp: i1_def i2_def i_def T1_def T2_def T_def snb_def nb_def
        simp del: of_nat_Suc
        intro!: order_trans[OF _ nb_le_snb])
    show ?case unfolding i_def[symmetric] by unfold_locales
  qed
  show "unique_solution i"
    using i'.solution i'.unique_solution interval(1)[symmetric] i'.interval[symmetric]
    by unfold_locales (auto simp del: of_nat_Suc)
qed

subsection \<open>Picard-Lindelöf for @{term "X=(\<lambda>_. UNIV)"} \label{sec:pl-us}\<close>

locale unique_on_strip = ivp_on_interval + continuous_rhs T X f +
  global_lipschitz T X f L for L +
  assumes strip: "X = UNIV"

sublocale unique_on_strip < unique_on_closed
  using strip by unfold_locales auto

subsection \<open>Picard-Lindelöf on cylindric domain \label{sec:pl-rect}\<close>

locale cylinder = ivp i for i::"'a::banach ivp" +
  fixes e b
  assumes e_pos: "e > 0"
  assumes b_pos: "b > 0"
  assumes interval: "T = {t0 - e .. t0 + e}"
  assumes cylinder: "X = cball x0 b"

locale solution_in_cylinder = cylinder + continuous_rhs T X f +
  fixes B
  assumes norm_f: "\<And>x t. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f (t, x)) \<le> B"
  assumes e_bounded: "e \<le> b / B"
begin

lemma B_nonneg: "B \<ge> 0"
proof -
  have "0 \<le> norm (f (t0, x0))" by simp
  also from iv_defined norm_f have "... \<le> B" by simp
  finally show ?thesis by simp
qed

lemma closed_real_closed_segment: "\<And>a b. closed (closed_segment a b::real set)"
  by (auto simp: closed_segment_real)

lemma in_bounds_derivativeI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "\<And>s. s \<in> open_segment t0 t \<Longrightarrow> (x has_vector_derivative f (s, y s)) (at s within open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi>\<in>closed_segment t0 t \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
proof cases
  assume "b = 0 \<or> B = 0" with assms e_bounded interval e_pos have "t = t0"
    by auto
  thus ?thesis using iv_defined init by simp
next
  assume "\<not>(b = 0 \<or> B = 0)"
  hence "b > 0" "B > 0" using B_nonneg b_pos by auto
  show ?thesis
  proof cases
    assume "t0 \<noteq> t"
    then have b_less: "B * abs (t - t0) \<le> b"
      using e_pos e_bounded using \<open>b > 0\<close> \<open>B > 0\<close> \<open>t \<in> T\<close>
      by (auto simp: field_simps interval abs_real_def)
       (metis add_right_mono distrib_left mult_le_cancel_left_pos order_trans)+
    def b\<equiv>"B * abs (t - t0)"
    have "b > 0" using \<open>t0 \<noteq> t\<close> by (auto intro!: mult_pos_pos simp: algebra_simps b_def \<open>B > 0\<close>)
    have subs: "closed_segment t0 t \<subseteq> {t0 - e..t0 + e}"
      using interval \<open>t \<in> T\<close> by (auto simp: closed_segment_real)
    from cont
    have closed: "closed {s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}}"
      by (intro continuous_closed_preimage continuous_intros
        closed_real_closed_segment)
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
          (insert e_pos subs s_bound, auto simp: closed_segment_real)
      have bnd_cont: "continuous_on (closed_segment t0 s) (op * B)"
        and bnd_deriv: "(\<And>x. x \<in> open_segment t0 s \<Longrightarrow>
          (op * B has_vector_derivative B) (at x within open_segment t0 s))"
        by (auto intro!: continuous_intros derivative_eq_intros
          simp: has_vector_derivative_def)
      have bnd: "norm (f (ss, y ss)) \<le> B" if ss: "ss \<in> open_segment t0 s" for ss
      proof -
        from st ss have "ss \<in> closed_segment t0 t" by auto
        have less_b: "norm (x ss - x t0) < b"
        proof (rule ccontr)
          assume "\<not> norm (x ss - x t0) < b"
          hence "norm (x ss - x t0) \<in> {b..}" by auto
          from min[rule_format, OF \<open>ss \<in> closed_segment t0 t\<close> this]
          show False using ss \<open>s \<noteq> t0\<close>
            by (auto simp: dist_real_def open_segment_real split_ifs)
        qed
        show ?thesis
          apply (rule norm_f)
          subgoal using ss st subs interval by auto
          subgoal using ss st b_less less_b
            by (intro y_bounded)
              (auto simp: cylinder dist_norm b_def init norm_minus_commute)
          done
      qed
      have subs: "open_segment t0 s \<subseteq> open_segment t0 t" using s_bound \<open>s \<noteq> t0\<close>
        by (auto simp: closed_segment_real open_segment_real)
      with differentiable_bound_general_open_segment[OF cont bnd_cont
        has_vector_derivative_within_subset[OF solves subs] bnd_deriv bnd] st
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
        using assms interval \<open>0 < b\<close>
        by (auto simp: closed_segment_real )
      from IVT'_closed_segment_real[OF this continuous_on_norm[OF cont_diff]]
      obtain s where s: "s \<in> closed_segment t0 t" "norm (x s - x t0) = b"
        using \<open>b > 0\<close> by auto
      have "s \<in> {s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}}"
        using s \<open>t \<in> T\<close> by (auto simp: interval)
      with mvt_result have "s = t" by blast
      hence "s = t" using s \<open>t \<in> T\<close> by (auto simp: interval)
      with s H show False by simp
    qed
    hence "x t \<in> cball x0 b" using init
      by (auto simp: dist_commute dist_norm[symmetric])
    thus "x t \<in> cball x0 (B * abs (t - t0))" unfolding cylinder b_def .
  qed (simp add: init[symmetric])
qed

lemma in_bounds_derivative_globalI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "\<And>s. s \<in> open_segment t0 t \<Longrightarrow>
    (x has_vector_derivative f (s, y s)) (at s within open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi>\<in>(closed_segment t0 t) \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> X"
proof -
  from in_bounds_derivativeI[OF assms]
  have "x t \<in> cball x0 (B * abs (t - t0))" .
  moreover have "B * abs (t - t0) \<le> b" using e_bounded b_pos B_nonneg \<open>t \<in> T\<close>
    apply (cases "B = 0", simp)
    subgoal
      apply (auto simp: field_simps interval abs_real_def)
      subgoal by (metis add_right_mono less_eq_real_def order_trans
         real_mult_le_cancel_iff2 ring_class.ring_distribs(1))
      subgoal by (metis add_less_same_cancel2 add_right_mono le_less_trans
        mult_le_cancel_left_pos mult_left_mono_neg not_less
        ring_class.ring_distribs(1) zero_le_mult_iff)
      done
    done
  ultimately show ?thesis by (auto simp: cylinder)
qed

lemma integral_in_bounds:
  assumes "t \<ge> t0" "t \<in> T" "x t0 = x0" "x \<in> {t0..t} \<rightarrow> X"
  assumes cont: "continuous_on {t0..t} x"
  shows "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) \<in> X" (is "x0 + ?ix t \<in> X")
proof cases
  assume "t = t0"
  thus ?thesis by (auto simp: iv_defined)
next
  assume "t \<noteq> t0"
  have cont_f:"continuous_on {t0..t} (\<lambda>t. f (t, x t))"
    using assms
    by (intro continuous_Sigma)
      (auto intro: cont continuous_on_subset[OF continuous] simp: interval)
  show ?thesis
    using assms \<open>t \<noteq> t0\<close>
    by (intro in_bounds_derivative_globalI[where y=x and x="\<lambda>t. x0 + ?ix t"])
      (auto simp: interval closed_segment_real open_segment_real
        intro!: cont_f has_vector_derivative_const
          has_vector_derivative_within_subset[OF integral_has_vector_derivative]
          has_vector_derivative_add[THEN vector_derivative_eq_rhs]
          continuous_intros indefinite_integral_continuous)
qed

lemma integral_in_bounds':
  assumes "\<not> t0 \<le> t" "t \<in> T" "x t0 = x0" "x \<in> {t..t0} \<rightarrow> X"
  assumes cont: "continuous_on {t..t0} x"
  shows "x0 + integral {t..t0} (\<lambda>t. - f (t, x t)) \<in> X" (is "x0 + ?ix t \<in> X")
proof cases
  assume "t = t0"
  thus ?thesis by (auto simp: iv_defined)
next
  assume "t \<noteq> t0"
  have cont_f:"continuous_on {t .. t0} (\<lambda>t. f (t, x t))"
    using assms
    by (intro continuous_Sigma continuous_on_minus)
      (auto intro: cont continuous_on_subset[OF continuous] simp: interval)
  show ?thesis
    using assms \<open>t \<noteq> t0\<close>
    by (intro in_bounds_derivative_globalI[where y=x and x="\<lambda>t. x0 + ?ix t"])
       (auto simp: interval closed_segment_real open_segment_real 
        intro!: cont_f 
          indefinite_integral2_continuous
          has_vector_derivative_within_subset[OF integral2_has_vector_derivative]
          has_vector_derivative_const
          has_vector_derivative_diff[THEN vector_derivative_eq_rhs]
          continuous_intros)
qed

lemma solves_in_cone:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "\<And>s. s \<in> (open_segment t0 t) \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within open_segment t0 t)"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
  using assms
  by (rule in_bounds_derivativeI)

lemma is_solution_in_cone:
  assumes "t \<in> T"
  assumes sol: "is_solution x"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
proof cases
  assume "t = t0"
  thus ?thesis by (auto simp: is_solutionD(1)[OF sol])
next
  assume "t \<noteq> t0"
  have subset1: "(closed_segment t0 t) \<subseteq> T" using assms interval by (auto simp: closed_segment_real)
  have subset2: "(open_segment t0 t) \<subseteq> T" using assms by (auto simp: open_segment_real interval)
  from is_solutionD(1)[OF sol]
    is_solutionD(2)[OF sol, THEN has_vector_derivative_within_subset[OF _ subset2]]
    is_solutionD(3)[OF sol set_mp[OF subset1]]
    solution_continuous_on[OF sol, THEN continuous_on_subset[OF _ subset1]]
  show ?thesis
    using assms(1) subset1 subset2 \<open>t \<noteq> t0\<close>
    by (intro solves_in_cone[where x=x]) (auto simp: interval open_segment_real
      at_within_open[where S="open_segment t0 t", symmetric])
qed

end

text \<open>For the numerical approximation, it is necessary that f is
lipschitz-continuous outside the actual domain - therefore X'.\<close>

locale unique_on_cylinder =
  solution_in_cylinder + global_lipschitz: global_lipschitz T X' f L for L X' +
  assumes lipschitz_on_domain: "X \<subseteq> X'"
begin

lemma lipschitz': "t \<in> T \<Longrightarrow> lipschitz X (\<lambda>x. f (t, x)) L" "0 \<le> L"
  using global_lipschitz.lipschitz lipschitz_on_domain
  by (auto intro: lipschitz_subset intro!: lipschitz_nonneg[OF global_lipschitz.lipschitz] iv_defined)

sublocale unique_pos: ivp_on_interval "i \<lparr>ivp_T:={t0 .. t0 + e}\<rparr>" "t0 + e"
  using e_pos iv_defined
  by unfold_locales auto

sublocale unique_pos: unique_on_closed "i \<lparr>ivp_T:={t0 .. t0 + e}\<rparr>" "t0 + e" L
proof
  show "closed unique_pos.X" by (simp_all add: cylinder closed_cball)
  show "continuous_on (unique_pos.T \<times> unique_pos.X) unique_pos.f"
    using continuous interval by (auto intro: continuous_on_subset)
  fix t assume t: "t \<in> unique_pos.T" with lipschitz' interval
  show "lipschitz unique_pos.X (\<lambda>x. unique_pos.f (t, x)) L" by simp
  fix x
  assume "x unique_pos.t0 = unique_pos.x0"
    "x \<in> {unique_pos.t0 .. t} \<rightarrow> unique_pos.X"
    "continuous_on {unique_pos.t0 .. t} x"
  thus "unique_pos.x0 + integral {unique_pos.t0..t} (\<lambda>t. unique_pos.f (t, x t)) \<in>
      unique_pos.X"
    using t interval
    by (auto intro: integral_in_bounds)
qed

sublocale unique_neg: ivp "i \<lparr>ivp_T:={t0 - e.. t0}\<rparr>"
  using e_pos iv_defined
  by unfold_locales auto

sublocale unique_neg: unique_solution "i \<lparr>ivp_T:={t0 - e.. t0}\<rparr>"
proof
  let ?mirror = "\<lambda>t. 2 * t0 - t"
  have mirror_eq: "((\<lambda>x. (2 * t0 - fst x, snd x)) ` (T \<times> X)) = T \<times> X"
    by (auto intro: image_eqI[where x="(?mirror x, y)" for x y] simp: interval)
  have mirror_imp: "\<And>t. t \<in> T \<Longrightarrow> ?mirror t \<in> T"
    by (auto simp: interval)
  have cont_mirror: "continuous_on (T \<times> X) (- f o (\<lambda>(t, x). (?mirror t, x)))"
    apply (rule continuous_on_compose)
    using continuous
    by (auto simp: split_beta' mirror_eq
      intro!: continuous_on_Pair continuous_intros)
  interpret rev:
    unique_on_cylinder "i \<lparr>ivp_f:=(\<lambda>(t, x). -f(?mirror t, x))\<rparr>" e b B L X'
    apply unfold_locales
    subgoal using iv_defined by simp
    subgoal using iv_defined by simp
    subgoal using e_pos by simp
    subgoal using b_pos by simp
    subgoal using interval by simp
    subgoal using cylinder by simp
    subgoal using cont_mirror by (simp add: split_beta')
    subgoal using norm_f by (simp add: mirror_imp)
    subgoal using e_bounded by simp
    subgoal using global_lipschitz.lipschitz by (simp add: lipschitz_uminus mirror_imp)
    subgoal using global_lipschitz.lipschitz lipschitz_on_domain by simp
    done
  have *: "op - (2 * t0) ` {t0 - e..t0} = {t0 .. t0 + e}"
    by (auto intro!: image_eqI[where x="?mirror x" for x])
  have "unique_neg.is_solution (rev.unique_pos.solution o ?mirror)"
    using rev.unique_pos.is_solution_solution
    by (simp add: unique_neg.solution_mirror_eq o_def *)
  thus "\<exists>x. unique_neg.is_solution x" by blast
  then interpret unique_neg: has_solution "i\<lparr>ivp_T := {t0 - e..t0}\<rparr>"
    by unfold_locales
  fix y t assume "t \<in> unique_neg.T" and y: "unique_neg.is_solution y"
  hence t: "?mirror t \<in> rev.unique_pos.T" by auto
  from unique_neg.mirror_solution[OF y]
    unique_neg.mirror_solution[OF unique_neg.is_solution_solution]
  have **: "rev.unique_pos.is_solution (y o ?mirror)"
    "rev.unique_pos.is_solution (unique_neg.solution o ?mirror)"
    by (auto simp: o_def *)
  from rev.unique_pos.unique_solution[OF **(1) t]
    rev.unique_pos.unique_solution[OF **(2) t]
  show "y t = unique_neg.solution t"
    by simp
qed

sublocale unique_solution
proof -
  interpret
    connected_solutions
      i "i\<lparr>ivp_T := {t0 - e..t0}\<rparr>" "i\<lparr>ivp_T := {t0..t0+e}\<rparr>" unique_neg.solution
    using e_pos unique_neg.solution_t0 unique_pos.solution_t0
    by unfold_locales (auto simp: interval)
  interpret
    connected_unique_solutions
      i "i\<lparr>ivp_T := {t0 - e..t0}\<rparr>" "i\<lparr>ivp_T := {t0..t0+e}\<rparr>" t0
    using e_pos unique_neg.solution_t0 unique_pos.solution_t0
    by unfold_locales auto
  show "unique_solution i" ..
qed

end

locale unique_on_superset_domain = subset?: unique_solution +
  fixes X''
  assumes superset: "X \<subseteq> X''"
  assumes segment_subset: "\<And>t. t \<in> T \<Longrightarrow> (closed_segment t0 t) \<subseteq> T"
  assumes solution_in_subset: "\<And>t x. t \<in> T \<Longrightarrow> x t0 = x0 \<Longrightarrow>
    (\<And>s. s \<in> closed_segment t0 t \<Longrightarrow>
    (x has_vector_derivative f (s, x s)) (at s within closed_segment t0 t)) \<Longrightarrow>
    x t \<in> X"
begin

sublocale has_solution "i\<lparr>ivp_X:=X''\<rparr>"
  using iv_defined superset
  by unfold_locales (auto intro!: exI[where x=solution] is_solution_on_superset_domain)

lemma is_solution_eq_is_solution_on_supersetdomain:
  shows "subset.is_solution = ivp.is_solution (i\<lparr>ivp_X:=X''\<rparr>)"
proof -
  interpret ivp': ivp "i\<lparr>ivp_X:=X''\<rparr>" using iv_defined by unfold_locales auto
  show ?thesis
  proof (safe intro!: ext)
   fix x assume "is_solution x"
    moreover
    from is_solutionD[OF this] solution_continuous_on[OF this]
    have "\<And>t. t \<in> subset.T \<Longrightarrow> x t \<in> subset.X"
      using segment_subset
      by (intro solution_in_subset; force intro!: continuous_on_subset
          continuous_on_subset[OF _ segment_subset]
          has_vector_derivative_within_subset[OF _ segment_subset])
    ultimately show "subset.is_solution x"
      by (auto intro!: subset.is_solutionI dest: is_solutionD)
  qed (intro subset.is_solution_on_superset_domain superset)
qed

lemma sup_solution_is_solution: "is_solution x \<Longrightarrow> subset.is_solution x"
  using superset
  by (subst is_solution_eq_is_solution_on_supersetdomain) auto

lemma solutions_eq:
  "t \<in> T \<Longrightarrow> solution t = subset.solution t"
  using sup_solution_is_solution
  by (auto intro!: subset.unique_solution)

sublocale unique_solution "i\<lparr>ivp_X:=X''\<rparr>"
proof
  fix y t
  assume "t \<in> T" hence t: "t \<in> subset.T" by simp
  assume sol': "is_solution y"
  hence sol: "subset.is_solution y"
    by (rule sup_solution_is_solution)
  from unique_solution[OF sol t] have "y t = subset.solution t" .
  also
  note solutions_eq[OF \<open>t \<in> T\<close>, symmetric]
  finally show "y t = ivp.solution (i\<lparr>ivp_X := X''\<rparr>) t" .
qed

end

locale unique_of_superset =
  sub?: has_solution +
  super?: unique_solution "i\<lparr>ivp_X:=X'\<rparr>" for X' +
  assumes subset: "sub.X \<subseteq> X'"
begin

lemma sub_is_solution: "super.is_solution sub.solution"
  using sub.is_solutionD[OF sub.is_solution_solution] subset
  by (intro is_solutionI) auto

lemma sub_eq_sup_solution: "\<And>t. t \<in> T \<Longrightarrow> sub.solution t = super.solution t"
  by (auto intro!: super.unique_solution sub_is_solution)

sublocale unique_solution
proof
  fix y t
  assume "sub.is_solution y"
    and "t \<in> sub.T"
  from this have t: "t \<in> super.T"
    and y: "super.is_solution y"
    by (auto intro!: sub.is_solution_on_superset_domain[OF _ subset])
  show "y t = sub.solution t"
    using y
    unfolding sub_eq_sup_solution[OF t]
    by (rule super.unique_solution[OF _ t])
qed

end

locale derivative_on_prod =
  fixes T X and f::"(real \<times> 'a::banach) \<Rightarrow> 'a" and f':: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow> 'a"
  assumes nonempty: "T \<noteq> {}" "X \<noteq> {}"
  assumes f': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow>
    (f has_derivative (f' tx)) (at tx within (T \<times> X))"

end
